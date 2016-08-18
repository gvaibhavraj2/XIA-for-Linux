#include <linux/slab.h>
#include <net/xia_dag.h>
#include <net/xia_lpm.h>
#include <linux/rwlock.h>
#include <net/xia.h>
#include <linux/vmalloc.h>


typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;


#define POPTRIE_S               18
#define POPTRIE_INIT_FIB_SIZE   4096

#define popcnt(v)               hweight64(v)
#define EXT_NH(n)       ((n)->ext ? (n)->ext->nexthop : 0)

typedef struct uint160_t{
    	uint32_t prefix1;
    	__uint128_t prefix2;
}XID;

/* Internal node */
typedef struct poptrie_node {
    	u64 leafvec;
    	u64 vector;
    	u32 base0;
    	u32 base1;
} poptrie_node_t;

/* Leaf node */
typedef u16 poptrie_leaf_t;

/*
 * Radix tree node for XID's
 */
struct radix_node160 {
    	int valid;
    	struct radix_node160 *left;
    	struct radix_node160 *right;

    	/* Next hop */
    	XID prefix;
    	int len;
    	poptrie_leaf_t nexthop;

    	/* Propagated route */
    	struct radix_node160 *ext;

    	/* Mark for update */
    	int mark;
};

/*
 * FIB mapping table
 */
struct poptrie_fib {
    	void **entries;
    	int n;
    	int sz;
	bool *valid;
};


struct popt_fib_xid_table {
	/* Root */
    	u32 root;

    	/* FIB */
    	struct poptrie_fib fib;

    	/* Memory management */
    	poptrie_node_t *nodes;
    	poptrie_leaf_t *leaves;
    	void *cnodes;
    	void *cleaves;

    	/* Size */
    	int nodesz;
    	int leafsz;

    	u32 last_base0;
    	u32 last_base1;

    	/* Direct pointing */
    	u32 *dir;
    	u32 *altdir;

    	/* RIB */
    	struct radix_node160 *radix;

    	/* Control */
    	int _allocated;

	/* RCU is currently not used on the tree, so we use a rwlock. */
	rwlock_t		writers_lock;
};

struct poptrie_stack {
	int inode;
	int idx;
	int width;
	poptrie_leaf_t nexthop;
};



static __inline__ __uint128_t
INDEX(XID a, int s, int n)
{
	if ( 0 == ((s) + (n)) ) { 
		return 0;
	} else {
		if((160-((s) + (n)))>128){
		    int temp = (160-((s) + (n)));
		    a.prefix2 = (__uint128_t)0;
		    a.prefix1 = a.prefix1 >> (temp-128);
		    a.prefix2 = (__uint128_t)a.prefix1;
		    a.prefix1  = (u32)0;
		    return a.prefix2 & ((1ULL << (n)) - 1);
		}
		else {
		    int temp = (160-((s) + (n)));
		    a.prefix2 = a.prefix2 >> temp;
		    return a.prefix2 & ((1ULL << (n)) - 1);
		}

	}
}
#define VEC_INIT(v)     ((v) = 0)
#define VEC_BT(v, i)    ((v) & (__uint128_t)1 << (i))
#define BITINDEX(v)     ((v) & ((1 << 6) - 1))
#define NODEINDEX(v)    ((v) >> 6)
#define VEC_SET(v, i)   ((v) |= (__uint128_t)1 << (i))
#define VEC_CLEAR(v, i) ((v) &= ~((__uint128_t)1 << (i)))
#define POPCNT(v)       popcnt(v)
#define ZEROCNT(v)      popcnt(~(v))
#define POPCNT_LS(v, i) popcnt((v) & (((u64)2 << (i)) - 1))
#define ZEROCNT_LS(v, i) popcnt((~(v)) & (((u64)2 << (i)) - 1))



/* Prototype declarations */
static int
_route_add(struct popt_fib_xid_table *, struct radix_node160 **, XID, int,
           poptrie_leaf_t, int, struct radix_node160 *,
	   struct radix_node160 **);
static int _route_add_propagate(struct radix_node160 *, struct radix_node160 *);
static int
_update_part(struct popt_fib_xid_table *, struct radix_node160 *, int,
             struct poptrie_stack *, u32 *, int);
static int
_update_subtree(struct popt_fib_xid_table *, struct radix_node160 *, XID, int);
static int
_descend_and_update(struct popt_fib_xid_table *, struct radix_node160 *, int,
                    struct poptrie_stack *, XID, int, int, u32 *);
static int
_update_inode_chunk(struct popt_fib_xid_table *, struct radix_node160 *, int,
                    poptrie_node_t *, poptrie_leaf_t *);
static int
_update_inode_chunk_rec(struct popt_fib_xid_table *, struct radix_node160 *, int,
                        poptrie_node_t *, poptrie_leaf_t *, int, int);
static int
_update_inode(struct popt_fib_xid_table *, struct radix_node160 *, int, poptrie_node_t *,
              poptrie_leaf_t *);
static int
_update_dp1(struct popt_fib_xid_table *, struct radix_node160 *, int, XID, int,
            int);
static int
_update_dp2(struct popt_fib_xid_table *, struct radix_node160 *, int, XID, int,
            int);
static void _update_clean_root(struct popt_fib_xid_table *, int, int);
static void _update_clean_node(struct popt_fib_xid_table *, poptrie_node_t *, int);
static void _update_clean_inode(struct popt_fib_xid_table *, int, int);
static void _update_clean_subtree(struct popt_fib_xid_table *, int);
static struct radix_node160 * _next_block(struct radix_node160 *, int, int, int);
static void
_parse_triangle(struct radix_node160 *, u64 *, struct radix_node160 *, int, int);
static void _clear_mark(struct radix_node160 *);
static int _route_change_propagate(struct radix_node160 *, struct radix_node160 *);
static int
_route_change(struct popt_fib_xid_table *, struct radix_node160 **, XID, int,
              poptrie_leaf_t, int);
static int
_route_update(struct popt_fib_xid_table *, struct radix_node160 **, XID, int,
              poptrie_leaf_t, int, struct radix_node160 *);
static int
_route_del(struct popt_fib_xid_table *, struct radix_node160 **, XID, int, int,
           struct radix_node160 *, struct radix_node160 **);
static int
_route_del_propagate(struct radix_node160 *, struct radix_node160 *,
                     struct radix_node160 *);
static u32
_rib_lookup(struct radix_node160 *, XID, int, struct radix_node160 *);
static void _release_radix160(struct radix_node160 *);
static u32
_rib_lookup_prefix(struct radix_node160 *node, XID addr, int depth, int height,
            struct radix_node160 *en);
bool match_xids(const u8 *xid1, const u8 *xid2);


/*
 * Bit scan
 */
static __inline__ int
bsr(u64 x)
{
	u64 r;

	if ( !x ) {
		return 0;
	}
	__asm__ __volatile__ ( " bsrq %1,%0 " : "=r"(r) : "r"(x) );

	return r;
}
static int power(int y)
{
	if( y == 0)
		return 1;
	else if (y%2 == 0)
		return power(y/2)*power(y/2);
	else
		return 2*power(y/2)*power(y/2);

}
static int
get_new_node(struct popt_fib_xid_table *poptrie,int n)
{
	if (poptrie->last_base1 == (1 << poptrie->nodesz))
		return -1;
	u32 temp = poptrie->last_base1;
	u32 temp1 = poptrie->last_base1;
	temp+=power(n);
	poptrie->last_base1 = temp;
	return temp1;
}

static int
get_new_leaf(struct popt_fib_xid_table *poptrie,int n)
{
	if (poptrie->last_base0 == (1 << poptrie->leafsz))
		return -1;
	u32 temp = poptrie->last_base0;
	u32 temp1 = poptrie->last_base0;
	temp+= power(n);
	poptrie->last_base0 = temp;
	return temp1;
}

void free_leaf(void){
	//To be added
}

void free_node(void){
	//To be added
}

/*
 * Add a route
 */
int
poptrie160_route_add(struct popt_fib_xid_table *poptrie, XID prefix, int len,
		     void *nexthop)
{
	struct radix_node160 *final;
	int ret;
	int i;
	int n;

	/* Find the FIB entry mapping first */
	for (i = 0; i < poptrie->fib.n; i++) {
		if (poptrie->fib.entries[i] == nexthop &&
		    poptrie->fib.valid[i]) {
			/* Found the matched entry */
			n = i;
			break;
		}
	}

	if (i == poptrie->fib.n) {
		/* No matching FIB entry was found */
		if (poptrie->fib.n >= poptrie->fib.sz) {
		/* The FIB mapping table is full */
			return -1;
		}

		/* Append new FIB entry */
		n = poptrie->fib.n;
		poptrie->fib.entries[n] = nexthop;
		poptrie->fib.valid[n] = true;
		poptrie->fib.n++;
	}

	/* Insert the prefix to the radix tree, then
	 * incrementally update the poptrie data structure.
	 */
	ret = _route_add(poptrie, &poptrie->radix, prefix, len, n, 0, NULL,
			 &final);
	if (ret < 0)
		return ret;
	ret = _update_subtree(poptrie, final, prefix, ret);
	if (ret < 0)
		return ret;

	return 0;
}

/*
 * Change a route
 */
 
int
poptrie160_route_change(struct popt_fib_xid_table *poptrie, XID prefix, int len,
                     void *nexthop)
{
	int i;
	int n;

	for ( i = 0; i < poptrie->fib.n; i++ ) {
	if ( poptrie->fib.entries[i] == nexthop && poptrie->fib.valid[i] ) {
	    n = i;
	    break;
	}
	}
	if ( i == poptrie->fib.n ) {
		n = poptrie->fib.n;
		poptrie->fib.entries[n] = nexthop;
		poptrie->fib.valid[n] = true;
		poptrie->fib.n++;
	}

	return _route_change(poptrie, &poptrie->radix, prefix, len, n, 0);
}

/*
 * Update a route (add if not exists like BGP update)
 */
int
poptrie160_route_update(struct popt_fib_xid_table *poptrie, XID prefix, int len,
                      void *nexthop)
{
	int ret;
	int i;
	int n;

	for ( i = 0; i < poptrie->fib.n; i++ ) {
	if ( poptrie->fib.entries[i] == nexthop && poptrie->fib.valid[i]) {
	    n = i;
	    break;
	}
	}
	if ( i == poptrie->fib.n ) {
		n = poptrie->fib.n;
		poptrie->fib.entries[n] = nexthop;
		poptrie->fib.valid[n] = true;
		poptrie->fib.n++;
	}

	/* Insert to the radix tree */
	ret = _route_update(poptrie, &poptrie->radix, prefix, len, n, 0, NULL);
	if ( ret < 0 ) {
		
	}
	return 0;
}

/*
 * Delete a route
 */

int
poptrie160_route_del(struct popt_fib_xid_table *poptrie, XID prefix, int len)
{
	/* Search and delete the corresponding entry */
	struct radix_node160 *final;
	int ret = _route_del(poptrie, &poptrie->radix, prefix, len, 0, NULL, &final);
	if (ret < 0)		
		return ret;		
	ret = _update_subtree(poptrie, final, prefix, ret);		
	if (ret < 0)		
		return ret;
	return 0;
	
}

/*
 * Lookup a route by the specified address
 */
void *
poptrie160_lookup(struct popt_fib_xid_table *poptrie, XID addr)
{
	int inode;
	int base;
	int idx;
	int pos;

	/* Top tier */
	idx = INDEX(addr, 0, POPTRIE_S);
	pos = POPTRIE_S;
	base = poptrie->root;

	/* Direct pointing */
	if ( poptrie->dir[idx] & ((u32)1 << 31) ) {
		return poptrie->fib.entries[poptrie->dir[idx] & (((u32)1 << 31) - 1)];
	} else {
		base = poptrie->dir[idx];
		idx = INDEX(addr, pos, 6);
		pos += 6;
	}

	for ( ;; ) {
	inode = base;
	if ( VEC_BT(poptrie->nodes[inode].vector, idx) ) {
	    /* Internal node */
	    base = poptrie->nodes[inode].base1;
	    idx = POPCNT_LS(poptrie->nodes[inode].vector, idx);
	    /* Next internal node index */
	    base = base + (idx - 1);
	    /* Next node vector */
	    idx = INDEX(addr, pos, 6);
	    pos += 6;
	} else {
	    /* Leaf */
	    base = poptrie->nodes[inode].base0;
	    idx = POPCNT_LS(poptrie->nodes[inode].leafvec, idx);
	    return poptrie->fib.entries[poptrie->leaves[base + idx - 1]];
	}
	}

	/* Not to be reached here, but put this to dismiss a compiler warning. */
	return 0;
}



/*
 * Lookup the next hop from the radix tree (RIB table)
 */
void *
poptrie160_rib_lookup(struct popt_fib_xid_table *poptrie, XID addr)
{
	return poptrie->fib.entries[_rib_lookup(poptrie->radix, addr, 0, NULL)];
}

/*
 * Update the partial tree
 */
static int
_update_part(struct popt_fib_xid_table *poptrie, struct radix_node160 *tnode, int inode,
             struct poptrie_stack *stack, u32 *root, int alt)
{
	struct poptrie_node *cnodes;
	int ret;
	poptrie_leaf_t sleaf;
	int vcomp;
	int nroot;
	int oroot;
	int p;
	int n;
	int base1;
	int base0;
	int i;
	int j;
	poptrie_leaf_t leaves[1 << 6];
	u64 prev;
	struct poptrie_node *node;
	u64 vector;
	u64 leafvec;

	stack--;

	/* Build the updated part */
	if ( stack->idx < 0 ) {
		cnodes = kmalloc(sizeof(struct poptrie_node), GFP_ATOMIC);
		if ( NULL == cnodes ) {
		    return -1;
		}

		ret = _update_inode_chunk_rec(poptrie, tnode, inode, cnodes, &sleaf, 0,
		                      0);
		if ( ret < 0 ) {
		    return -1;
		}
		if ( ret > 0 ) {
		    /* Clean */
		    cnodes[0].base0 = -1;

		    /* Replace the root with an atomic instruction */
		    nroot = ((u32)1 << 31) | sleaf;
		    __asm__ __volatile__ ("lock xchgl %%eax,%0"
		                  : "=m"(*root), "=a"(oroot) : "a"(nroot));
		    if ( !alt ) {
			_update_clean_subtree(poptrie, oroot);
			if ( (int)oroot >= 0 ) {
				free_node();
			}
		    }

		    return 0;
		}

		/* Replace the root */
		nroot = get_new_node(poptrie,0);
		if ( nroot < 0 ) {
		    return -1;
		}
		memcpy(poptrie->nodes + nroot, cnodes, sizeof(struct poptrie_node));
		oroot = poptrie->root;
		poptrie->root = nroot;

		/* Replace the root with an atomic instruction */
		__asm__ __volatile__ ("lock xchgl %%eax,%0"
		              : "=m"(*root), "=a"(oroot) : "a"(nroot));

		/* Clean */
		if ( !alt && !(oroot & ((u32)1 << 31)) ) {
		    _update_clean_root(poptrie, nroot, oroot);
		}

		return 0;
	}

	/* Allocate */
	#if POPTRIE_S < 6
		cnodes = kmalloc(sizeof(struct poptrie_node), GFP_ATOMIC);
	#else
		cnodes = kmalloc(sizeof(struct poptrie_node) << (POPTRIE_S - 6),
			GFP_ATOMIC);
	#endif
	if ( NULL == cnodes ) {
		return -1;
	}

	/* Not the root */
	ret = _update_inode_chunk_rec(poptrie, tnode, inode, cnodes, &sleaf, 0, 0);
	if ( ret < 0 ) {
		return -1;
	}
	if ( ret > 0 ) {
		vcomp = 1;
		cnodes[0].base0 = -1;
	} else {
		vcomp = 0;
	}

	while ( vcomp && stack->idx >= 0 ) {
		/* Perform vertical compresion */
		if ( stack->inode < 0 ) {
		    if ( stack->nexthop != sleaf ) {
			/* Compression ends here */
			vcomp = 0;
			for ( i = 0; i < (1 << (stack->width - 6)); i++ ) {
			    VEC_INIT(cnodes[i].vector);
			    VEC_INIT(cnodes[i].leafvec);
			    if ( i == NODEINDEX(stack->idx) ) {
				if ( 0 == BITINDEX(stack->idx) ) {
				    base0 = get_new_leaf(poptrie,1);
				    if ( base0 < 0 ) {
					return -1;
				    }
				    poptrie->leaves[base0] = sleaf;
				    poptrie->leaves[base0 + 1] = stack->nexthop;
				    VEC_SET(cnodes[i].leafvec, 0);
				    VEC_SET(cnodes[i].leafvec, 1);
				} else if ( ((1 << 6) - 1) == BITINDEX(stack->idx) ) {
				    base0 = get_new_leaf(poptrie,1);
				    if ( base0 < 0 ) {
					return -1;
				    }
				    poptrie->leaves[base0] = stack->nexthop;
				    poptrie->leaves[base0 + 1] = sleaf;
				    VEC_SET(cnodes[i].leafvec, 0);
				    VEC_SET(cnodes[i].leafvec, BITINDEX(stack->idx));
				} else {
				    base0 = get_new_leaf(poptrie,2);
				    if ( base0 < 0 ) {
					return -1;
				    }
				    poptrie->leaves[base0] = stack->nexthop;
				    poptrie->leaves[base0 + 1] = sleaf;
				    poptrie->leaves[base0 + 2] = stack->nexthop;
				    VEC_SET(cnodes[i].leafvec, 0);
				    VEC_SET(cnodes[i].leafvec, BITINDEX(stack->idx));
				    VEC_SET(cnodes[i].leafvec,
					    BITINDEX(stack->idx) + 1);
				}
			    } else {
				base0 = get_new_leaf(poptrie,0);
				if ( base0 < 0 ) {
				    return -1;
				}
				poptrie->leaves[base0] = stack->nexthop;
				VEC_SET(cnodes[i].leafvec, 0);
			    }
			    cnodes[i].base0 = base0;
			    cnodes[i].base1 = -1;
			}
		    }
		} else {
		    node = &poptrie->nodes[stack->inode + NODEINDEX(stack->idx)];
		    vector = node->vector;
		    if ( VEC_BT(node->vector, BITINDEX(stack->idx)) ) {
			/* Internal node to leaf */
			VEC_CLEAR(vector, BITINDEX(stack->idx));
			VEC_INIT(leafvec);
			n = 0;
			prev = (u64)-1;
			for ( i = 0; i < (1 << 6); i++ ) {
			    if ( !VEC_BT(vector, i) ) {
				if ( i == BITINDEX(stack->idx) ) {
				    if ( sleaf != prev ) {
					leaves[n] = sleaf;
					VEC_SET(leafvec, i);
					n++;
				    }
				    prev = sleaf;
				} else {
				    p = POPCNT_LS(node->leafvec, i);
				    if ( poptrie->leaves[node->base0 + p - 1]
					 != prev ) {
					leaves[n]
					    = poptrie->leaves[node->base0 + p - 1];
					VEC_SET(leafvec, i);
					n++;
				    }
				    prev = poptrie->leaves[node->base0 + p - 1];
				}
			    }
			}

			if ( 1 != n || 0 != POPCNT(vector) || (stack - 1)->idx < 0 ) {
			    vcomp = 0;
			    base0 = get_new_leaf(poptrie,bsr(n - 1) + 1);
			    if ( base0 < 0 ) {
				return -1;
			    }
			    memcpy(poptrie->leaves + base0, leaves,
				   sizeof(poptrie_leaf_t) * n);

			    p = POPCNT(vector);
			    n = p;
			    if ( n > 0 ) {
				base1 = get_new_node(poptrie,bsr(n - 1) + 1);
				if ( base1 < 0 ) {
				    return -1;
				}
			    } else {
				base1 = -1;
			    }

			    /* Copy all */
			    n = 0;
			    for ( i = 0; i < (1 << 6); i++ ) {
				if ( VEC_BT(vector, i) ) {
				    p = POPCNT_LS(node->vector, i);
				    p = (p - 1);
				    memcpy(&poptrie->nodes[base1 + n],
					   &poptrie->nodes[node->base1 + p],
					   sizeof(poptrie_node_t));
				    n += 1;
				}
			    }

			    memcpy(cnodes, poptrie->nodes + stack->inode,
				   sizeof(poptrie_node_t) << (stack->width - 6));
			    cnodes[NODEINDEX(stack->idx)].vector = vector;
			    cnodes[NODEINDEX(stack->idx)].leafvec = leafvec;
			    cnodes[NODEINDEX(stack->idx)].base0 = base0;
			    cnodes[NODEINDEX(stack->idx)].base1 = base1;
			}
		    } else {
			/* Leaf node is changed */
			VEC_INIT(leafvec);
			n = 0;
			prev = (u64)-1;
			for ( i = 0; i < (1 << 6); i++ ) {
			    if ( !VEC_BT(vector, i) ) {
				if ( i == BITINDEX(stack->idx) ) {
				    if ( sleaf != prev ) {
					leaves[n] = sleaf;
					VEC_SET(leafvec, i);
					n++;
				    }
				    prev = sleaf;
				} else {
				    p = POPCNT_LS(node->leafvec, i);
				    if ( poptrie->leaves[node->base0 + p - 1]
					 != prev ) {
					leaves[n]
					    = poptrie->leaves[node->base0 + p - 1];
					VEC_SET(leafvec, i);
					n++;
				    }
				    prev =  poptrie->leaves[node->base0 + p - 1];
				}
			    }
			}

			if ( 1 != n || 0 != POPCNT(vector) || (stack - 1)->idx < 0 ) {
			    vcomp = 0;
			    if ( node->leafvec == leafvec ) {
				/* Nothing has changed */
				return 0;
			    }

			    base0 = get_new_leaf(poptrie,bsr(n - 1) + 1);
			    if ( base0 < 0 ) {
				return -1;
			    }
			    memcpy(poptrie->leaves + base0, leaves,
				   sizeof(poptrie_leaf_t) * n);

			    memcpy(cnodes, poptrie->nodes + stack->inode,
				   sizeof(poptrie_node_t) << (stack->width - 6));
			    cnodes[NODEINDEX(stack->idx)].vector = vector;
			    cnodes[NODEINDEX(stack->idx)].leafvec = leafvec;
			    cnodes[NODEINDEX(stack->idx)].base0 = base0;
			}
		    }
		}

		stack--;
	}

	while ( stack->idx >= 0 ) {
	if ( stack->inode < 0 ) {
	    /* Create a new node */
	    base1 = get_new_node(poptrie,0);
	    if ( base1 < 0 ) {
		return -1;
	    }
	    memcpy(poptrie->nodes + base1, cnodes, sizeof(poptrie_node_t));
	    /* Build the next one */
	    for ( i = 0; i < (1 << (stack->width - 6)); i++ ) {
		VEC_INIT(cnodes[i].vector);
		VEC_INIT(cnodes[i].leafvec);
		cnodes[i].base1 = -1;
		cnodes[i].base0 = -1;
	    }
	    VEC_SET(cnodes[NODEINDEX(stack->idx)].vector, BITINDEX(stack->idx));
	    cnodes[NODEINDEX(stack->idx)].base1 = base1;

	    for ( i = 0; i < (1 << (stack->width - 6)); i++ ) {
		base0 = get_new_leaf(poptrie,0);
		if ( base0 < 0 ) {
		    return -1;
		}
		poptrie->leaves[base0] = stack->nexthop;
		if ( VEC_BT(cnodes[i].vector, 0) ) {
		    VEC_SET(cnodes[i].leafvec, 1);
		} else {
		    VEC_SET(cnodes[i].leafvec, 0);
		}
		cnodes[i].base0 = base0;
	    }
	} else {
	    /* Parent internal node is specified */
	    node = &poptrie->nodes[stack->inode + NODEINDEX(stack->idx)];
	    if ( VEC_BT(node->vector, BITINDEX(stack->idx)) ) {
		/* Same vector, then allocate and replace */
		p = POPCNT(node->vector);
		n = p;
		base1 = get_new_node(poptrie,bsr(n - 1) + 1);
		if ( base1 < 0 ) {
		    return -1;
		}
		/* Copy all */
		n = 0;
		for ( i = 0; i < (1 << 6); i++ ) {
		    if ( VEC_BT(node->vector, i) ) {
		        if ( i == BITINDEX(stack->idx) ) {
		            memcpy(&poptrie->nodes[base1 + n], cnodes,
		                   sizeof(poptrie_node_t));
		        } else {
		            memcpy(&poptrie->nodes[base1 + n],
		                   &poptrie->nodes[node->base1 + n],
		                   sizeof(poptrie_node_t));
		        }
		        n += 1;
		    }
		}
		oroot = node->base1;
		node->base1 = base1;

		_update_clean_node(poptrie, node, oroot);

		return 0;
	    } else {
		/* Different vector, then allocate and go up */
		vector = node->vector;
		VEC_SET(vector, BITINDEX(stack->idx));

		p = POPCNT(vector);
		n = p;
		base1 = get_new_node(poptrie,bsr(n - 1) + 1);
		if ( base1 < 0 ) {
		    return -1;
		}

		VEC_INIT(leafvec);
		n = ZEROCNT(vector);
		if ( n > 0 ) {
		    n = 0;
		    prev = (u64)-1;
		    for ( i = 0; i < (1 << 6); i++ ) {
		        if ( !VEC_BT(vector, i) ) {
		            p = POPCNT_LS(node->leafvec, i);
		            if ( poptrie->leaves[node->base0 + p - 1]
		                 != prev ) {
		                leaves[n]
		                    = poptrie->leaves[node->base0 + p - 1];
		                VEC_SET(leafvec, i);
		                prev = poptrie->leaves[node->base0 + p - 1];
		                n++;
		            }
		        }
		    }
		    base0 = get_new_leaf(poptrie,bsr(n - 1)+1);
		    if ( base0 < 0 ) {
		        return -1;
		    }
		    memcpy(poptrie->leaves + base0, leaves,
		           sizeof(poptrie_leaf_t) * n);
		} else {
		    base0 = -1;
		}

		/* Copy all */
		n = 0;
		j = 0;
		for ( i = 0; i < (1 << 6); i++ ) {
		    if ( VEC_BT(node->vector, i) ) {
		        memcpy(&poptrie->nodes[base1 + n],
		               &poptrie->nodes[node->base1 + j],
		               sizeof(poptrie_node_t));
		        n += 1;
		        j += 1;
		    } else if ( i == BITINDEX(stack->idx) ) {
		        memcpy(&poptrie->nodes[base1 + n], cnodes,
		               sizeof(poptrie_node_t));
		        n += 1;
		    }
		}

		memcpy(cnodes, poptrie->nodes + stack->inode,
		       sizeof(poptrie_node_t) << (stack->width - 6));
		cnodes[NODEINDEX(stack->idx)].base1 = base1;
		cnodes[NODEINDEX(stack->idx)].base0 = base0;
		cnodes[NODEINDEX(stack->idx)].vector = vector;
		cnodes[NODEINDEX(stack->idx)].leafvec = leafvec;
	    }
	}
	stack--;
	}

	/* Replace the root */
	nroot = get_new_leaf(poptrie,0);
	if ( nroot < 0 ) {
		return -1;
	}
	memcpy(poptrie->nodes + nroot, cnodes, sizeof(poptrie_node_t));
	oroot = poptrie->root;
	poptrie->root = nroot;

	/* Swap */
	__asm__ __volatile__ ("lock xchgl %%eax,%0"
		          : "=m"(*root), "=a"(oroot) : "a"(nroot));

	/* Clean */
	if ( !alt && !(oroot & ((u32)1<<31)) ) {
		_update_clean_root(poptrie, nroot, oroot);
	}

	return 0;
}

/*
 * Updated the marked subtree
 */
static int
_update_subtree(struct popt_fib_xid_table *poptrie, struct radix_node160 *node,
                XID prefix, int depth)
{
	int ret;
	struct poptrie_stack stack[160 / 6 + 1];
	struct radix_node160 *ntnode;
	int idx;
	int i;
	u32 *tmpdir;

	stack[0].inode = -1;
	stack[0].idx = -1;
	stack[0].width = -1;

	if ( depth < POPTRIE_S ) {
		/* Copy first */
		memcpy(poptrie->altdir, poptrie->dir, sizeof(u32) << POPTRIE_S);
		ret = _update_dp1(poptrie, poptrie->radix, 1, prefix, depth, 0);

		/* Replace the root */
		tmpdir = poptrie->dir;
		poptrie->dir = poptrie->altdir;
		poptrie->altdir = tmpdir;

		/* Clean */
		idx = INDEX(prefix, 0, POPTRIE_S) >> (POPTRIE_S - depth) << (POPTRIE_S - depth);
		for ( i = 0; i < (1 << (POPTRIE_S - depth)); i++ ) {
			if (poptrie->dir[idx + i] !=
			    poptrie->altdir[idx + i] ) {
				if ( (poptrie->dir[idx + i] & ((u32)1 << 31))
					&& !(poptrie->altdir[idx + i] & ((u32)1 << 31)) ) {
					_update_clean_subtree(poptrie, poptrie->altdir[idx + i]);
					free_node();
				} else if ( !(poptrie->altdir[idx + i] & ((u32)1 << 31)) ) {
					_update_clean_root(poptrie, poptrie->dir[idx + i], poptrie->altdir[idx + i]);
				}
			}
		}
	} else if ( depth == POPTRIE_S ) {
		ret = _update_dp1(poptrie, poptrie->radix, 0, prefix, depth, 0);
	} else {
		idx = INDEX(prefix, 0, POPTRIE_S);
		ntnode = _next_block(poptrie->radix, idx, 0, POPTRIE_S);
		/* Get the corresponding node */
		if ( poptrie->dir[idx] & ((u32)1 << 31) ) {
			/* Leaf */
			ret = _descend_and_update(poptrie, ntnode, -1, &stack[1], prefix,
		                      depth, POPTRIE_S, &poptrie->dir[idx]);
		} else {
			/* Node */
			ret = _descend_and_update(poptrie, ntnode, poptrie->dir[idx],
		                      &stack[1], prefix, depth, POPTRIE_S,
		                      &poptrie->dir[idx]);
		}
	}

	if ( ret < 0 ) {
		return -1;
	}

	/* Clear marks */
	_clear_mark(node);

	return 0;
}

/*
 * Update the marked parts while traversing from the root to the marked bottom
 */
static int
_descend_and_update(struct popt_fib_xid_table *poptrie, struct radix_node160 *tnode,
                    int inode, struct poptrie_stack *stack, XID prefix,
                    int len, int depth, u32 *root)
{
	int idx;
	int p;
	int n;
	struct poptrie_node *node;
	struct radix_node160 *ntnode;
	int width;

	/* Get the corresponding child */
	if ( 0 == depth ) {
		width = POPTRIE_S;
	} else {
		width = 6;
	}

	if ( len <= depth + width ) {
	/* This is the top of the marked part */
		return _update_part(poptrie, tnode, inode, stack, root, 0);
	} else {
		/* This is not the top of the marked part, then traverse to a child */
		idx = INDEX(prefix, depth, width);

		if ( inode < 0 ) {
		    /* The root of the next block */
		    ntnode = _next_block(tnode, idx, 0, width);
		    if ( NULL == ntnode ) {
			return _update_part(poptrie, tnode, inode, stack, root, 0);
		    } else {
			stack->inode = inode;
			stack->idx = idx;
			stack->width = width;
			stack->nexthop = EXT_NH(tnode);
			stack++;
			return _descend_and_update(poptrie, ntnode, -1, stack, prefix,
				                   len, depth + width, root);
		    }
		}

		/* Get the corresponding node */
		node = poptrie->nodes + inode + NODEINDEX(idx);

		/* Check the vector */
		if ( VEC_BT(node->vector, BITINDEX(idx)) ) {
		    /* Internal node, then traverse to the child */
		    p = POPCNT_LS(node->vector, BITINDEX(idx));
		    n = (p - 1);
		    /* The root of the next block */
		    ntnode = _next_block(tnode, idx, 0, width);
		    if ( NULL == ntnode ) {
			return _update_part(poptrie, tnode, inode, stack, root, 0);
		    } else {
			stack->inode = inode;
			stack->idx = idx;
			stack->width = width;
			stack++;
			return _descend_and_update(poptrie, ntnode, node->base1 + n,
				                   stack, prefix, len, depth + width,
				                   root);
		    }
		} else {
		    /* Leaf node, then update from this node */
		    /* The root of the next block */
		    ntnode = _next_block(tnode, idx, 0, width);
		    if ( NULL == ntnode ) {
			return _update_part(poptrie, tnode, inode, stack, root, 0);
		    } else {
			stack->inode = inode;
			stack->idx = idx;
			stack->width = width;
			stack++;
			return _descend_and_update(poptrie, ntnode, -1, stack, prefix,
				                   len, depth + width, root);
		    }
		}
	}

	return 0;
}

/*
 * Update an internal node chunk
 */
static int
_update_inode_chunk(struct popt_fib_xid_table *poptrie, struct radix_node160 *node,
                    int inode, poptrie_node_t *nodes, poptrie_leaf_t *leaf)
{
	int ret;

	ret = _update_inode_chunk_rec(poptrie, node, inode, nodes, leaf, 0, 0);
	if ( ret > 0 ) {
	/* Clean */
	free_node();
	}

	return ret;
}
static int
_update_inode_chunk_rec(struct popt_fib_xid_table *poptrie, struct radix_node160 *node,
                        int inode, poptrie_node_t *nodes, poptrie_leaf_t *leaf,
                        int pos, int r)
{
	int ret;
	int ret0;
	int ret1;
	struct radix_node160 tmp;
	poptrie_leaf_t sleaf0;
	poptrie_leaf_t sleaf1;

	if ( 0 == r ) {
	if ( NULL != leaf ) {
	    ret = _update_inode(poptrie, node, inode + pos, nodes + pos,
		                &sleaf0);
	    if ( ret < 0 ) {
		return -1;
	    }
	    if ( ret > 0 ) {
		*leaf = sleaf0;
	    }
	} else {
	    ret = _update_inode(poptrie, node, inode + pos, nodes + pos, NULL);
	    if ( ret < 0 ) {
		return -1;
	    }
	}
	return ret;
	}

	/* Decrement */
	r--;

	/* Left */
	if ( node->left ) {
		ret0 = _update_inode_chunk_rec(poptrie, node->left, inode, nodes,
		                       leaf ? &sleaf0 : NULL, pos, r);
	if ( ret0 < 0 ) {
	    return -1;
	}
	} else {
		tmp.left = NULL;
		tmp.right = NULL;
		tmp.ext = node->ext;
		ret0 = _update_inode_chunk_rec(poptrie, &tmp, inode, nodes,
				               leaf ? &sleaf0 : NULL, pos, r);
		if ( ret0 < 0 ) {
		    return -1;
		}
	}

	/* Right */
	if ( node->right ) {
		ret1 = _update_inode_chunk_rec(poptrie, node->right, inode, nodes,
				               leaf ? &sleaf1 : NULL,
				               pos + (1 << r), r);
		if ( ret1 < 0 ) {
		    return -1;
		}
	} else {
		tmp.left = NULL;
		tmp.right = NULL;
		tmp.ext = node->ext;
		ret1 = _update_inode_chunk_rec(poptrie, &tmp, inode, nodes,
				               leaf ? &sleaf1 : NULL,
				               pos + (1 << r), r);
		if ( ret1 < 0 ) {
		    return -1;
		}
		}
		if ( ret0 > 0 && ret1 > 0 && NULL != leaf && sleaf0 == sleaf1 ) {
			*leaf = sleaf0;
			return 1;
		}

		return 0;
}

/*
 * Update an internal node
 */
static int
_update_inode(struct popt_fib_xid_table *poptrie, struct radix_node160 *node, int inode,
              poptrie_node_t *n, poptrie_leaf_t *leaf)
{
	int i;
	u64 vector;
	u64 leafvec;
	int nvec;
	int nlvec;
	struct radix_node160 nodes[1 << 6];
	poptrie_node_t children[1 << 6];
	poptrie_leaf_t leaves[1 << 6];
	u64 prev;
	int base0;
	int base1;
	int ret;
	poptrie_leaf_t sleaf;
	int p;
	int ninode;

	/* Parse triangle */
	VEC_INIT(vector);
	_parse_triangle(node, &vector, nodes, 0, 0);

	/* Traverse children first */
	VEC_INIT(leafvec);
	prev = (u64)-1;
	nvec = 0;
	nlvec = 0;
	for ( i = 0; i < (1 << 6); i++ ) {
	if ( VEC_BT(vector, i) ) {
	    /* Internal node */
	    if ( (nodes[i].left && nodes[i].left->mark)
		 || (nodes[i].right && nodes[i].right->mark)
		 || inode < 0 ) {
		/* One or more child is marked */
		if ( inode >= 0 ) {
		    if ( VEC_BT(poptrie->nodes[inode].vector, i) ) {
		        p = POPCNT_LS(poptrie->nodes[inode].vector, i);
		        ninode = poptrie->nodes[inode].base1 + (p - 1);
		    } else {
		        ninode = -1;
		    }
		} else {
		    ninode = -1;
		}
		ret = _update_inode_chunk(poptrie, &nodes[i], ninode,
		                          children + i, &sleaf);
		if ( ret < 0 ) {
		    return -1;
		}
		if ( ret > 0 ) {
		    /* The vertical compression is performed then check the
		       horizontal compression */
		    VEC_CLEAR(vector, i);
		    if ( prev != sleaf ) {
		        VEC_SET(leafvec, i);
		        leaves[nlvec] = sleaf;
		        nlvec++;
		    }
		    prev = sleaf;
		} else {
		    /* Not compressed */
		    nvec++;
		}
	    } else {
		/* None of children is marked, then copy */
		if ( VEC_BT(poptrie->nodes[inode].vector, i) ) {
		    /* Connect to the working internal node */
		    p = POPCNT_LS(poptrie->nodes[inode].vector, i);
		    memcpy(children + i,
		           poptrie->nodes + poptrie->nodes[inode].base1
		           + (p - 1), sizeof(poptrie_node_t));
		    nvec++;
		} else {
		    /* The working child is a leaf node */
		    VEC_CLEAR(vector, i);
		    p = POPCNT_LS(poptrie->nodes[inode].leafvec, i);
		    sleaf
		        = poptrie->leaves[poptrie->nodes[inode].base0 + p - 1];
		    if ( prev != sleaf ) {
		        VEC_SET(leafvec, i);
		        leaves[nlvec] = sleaf;
		        nlvec++;
		    }
		    prev = sleaf;
		}
	    }
	} else {
	    /* Leaf compression */
	    if ( prev != EXT_NH(&nodes[i]) ) {
		VEC_SET(leafvec, i);
		leaves[nlvec] = EXT_NH(&nodes[i]);
		nlvec++;
	    }
	    prev = EXT_NH(&nodes[i]);
	}
	}

	/* Internal nodes */
	base1 = -1;
	if ( nvec > 0 ) {
		p = nvec;
		base1 = get_new_node(poptrie,bsr(p - 1) + 1);
		if ( base1 < 0 ) {
		    return -1;
		}
	}
	/* Leaves */
	base0 = -1;
	if ( nlvec > 0 ) {
		p = nlvec;
		base0 = get_new_leaf(poptrie,bsr(p - 1)+1);
		if ( base0 < 0 ) {
		    if ( base1 >= 0 ) {
			free_leaf();
		    }
		    return -1;
		}
	}

	/* Internal nodes */
	int num = 0;
	for ( i = 0; i < (1 << 6); i++ ) {
	if ( VEC_BT(vector, i) ) {
	    memcpy(&poptrie->nodes[base1 + num], &children[i],
		   sizeof(poptrie_node_t));
	    num++;
	}
	}
	/* Leaves */
	for ( i = 0; i < nlvec; i++ ) {
		poptrie->leaves[base0 + i] = leaves[i];
	}
	n->vector = vector;
	n->leafvec = leafvec;
	n->base0 = base0;
	n->base1 = base1;

	if ( 0 == nvec && 1 == nlvec && NULL != leaf ) {
		/* Only one leaf belonging to this internal node, then compress
		   this (but can't do this for the top tier when leaf is NULL) */
		*leaf = leaves[0];
		return 1;
	}

	return 0;
}

/*
 * Update a partial tree (direct pointing)
 */
static int
_update_dp1(struct popt_fib_xid_table *poptrie, struct radix_node160 *tnode, int alt,
            XID prefix, int len, int depth)
{
	int i;
	int idx;

	if ( depth == len ) {
		return _update_dp2(poptrie, tnode, alt, prefix, len, depth);
	}
	int temp = 160-depth-1;
	if(temp<128){
	if(prefix.prefix2 >> (temp) & 1){
		/* Right */
	    if ( tnode->right ) {
		return _update_dp1(poptrie, tnode->right, alt, prefix, len,
		                   depth + 1);
	    } else {
		idx = INDEX(prefix, 0, POPTRIE_S)
		    >> (POPTRIE_S - len)
		    << (POPTRIE_S - len);
		for ( i = 0; i < (1 << (POPTRIE_S - len)); i++ ) {
		    if ( alt ) {
		        poptrie->altdir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		    } else {
		        poptrie->dir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		        _update_clean_subtree(poptrie, poptrie->dir[idx + i]);
		        if ( (int)poptrie->dir[idx + i] >= 0 ) {
		            free_leaf();
		        }
		    }
		}
		return 0;
	    }
	   } 
	else{
	    /* Left */
	    if ( tnode->left ) {
		return _update_dp1(poptrie, tnode->left, alt, prefix, len,
		                   depth + 1);
	    } else {
		idx = INDEX(prefix, 0, POPTRIE_S)
		    >> (POPTRIE_S - len)
		    << (POPTRIE_S - len);
		for ( i = 0; i < (1 << (POPTRIE_S - len)); i++ ) {
		    if ( alt ) {
		        poptrie->altdir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		    } else {
		        poptrie->dir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		        _update_clean_subtree(poptrie, poptrie->dir[idx + i]);
		        if ( (int)poptrie->dir[idx + i] >= 0 ) {
		            free_leaf();
		        }
		    }
		}
		return 0;
	    }
	}    
	    }
	else{
	    if(prefix.prefix1 >> (temp-160) & 1){
		        /* Right */
		if ( tnode->right ) {
		    return _update_dp1(poptrie, tnode->right, alt, prefix, len,
		                       depth + 1);
		} else {
		    idx = INDEX(prefix, 0, POPTRIE_S)
		        >> (POPTRIE_S - len)
		        << (POPTRIE_S - len);
		    for ( i = 0; i < (1 << (POPTRIE_S - len)); i++ ) {
		        if ( alt ) {
		            poptrie->altdir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		        } else {
		            poptrie->dir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		            _update_clean_subtree(poptrie, poptrie->dir[idx + i]);
		            if ( (int)poptrie->dir[idx + i] >= 0 ) {
		                free_leaf();
		            }
		        }
		    }
		    return 0;
		}
	    }
	    else{
		if ( tnode->left ) {
		return _update_dp1(poptrie, tnode->left, alt, prefix, len,
		                   depth + 1);
	    } else {
		idx = INDEX(prefix, 0, POPTRIE_S)
		    >> (POPTRIE_S - len)
		    << (POPTRIE_S - len);
		for ( i = 0; i < (1 << (POPTRIE_S - len)); i++ ) {
		    if ( alt ) {
		        poptrie->altdir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		    } else {
		        poptrie->dir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		        _update_clean_subtree(poptrie, poptrie->dir[idx + i]);
		        if ( (int)poptrie->dir[idx + i] >= 0 ) {
		            free_leaf();
		        }
		    }
		}
		return 0;
	    }
	    }

	}    


}
static int
_update_dp2(struct popt_fib_xid_table *poptrie, struct radix_node160 *tnode, int alt,
            XID prefix, int len, int depth)
{
	int i;
	int idx;
	int ret;
	struct poptrie_stack stack[160 / 6 + 1];

	if ( depth == POPTRIE_S ) {
		idx = INDEX(prefix, 0, POPTRIE_S);
		stack[0].inode = -1;
		stack[0].idx = -1;
		stack[0].width = -1;

		if ( poptrie->dir[idx] & ((u32)1 << 31) ) {
		    if ( alt ) {
			ret = _update_part(poptrie, tnode, -1, &stack[1],
				           &poptrie->altdir[idx], alt);
		    } else {
			ret = _update_part(poptrie, tnode, -1, &stack[1],
				           &poptrie->dir[idx], alt);
		    }
		} else {
		    if ( alt ) {
			ret = _update_part(poptrie, tnode, poptrie->dir[idx], &stack[1],
				           &poptrie->altdir[idx], alt);
		    } else {
			ret = _update_part(poptrie, tnode, poptrie->dir[idx], &stack[1],
				           &poptrie->dir[idx], alt);
		    }
		}
		return ret;
	}

	if ( tnode->left ) {
		_update_dp2(poptrie, tnode->left, alt, prefix, len, depth + 1);
	} else {
		idx = INDEX(prefix, 0, POPTRIE_S)
	    		>> (POPTRIE_S - depth) << (POPTRIE_S - depth);
	for ( i = 0; i < (1 << (POPTRIE_S - depth - 1)); i++ ) {
	    if ( alt ) {
		poptrie->altdir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
	    } else {
		poptrie->dir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		_update_clean_subtree(poptrie, poptrie->dir[idx + i]);
		if ( (int)poptrie->dir[idx + i] >= 0 ) {
		    free_node();
		}
	    }
	}
	}
	if ( tnode->right ) {
		int temp = 160-depth-1;
		if(temp<128){
		    prefix.prefix2 |= 1<< temp;
		}
		else{
		    prefix.prefix1 |= 1<< (temp-128);
		}
		return _update_dp2(poptrie, tnode->right, alt, prefix, len, depth + 1);
	} else {
	idx = INDEX(prefix, 0, POPTRIE_S)
	    >> (POPTRIE_S - depth)
	    << (POPTRIE_S - depth);
	idx += 1 << (POPTRIE_S - depth - 1);
	for ( i = 0; i < (1 << (POPTRIE_S - depth - 1)); i++ ) {
	    if ( alt ) {
		poptrie->altdir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
	    } else {
		poptrie->dir[idx + i] = ((u32)1 << 31) | EXT_NH(tnode);
		_update_clean_subtree(poptrie, poptrie->dir[idx + i]);
		if ( (int)poptrie->dir[idx + i] >= 0 ) {
		   free_node();
		}
	    }
	}
	}

	return 0;
}

/*
 * Update and clean from the root
 */
static void
_update_clean_root(struct popt_fib_xid_table *poptrie, int nroot, int oroot)
{
	int i;
	int nn;
	int on;
	int nbase;

	nn = 0;
	on = 0;
	for ( i = 0; i < (1 << 6); i++ ) {
	if ( VEC_BT(poptrie->nodes[nroot].vector, i) ) {
	    nbase = poptrie->nodes[nroot].base1 + nn;
	    nn++;
	} else {
	    nbase = -1;
	}
	if ( VEC_BT(poptrie->nodes[oroot].vector, i) ) {
	    _update_clean_inode(poptrie, nbase,
		                poptrie->nodes[oroot].base1 + on);
	    on++;
	}
	}

	if ( poptrie->nodes[nroot].base1 != poptrie->nodes[oroot].base1
	 && (u32)-1 != poptrie->nodes[oroot].base1 ) {
		free_node();
	}
	if ( poptrie->nodes[nroot].base0 != poptrie->nodes[oroot].base0
	 && (u32)-1 != poptrie->nodes[oroot].base0 ) {
		free_leaf();
	}
	/* Clear */
	if ( oroot != nroot ) {
		free_node();
	}
}

/*
 * Update and clean from the specified node
 */
static void
_update_clean_node(struct popt_fib_xid_table *poptrie, poptrie_node_t *node, int oinode)
{
	int i;
	int n;

	if ( oinode < 0 ) {
		return;
	}

	n = 0;
	for ( i = 0; i < (1 << 6); i++ ) {
	if ( VEC_BT(node->vector, i) ) {
	    _update_clean_inode(poptrie, node->base1 + n, oinode + n);
	    n++;
	}
	}

	/* Clear */
	if ( (int)node->base1 != oinode ) {
	 	free_node();
	}
}
static void
_update_clean_inode(struct popt_fib_xid_table *poptrie, int ninode, int oinode)
{
	int i;
	int obase;
	int nbase;

	if ( ninode == oinode ) {
		/* Identical node, then immediately quit from the procedure */
		return;
	}

	if ( ninode >= 0 ) {
		obase = poptrie->nodes[oinode].base1;
		nbase = poptrie->nodes[ninode].base1;
		for ( i = 0; i < (1 << 6); i++ ) {
		    if ( VEC_BT(poptrie->nodes[oinode].vector, i) ) {
			if ( VEC_BT(poptrie->nodes[ninode].vector, i) ) {
			    _update_clean_inode(poptrie, nbase, obase);
			} else {
			    _update_clean_inode(poptrie, -1, obase);
			}
		    }
		    if ( VEC_BT(poptrie->nodes[oinode].vector, i) ) {
			obase += 1;
		    }
		    if ( VEC_BT(poptrie->nodes[ninode].vector, i) ) {
			nbase += 1;
		    }
	}

	if ( (u32)-1 != poptrie->nodes[oinode].base1
	     && poptrie->nodes[oinode].base1 != poptrie->nodes[ninode].base1 ) {
	    free_node();
	}
	if ( (u32)-1 != poptrie->nodes[oinode].base0
	     && poptrie->nodes[oinode].base0 != poptrie->nodes[ninode].base0 ) {
	    free_leaf();
	}
	} else {
		obase = poptrie->nodes[oinode].base1;
		for ( i = 0; i < (1 << 6); i++ ) {
		    if ( VEC_BT(poptrie->nodes[oinode].vector, i) ) {
			_update_clean_inode(poptrie, -1, obase);
			obase += 1;
		    }
		}

		if ( (u32)-1 != poptrie->nodes[oinode].base1 ) {
		    free_node();
		}
		if ( (u32)-1 != poptrie->nodes[oinode].base0 ) {
		    free_leaf();
		}
	}
}

/*
 * Update and clean a subtree
 */
static void
_update_clean_subtree(struct popt_fib_xid_table *poptrie, int oinode)
{
	int i;
	int n;
	struct poptrie_node *node;

	if ( oinode < 0 ) {
		return;
	}

	node = &poptrie->nodes[oinode];

	n = 0;
	for ( i = 0; i < (1 << 6); i++ ) {
	if ( VEC_BT(node->vector, i) ) {
	    _update_clean_subtree(poptrie, node->base1 + n);
	    n++;
	}
	}

	/* Clear */
	if ( (int)node->base1 >= 0 ) {
		free_node();
	}

	if ( (int)node->base0 >= 0 ) {
		free_leaf();
	}
}

/*
 * Get the descending block from the index and shift
 */
static struct radix_node160 *
_next_block(struct radix_node160 *node, int idx, int shift, int depth)
{
	if ( NULL == node ) {
		return NULL;
	}

	if ( shift == depth ) {
		return node;
	}

	if ( (idx >> (depth - shift - 1)) & 0x1 ) {
		/* Right */
		return _next_block(node->right, idx, shift + 1, depth);
	} else {
		/* Left */
		return _next_block(node->left, idx, shift + 1, depth);
	}
}

/*
 * Parse triangle (k-bit subtree)
 */
static void
_parse_triangle(struct radix_node160 *node, u64 *vector,
                struct radix_node160 *nodes, int pos, int depth)
{
	int i;
	int hlen;

	if ( 6 == depth ) {
		/* Bottom of the triangle */
		memcpy(&nodes[pos], node, sizeof(struct radix_node160));
		if ( node->left || node->right ) {
		    /* Child internal nodes exist */
		    VEC_SET(*vector, pos);
		}
		return;
	}

	/* Calculate half length */
	hlen = (1 << (6 - depth - 1));

	/* Left */
	if ( node->left ) {
		_parse_triangle(node->left, vector, nodes, pos, depth + 1);
	} else {
		for ( i = pos; i < pos + hlen; i++ ) {
		    memcpy(&nodes[i], node, sizeof(struct radix_node160));
		    nodes[i].left = NULL;
		    nodes[i].right = NULL;
		}
	}
	/* Right */
	if ( node->right ) {
		_parse_triangle(node->right, vector, nodes, pos + hlen, depth + 1);
	} else {
		for ( i = pos + hlen; i < pos + hlen * 2; i++ ) {
		    memcpy(&nodes[i], node, sizeof(struct radix_node160));
		    nodes[i].left = NULL;
		    nodes[i].right = NULL;
		}
	}
}

/*
 * Clear all the marks
 */
static void
_clear_mark(struct radix_node160 *node)
{
	if ( !node->mark ) {
		return;
	}
	node->mark = 0;
	if ( node->left ) {
		_clear_mark(node->left);
	}
	if ( node->right ) {
		_clear_mark(node->right);
	}
}

/*
 * Recursive function to add a route to the poptrie data structure while
 * inserting the route to the RIB (radix tree)
 */
static int
_route_add(struct popt_fib_xid_table *poptrie, struct radix_node160 **node,
           XID prefix, int len, poptrie_leaf_t nexthop, int depth,
           struct radix_node160 *ext, struct radix_node160 **final)
{
	if (NULL == *node) {
		*node = kmalloc(sizeof(struct radix_node160), GFP_ATOMIC);
		if (NULL == *node) {
			/* Memory error */
			return -1;
		}
		(*node)->valid = 0;
		(*node)->left = NULL;
		(*node)->right = NULL;
		(*node)->ext = ext;
		(*node)->mark = 0;
	}

	if (len == depth) {
		/* Matched */
		if ((*node)->valid) {
			/* Already exists */
			return -1;
		}
		(*node)->valid = 1;
		(*node)->nexthop = nexthop;
		(*node)->len = len;

		/* Propagate this route to children */
		(*node)->mark = _route_add_propagate(*node, *node);

		/* Update the poptrie subtree */
		*final = *node;
		return depth;
	} else {
		if ((*node)->valid) {
			ext = *node;
		}
	int temp = 160-depth-1;
	if(temp<128){
	    if(prefix.prefix2 >> (temp) & 1)
		return _route_add(poptrie, &((*node)->right), prefix, len, nexthop,
		              depth + 1, ext, final);
	    else
	    return _route_add(poptrie, &((*node)->left), prefix, len, nexthop,
		              depth + 1, ext, final);
	}
	else{
	    if(prefix.prefix1 >> (temp-160) & 1)
		return _route_add(poptrie, &((*node)->right), prefix, len, nexthop,
		              depth + 1, ext, final);
	    else
		return _route_add(poptrie, &((*node)->left), prefix, len, nexthop,
		              depth + 1, ext, final);
	}

	}
}
static int
_route_add_propagate(struct radix_node160 *node, struct radix_node160 *ext)
{
	if ( NULL != node->ext ) {
	if ( ext->len > node->ext->len ) {
	    /* This new node is more specific */
	    if ( ext->nexthop != EXT_NH(node) ) {
		/* Prefix and next hop are updated */
		node->mark = 1;
	    }
	    node->mark = 1;
	    node->ext = ext;
	} else {
	    /* This new node is less specific, then terminate */
	    node->mark = 1;
	    return node->mark;
	}
	} else {
		/* The new route is propagated */
		node->mark = 1;
		node->ext = ext;
	}
	if ( NULL != node->left ) {
		node->mark |= _route_add_propagate(node->left, ext);
	}
	if ( NULL != node->right ) {
		node->mark |= _route_add_propagate(node->right, ext);
	}

	return node->mark;
}

/*
 * Change a route
 */

static int
_route_change(struct popt_fib_xid_table *poptrie, struct radix_node160 **node,
              XID prefix, int len, poptrie_leaf_t nexthop, int depth)
{
	if ( NULL == *node ) {
		/* Must have the entry for route_change() */
		return -1;
	}

	if ( len == depth ) {
		/* Matched */
		if ( !(*node)->valid ) {
		    /* Not exists */
		    return -1;
		}
		/* Update the entry */
		if ( (*node)->nexthop != nexthop ) {
		    (*node)->nexthop = nexthop;
		    (*node)->mark = _route_change_propagate(*node, *node);

		    /* Marked root */
		    return _update_subtree(poptrie, *node, prefix, depth);
		}

		return 0;
	} else {
		int temp = 160-depth-1;
		if(temp<128){
		    if(prefix.prefix2 >> (temp) & 1){
			return _route_change(poptrie, &((*node)->right), prefix, len,
				         nexthop, depth + 1);
		    }
		    else{
			return _route_change(poptrie, &((*node)->left), prefix, len,
				         nexthop, depth + 1);
		    }    
		}
		else{
		    if(prefix.prefix1 >> (temp-160) & 1){
			return _route_change(poptrie, &((*node)->right), prefix, len,
				         nexthop, depth + 1);
		    }
		    else{
			return _route_change(poptrie, &((*node)->left), prefix, len,
				         nexthop, depth + 1);
		    }    
		}    

	}
}

static int
_route_change_propagate(struct radix_node160 *node, struct radix_node160 *ext)
{
	/* Mark if the cache is updated */
	if ( ext == node->ext ) {
		node->mark = 1;
	}

	if ( NULL != node->left ) {
		node->mark |= _route_change_propagate(node->left, ext);
	}
	if ( NULL != node->right ) {
		node->mark |= _route_change_propagate(node->right, ext);
	}

	return node->mark;
}

/*
 * Update a route
 */

static int
_route_update(struct popt_fib_xid_table *poptrie, struct radix_node160 **node,
              XID prefix, int len, poptrie_leaf_t nexthop, int depth,
              struct radix_node160 *ext)
{
	if ( NULL == *node ) {
		*node = kmalloc(sizeof(struct radix_node160), GFP_ATOMIC);
	if ( NULL == *node ) {
	     	/* Memory error */
	    	return -1;
	}
	(*node)->valid = 0;
	(*node)->left = NULL;
	(*node)->right = NULL;
	(*node)->ext = ext;
	(*node)->mark = 0;
	}

	if ( len == depth ) {
	/* Matched */
	if ( (*node)->valid ) {
	    /* Already exists */
	    if ( (*node)->nexthop != nexthop ) {
		(*node)->nexthop = nexthop;
		(*node)->mark = _route_change_propagate(*node, *node);

		/* Marked root */
		return _update_subtree(poptrie, *node, prefix, depth);
	    }
	    return 0;
	} else {
	    (*node)->valid = 1;
	    (*node)->nexthop = nexthop;
	    (*node)->len = len;

	    /* Propagate this route to children */
	    (*node)->mark = _route_add_propagate(*node, *node);

	    /* Update MBT */
	    return _update_subtree(poptrie, *node, prefix, depth);
	}
	} else {
	if ( (*node)->valid ) {
	    ext = *node;
	}
	int temp = 160-depth-1;
	if(temp<128){
	    if(prefix.prefix2 >> (temp) & 1){
		return _route_update(poptrie, &((*node)->right), prefix, len,
		                 nexthop, depth + 1, ext);
	    }
	    else{
		return _route_update(poptrie, &((*node)->left), prefix, len,
		                 nexthop, depth + 1, ext);
	    }
	    }
	else{
	    if(prefix.prefix1 >> (temp-160) & 1){
		return _route_update(poptrie, &((*node)->right), prefix, len,
		                 nexthop, depth + 1, ext);
	    }
	    else{
		return _route_update(poptrie, &((*node)->left), prefix, len,
		                 nexthop, depth + 1, ext);
	    }    
	}        

	}
}

static u32
_rib_lookup_prefix(struct radix_node160 *node, XID addr, int depth, int height,
            struct radix_node160 *en)
{
    if ( NULL == node ) {
        return 0;
    }
    if ( node->valid ) {
        en = node;
    }
    if (depth == height) {
	return en->nexthop;
    }
    int temp = 160-depth-1;
    if(temp<128){
            if(addr.prefix2 >> (temp) & 1){
                        if ( NULL == node->right ) {
                    if ( NULL != en ) {
                        return en->nexthop;
                    } else {
                        return 0;
                    }
                } else {
                    return _rib_lookup_prefix(node->right, addr, depth + 1, height, en);
                }
            }
            else{
                        if ( NULL == node->left ) {
                    if ( NULL != en ) {
                        return en->nexthop;
                    } else {
                        return 0;
                    }
                } else {
                    return _rib_lookup_prefix(node->left, addr, depth + 1, height, en);
                }
            }
            }
    else{
        if(addr.prefix1 >> (temp-160) & 1){
                if ( NULL == node->right ) {
		        if ( NULL != en ) {
		            return en->nexthop;
		        } else {
		            return 0;
		        }
            } else {
                return _rib_lookup_prefix(node->right, addr, depth + 1, height, en);
            }
            }
        else{
             if ( NULL == node->left ) {
		    if ( NULL != en ) {
		        return en->nexthop;
		    } else {
		        return 0;
		    }
        } else {
            return _rib_lookup_prefix(node->left, addr, depth + 1, height, en);
        }
        }    
    }            
   
}


/*
 * Delete a route
 */
 
static int
_route_del(struct popt_fib_xid_table *poptrie, struct radix_node160 **node,
           XID prefix, int len, int depth, struct radix_node160 *ext, struct radix_node160 **final)
{
	int ret;

	if ( NULL == *node ) {
		return -1;
	}

	if ( len == depth ) {
		if ( !(*node)->valid ) {
		    /* No entry found */
		    return -1;
		}

		/* Propagate first */
		(*node)->mark = _route_del_propagate(*node, *node, ext);

		/* Invalidate the node */
		(*node)->valid = 0;
		(*node)->nexthop = 0;
		
		*final = *node;			
		return depth;
	
	} else {
	/* Update the propagate node if valid */
	if ( (*node)->valid ) {
	    ext = *node;
	}
	/* Traverse a child node */
	int temp = 160-depth-1;
	if(temp<128){
	    if(prefix.prefix2 >> (temp) & 1){
		ret = _route_del(poptrie, &((*node)->right), prefix, len, depth + 1,
		             ext, final);
	    }
	    else{
		ret = _route_del(poptrie, &((*node)->left), prefix, len, depth + 1,
		             ext, final);
	    }
	    }
	else{
	    if(prefix.prefix1 >> (temp-160) & 1){
		ret = _route_del(poptrie, &((*node)->right), prefix, len, depth + 1,
		             ext, final);
	    }
	    else{
		ret = _route_del(poptrie, &((*node)->left), prefix, len, depth + 1,
		             ext, final);
	    }    
	}        

	if ( ret < 0 ) {
	    return ret;
	}
	/* Delete this node if both children are empty */
	if ( NULL == (*node)->left && NULL == (*node)->right ) {
	    kfree(*node);
	    *node = NULL;
	}
	return ret;
	}

	return -1;
}

static int
_route_del_propagate(struct radix_node160 *node, struct radix_node160 *oext,
                     struct radix_node160 *next)
{
	if ( oext == node->ext ) {
		if ( oext->nexthop != EXT_NH(node) ) {
		    /* Next hop will change */
		    node->mark = 1;
		}
		/* Replace the extracted node */
		node->ext = next;
		node->mark = 1;
	}
	if ( NULL != node->left ) {
		node->mark |= _route_del_propagate(node->left, oext, next);
	}
	if ( NULL != node->right ) {
		node->mark |= _route_del_propagate(node->right, oext, next);
	}

	return node->mark;
}

/*
 * Lookup from the RIB table
 */
static u32
_rib_lookup(struct radix_node160 *node, XID addr, int depth,
            struct radix_node160 *en)
{
	if ( NULL == node ) {
		return 0;
	}
	if ( node->valid ) {
		en = node;
	}
	int temp = 160-depth-1;
	if(temp<128){
	    if(addr.prefix2 >> (temp) & 1){
		        if ( NULL == node->right ) {
		    if ( NULL != en ) {
		        return en->nexthop;
		    } else {
		        return 0;
		    }
		} else {
		    return _rib_lookup(node->right, addr, depth + 1, en);
		}
	    }
	    else{
		        if ( NULL == node->left ) {
		    if ( NULL != en ) {
		        return en->nexthop;
		    } else {
		        return 0;
		    }
		} else {
		    return _rib_lookup(node->left, addr, depth + 1, en);
		}
	    }
	    }
	else{
	if(addr.prefix1 >> (temp-160) & 1){
		if ( NULL == node->right ) {
			if ( NULL != en ) {
			    return en->nexthop;
			} else {
			    return 0;
			}
	    } else {
		return _rib_lookup(node->right, addr, depth + 1, en);
	    }
	    }
	else{
	     if ( NULL == node->left ) {
		    if ( NULL != en ) {
			return en->nexthop;
		    } else {
			return 0;
		    }
	} else {
	    return _rib_lookup(node->left, addr, depth + 1, en);
	}
	}    
	}            

}


/*
 * Free the allocated memory by the radix tree
 */
static void
_release_radix160(struct radix_node160 *node)
{
	if ( NULL != node  ) {
		_release_radix160(node->left);
		_release_radix160(node->right);
		kfree(node);
    }
}

/*
 * Release the poptrie data structure
 */
void
poptrie160_release(struct popt_fib_xid_table *poptrie)
{
	/* Release the radix tree */
	_release_radix160(poptrie->radix);

	if ( poptrie->nodes ) {
		vfree(poptrie->nodes);
	}
	if ( poptrie->leaves ) {
		vfree(poptrie->leaves);
	}
	if ( poptrie->cnodes ) {
		vfree(poptrie->cnodes);
	}
	if ( poptrie->cleaves ) {
		vfree(poptrie->cleaves);
	}
	if ( poptrie->dir ) {
		vfree(poptrie->dir);
	}
	if ( poptrie->altdir ) {
		vfree(poptrie->altdir);
	}
	if ( poptrie->fib.entries ) {
		vfree(poptrie->fib.entries);
	}
	if ( poptrie->_allocated ) {
		vfree(poptrie);
	}
}


static inline struct popt_fib_xid_table *xtbl_txtbl(struct fib_xid_table *xtbl)
{
	return (struct popt_fib_xid_table *)xtbl->fxt_data;
}
static XID xid_XID(const u8 *fx_xid){
	XID addr;	
	addr.prefix1 = (u32)((fx_xid)[0]<<24+(fx_xid)[1]<<16+(fx_xid)[2]<<8+(fx_xid)[3]);
	__uint128_t prefix = (__uint128_t)0;
	int i;
	for( i=4; i<20; i++)
	{
		prefix	+= fx_xid[i]<<(20-i-1)*8;
	}	
	addr.prefix2 = prefix;
	return addr;
}


static void popt_xtbl_death_work(struct work_struct *work);

#define	XIA_POPT_SZ1	19
#define	XIA_POPT_SZ0	22

static int popt_xtbl_init(struct xip_ppal_ctx *ctx, struct net *net,
			  struct xia_lock_table *locktbl,
			  const xia_ppal_all_rt_eops_t all_eops,
			  const struct xia_ppal_rt_iops *all_iops)
{
	struct fib_xid_table *new_xtbl;
	struct popt_fib_xid_table *txtbl;
	int ret;
	int i;

	if (ctx->xpc_xtbl)
		return -EEXIST; /* Duplicate. */

	new_xtbl = kzalloc(sizeof(*new_xtbl) + sizeof(*txtbl), GFP_KERNEL);
	if (!new_xtbl)
		return -ENOMEM;
	txtbl = xtbl_txtbl(new_xtbl);


	if ( NULL == txtbl ) {
		/* Allocate new one */
		txtbl = kmalloc(sizeof(struct popt_fib_xid_table), GFP_ATOMIC);
		if ( NULL == txtbl ) {
		    return NULL;
		}
		(void)memset(txtbl, 0, sizeof(struct popt_fib_xid_table));
		/* Set the flag indicating that this data structure needs vfree() when
		   released. */
		txtbl->_allocated = 1;
	} else {
		/* Write zero's */
		(void)memset(txtbl, 0, sizeof(struct popt_fib_xid_table));
	}

	/* Allocate the nodes and leaves */
	txtbl->nodes =vmalloc(sizeof(poptrie_node_t) * (1 << XIA_POPT_SZ1));
	if ( NULL == txtbl->nodes ) {
		poptrie160_release(txtbl);
		return NULL;
	}
	txtbl->nodesz = XIA_POPT_SZ1;
	txtbl->leaves =vmalloc(sizeof(poptrie_leaf_t) * (1 << XIA_POPT_SZ0));
	if ( NULL == txtbl->leaves ) {
		poptrie160_release(txtbl);
		return NULL;
	}
	txtbl->leafsz = XIA_POPT_SZ0;

	/* Prepare the memory management system for the internal node array */
	txtbl->cnodes =vmalloc(sizeof(*txtbl->cnodes) * (1 << XIA_POPT_SZ1));
	if ( NULL == txtbl->cnodes ) {
		poptrie160_release(txtbl);
		return NULL;
	}
	txtbl->last_base1 = 0;

	/* Prepare the memory management system for the leaf node array */
	txtbl->cleaves =vmalloc(sizeof(*txtbl->cleaves) * (1 << XIA_POPT_SZ0));
	if ( NULL == txtbl->cleaves ) {
		poptrie160_release(txtbl);
		return NULL;
	}
	txtbl->last_base0 = 0;

	/* Prepare the direct pointing array */
	txtbl->dir =vmalloc(sizeof(u32) << POPTRIE_S);
	if ( NULL == txtbl->dir ) {
		poptrie160_release(txtbl);
		return NULL;
	}
	for ( i = 0; i < (1 << POPTRIE_S); i++ ) {
		txtbl->dir[i] = (u32)1 << 31;
	}

	/* Prepare the alternative direct pointing array for the update procedure */
	txtbl->altdir =vmalloc(sizeof(u32) << POPTRIE_S);
	if ( NULL == txtbl->altdir ) {
		poptrie160_release(txtbl);
		return NULL;
	}

	/* Prepare the FIB mapping table */
	txtbl->fib.entries =vmalloc(sizeof(void *) * POPTRIE_INIT_FIB_SIZE);
	txtbl->fib.valid = vmalloc(sizeof(bool) * POPTRIE_INIT_FIB_SIZE);
	if ( NULL == txtbl->fib.entries ) {
		poptrie160_release(txtbl);
		return NULL;
	}
	txtbl->fib.sz = POPTRIE_INIT_FIB_SIZE;
	txtbl->fib.n = 0;
	/* Insert a NULL entry */
	int v = txtbl->fib.n++;
	txtbl->fib.entries[v] = NULL;
	txtbl->fib.valid[v] = true;

	
	new_xtbl->fxt_ppal_type = ctx->xpc_ppal_type;
	new_xtbl->fxt_net = net;
	rwlock_init(&txtbl->writers_lock);
	new_xtbl->all_eops = all_eops;
	new_xtbl->all_iops = all_iops;

	atomic_set(&new_xtbl->refcnt, 1);
	INIT_WORK(&new_xtbl->fxt_death_work, popt_xtbl_death_work);
	ctx->xpc_xtbl = new_xtbl;

	return 0;
}

static void *popt_fxid_ppal_alloc(size_t ppal_entry_size, gfp_t flags)
{
	return kmalloc(ppal_entry_size, flags);
}

static void popt_fxid_init(struct fib_xid *fxid, int table_id, int entry_type)
{
	BUILD_BUG_ON(XRTABLE_MAX_INDEX >= 0x100);
	BUG_ON(table_id >= XRTABLE_MAX_INDEX);
	fxid->fx_table_id = table_id;

	BUILD_BUG_ON(XIA_LPM_MAX_PREFIX_LEN >= 0x100);
	BUG_ON(entry_type > XIA_LPM_MAX_PREFIX_LEN);
	fxid->fx_entry_type = entry_type;

	fxid->dead.xtbl = NULL;
}



static void popt_xtbl_death_work(struct work_struct *work)
{
	struct fib_xid_table *xtbl = container_of(work, struct fib_xid_table,
		fxt_death_work);
	struct popt_fib_xid_table * poptrie = xtbl_txtbl(xtbl);
	poptrie160_release(poptrie);
	kfree(xtbl);
}

/* No extra information is needed, so @parg is empty. */
static void popt_fib_unlock(struct fib_xid_table *xtbl, void *parg)
{
	write_unlock(&xtbl_txtbl(xtbl)->writers_lock);
}

static struct fib_xid *popt_fxid_find_rcu(struct fib_xid_table *xtbl,
					  const u8 *xid)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	XID addr = xid_XID(xid);
	struct fib_xid* ret = (struct fib_xid*)poptrie160_lookup(txtbl , addr);
	return ret;
}

/* No extra information is needed, so @parg is empty. */
static struct fib_xid *popt_fxid_find_lock(void *parg,
	struct fib_xid_table *xtbl, const u8 *xid)
{
	return popt_fxid_find_rcu(xtbl,xid);
}


static int popt_iterate_xids(struct fib_xid_table *xtbl,
			     int (*locked_callback)(struct fib_xid_table *xtbl,
						    struct fib_xid *fxid,
						    const void *arg),
			     const void *arg)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	int rc = 0;

	read_lock(&txtbl->writers_lock);
	int i;
	for( i = 1 ; i < txtbl->fib.n ; i++)
	{	
		if(txtbl->fib.valid[i])	{	
			struct fib_xid* cur= (struct fib_xid*)txtbl->fib.entries[i];
	
			XID addr = xid_XID(cur);
			rc = locked_callback(xtbl, cur, arg);
			if (rc)
				goto out;
		}
	}
	
out:
	read_unlock(&txtbl->writers_lock);
	return rc;
}

/* No extra information is needed, so @parg is empty. */
static int popt_fxid_add_locked(void *parg, struct fib_xid_table *xtbl,
				struct fib_xid *fxid)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	int len_in_bits = (fxid->fx_entry_type);
	XID addr = xid_XID(fxid->fx_xid);	
	int ret = poptrie160_route_add(txtbl, addr, len_in_bits, (void *)fxid);

	if (ret == 0)
		atomic_inc(&xtbl->fxt_count);
	return ret;
}

static int popt_fxid_add(struct fib_xid_table *xtbl, struct fib_xid *fxid)
{	
	int rc;
	write_lock(&xtbl_txtbl(xtbl)->writers_lock);
	rc = popt_fxid_add_locked(NULL, xtbl, fxid);
	write_unlock(&xtbl_txtbl(xtbl)->writers_lock);
	return rc;
}


/* No extra information is needed, so @parg is empty. */
static void popt_fxid_rm_locked(void *parg, struct fib_xid_table *xtbl,
				struct fib_xid *fxid)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	XID addr = xid_XID(fxid->fx_xid);
	int ret; 
	ret = poptrie160_route_del(txtbl , addr , fxid->fx_entry_type);

	if(ret==0) {
		int i;
		for( i=1; i< txtbl->fib.n;i++){
			if(txtbl->fib.valid[i]){
			struct fib_xid *temp = (struct fib_xid*)txtbl->fib.entries[i];
			if(match_xids(temp->fx_xid,fxid->fx_xid) && temp->fx_entry_type==fxid->fx_entry_type)
				{
					txtbl->fib.valid[i]=false;
				}
		}			
		}
		atomic_dec(&xtbl->fxt_count);
		}
}

static void popt_fxid_rm(struct fib_xid_table *xtbl, struct fib_xid *fxid)
{
	write_lock(&xtbl_txtbl(xtbl)->writers_lock);
	popt_fxid_rm_locked(NULL, xtbl, fxid);
	write_unlock(&xtbl_txtbl(xtbl)->writers_lock);
}

/* popt_xid_rm() removes the entry with the longest matching prefix,
 * since we have no prefix information for @xid.
 */
static struct fib_xid *popt_xid_rm(struct fib_xid_table *xtbl, const u8 *xid)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	XID addr = xid_XID(xid);	
	struct fib_xid *fxid = 	poptrie160_lookup(txtbl, addr);
	popt_fxid_rm(xtbl, fxid);
	return fxid;
}

static void popt_fxid_replace_locked(struct fib_xid_table *xtbl,
				     struct fib_xid *old_fxid,
				     struct fib_xid *new_fxid)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	XID addr_old = xid_XID(old_fxid->fx_xid);
	XID addr_new = xid_XID(new_fxid->fx_xid);
	poptrie160_route_change(txtbl , addr_old , old_fxid->fx_entry_type, (void*)new_fxid);
	
}

//Function to compare two XID's
bool match_xids(const u8 *xid1, const u8 *xid2){
	int i;	
	for(i = 0; i <20 ;i++){
		if(xid1[i]!=xid2[i]) return false;	
	}
	return true;

}


struct fib_xid *
poptrie160_exact_lookup(struct popt_fib_xid_table *poptrie, const u8 *xid,
			u8 prefix_len)
{
	struct fib_xid *temp;
	int i;

	for (i = 1; i < poptrie->fib.n; i++) {
		if (poptrie->fib.valid[i]) {
			temp = (struct fib_xid *)poptrie->fib.entries[i];
			if (match_xids(temp->fx_xid, xid) &&
			    temp->fx_entry_type == prefix_len)
				return temp;
		}
	}

	return NULL;
}

int popt_fib_newroute_lock(struct fib_xid *new_fxid,
			   struct fib_xid_table *xtbl,
			   struct xia_fib_config *cfg, int *padded)
{
	struct fib_xid *cur_fxid;
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	
	const u8 *id;

	if (padded)
		*padded = 0;

	/* Acquire lock and do exact matching to find @cur_fxid. */
	id = cfg->xfc_dst->xid_id;
	XID addr = xid_XID(id);
	write_lock(&txtbl->writers_lock);
	cur_fxid = poptrie160_exact_lookup(txtbl, id, new_fxid->fx_entry_type);
	if (cur_fxid) {
		if ((cfg->xfc_nlflags & NLM_F_EXCL) ||
		    !(cfg->xfc_nlflags & NLM_F_REPLACE))
			return -EEXIST;

		if (cur_fxid->fx_table_id != new_fxid->fx_table_id)
			return -EINVAL;

		popt_fxid_replace_locked(xtbl, cur_fxid, new_fxid);
		fxid_free(xtbl, cur_fxid);
		return 0;
	}

	if (!(cfg->xfc_nlflags & NLM_F_CREATE))
		return -ENOENT;

	/* Add new entry. */
	BUG_ON(popt_fxid_add_locked(NULL, xtbl, new_fxid));

	if (padded)
		*padded = 1;
	return 0;

}

/* popt_fib_newroute() differs from all_fib_newroute() because its lookup
 * function has the option of doing longest prefix or exact matching, and
 * all_fib_newroute() is not flexible enough to do that.
 *
 * This simple version of newroute simply adds the entry, without
 * flushing any anchors.
 */
static int popt_fib_newroute(struct fib_xid *new_fxid,
			     struct fib_xid_table *xtbl,
			     struct xia_fib_config *cfg, int *padded)
{
	int rc = popt_fib_newroute_lock(new_fxid, xtbl, cfg, padded);
	popt_fib_unlock(xtbl, NULL);
	return rc;
}

/* popt_fib_delroute() differs from all_fib_delroute() because its lookup
 * function has the option of doing longest prefix or exact matching, and
 * all_fib_delroute() is not flexible enough to do that.
 */
int popt_fib_delroute(struct xip_ppal_ctx *ctx, struct fib_xid_table *xtbl,
		      struct xia_fib_config *cfg)
{
	
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	XID addr = xid_XID(cfg->xfc_dst->xid_id);
	struct fib_xid *fxid;
	int rc;
	const u8 *id;
	if (!valid_prefix(cfg))
		return -EINVAL;

	/* Do exact matching to find @fxid. */
	id  = cfg->xfc_dst->xid_id;
	fxid  = (struct fib_xid*)poptrie160_exact_lookup(txtbl , id , *(u8 *)cfg->xfc_protoinfo);
	if (!fxid) {
		rc = -ENOENT;
		goto unlock;
	}
	if (fxid->fx_table_id != cfg->xfc_table) {
		rc = -EINVAL;
		goto unlock;
	}
	
	popt_fxid_rm_locked(NULL, xtbl, fxid);
	popt_fib_unlock(xtbl, NULL);
	fxid_free(xtbl, fxid);
	return 0;

unlock:
	popt_fib_unlock(xtbl, NULL);
	return rc;
	
}

/* Dump all entries in popt. */
static int popt_xtbl_dump_rcu(struct fib_xid_table *xtbl,
			      struct xip_ppal_ctx *ctx, struct sk_buff *skb,
			      struct netlink_callback *cb)
{	
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);
	int rc = 0;
	read_lock(&txtbl->writers_lock);
	int no_of_entries = txtbl->fib.n;
	int i;
	for(i =1 ; i<no_of_entries ; i++)
	{
		if(txtbl->fib.valid[i]){	
			struct fib_xid *fxid = (struct fib_xid*)txtbl->fib.entries[i];
			rc = xtbl->all_eops[fxid->fx_table_id].
					dump_fxid(fxid, xtbl, ctx, skb, cb);
				if (rc < 0)
					goto out;
		}
	}
out:
	read_unlock(&txtbl->writers_lock);
	return rc;
}

struct fib_xid *popt_fib_get_pred_locked(struct fib_xid_table *xtbl, struct fib_xid *fxid)
{
	struct popt_fib_xid_table *txtbl = xtbl_txtbl(xtbl);	
	XID addr = xid_XID(fxid->fx_xid);
	int height = fxid->fx_entry_type;	
	struct fib_xid* ret = (struct fib_xid*)txtbl->fib.entries[_rib_lookup_prefix(txtbl->radix, addr, 0, height, NULL)];
	return ret;
}

/* Main entries for LPM need to display the prefix length when dumped,
 * so popt_fib_mrd_dump() differs from fib_mrd_dump().
 */
int popt_fib_mrd_dump(struct fib_xid *fxid, struct fib_xid_table *xtbl,
		      struct xip_ppal_ctx *ctx, struct sk_buff *skb,
		      struct netlink_callback *cb)
{
	struct nlmsghdr *nlh;
	u32 portid = NETLINK_CB(cb->skb).portid;
	u32 seq = cb->nlh->nlmsg_seq;
	struct rtmsg *rtm;
	struct fib_xid_redirect_main *mrd = fxid_mrd(fxid);
	struct xia_xid dst;

	nlh = nlmsg_put(skb, portid, seq, RTM_NEWROUTE, sizeof(*rtm),
			NLM_F_MULTI);
	if (nlh == NULL)
		return -EMSGSIZE;

	rtm = nlmsg_data(nlh);
	rtm->rtm_family = AF_XIA;
	rtm->rtm_dst_len = sizeof(struct xia_xid);
	rtm->rtm_src_len = 0;
	rtm->rtm_tos = 0; /* XIA doesn't have a tos. */
	rtm->rtm_table = XRTABLE_MAIN_INDEX;
	/* XXX One may want to vary here. */
	rtm->rtm_protocol = RTPROT_UNSPEC;
	/* XXX One may want to vary here. */
	rtm->rtm_scope = RT_SCOPE_UNIVERSE;
	rtm->rtm_type = RTN_UNICAST;
	/* XXX One may want to put something here, like RTM_F_CLONED. */
	rtm->rtm_flags = 0;

	dst.xid_type = xtbl_ppalty(xtbl);
	memmove(dst.xid_id, fxid->fx_xid, XIA_XID_MAX);

	if (unlikely(nla_put(skb, RTA_DST, sizeof(dst), &dst) ||
		     nla_put(skb, RTA_GATEWAY, sizeof(mrd->gw), &mrd->gw)))
		goto nla_put_failure;

	/* Add prefix length to packet. */
	if (unlikely(nla_put(skb, RTA_PROTOINFO, sizeof(fxid->fx_entry_type),
			     &(fxid->fx_entry_type))))
		goto nla_put_failure;

	nlmsg_end(skb, nlh);
	return 0;

nla_put_failure:
	nlmsg_cancel(skb, nlh);
	return -EMSGSIZE;	
}

const struct xia_ppal_rt_iops xia_ppal_popt_rt_iops = {
	.xtbl_init = popt_xtbl_init,
	.xtbl_death_work = popt_xtbl_death_work,

	.fxid_ppal_alloc = popt_fxid_ppal_alloc,
	.fxid_init = popt_fxid_init,

	/* Note that there is no RCU-specific version. */
	.fxid_find_rcu = popt_fxid_find_rcu,
	.fxid_find_lock = popt_fxid_find_lock,
	.iterate_xids = popt_iterate_xids,
	/* Note that there is no RCU-specific version. */
	.iterate_xids_rcu = popt_iterate_xids,

	.fxid_add = popt_fxid_add,
	.fxid_add_locked = popt_fxid_add_locked,

	.fxid_rm = popt_fxid_rm,
	.fxid_rm_locked = popt_fxid_rm_locked,
	.xid_rm = popt_xid_rm,

	.fxid_replace_locked = popt_fxid_replace_locked,

	.fib_unlock = popt_fib_unlock,

	.fib_newroute = popt_fib_newroute,
	.fib_delroute = popt_fib_delroute,

	.xtbl_dump_rcu = popt_xtbl_dump_rcu,
};


