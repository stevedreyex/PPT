// Description: Implementation of the SRRIP policy.
#define MAX_RRPV 3


extern cache_t2 D1;

__attribute__((always_inline))
static __inline__
void srrip_sim(Addr a, UChar size, ULong* m1, ULong *mL){
    int i, j;
    cache_t2* c = &D1;
    UWord block1 =  a         >> c->line_size_bits;
    UInt  set_no   = block1 & c->sets_min_1;

    /* Tags used in real caches are minimal to save space.
        * As the last bits of the block number of addresses mapping
        * into one cache set are the same, real caches use as tag
        *   tag = block >> log2(#sets)
        * But using the memory block as more specific tag is fine,
        * and saves instructions.
        */
    UWord tag   = block1;

    UWord *set;

    set = &(c->tags[set_no * c->assoc]);

    /* This loop is unrolled for just the first case, which is the most */
    /* common.  We can't unroll any further because it would screw up   */
    /* if we have a direct-mapped (1-way) cache.                        */
    if (tag == set[0])
        return;

    long long int p= c->assoc*set_no;

    // Could found
    for(j=p;j<p+c->assoc;j++){
        if(set[j] == tag){
            // set the status to 0 (recently used)
			// Cache hit (i)
			c->RRPV[j] = 0;
			return;
        }
    }
step1:
    // Cache miss
	// (1) search for first ‘1’ from left
	for (i = 0; i < c->assoc; i++) {
		if (c->RRPV[p + i] == 3) {
			// (2) if found goto step 5
			goto step5;
		}
	}
	// (3) if all are ‘0’ then set all to ‘1’
	for (i = 0; i < c->assoc; i++) {
		c->RRPV[p + i]++;
	}
	// (4) goto step 1
	goto step1;
step5:
	// (5) replace block and set its status to ‘2’
	set[p + i] = tag;
	c->RRPV[p + i] = 2;
	(*m1)++;
}

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initsrrip(cache_t config, cache_t2* c)
{
   Int i;

   c->size      = config.size;
   c->assoc     = config.assoc;
   c->line_size = config.line_size;

   c->sets           = (c->size / c->line_size) / c->assoc;
   c->sets_min_1     = c->sets - 1;
   c->line_size_bits = log2(c->line_size);
   c->tag_shift      = c->line_size_bits + log2(c->sets);

   if (c->assoc == 1) {
      sprintf(c->desc_line, "%d B, %d B, direct-mapped", 
                                 c->size, c->line_size);
   } else {
      sprintf(c->desc_line, "%d B, %d B, %d-way associative",
                                 c->size, c->line_size, c->assoc);
   }

   c->cacheLfu = (std::pair<long long int,long long int> *)malloc(sizeof(std::pair<long long int,long long int>) * c->sets * c->assoc);

   //init
   for (i = 0; i < c->sets * c->assoc; i++)
      c->tags[i] = 0;

    c->RRPV = (short int *)malloc(sizeof(short int) * c->sets * c->assoc);
    // Initial state all block with status 3 (avail to be replaced)
    memset(c->RRPV, 3, sizeof(int) * c->sets * c->assoc);
}

static void srrip_init(cache_t D1c, cache_t LLc)
{
   cachesim_initsrrip(D1c, &D1);
}