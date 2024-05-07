#include"common.h"

extern cache_t2 LL;
extern cache_t2 D1;

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initlfu(cache_t config, cache_t2* c)
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
   {
	// First is the tag value and second is the frequency of the tag
	  c->cacheLfu[i].first = -1;
	  c->cacheLfu[i].second = 0;
   }
}

static void lfu_init(cache_t D1c, cache_t LLc)
{
   cachesim_initlfu(D1c, &D1);
}

__attribute__((always_inline))
static __inline__
void lfu_sim(Addr a, UChar size, ULong* m1, ULong *mL){
	int i, j;
	std::pair<long long, long long> *set;
	cache_t2* c = &D1;
	UWord block1 =  a         >> c->line_size_bits;
	UInt  set_no   = block1 & c->sets_min_1;
	/* Tags used in real caches are minimal to save space.
    * As the last bits of the block number of addresses mapping
    * into one cache set are the same, real caches use as tag
    *   tag = block >> log2(#sets)
    * But using the memory block as more specific tag is fine,
    * and saves instructions.
	* 
	* However, if you want to observe some rules, don't forget >> c->assoc
    */
	UWord tag   = block1;
	set = &(c->cacheLfu[set_no * c->assoc]);


	/* This loop is unrolled for just the first case, which is the most */
	/* common.  We can't unroll any further because it would screw up   */
	/* if we have a direct-mapped (1-way) cache.                        */
	if (tag == set[0].first){
		set[0].second++;
		return;
	}

	int min_elem_ind = -1;
	int min_freq = 1e9;
	long long int p= c->assoc*set_no;

	// Could found
	for(j=p;j<p+c->assoc;j++){
		if(set[j].first == tag){
			set[j].second++;
			return;
		}
	}

	// Not found
	if (j == p+c->assoc){
		for(j=p;j<p+c->assoc;j++){
			if(set[j].second < min_freq){
				min_freq = set[j].second;
				min_elem_ind = j;
			}
		}
		// Replace
		set[min_elem_ind].first = tag;
		set[min_elem_ind].second = 1;
		(*m1)++;
		return;
	}
}