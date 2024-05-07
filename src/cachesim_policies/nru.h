#include<bits/stdc++.h>


using namespace std;


static long long int **cacheNru; 
 	static int **validNru , **referencedNru ;

void check(long long int setNumber,int noOfWays)
{
	int i;
	//printf("inside check\n");
	for ( i = 0; i < noOfWays; ++i)
	{
		//printf("%d is way,%d is referencedNru\n",i,referencedNru[setNumber][i]);
		if(referencedNru[setNumber][i] == 0)
			return;
	}

	for ( i = 0; i < noOfWays; ++i)
	{
		referencedNru[setNumber][i] = 0;
	}


}


void replacement(long long int setNumber,long long int tagNumber,int noOfWays)
{
	int i;
	for(i=0;i<noOfWays;i++)
		if(validNru[setNumber][i] == 0)
		{
			validNru[setNumber][i] = 1;
			cacheNru[setNumber][i] = tagNumber;
			referencedNru[setNumber][i] = 1;
			check(setNumber,noOfWays);
			referencedNru[setNumber][i] = 1;
			return;
		}

	for(i=0;i<noOfWays;i++)
		if(referencedNru[setNumber][i] == 0)
		{
			// validNru[setNumber][i] = 1;
			referencedNru[setNumber][i] = 1;
			cacheNru[setNumber][i] = tagNumber;
			check(setNumber,noOfWays);
			referencedNru[setNumber][i] = 1;
			return;
		}

		
	

}
/*
void displ(int setno)
{
	for(int j=0;j<noOfWays;j++)
		printf("%d is way %lld is tag and %d is validNruity and %d is referencedNru\n",j,cacheNru[setno][j],validNru[setno][j],referencedNru[setno][j]);
		
		printf("\n\n");
}*/

int nru(long long int tagNumber, int setNumber,int noOfWays,int size)
{
	
	int i,j,hits=0, flag = 0;
	static int noOfSets = pow(2,15)/ (noOfWays*size);
	static int count = 0;
 	// cout << setNumber << "is setnumber and " << tagNumber<< "is tagnumber\n";
 	// printf("creating sets\n");

    

		// printf("sets initialized with memory\n");
	if(count == 0)
	{
	
	cacheNru = (long long int **)malloc(noOfSets * sizeof(long long int *)); 
 	validNru = (int **)malloc(noOfSets * sizeof(int *)); 
 	referencedNru = (int **)malloc(noOfSets * sizeof(int *));

 	for (i=0; i<noOfSets; i++) 
        { 
        	cacheNru[i] = (long long int *)malloc(noOfWays * sizeof(long long int));
        	validNru[i] = (int *)malloc(noOfWays * sizeof(int));
     		referencedNru[i] = (int *)malloc(noOfWays * sizeof(int));
        	   	
		}

	for (int i = 0; i < noOfSets; ++i)
	{
		for (int j = 0; j < noOfWays; ++j)
		{
			validNru[i][j] = 0;
			cacheNru[i][j]= 0;
			referencedNru[i][j] = 0;
		}

	}
	count = 1;

	}

	// printf("starting nru simulation\n");
	// for(i=0;i<size;i++)
	
	// flag = 0;

	// setNumber = setValue[i];
	// tagNumber = tagValue[i];
	//printf("%d is setNumber and %lld is tagNumber\n",setNumber,tagNumber );
	for(j=0;j<noOfWays;j++)
	{
		
		if(cacheNru[setNumber][j] == tagNumber)
		{
			
			// flag = 1;
			referencedNru[setNumber][j] = 1;
			check(setNumber,noOfWays);
			referencedNru[setNumber][j] = 1;	
			//displ(setNumber);
			//printf("\nhit at position %d\n",j);

			return 1;
		}
	
	}
	
		
	replacement(setNumber,tagNumber,noOfWays);
	
	return 0;
		
}

	
/*
 * Implementation of the Not Recently Used (NRU) cache replacement policy.
 * From "High Performance Cache Replacement Using Re-Reference Interval Prediction (RRIP)"
 * Algorithm provided at page 64 figure 3
 */

extern cache_t2 LL;
extern cache_t2 D1;

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initnru(cache_t config, cache_t2* c)
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

    c->referencedNru = (bool *)malloc(sizeof(bool) * c->sets * c->assoc);
	// Initial state all block with status 1 (avail to be replaced)
    memset(c->referencedNru, 1, sizeof(bool) * c->sets);
}

__attribute__((always_inline))
static __inline__
void nru_sim(Addr a, UChar size, ULong* m1, ULong *mL){
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
			c->referencedNru[p] = 0;
			return;
        }
    }

step1:
	// Cache miss
	// (1) search for first ‘1’ from left
	for (i = 0; i < c->assoc; i++) {
		if (c->referencedNru[p + i] == 1) {
			// (2) if found goto step 5
			goto step5;
		}
	}
	// (3) if all are ‘0’ then set all to ‘1’
	for (i = 0; i < c->assoc; i++) {
		c->referencedNru[p + i] = 1;
	}
	// (4) goto step 1
	goto step1;
step5:
	// (5) replace block and set its status to ‘1’
	set[p + i] = tag;
	c->referencedNru[p + i] = 1;
	(*m1)++;
}

static void nru_init(cache_t D1c, cache_t LLc)
{
   cachesim_initnru(D1c, &D1);
}