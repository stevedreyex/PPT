#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include"common.h"
// length of the tag
typedef  unsigned long   UWord;
UWord* tags;
long long int tagValue;
long long int setValue;
long long int value[4096];
int valid[4096], tim[4096];
static int count=0;

int lru(long long int tagValue, long long int setValue, long long int size, int numberOfWays, long long int block_size)
{
	long long int cache_size = 1024*32, no_of_blocks = cache_size/block_size;
	long long int i,j,k,temp1,temp2,flag;
	long long int no_of_sets = no_of_blocks/numberOfWays;
	if(count == 0)
	{	
		// initialize this only once
		for(i=0;i<no_of_blocks;i++)
		{
			value[i] = 0;
			valid[i] = 0;
			tim[i] = 0;
		} // create only once
		count = 1;
	}	
	// LRU algorithm
	temp1 = setValue*numberOfWays;
	temp2 = temp1+numberOfWays-1;
	flag = 0;		
	// setno. ranges from setvalue*numberofways to setvalue*numberofways + numberofways - 1
	for(j=temp1;j<=temp2;j++)
	{
		if(valid[j] == 1 && tagValue == value[j])
		{
			valid[j] = 1;
			tim[j] = i;
			return 0;                // return HIT
		}
	}
	flag = 0;
	for(j=temp1;j<=temp2;j++)
	{
		if(valid[j] == 0)
		{
			// allot this empty block to that instruction
			value[j] = tagValue;
			flag = 2;
			tim[j] = i;
			valid[j] = 1;
			return 1;               // return cold MISS
		}
	}
	if(flag != 2)
	{
		k = temp1;
		// replacement takes place as per the policy
		for(j=temp1;j<=temp2;j++)
		{
			if(tim[k]>tim[j])
				k = j;
		}
		// now we need to replace this block with index stored in 'k'
		value[k] = tagValue;
		tim[k] = i;
		valid[k] = 1;
		// block replaced and miss has also been incremented
		return 1;                      // return MISS
	}
	return 0;
}



/*--------------------------------------------------------------------*/
/*--- Cache simulation                                    cg_sim.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Cachegrind, a high-precision tracing profiler
   built with Valgrind.

   Copyright (C) 2002-2017 Nicholas Nethercote
      njn@valgrind.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>.

   The GNU General Public License is contained in the file COPYING.
*/

/* Notes:
  - simulates a write-allocate cache
  - (block --> set) hash function uses simple bit selection
  - handling of references straddling two cache blocks:
      - counts as only one cache access (not two)
      - both blocks hit                  --> one hit
      - one block hits, the other misses --> one miss
      - both blocks miss                 --> one miss (not two)
*/

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initlru(cache_t config, cache_t2* c)
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

   c->tags = (UWord *)malloc(sizeof(UWord) * c->sets * c->assoc);

   for (i = 0; i < c->sets * c->assoc; i++)
      c->tags[i] = 0;
}

/* This attribute forces GCC to inline the function, getting rid of a
 * lot of indirection around the cache_t2 pointer, if it is known to be
 * constant in the caller (the caller is inlined itself).
 * Without inlining of simulator functions, cachegrind can get 40% slower.
 */
__attribute__((always_inline))
static __inline__
Bool cachesim_setref_is_miss(cache_t2* c, UInt set_no, UWord tag)
{
   int i, j;
   UWord *set;

   set = &(c->tags[set_no * c->assoc]);

   /* This loop is unrolled for just the first case, which is the most */
   /* common.  We can't unroll any further because it would screw up   */
   /* if we have a direct-mapped (1-way) cache.                        */
   if (tag == set[0])
      return False;

   /* If the tag is one other than the MRU, move it into the MRU spot  */
   /* and shuffle the rest down.                                       */
   for (i = 1; i < c->assoc; i++) {
      if (tag == set[i]) {
         for (j = i; j > 0; j--) {
            set[j] = set[j - 1];
         }
         set[0] = tag;

         return False;
      }
   }

   /* A miss;  install this tag as MRU, shuffle rest down. */
   for (j = c->assoc - 1; j > 0; j--) {
      set[j] = set[j - 1];
   }
   set[0] = tag;

   return True;
}

__attribute__((always_inline))
static __inline__
Bool cachesim_ref_is_miss(cache_t2* c, Addr a, UChar size)
{
   /* A memory block has the size of a cache line */
   UWord block1 =  a         >> c->line_size_bits;
   UWord block2 = (a+size-1) >> c->line_size_bits;
   UInt  set1   = block1 & c->sets_min_1;

   /* Tags used in real caches are minimal to save space.
    * As the last bits of the block number of addresses mapping
    * into one cache set are the same, real caches use as tag
    *   tag = block >> log2(#sets)
    * But using the memory block as more specific tag is fine,
    * and saves instructions.
    */
   UWord tag1   = block1;

   /* Access entirely within line. */
   if (block1 == block2)
      return cachesim_setref_is_miss(c, set1, tag1);

   /* Access straddles two lines. */
   else if (block1 + 1 == block2) {
      UInt  set2 = block2 & c->sets_min_1;
      UWord tag2 = block2;

      /* always do both, as state is updated as side effect */
      if (cachesim_setref_is_miss(c, set1, tag1)) {
         cachesim_setref_is_miss(c, set2, tag2);
         return True;
      }
      return cachesim_setref_is_miss(c, set2, tag2);
   }
   printf("addr: %lx  size: %u  blocks: %lu %lu",
               a, size, block1, block2);
   printf("item straddles more than two cache sets");
   /* not reached */
   return True;
}

extern cache_t2 LL;
extern cache_t2 D1;

static void lru_init(cache_t D1c, cache_t LLc)
{
   cachesim_initlru(D1c, &D1);
   cachesim_initlru(LLc, &LL);
}

__attribute__((always_inline))
static __inline__
void lru_sim(Addr a, UChar size, ULong* m1, ULong *mL)
{
   if (cachesim_ref_is_miss(&D1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size))
         (*mL)++;
   }
}
/*--------------------------------------------------------------------*/
/*--- end                                                 cg_sim.c ---*/
/*--------------------------------------------------------------------*/

