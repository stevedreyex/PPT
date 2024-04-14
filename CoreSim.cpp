
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

#include <math.h>
#include <stdio.h>

#define BUFFER_SIZE 1024

typedef unsigned long long int ULong;
typedef unsigned long Addr;

// For cache simulation
typedef struct {
   int size;       // bytes
   int assoc;
   int line_size;  // bytes
} cache_t;

typedef struct {
   int          size;                   /* bytes */
   int          assoc;
   int          line_size;              /* bytes */
   int          sets;
   int          sets_min_1;
   int          line_size_bits;
   int          tag_shift;
   char        desc_line[128];         /* large enough */
   unsigned long*       tags;
} cache_t2;

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initcache(cache_t config, cache_t2* c)
{
   int i;

   c->size      = config.size;
   c->assoc     = config.assoc;
   c->line_size = config.line_size;

   c->sets           = (c->size / c->line_size) / c->assoc;
   c->sets_min_1     = c->sets - 1;
   c->line_size_bits = log2(c->line_size);
   c->tag_shift      = c->line_size_bits + log2(c->sets);

   if (c->assoc == 1) {
      printf(c->desc_line, "%d B, %d B, direct-mapped", 
                                 c->size, c->line_size);
   } else {
      printf(c->desc_line, "%d B, %d B, %d-way associative",
                                 c->size, c->line_size, c->assoc);
   }

   c->tags = (unsigned long *)malloc(sizeof(unsigned long) * c->sets * c->assoc);

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
bool cachesim_setref_is_miss(cache_t2* c, unsigned int set_no, unsigned long tag)
{
   int i, j;
   unsigned long *set;

   set = &(c->tags[set_no * c->assoc]);

   /* This loop is unrolled for just the first case, which is the most */
   /* common.  We can't unroll any further because it would screw up   */
   /* if we have a direct-mapped (1-way) cache.                        */
   if (tag == set[0])
      return false;

   /* If the tag is one other than the MRU, move it into the MRU spot  */
   /* and shuffle the rest down.                                       */
   for (i = 1; i < c->assoc; i++) {
      if (tag == set[i]) {
         for (j = i; j > 0; j--) {
            set[j] = set[j - 1];
         }
         set[0] = tag;

         return false;
      }
   }

   /* A miss;  install this tag as MRU, shuffle rest down. */
   for (j = c->assoc - 1; j > 0; j--) {
      set[j] = set[j - 1];
   }
   set[0] = tag;

   return true;
}

__attribute__((always_inline))
static __inline__
bool cachesim_ref_is_miss(cache_t2* c, Addr a, char size)
{
   /* A memory block has the size of a cache line */
   unsigned long block1 =  a         >> c->line_size_bits;
   unsigned long block2 = (a+size-1) >> c->line_size_bits;
   unsigned int  set1   = block1 & c->sets_min_1;

   /* Tags used in real caches are minimal to save space.
    * As the last bits of the block number of addresses mapping
    * into one cache set are the same, real caches use as tag
    *   tag = block >> log2(#sets)
    * But using the memory block as more specific tag is fine,
    * and saves instructions.
    */
   unsigned long tag1   = block1;

   /* Access entirely within line. */
   if (block1 == block2)
      return cachesim_setref_is_miss(c, set1, tag1);

   /* Access straddles two lines. */
   else if (block1 + 1 == block2) {
      unsigned int  set2 = block2 & c->sets_min_1;
      unsigned long tag2 = block2;

      /* always do both, as state is updated as side effect */
      if (cachesim_setref_is_miss(c, set1, tag1)) {
         cachesim_setref_is_miss(c, set2, tag2);
         return true;
      }
      return cachesim_setref_is_miss(c, set2, tag2);
   }
   printf("addr: %lx  size: %u  blocks: %lu %lu",
               a, size, block1, block2);
   printf("item straddles more than two cache sets");
   /* not reached */
   return true;
}


static cache_t2 LL;
static cache_t2 I1;
static cache_t2 D1;

static void cachesim_initcaches(cache_t D1c, cache_t LLc)
{
   cachesim_initcache(D1c, &D1);
   cachesim_initcache(LLc, &LL);
}

__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_Gen(Addr a, char size, ULong* m1, ULong *mL)
{
   if (cachesim_ref_is_miss(&I1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size))
         (*mL)++;
   }
}

// common special case IrNoX
__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_NoX(Addr a, char size, ULong* m1, ULong *mL)
{
   unsigned long block  = a >> I1.line_size_bits;
   unsigned int  I1_set = block & I1.sets_min_1;

   // use block as tag
   if (cachesim_setref_is_miss(&I1, I1_set, block)) {
      unsigned int  LL_set = block & LL.sets_min_1;
      (*m1)++;
      // can use block as tag as L1I and LL cache line sizes are equal
      if (cachesim_setref_is_miss(&LL, LL_set, block))
         (*mL)++;
   }
}

__attribute__((always_inline))
static __inline__
void cachesim_D1_doref(Addr a, char size, ULong* m1, ULong *mL)
{
   if (cachesim_ref_is_miss(&D1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size))
         (*mL)++;
   }
}

/* Check for special case IrNoX. Called at instrumentation time.
 *
 * Does this Ir only touch one cache line, and are L1I/LL cache
 * line sizes the same? This allows to get rid of a runtime check.
 *
 * Returning false is always fine, as this calls the generic case
 */
static bool cachesim_is_IrNoX(Addr a, char size)
{
   unsigned long block1, block2;

   if (I1.line_size_bits != LL.line_size_bits) return false;
   block1 =  a         >> I1.line_size_bits;
   block2 = (a+size-1) >> I1.line_size_bits;
   if (block1 != block2) return false;

   return true;
}

/*--------------------------------------------------------------------*/
/*--- end                                                 cg_sim.c ---*/
/*--------------------------------------------------------------------*/

int main(int argc, char **argv){
   cache_t  D1c, LLc;
   D1c = (cache_t) { 32768, 8, 64 };
   LLc = (cache_t) { 2097152, 16, 64 };
   cachesim_initcaches(D1c, LLc);
   char line[BUFFER_SIZE];
   char access;
   int line_no, size;
   unsigned long long int addr;
   ULong D1mr = 0, DLmr = 0;
   ULong D1mw = 0, DLmw = 0;
   ULong Dr = 0, Dw = 0;

   // Read the content from trace file
   FILE *fp;
   fp = fopen(argv[1], "r");
   if (fp == NULL) {
      printf("Error! Could not open file\n");
      return -1;
   }

   while (fgets(line, BUFFER_SIZE, fp) != NULL) {
      Addr addr;
      char type;
      sscanf(line, "**%*d** & %c %d %llx %d", &access, &line_no, &addr, &size);
      if (access == 'R') {
         Dr++;
         cachesim_D1_doref(addr, size, &D1mr, &DLmr);
      } else {
         Dw++;
         cachesim_D1_doref(addr, size, &D1mw, &DLmw);
      }
   }

   printf("Dr: %llu, D1mr: %llu, DLmr: %llu\n", Dr, D1mr, DLmr);
   printf("Dw: %llu, D1mw: %llu, DLmw: %llu\n", Dw, D1mw, DLmw);
}