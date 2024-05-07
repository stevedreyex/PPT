#ifndef COMMON_H
#define COMMON_H

#include<utility>
#include<bitset>

typedef  unsigned char   UChar;
typedef    signed char   Char;
typedef           char   HChar; /* signfulness depends on host */

typedef  unsigned int    UInt;
typedef    signed int    Int;

typedef  unsigned char   Bool;
#define  True   ((Bool)1)
#define  False  ((Bool)0)

typedef  unsigned long   UWord;

typedef  UWord           SizeT;
typedef  UWord           Addr;

typedef  unsigned long long int   ULong;
typedef    signed long long int   Long;

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
   union{
        int          *fifo_tail_pos;
        bool         *referencedNru;
        short int    *RRPV;
   };
   union {
        unsigned long*       tags;
        std::pair<long long int,long long int>* cacheLfu;
   };
   
} cache_t2;

#endif