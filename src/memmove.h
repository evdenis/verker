#ifndef __MEMMOVE_H__
#define __MEMMOVE_H__

#include "kernel_definitions.h"

/**
 * memmove - Copy one area of memory to another
 * @dest: Where to copy to
 * @src: Where to copy from
 * @count: The size of the area.
 *
 * Unlike memcpy(), memmove() copes with overlapping areas.
 */

/*@ requires \typeof(dest) <: \type(char *);
    requires \typeof(src) <: \type(char *);
    requires \valid((char *)dest+(0..count-1));
    requires \valid_read((char *)src+(0..count-1));
    requires \base_addr(dest) == \base_addr(src) ^^
             \base_addr(dest) != \base_addr(src);
    assigns ((char *)dest)[0..count-1];
    behavior same_addr:
      assumes \base_addr(dest) == \base_addr(src);
      ensures \forall integer i; 0 <= i < count ==> ((char *)dest)[i] == \at(((char *)src)[i], Pre);
    behavior diff_addr:
      assumes \base_addr(dest) != \base_addr(src);
      ensures \forall integer i; 0 <= i < count ==> ((char *)dest)[i] == \at(((char *)src)[i], Pre);
 */
void *memmove(void *dest, const void *src, size_t count);

#endif // __MEMMOVE_H__
