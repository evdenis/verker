#ifndef __MEMCHR_H__
#define __MEMCHR_H__

#include "kernel_definitions.h"

/**
 * memchr - Find a character in an area of memory.
 * @s: The memory area
 * @c: The byte to search for
 * @n: The size of the area.
 *
 * returns the address of the first occurrence of @c, or %NULL
 * if @c is not found
 */

/*@ requires \valid_read((char *)s+(0..n-1));
    terminates \true;
    assigns \result \from s;
    exits \false;
    behavior found:
       assumes \exists integer i; 0 <= i < n && ((char *)s)[i] == (char) c;
       ensures 0 <= (char *)\result - (char *)s < n;
       ensures \forall integer i; 0 <= i < (char *)\result - (char *)s ==>
               ((char *)s)[i] != (char) c;
       ensures *((char *)\result) == (char) c;
    behavior not_exists:
       assumes \forall integer i; 0 <= i < n ==> ((char *)s)[i] != (char) c;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
void *memchr(const void *s, int c, size_t n);

#endif // __MEMCHR_H__
