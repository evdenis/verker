#ifndef __MEMSET_H__
#define __MEMSET_H__

#include "kernel_definitions.h"

/**
 * memset - Fill a region of memory with the given value
 * @s: Pointer to the start of the area.
 * @c: The byte to fill the area with
 * @count: The size of the area.
 *
 * Do not use memset() to access IO space, use memset_io() instead.
 */

/*@ requires \valid((char *)s+(0..count-1));
    terminates \true;
    assigns ((char *)s)[0..count-1];
    assigns \result \from s;
    exits \false;
    ensures \forall integer i; 0 <= i < count ==> ((char *)s)[i] == (char) c;
    ensures \result == s;
 */
void *memset(void *s, int c, size_t count);

#endif // __MEMSET_H__
