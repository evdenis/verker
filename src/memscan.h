#ifndef __MEMSCAN_H__
#define __MEMSCAN_H__

#include "kernel_definitions.h"

/**
 * memscan - Find a character in an area of memory.
 * @addr: The memory area
 * @c: The byte to search for
 * @size: The size of the area.
 *
 * returns the address of the first occurrence of @c, or 1 byte past
 * the area if @c is not found
 */

/*@ requires \valid_read((char *)addr+(0..size-1));
    terminates \true;
    assigns \result \from addr;
    exits \false;
    ensures 0 <= (char *)\result - (char *)addr <= size;
    behavior found:
       assumes \exists integer i; 0 <= i < size &&
               (unsigned char)((char *)addr)[i] == c;
       ensures \exists integer i; 0 <= i < size &&
               (\forall integer j; 0 <= j < i ==>
                   (unsigned char)((char *)addr)[j] != c) &&
               (unsigned char)((char *)addr)[i] == c &&
               (char *)\result == (char *)addr + i;
    behavior not_exists:
       assumes \forall integer i; 0 <= i < size ==>
               (unsigned char)((char *)addr)[i] != c;
       ensures (char *)\result == (char *)addr + size;
    complete behaviors;
    disjoint behaviors;
 */
void *memscan(void *addr, int c, size_t size);

#endif // __MEMSCAN_H__
