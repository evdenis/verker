#ifndef __MEMCMP_H__
#define __MEMCMP_H__

#include "kernel_definitions.h"

/**
 * memcmp - Compare two areas of memory
 * @cs: One area of memory
 * @ct: Another area of memory
 * @count: The size of the area.
 */

/*@ requires \valid_read(((char *)cs)+(0..count-1));
    requires \valid_read(((char *)ct)+(0..count-1));
    terminates \true;
    assigns \nothing;
    exits \false;
    //ensures \result == 0 <==> memcmp((char *)cs, (char *)ct, count) == 0;
    //ensures \result < 0  <==> memcmp((char *)cs, (char *)ct, count) < 0;
    //ensures \result > 0  <==> memcmp((char *)cs, (char *)ct, count) > 0;
    // the body subtracts (unsigned char) values, so the equality direction
    // is stated on those; for chars that is the same relation
    ensures \result != 0 ==>
            (\exists integer i; 0 <= i < count &&
                                ((char *)cs)[i] != ((char *)ct)[i]);
    ensures \result == 0 ==>
            (\forall integer i; 0 <= i < count ==>
                                (unsigned char)((char *)cs)[i] == (unsigned char)((char *)ct)[i]);
    behavior equal:
       assumes \forall integer i; 0 <= i < count ==>
               (unsigned char)((char *)cs)[i] == (unsigned char)((char *)ct)[i];
       ensures \result == 0;
    behavior diff:
       assumes \exists integer i; 0 <= i < count &&
               (unsigned char)((char *)cs)[i] != (unsigned char)((char *)ct)[i];
       ensures \exists integer i; 0 <= i < count &&
               (\forall integer j; 0 <= j < i ==>
                   (unsigned char)((char *)cs)[j] == (unsigned char)((char *)ct)[j]) &&
               (unsigned char)((char *)cs)[i] != (unsigned char)((char *)ct)[i] &&
               \result == (unsigned char)((char *)cs)[i] - (unsigned char)((char *)ct)[i];
    complete behaviors;
    disjoint behaviors;
 */
__visible int memcmp(const void *cs, const void *ct, size_t count);

#endif // __MEMCMP_H__
