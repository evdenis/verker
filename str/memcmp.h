#ifndef __MEMCMP_H__
#define __MEMCMP_H__

#include "kernel_definitions.h"

/*@ requires \typeof(cs) <: \type(u8 *);
    requires \typeof(ct) <: \type(u8 *);
    requires \valid(((u8 *)cs)+(0..count-1));
    requires \valid(((u8 *)ct)+(0..count-1));
    requires \base_addr((u8 *)cs) == \base_addr((u8 *)ct) ^^
             \base_addr((u8 *)cs) != \base_addr((u8 *)ct);
    assigns \nothing;
    behavior equal:
       assumes \forall integer i; 0 <= i < count ==> ((u8 *)cs)[i] == ((u8 *)ct)[i];
       ensures \result == 0;
    behavior diff:
       assumes \exists integer i; 0 <= i < count && ((u8 *)cs)[i] != ((u8 *)ct)[i];
       ensures \exists integer i; 0 <= i < count &&
               (\forall integer j; 0 <= j < i ==> ((u8 *)cs)[j] == ((u8 *)ct)[j]) &&
               ((u8 *)cs)[i] != ((u8 *)ct)[i] &&
               \result == ((u8 *)cs)[i] - ((u8 *)ct)[i];
    complete behaviors;
    disjoint behaviors;
 */
__visible int memcmp(const void *cs, const void *ct, size_t count);

#endif // __MEMCMP_H__
