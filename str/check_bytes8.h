#ifndef __CHECK_BYTES8_H__
#define __CHECK_BYTES8_H__

#include "kernel_definitions.h"

/*@ requires \valid(start+(0..bytes-1));
    assigns \nothing;
    behavior found:
       assumes \exists u8 *i; start <= i < start + bytes && *i != value;
       ensures start <= (u8 *)\result <= start + bytes;
       ensures *((u8 *)\result) != value;
       ensures \forall u8 *j; start <= j < (u8 *)\result ==> *j == value;
    behavior not_exists:
       assumes \forall u8 *i; start <= i < start + bytes ==> *i == value;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes);

#endif // __CHECK_BYTES8_H__
