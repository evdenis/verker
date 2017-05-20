#ifndef __CHECK_BYTES8_H__
#define __CHECK_BYTES8_H__

#include "kernel_definitions.h"

/*@ axiomatic CheckBytes8 {
    logic u8 *check_bytes8(u8 *start, u8 value, integer bytes) =
       bytes == 0 ? (u8 *) \null :
          (*start != value ? start : check_bytes8(start + 1, value, bytes - 1));
    lemma check_bytes8_shift1:
       \forall u8 *start, value, integer bytes;
          bytes > 0 && \valid(start+(0..bytes-1)) && *start == value ==>
             check_bytes8(start, value, bytes) == check_bytes8(start + 1, value, bytes - 1);
    lemma check_bytes8_stop:
       \forall u8 *start, value, integer bytes;
          bytes > 0 && \valid(start+(0..bytes-1)) && *start != value ==>
             check_bytes8(start, value, bytes) == start;
    lemma check_bytes8_stop_bytes_zero:
       \forall u8 *start, value;
          check_bytes8(start, value, 0) == \null;
    }
 */

/*@ requires \valid(start+(0..bytes-1));
    assigns \nothing;
    ensures \result == check_bytes8(start, value, bytes);
    behavior found:
       assumes \exists u8 *i; start <= i < start + bytes && *i != value;
       ensures start <= (u8 *)\result < start + bytes;
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
