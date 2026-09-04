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

/*@ requires \valid_read(start+(0..bytes-1));
    terminates \true;
    assigns \result \from start;
    exits \false;
    ensures \result == check_bytes8(start, value, bytes);
    behavior found:
       assumes \exists integer i; 0 <= i < bytes && start[i] != value;
       ensures \exists integer i; 0 <= i < bytes &&
               (\forall integer j; 0 <= j < i ==> start[j] == value) &&
               start[i] != value &&
               \result == (void *)(start + i);
    behavior not_exists:
       assumes \forall integer i; 0 <= i < bytes ==> start[i] == value;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes);

#endif // __CHECK_BYTES8_H__
