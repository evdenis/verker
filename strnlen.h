#ifndef __STRNLEN_H__
#define __STRNLEN_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ axiomatic Strnlen {
    predicate valid_strn(char *s, size_t cnt) =
       (\exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n))) ||
       \valid(s+(0..cnt));

    axiom valid_strn_shift1:
       \forall char *s, size_t cnt;
       valid_strn(s, cnt) && cnt > 0 && *s != '\0' ==>
          valid_strn(s+1, (size_t)(cnt-1));

    logic size_t strnlen(char *s, size_t cnt) =
       (s[0] == '\0' || cnt == 0) ?
          (size_t)0 :
          (size_t)((size_t)1 + strnlen(s + 1, (size_t)(cnt-(size_t)1)));

    axiom strnlen_range:
       \forall char *s, size_t cnt;
          valid_strn(s, cnt) ==>
             0 <= strnlen(s, cnt) <= cnt;

    axiom strnlen_null:
       \forall char *s, size_t cnt;
       strnlen(s, cnt) == 0 <==> (*s == '\0' || cnt == 0);

    axiom strnlen_before_zero:
       \forall char* s, size_t i, cnt;
          valid_strn(s, cnt) &&
          0 <= i < strnlen(s, cnt) ==> s[i] != '\0';

    axiom strnlen_at_zero:
       \forall char* s, size_t cnt;
          valid_strn(s, cnt) && strnlen(s, cnt) < cnt ==>
             s[strnlen(s, cnt)] == '\0';

    axiom strnlen_at_cnt:
       \forall char* s, size_t i, cnt;
          valid_strn(s, cnt) && i == strnlen(s, cnt) ==>
             s[i] == '\0' || i == cnt;

    axiom strnlen_zero:
       \forall char *s, size_t cnt, n;
          valid_strn(s, cnt) &&
          n < cnt  &&
          s[n] == '\0' &&
          (\forall size_t i; i < n ==> s[i] != '\0') ==>
             strnlen(s, cnt) == n;

    axiom strnlen_cnt:
       \forall char *s, size_t cnt;
          valid_strn(s, cnt) &&
          (\forall size_t n; n < cnt ==> s[n] != '\0') ==>
             strnlen(s, cnt) == cnt;

    axiom strnlen_shift:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          i <= strnlen(s, cnt) ==>
             strnlen(s + i, cnt) == strnlen(s, cnt) - i;

    axiom strnlen_shift_ex:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          0 < i <= strnlen(s, cnt) ==>
             strnlen(s + i, cnt) < strnlen(s, cnt);

    axiom strnlen_shift1:
       \forall char *s, size_t cnt;
          valid_strn(s, cnt) && cnt > 0 && *s != '\0' ==>
             strnlen(s, cnt) == strnlen(s+1, (size_t)(cnt-1)) + 1;

    axiom strnlen_less:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          i <= cnt ==>
             strnlen(s, i) <= strnlen(s, cnt);

    axiom valid_str_strn:
       \forall char *s, size_t cnt;
          valid_str(s) && cnt <= strlen(s) ==>
             valid_strn(s, cnt);
    }
 */

/**
 * strnlen - Find the length of a length-limited string
 * @s: The string to be sized
 * @count: The maximum number of bytes to search
 */

/*@ requires valid_strn(s, count);
    assigns \nothing;
    ensures \result == strnlen(s, count);
    behavior null_byte:
       assumes \exists integer i; 0 <= i <= count && s[i] == '\0';
       ensures s[\result] == '\0';
       ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';
    behavior count_len:
       assumes \forall integer i; 0 <= i <= count ==> s[i] != '\0';
       ensures \result == count;
    complete behaviors;
    disjoint behaviors;
 */
size_t strnlen(const char *s, size_t count);

#endif // __STRNLEN_H__
