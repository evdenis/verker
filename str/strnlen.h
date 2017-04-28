#ifndef __STRNLEN_H__
#define __STRNLEN_H__

#include "kernel_definitions.h"

/*@ axiomatic Strings {
    predicate valid_strn(char *s, size_t count) =
       (\exists size_t n; (n < count) && s[n] == '\0' && \valid(s+(0..n))) ||
       \valid(s+(0..count));

    lemma valid_strn_shift1:
       \forall char *s, size_t count;
       valid_strn(s, count) && count > 0 && *s != '\0' ==>
       valid_strn(s+1, (size_t)(count-1));

    logic size_t strnlen(char *s, size_t count) =
       (s[0] == '\0' || count == 0) ?
          (size_t)0 :
          (size_t)((size_t)1 + strnlen(s + 1, (size_t)(count-(size_t)1)));

    lemma strnlen_range:
       \forall char *s, size_t count;
       valid_strn(s, count) ==>
          0 <= strnlen(s, count) <= count;

    lemma strnlen_before_zero:
       \forall char* s, size_t i, cnt;
          valid_strn(s, cnt) &&
          0 <= i < strnlen(s, cnt) ==> s[i] != '\0';

    lemma strnlen_at_zero:
       \forall char* s, size_t cnt;
          valid_strn(s, cnt) && strnlen(s, cnt) < cnt ==>
          s[strnlen(s, cnt)] == '\0';

    lemma strnlen_at_count:
       \forall char* s, size_t i, cnt;
          valid_strn(s, cnt) && i == strnlen(s, cnt) ==>
          s[i] == '\0' || i == cnt;

    lemma strnlen_zero:
       \forall char *s, size_t count, n;
       valid_strn(s, count) &&
       n < count   &&
       s[n] == '\0' &&
       (\forall size_t i; i < n ==> s[i] != '\0') ==>
           strnlen(s, count) == n;

    lemma strnlen_count:
       \forall char *s, size_t count;
       valid_strn(s, count) &&
       (\forall size_t n; n < count ==> s[n] != '\0') ==>
           strnlen(s, count) == count;

    lemma strnlen_shift:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          i <= strnlen(s, cnt) ==>
          strnlen(s + i, cnt) == strnlen(s, cnt) - i;

    lemma strnlen_shift_ex:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          0 < i <= strnlen(s, cnt) ==>
          strnlen(s + i, cnt) < strnlen(s, cnt);

    lemma strnlen_less:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          i <= cnt ==>
          strnlen(s, i) <= strnlen(s, cnt);
    }
 */

/*@ requires valid_strn(s, count);
    assigns \nothing;
    ensures \result == strnlen(s, count);
 */
size_t strnlen(const char *s, size_t count);

#endif // __STRNLEN_H__