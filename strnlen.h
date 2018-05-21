#ifndef __STRNLEN_H__
#define __STRNLEN_H__

#include "strlen.h"
#include "kernel_definitions.h"

/*@ axiomatic Strnlen {
    predicate valid_strn(char *s, size_t cnt) =
       (\exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n))) ||
       \valid(s+(0..cnt));

    lemma valid_strn_shift1:
       \forall char *s, size_t cnt;
       valid_strn(s, cnt) && cnt > 0 && *s != '\0' ==>
          valid_strn(s+1, (size_t)(cnt-1));
    lemma valid_str_to_valid_strn:
       \forall char *s, size_t cnt;
         valid_str(s) ==> valid_strn(s, cnt);

    logic size_t strnlen(char *s, size_t cnt) =
       (s[0] == '\0' || cnt == 0) ?
          (size_t)0 :
          (size_t)((size_t)1 + strnlen(s + 1, (size_t)(cnt-(size_t)1)));

    lemma strnlen_range:
       \forall char *s, size_t cnt;
          valid_strn(s, cnt) ==>
             0 <= strnlen(s, cnt) <= cnt;

    lemma strnlen_null:
       \forall char *s, size_t cnt; \valid(s) ==>
         (strnlen(s, cnt) == 0 <==> (*s == '\0' || cnt == 0));

    lemma strnlen_zero_count:
       \forall char *s;
         strnlen(s, 0) == 0;

    lemma strnlen_min_len:
      \forall char *s, size_t cnt;
       (\exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n))) ==>
         strnlen(s, cnt) == \min(strlen(s), cnt);

    lemma strnlen_before_zero:
       \forall char* s, size_t i, cnt;
          valid_strn(s, cnt) &&
          0 <= i < strnlen(s, cnt) ==> s[i] != '\0';

    lemma strnlen_at_zero:
       \forall char* s, size_t cnt;
          valid_strn(s, cnt) && strnlen(s, cnt) < cnt ==>
             s[strnlen(s, cnt)] == '\0';

    lemma strnlen_at_cnt:
       \forall char* s, size_t i, cnt;
          valid_strn(s, cnt) && i == strnlen(s, cnt) ==>
             s[i] == '\0' || i == cnt;

    lemma strnlen_zero:
       \forall char *s, size_t cnt, n;
          valid_strn(s, cnt) &&
          n < cnt  &&
          s[n] == '\0' &&
          (\forall size_t i; i < n ==> s[i] != '\0') ==>
             strnlen(s, cnt) == n;

    lemma strnlen_cnt:
       \forall char *s, size_t cnt;
          valid_strn(s, cnt) &&
          (\forall size_t n; n < cnt ==> s[n] != '\0') ==>
             strnlen(s, cnt) == cnt;

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

    lemma strnlen_shift1:
       \forall char *s, size_t cnt;
          valid_strn(s, cnt) && cnt > 0 && *s != '\0' ==>
             strnlen(s, cnt) == strnlen(s+1, (size_t)(cnt-1)) + 1;

    lemma strnlen_cmp:
       \forall char *s1, *s2, size_t cnt;
       valid_str(s1) && valid_strn(s2, cnt) && strlen(s1) < strnlen(s2, cnt) ==>
         strnlen(s1, cnt) < strnlen(s2, cnt);

    lemma strnlen_less:
       \forall char *s, size_t i, cnt;
          valid_strn(s, cnt) &&
          i <= cnt ==>
             strnlen(s, i) <= strnlen(s, cnt);

    lemma valid_str_strn:
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
