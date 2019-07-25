#ifndef __STRNLEN_H__
#define __STRNLEN_H__

#include "strlen.h"
#include "kernel_definitions.h"

#ifndef LEMMA_FUNCTIONS

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
         strnlen(s, (size_t) 0) == 0;

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
    }
 */

#else

/*@ axiomatic Strnlen {
    predicate valid_strn(char *s, size_t cnt) =
       (\exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n))) ||
       \valid(s+(0..cnt));

    logic size_t strnlen(char *s, size_t cnt) =
       (s[0] == '\0' || cnt == 0) ?
          0 :
          (size_t)(1 + strnlen(s + 1, (size_t)(cnt-1)));
    }
 */

/*@ ghost
  @ /@ requires valid_strn(s, cnt);
  @  @ ensures  \result <= cnt;
  @  @ ensures  \valid(s+(0..\result));
  @  @ ensures  \forall integer j; 0 <= j < \result ==> s[j] != '\0';
  @  @ ensures  \result < cnt ==> s[\result] == '\0';
  @  @/
  @ size_t elim_valid_strn(char *s, size_t cnt)
  @ {
  @    /@ loop invariant \forall integer j; 0 <= j < i ==> s[j] != '\0';
  @     @ loop variant cnt - i;
  @     @/
  @    for (size_t i = 0; i < cnt; i++) {
  @      if (s[i] == '\0') return i;
  @    }
  @    return cnt;
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_strn(s, cnt);
  @  @ ensures  \result <= cnt;
  @  @ ensures  \valid(s+(0..\result));
  @  @ ensures  \forall integer j; 0 <= j < \result ==> s[j] != '\0';
  @  @ ensures  \result < cnt ==> s[\result] == '\0';
  @  @ ensures  strnlen(s, cnt) == \result;
  @  @/
  @ size_t elim_valid_strn_len(char *s, size_t cnt)
  @ {
  @    size_t size = elim_valid_strn(s, cnt);
  @    /@ loop invariant strnlen(s + i, (size_t)(cnt - i)) + i <= size ==>
  @     @                  strnlen(s, cnt) == strnlen(s + i, (size_t)(cnt - i)) + i;
  @     @ loop invariant 0 <= i <= size;
  @     @ loop variant size - i;
  @     @/
  @    for (size_t i = 0; i <= size; i++) {
  @      if (s[i] == '\0' || i == cnt) return i;
  @      //@ assert strnlen(s + i, (size_t)(cnt - i)) == (size_t)(strnlen(s + i + 1, (size_t)(cnt - i - 1)) + 1);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_strn(s, cnt);
  @  @ ensures  strnlen(s, cnt) <= cnt;
  @  @ ensures  \valid(s+(0..strnlen(s, cnt)));
  @  @ ensures  \forall integer j; 0 <= j < strnlen(s, cnt) ==> s[j] != '\0';
  @  @ ensures  strnlen(s, cnt) < cnt ==> s[strnlen(s, cnt)] == '\0';
  @  @/
  @ void valid_strn_len(char *s, size_t cnt)
  @ {
  @    elim_valid_strn_len(s, cnt);
  @ }
  @*/

/*@ ghost
  @ /@ requires n <= cnt;
  @  @ requires \valid(s+(0..n));
  @  @ requires \forall integer j; 0 <= j < n ==> s[j] != '\0';
  @  @ requires n < cnt ==> s[n] == '\0';
  @  @ ensures  valid_strn(s, cnt);
  @  @ ensures  strnlen(s, cnt) == n;
  @  @/
  @ void intro_valid_strn_len(char *s, size_t cnt, size_t n)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_strn(s, cnt) && cnt > 0 && *s != '\0';
  @  @ ensures  valid_strn(s+1, (size_t)(cnt-1));
  @  @ ensures  strnlen(s + 1, (size_t)(cnt  - 1)) == strnlen(s, cnt) - 1;
  @  @/
  @ void valid_strn_shift1(char *s, size_t cnt)
  @ {
  @    intro_valid_strn_len(s + 1, cnt - 1, elim_valid_strn(s, cnt) - 1);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_strn(s, cnt);
  @  @ ensures  0 <= strnlen(s, cnt) <= cnt;
  @  @/
  @ void strnlen_range(char *s, size_t cnt)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s);
  @  @ ensures  valid_strn(s, cnt);
  @  @/
  @ void valid_str_to_valid_strn(char *s, size_t cnt)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires \exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n));
  @  @ ensures  strnlen(s, cnt) == \min(strlen(s), cnt);
  @  @/
  @ void strnlen_min_len(char *s, size_t cnt)
  @ {
  @    //@ assert valid_str(s);
  @    //@ assert valid_strn(s, cnt);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_strn(s, cnt);
  @  @ requires i == strnlen(s, cnt);
  @  @ ensures  s[i] == '\0' || i == cnt;
  @  @/
  @ void strnlen_at_cnt(char *s, size_t cnt, size_t i)
  @ {
  @ }
  @*/

#endif /* LEMMA_FUNCTIONS */


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
