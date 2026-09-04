#ifndef __STRNLEN_H__
#define __STRNLEN_H__

#include "strlen.h"
#include "kernel_definitions.h"

/*@ axiomatic Strnlen {
    predicate valid_strn(char *s, size_t cnt) =
       (\exists size_t n; (n < cnt) && s[n] == '\0' && \valid(s+(0..n))) ||
       \valid(s+(0..cnt));

    lemma valid_str_to_valid_strn:
       \forall char *s, size_t cnt;
         valid_str(s) ==> valid_strn(s, cnt);

    logic size_t strnlen(char *s, size_t cnt) =
       (s[0] == '\0' || cnt == 0) ?
          (size_t)0 :
          (size_t)((size_t)1 + strnlen(s + 1, (size_t)(cnt-(size_t)1)));

    lemma strnlen_zero_count:
       \forall char *s;
         strnlen(s, (size_t) 0) == 0;

    }
 */

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas: the facts need induction, and vanilla ACSL has no equivalent of
 * AstraVer's self-generalising 'lemma' contract.
 */

/*@ ghost
  @ /@ requires valid_strn(s, cnt);
  @  @ terminates \true;
  @  @ assigns \nothing;
  @  @ ensures \result <= cnt;
  @  @ ensures \valid(s+(0..\result));
  @  @ ensures \forall integer j; 0 <= j < \result ==> s[j] != '\0';
  @  @ ensures \result < cnt ==> s[\result] == '\0';
  @  @/
  @ size_t elim_valid_strn(char *s, size_t cnt)
  @ {
  @    /@ loop invariant 0 <= i <= cnt;
  @     @ loop invariant \forall integer j; 0 <= j < i ==> s[j] != '\0';
  @     @ loop assigns i;
  @     @ loop variant cnt - i;
  @     @/
  @    for (size_t i = 0; i < cnt; i++) {
  @      if (s[i] == '\0') return i;
  @    }
  @    return cnt;
  @ }
  @*/

/*@ ghost
  @ /@ requires n <= cnt;
  @  @ requires \valid(s+(0..n));
  @  @ requires \forall integer j; 0 <= j < n ==> s[j] != '\0';
  @  @ requires n < cnt ==> s[n] == '\0';
  @  @ terminates \true;
  @  @ decreases n;
  @  @ assigns \nothing;
  @  @ ensures valid_strn(s, cnt);
  @  @ ensures strnlen(s, cnt) == n;
  @  @/
  @ void intro_valid_strn_len(char *s, size_t cnt, size_t n)
  @ {
  @   if (n > 0) intro_valid_strn_len(s + 1, cnt - 1, n - 1);
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_strn(s, cnt);
  @  @ terminates \true;
  @  @ assigns \nothing;
  @  @ ensures strnlen(s, cnt) <= cnt;
  @  @ ensures \valid(s+(0..strnlen(s, cnt)));
  @  @ ensures \forall integer j; 0 <= j < strnlen(s, cnt) ==> s[j] != '\0';
  @  @ ensures strnlen(s, cnt) < cnt ==> s[strnlen(s, cnt)] == '\0';
  @  @/
  @ void valid_strn_len(char *s, size_t cnt)
  @ {
  @   size_t n = elim_valid_strn(s, cnt);
  @   intro_valid_strn_len(s, cnt, n);
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_strn(s, cnt);
  @  @ requires cnt > 0;
  @  @ requires s[0] != '\0';
  @  @ terminates \true;
  @  @ assigns \nothing;
  @  @ ensures valid_strn(s + 1, (size_t)(cnt - 1));
  @  @ ensures strnlen(s, cnt) == strnlen(s + 1, (size_t)(cnt - 1)) + 1;
  @  @/
  @ void valid_strn_shift(char *s, size_t cnt)
  @ {
  @   size_t n = elim_valid_strn(s, cnt);
  @   intro_valid_strn_len(s, cnt, n);
  @   intro_valid_strn_len(s + 1, cnt - 1, n - 1);
  @ }
  @*/



/*@ ghost
  @ /@ requires  valid_strn(s, cnt);
  @  @ requires  i <= strnlen(s, cnt);
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   strnlen(s + i, (size_t)(cnt - i)) == strnlen(s, cnt) - i;
  @  @/
  @ void strnlen_shift(char *s, size_t cnt, size_t i)
  @ {
  @   if (i > 0) {
  @     valid_strn_shift(s, cnt);
  @     strnlen_shift(s + 1, cnt - 1, i - 1);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_strn(s, cnt);
  @  @ requires  i <= cnt;
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   strnlen(s, i) <= strnlen(s, cnt);
  @  @/
  @ void strnlen_less(char *s, size_t i, size_t cnt)
  @ {
  @   if (i > 0 && s[0] != '\0') {
  @     valid_strn_shift(s, cnt);
  @     strnlen_less(s + 1, i - 1, cnt - 1);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  strlen(s) < cnt;
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   strnlen(s, cnt) == strlen(s);
  @  @/
  @ void strnlen_is_strlen(char *s, size_t cnt)
  @ {
  @   size_t m = elim_valid_str(s);
  @   intro_valid_str_len(s, m);
  @   intro_valid_strn_len(s, cnt, m);
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(s1);
  @  @ requires  valid_strn(s2, cnt);
  @  @ requires  strlen(s1) < strnlen(s2, cnt);
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   strnlen(s1, cnt) < strnlen(s2, cnt);
  @  @/
  @ void strnlen_cmp(char *s1, char *s2, size_t cnt)
  @ {
  @   valid_strn_len(s2, cnt);
  @   strnlen_is_strlen(s1, cnt);
  @ }
  @*/

/**
 * strnlen - Find the length of a length-limited string
 * @s: The string to be sized
 * @count: The maximum number of bytes to search
 */

/*@ requires valid_strn(s, count);
    // the returned pointer difference is cast to size_t, so it has to fit in
    // ptrdiff_t; WP's memory model does not bound object sizes on its own
    requires count <= LONG_MAX;
    terminates \true;
    assigns \nothing;
    exits \false;
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
