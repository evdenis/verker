#ifndef __STRLEN_H__
#define __STRLEN_H__

#include "kernel_definitions.h"

/*@ axiomatic Strlen {
    predicate valid_str(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    lemma valid_str_strend:
       \forall char *s;
          \valid(s) && *s == '\0' ==>
             valid_str(s);
    }
 */

/*
 * Lemma functions.
 *
 * The facts below need induction over the string, which no SMT solver
 * reaches. Under AstraVer they were written as 'lemma' functions, whose
 * contract the plugin generalised into an axiom automatically. Vanilla ACSL
 * has no such construct, so they are ordinary ghost functions: WP proves each
 * contract, and a caller makes the fact available by calling it from ghost
 * code.
 */

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ terminates \true;
  @  @ assigns \nothing;
  @  @ ensures s[\result] == '\0';
  @  @ ensures \valid(s+(0..\result));
  @  @ ensures \forall integer j; 0 <= j < \result ==> s[j] != '\0';
  @  @/
  @ size_t elim_valid_str(char *s)
  @ {
  @    /@ loop invariant 0 <= i;
  @     @ loop invariant \forall integer j; 0 <= j < i ==> s[j] != '\0';
  @     @ loop assigns i;
  @     @ loop variant SIZE_MAX - i;
  @     @/
  @    for (size_t i = 0; i <= SIZE_MAX; i++) {
  @      if (s[i] == '\0') return i;
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires \valid(s+(0..n));
  @  @ requires s[n] == '\0';
  @  @ requires \forall integer j; 0 <= j < n ==> s[j] != '\0';
  @  @ terminates \true;
  @  @ decreases n;
  @  @ assigns \nothing;
  @  @ ensures valid_str(s);
  @  @ ensures strlen(s) == n;
  @  @/
  @ void intro_valid_str_len(char *s, size_t n)
  @ {
  @   if (n > 0) intro_valid_str_len(s + 1, n - 1);
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ terminates \true;
  @  @ assigns \nothing;
  @  @ ensures s[strlen(s)] == '\0';
  @  @ ensures \valid(s+(0..strlen(s)));
  @  @ ensures \forall integer j; 0 <= j < strlen(s) ==> s[j] != '\0';
  @  @/
  @ void valid_str_len(char *s)
  @ {
  @   size_t n = elim_valid_str(s);
  @   intro_valid_str_len(s, n);
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires s[0] != '\0';
  @  @ terminates \true;
  @  @ assigns \nothing;
  @  @ ensures valid_str(s + 1);
  @  @ ensures strlen(s + 1) == strlen(s) - 1;
  @  @/
  @ void valid_str_shift(char *s)
  @ {
  @   size_t n = elim_valid_str(s);
  @   intro_valid_str_len(s, n);
  @   intro_valid_str_len(s + 1, n - 1);
  @ }
  @*/


/**
 * strlen - Find the length of a string
 * @s: The string to be sized
 */

/*@ requires valid_str(s);
    // the returned pointer difference is cast to size_t, so it has to fit in
    // ptrdiff_t; WP's memory model does not bound object sizes on its own
    requires strlen(s) <= LONG_MAX;
    terminates \true;
    assigns \nothing;
    exits \false;
    ensures \result == strlen(s);
    ensures s[\result] == '\0';
    ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';
 */
size_t strlen(const char *s);

#endif // __STRLEN_H__
