#ifndef __STRSPN_H__
#define __STRSPN_H__

#include "kernel_definitions.h"
#include "strlen.h"

#ifndef LEMMA_FUNCTIONS

/*@ axiomatic StrSpn {
    predicate in_array(char *s, char c) =
       \exists integer i; 0 <= i < strlen(s) && s[i] == c;

    logic integer strspn(char *s, char *accept) =
       *s == '\0' || ! in_array(accept, *s) ? 0 : 1 + strspn(s + 1, accept);

    lemma strspn_strend:
       \forall char *s, *accept;
          \valid(s) && *s == '\0' ==>
             strspn(s, accept) == 0;

    lemma strspn_empty_accept:
       \forall char *s, *accept;
          \valid(accept) && *accept == '\0' ==>
             strspn(s, accept) == 0;

    lemma strspn_shift1:
       \forall char *s, *accept;
          valid_str(s) && valid_str(accept) && *s != '\0' &&
          in_array(accept, *s) ==>
             strspn(s, accept) == strspn(s + 1, accept) + 1;

    lemma strspn_stop_not_in_accept:
       \forall char *s, *accept;
          valid_str(s) && valid_str(accept) && *s != '\0' &&
          !in_array(accept, *s) ==>
             strspn(s, accept) == 0;
    }
 */

#else

/*@ axiomatic StrSpn {
    predicate in_array(char *s, char c) =
       \exists integer i; 0 <= i < strlen(s) && s[i] == c;

    logic integer strspn(char *s, char *accept) =
       *s == '\0' || ! in_array(accept, *s) ? 0 : 1 + strspn(s + 1, accept);
    }
 */

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s);
  @  @ requires *s != '\0';
  @  @ requires *s != c;
  @  @ ensures  in_array(s, c) <==> in_array(s + 1, c);
  @  @/
  @  void in_array_shift1(char *s, char c)
  @  {
  @  }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s);
  @  @ requires *s != '\0';
  @  @ requires *s == c;
  @  @ ensures  in_array(s, c);
  @  @/
  @  void in_array_true(char *s, char c)
  @  {
  @  }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s);
  @  @ requires *s == '\0';
  @  @ ensures  !in_array(s, c);
  @  @/
  @  void in_array_false(char *s, char c)
  @  {
  @  }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires \valid(s);
  @  @ requires *s == '\0';
  @  @ ensures strspn(s, accept) == 0;
  @  @/
  @ void strspn_strend(char *s, char *accept)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires \valid(accept);
  @  @ requires *accept == '\0';
  @  @ ensures strspn(s, accept) == 0;
  @  @/
  @ void strspn_empty_accept(char *s, char *accept)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ decreases strlen(s);
  @  @ ensures \result != 0 <==> in_array(s, c);
  @  @/
  @ int in_array(char *s, char c)
  @ {
  @   if (*s == '\0') return 0;
  @   if (*s == c) return 1;
  @   return in_array(s + 1, c);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s) ;
  @  @ requires valid_str(accept);
  @  @ decreases strlen(s);
  @  @ ensures 0 <= strspn(s, accept) <= strlen(s);
  @  @/
  @ void strspn_range(char *s, char *accept)
  @ {
  @   if (*s != '\0' && in_array(accept, *s)) {
  @     strspn_range(s + 1, accept);
  @   }
  @ }
  @*/

#endif

/*
 * Lemma functions for in_array. See strlen.h for why these are ghost functions
 * rather than ACSL lemmas.
 */

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires *s == '\0';
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   !in_array(s, c);
  @  @/
  @ void in_array_false(char *s, char c)
  @ {
  @   valid_str_len(s);
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires *s != '\0';
  @  @ requires *s == c;
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   in_array(s, c);
  @  @/
  @ void in_array_true(char *s, char c)
  @ {
  @   valid_str_len(s);
  @   /@ assert 0 <= 0 < strlen(s) && s[0] == c; @/
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires in_array(s, c);
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   0 <= \result < strlen(s);
  @  @ ensures   s[\result] == c;
  @  @/
  @ size_t in_array_elim(char *s, char c)
  @ {
  @   size_t n = elim_valid_str(s);
  @   intro_valid_str_len(s, n);
  @   /@ loop invariant 0 <= i <= n;
  @    @ loop invariant \forall integer j; 0 <= j < i ==> s[j] != c;
  @    @ loop assigns i;
  @    @ loop variant n - i;
  @    @/
  @   for (size_t i = 0; i < n; i++) {
  @     if (s[i] == c) return i;
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires 0 <= i < strlen(s);
  @  @ requires s[i] == c;
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   in_array(s, c);
  @  @/
  @ void in_array_intro(char *s, char c, size_t i)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires *s != '\0';
  @  @ requires *s != c;
  @  @ requires in_array(s, c);
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   in_array(s + 1, c);
  @  @/
  @ void in_array_shift1_fwd(char *s, char c)
  @ {
  @   size_t i = in_array_elim(s, c);
  @   valid_str_shift(s);
  @   in_array_intro(s + 1, c, i - 1);
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires *s != '\0';
  @  @ requires in_array(s + 1, c);
  @  @ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   in_array(s, c);
  @  @/
  @ void in_array_shift1_bwd(char *s, char c)
  @ {
  @   valid_str_shift(s);
  @   size_t j = in_array_elim(s + 1, c);
  @   in_array_intro(s, c, j + 1);
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  valid_str(accept);
  @  @ terminates \true;
  @  @ decreases strlen(s);
  @  @ assigns   \nothing;
  @  @ ensures   0 <= strspn(s, accept) <= strlen(s);
  @  @/
  @ void strspn_range(char *s, char *accept)
  @ {
  @   if (*s != '\0') {
  @     valid_str_shift(s);
  @     strspn_range(s + 1, accept);
  @   }
  @ }
  @*/

/**
 * strspn - Calculate the length of the initial substring of @s which only contain letters in @accept
 * @s: The string to be searched
 * @accept: The string to search for
 */

/*@ requires valid_str(s);
    requires valid_str(accept);
    terminates \true;
    assigns \nothing;
    exits \false;
    ensures 0 <= \result <= strlen(s);
    ensures !in_array(accept, s[\result]);
    ensures \forall integer i; 0 <= i < \result ==> in_array(accept, s[i]);
    ensures \result == strspn(s, accept);
 */
size_t strspn(const char *s, const char *accept);

#endif // __STRSPN_H__
