#ifndef __STRSPN_H__
#define __STRSPN_H__

#include "kernel_definitions.h"
#include "strlen.h"

/**
 * strspn - Calculate the length of the initial substring of @s which only contain letters in @accept
 * @s: The string to be searched
 * @accept: The string to search for
 */

/*@ axiomatic StrSpn {
    predicate in_array(char *s, char c) = \exists char *p; s <= p < s + strlen(s) && *p == c;

    //lemma in_array_shift1:
    //   \forall char *s, c;
    //     valid_str(s) && s != '\0' && *s != c ==>
    //         in_array(s, c) <==> in_array(s + 1, c);
    //lemma in_array_true:
    //   \forall char *s, c;
    //      valid_str(s) && s != '\0' && *s == c ==>
    //         in_array(s, c);
    //lemma in_array_false:
    //   \forall char *s, c;
    //      valid_str(s) && s == '\0' ==>
    //        !in_array(s, c);

    logic integer strspn(char *s, char *accept) =
      *s == '\0' || ! in_array(accept, *s) ? 0 : 1 + strspn(s + 1, accept);

    //lemma strspn_strend:
    //   \forall char *s, *accept;
    //      \valid(s) && *s == '\0' ==>
    //         strspn(s, accept) == 0;

    //lemma strspn_empty_accept:
    //   \forall char *s, *accept;
    //      \valid(accept) && *accept == '\0' ==>
    //         strspn(s, accept) == 0;

    //lemma strspn_range:
    //   \forall char* s, *accept;
    //      valid_str(s) && valid_str(accept) ==>
    //         0 <= strspn(s, accept) <= strlen(s);

    //lemma strspn_shift1:
    //   \forall char *s, *accept;
    //      valid_str(s) && valid_str(accept) && *s != '\0' &&
    //      in_array(accept, *s) ==>
    //         strspn(s, accept) == strspn(s + 1, accept) + 1;

    //lemma strspn_stop_not_in_accept:
    //   \forall char *s, *accept;
    //      valid_str(s) && valid_str(accept) && *s != '\0' &&
    //      !in_array(accept, *s) ==>
    //         strspn(s, accept) == 0;
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

/*@ requires valid_str(s);
    requires valid_str(accept);
    assigns \nothing;
    ensures 0 <= \result <= strlen(s);
    ensures \forall char *t; accept <= t < accept + strlen(accept) ==> s[\result] != *t;
    ensures \forall char *p; s <= p < s + \result ==>
            (\exists char *t; accept <= t < accept + strlen(accept) && *p == *t);
    ensures \result == strspn(s, accept);
 */
size_t strspn(const char *s, const char *accept);

#endif // __STRSPN_H__
