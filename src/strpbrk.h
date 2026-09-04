#ifndef __STRPBRK_H__
#define __STRPBRK_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strspn.h"

/*@ axiomatic StrPBrk {
    logic char *strpbrk{L}(char *s, char *ct) =
      *s == '\0' ? (char*)\null : in_array(ct, *s) ? s : strpbrk(s + 1, ct);

    lemma strpbrk_strend:
       \forall char *cs, *ct;
          \valid(cs) && *cs == '\0' ==>
             strpbrk(cs, ct) == \null;

    lemma strpbrk_shift1:
       \forall char *cs, *ct;
          valid_str(cs) && valid_str(ct) && *cs != '\0' &&
          !in_array(ct, *cs) ==>
             strpbrk(cs, ct) == strpbrk(cs + 1, ct);

    lemma strpbrk_stop_in_ct:
       \forall char *cs, *ct;
          valid_str(cs) && valid_str(ct) && *cs != '\0' &&
          in_array(ct, *cs) ==>
             strpbrk(cs, ct) == cs;
    }
 */

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas.
 */

/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  valid_str(ct);
  @  @ terminates \true;
  @  @ decreases strlen(s);
  @  @ assigns   \nothing;
  @  @ ensures   strpbrk(s, ct) == \null ||
  @  @           0 <= strpbrk(s, ct) - s < strlen(s);
  @  @/
  @ void strpbrk_range(char *s, char *ct)
  @ {
  @   if (*s != '\0') {
  @     valid_str_shift(s);
  @     strpbrk_range(s + 1, ct);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  valid_str(ct);
  @  @ requires  *ct == '\0';
  @  @ terminates \true;
  @  @ decreases strlen(s);
  @  @ assigns   \nothing;
  @  @ ensures   strpbrk(s, ct) == \null;
  @  @/
  @ void strpbrk_empty_ct(char *s, char *ct)
  @ {
  @   if (*s != '\0') {
  @     in_array_false(ct, *s);
  @     valid_str_shift(s);
  @     strpbrk_empty_ct(s + 1, ct);
  @   }
  @ }
  @*/


/**
 * strpbrk - Find the first occurrence of a set of characters
 * @cs: The string to be searched
 * @ct: The characters to search for
 */

/*@ requires valid_str(cs);
    requires valid_str(ct);
    terminates \true;
    assigns \result \from cs, ct;
    exits \false;
    ensures \result == strpbrk(cs, ct);
    behavior found:
       assumes \exists integer i; 0 <= i < strlen(cs) && in_array(ct, cs[i]);
       ensures 0 <= \result - cs < strlen(cs);
       ensures in_array(ct, *\result);
       ensures \forall integer i; 0 <= i < \result - cs ==> !in_array(ct, cs[i]);
    behavior not_found:
       assumes \forall integer i; 0 <= i < strlen(cs) ==> !in_array(ct, cs[i]);
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strpbrk(const char *cs, const char *ct);

#endif // __STRPBRK_H__
