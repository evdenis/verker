#ifndef __STRPBRK_H__
#define __STRPBRK_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strspn.h"

#ifndef LEMMA_FUNCTIONS

/*@ axiomatic StrPBrk {
    logic char *strpbrk{L}(char *s, char *ct) =
      *s == '\0' ? (char*)\null : in_array(ct, *s) ? s : strpbrk(s + 1, ct);

    lemma strpbrk_strend:
       \forall char *cs, *ct;
          \valid(cs) && *cs == '\0' ==>
             strpbrk(cs, ct) == \null;

    lemma strpbrk_empty_ct:
       \forall char *cs, *ct;
          valid_str(cs) && valid_str(ct) && *ct == '\0' ==>
             strpbrk(cs, ct) == \null;

    lemma strpbrk_range:
       \forall char *cs, *ct;
          valid_str(cs) && valid_str(ct) ==>
             ((strpbrk(cs, ct) == \null) ^^
             (cs <= strpbrk(cs, ct) < cs + strlen(cs)));

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

#else

/*@ axiomatic StrPBrk {
    logic char *strpbrk{L}(char *s, char *ct) =
      *s == '\0' ? (char*)\null : in_array(ct, *s) ? s : strpbrk(s + 1, ct);
    }
 */

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(s);
  @  @ requires  valid_str(ct);
  @  @ decreases strlen(s);
  @  @ ensures   strpbrk(s, ct) == \null ^^ s <= strpbrk(s, ct) < s + strlen(s);
  @  @/
  @ void strpbrk_range(char *s, char *ct)
  @ {
  @   if (*s != '\0' && !in_array(ct, *s))
  @     strpbrk_range(s + 1, ct);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(s1);
  @  @ requires  valid_str(s2);
  @  @ requires  strlen(s2) >= strlen(s1);
  @  @ requires  valid_str(ct);
  @  @ requires  strpbrk(s1, ct) != \null;
  @  @ requires  \forall char *s; s2 <= s <= s2 + (strpbrk(s1, ct) - s1) ==> *s == s1[s - s2];
  @  @ decreases strlen(s1);
  @  @ ensures   strpbrk(s2, ct) != \null;
  @  @ ensures   strpbrk(s2, ct) - s2 == strpbrk(s1, ct) - s1;
  @  @/
  @ void strpbrk_frame(char *s1, char *s2, char *ct) {
  @   if (*s1 != '\0') {
  @     if (!in_array(ct, *s1)) {
  @       strpbrk_frame(s1 + 1, s2 + 1, ct);
  @     }
  @   }
  @ }
  @*/

#endif /* LEMMA_FUNCTIONS */

/**
 * strpbrk - Find the first occurrence of a set of characters
 * @cs: The string to be searched
 * @ct: The characters to search for
 */

/*@ requires valid_str(cs);
    requires valid_str(ct);
    assigns \nothing;
    ensures \result == strpbrk(cs, ct);
    behavior found:
       assumes \exists char *p, *t;
               cs <= p < cs + strlen(cs) &&
               ct <= t < ct + strlen(ct) &&
               *p == *t;
       ensures cs <= \result < cs + strlen(cs);
       ensures \exists char *t; ct <= t <= ct + strlen(ct) && *\result == *t;
       ensures \forall char *p, *t;
               cs <= p < \result &&
               ct <= t < ct + strlen(ct) ==>
               *p != *t;
    behavior not_found:
       assumes \forall char *p ,*t;
                cs <= p < cs + strlen(cs) &&
                ct <= t < ct + strlen(ct) ==>
                *p != *t;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strpbrk(const char *cs, const char *ct);

#endif // __STRPBRK_H__
