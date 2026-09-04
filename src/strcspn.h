#ifndef __STRCSPN_H__
#define __STRCSPN_H__

#include "kernel_definitions.h"
#include "strspn.h"
#include "strlen.h"

/*@ axiomatic StrCSpn {
    logic integer strcspn(char *s, char *reject) =
      *s == '\0' || in_array(reject, *s) ? 0 : 1 + strcspn(s + 1, reject);

    lemma strcspn_strend:
       \forall char *s, *reject;
          \valid(s) && *s == '\0' ==>
             strcspn(s, reject) == 0;

    lemma strcspn_shift1:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *s != '\0' &&
          !in_array(reject, *s) ==>
             strcspn(s, reject) == strcspn(s + 1, reject) + 1;

    lemma strcspn_stop_in_reject:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *s != '\0' &&
          in_array(reject, *s) ==>
             strcspn(s, reject) == 0;
    }
 */

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas. strcspn_range recurses on '*s != '\0'' alone: ghost code is C
 * and cannot branch on in_array, and the postcondition holds either way.
 */

/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  valid_str(reject);
  @  @ terminates \true;
  @  @ decreases strlen(s);
  @  @ assigns   \nothing;
  @  @ ensures   0 <= strcspn(s, reject) <= strlen(s);
  @  @/
  @ void strcspn_range(char *s, char *reject)
  @ {
  @   if (*s != '\0') {
  @     valid_str_shift(s);
  @     strcspn_range(s + 1, reject);
  @   }
  @ }
  @*/


/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  valid_str(reject);
  @  @ requires  *reject == '\0';
  @  @ terminates \true;
  @  @ decreases strlen(s);
  @  @ assigns   \nothing;
  @  @ ensures   strcspn(s, reject) == strlen(s);
  @  @/
  @ void strcspn_empty_reject(char *s, char *reject)
  @ {
  @   if (*s != '\0') {
  @     in_array_false(reject, *s);
  @     valid_str_shift(s);
  @     strcspn_empty_reject(s + 1, reject);
  @   }
  @ }
  @*/

/**
 * strcspn - Calculate the length of the initial substring of @s which does not contain letters in @reject
 * @s: The string to be searched
 * @reject: The string to avoid
 */

/*@ requires valid_str(s);
    requires valid_str(reject);
    terminates \true;
    assigns \nothing;
    exits \false;
    ensures \result == strcspn(s, reject);
    ensures 0 <= \result <= strlen(s);
    ensures \forall integer i; 0 <= i < \result ==> !in_array(reject, s[i]);
    behavior exists:
       assumes \exists integer i; 0 <= i < strlen(s) && in_array(reject, s[i]);
       ensures in_array(reject, s[\result]);
    behavior not_exists:
       assumes \forall integer i; 0 <= i < strlen(s) ==> !in_array(reject, s[i]);
       ensures \result == strlen(s);
    complete behaviors;
    disjoint behaviors;
 */
size_t strcspn(const char *s, const char *reject);

#endif // __STRCSPN_H__
