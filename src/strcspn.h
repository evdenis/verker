#ifndef __STRCSPN_H__
#define __STRCSPN_H__

#include "kernel_definitions.h"
#include "strspn.h"
#include "strlen.h"

#ifndef LEMMA_FUNCTIONS

/*@ axiomatic StrCSpn {
    logic integer strcspn(char *s, char *reject) =
      *s == '\0' || in_array(reject, *s) ? 0 : 1 + strcspn(s + 1, reject);

    lemma strcspn_strend:
       \forall char *s, *reject;
          \valid(s) && *s == '\0' ==>
             strcspn(s, reject) == 0;

    lemma strcspn_empty_reject:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *reject == '\0' ==>
             strcspn(s, reject) == strlen(s);

    lemma strcspn_range:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) ==>
             0 <= strcspn(s, reject) <= strlen(s);

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

#else

/*@ axiomatic StrCSpn {
    logic integer strcspn(char *s, char *reject) =
      *s == '\0' || in_array(reject, *s) ? 0 : 1 + strcspn(s + 1, reject);
    }
 */

/*@ ghost
  @ /@ lemma
  @  @ requires \valid(s);
  @  @ requires *s == '\0';
  @  @ ensures strcspn(s, reject) == 0;
  @  @/
  @ void strcspn_strend(char *s, char *reject)
  @ {
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s);
  @  @ requires \valid(reject);
  @  @ requires *reject == '\0';
  @  @ decreases strlen(s);
  @  @ ensures strcspn(s, reject) == strlen(s);
  @  @/
  @ void strcspn_empty_accept(char *s, char *reject)
  @ {
  @  if (*s != '\0')
  @    strcspn_empty_accept(s + 1, reject);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s) ;
  @  @ requires valid_str(reject);
  @  @ decreases strlen(s);
  @  @ ensures 0 <= strcspn(s, reject) <= strlen(s);
  @  @/
  @ void strcspn_range(char *s, char *reject)
  @ {
  @   if (*s != '\0' && !in_array(reject, *s)) {
  @     strcspn_range(s + 1, reject);
  @   }
  @ }
  @*/

#endif /* LEMMA_FUNCTIONS */

/**
 * strcspn - Calculate the length of the initial substring of @s which does not contain letters in @reject
 * @s: The string to be searched
 * @reject: The string to avoid
 */

/*@ requires valid_str(s);
    requires valid_str(reject);
    assigns \nothing;
    ensures \result == strcspn(s, reject);
    ensures 0 <= \result <= strlen(s);
    ensures \forall char *p, *t;
            s <= p < s + \result &&
            reject <= t < reject + strlen(reject) ==>
            *p != *t;
    behavior exists:
       assumes \exists char *p, *t;
               s <= p < s + strlen(s) &&
               reject <= t < reject + strlen(reject) &&
               *p == *t;
       ensures \exists char *t; reject <= t < reject + strlen(reject) && s[\result] == *t;
    behavior not_exists:
       assumes \forall char *p, *t;
               s <= p < s + strlen(s) &&
               reject <= t < reject + strlen(reject) ==>
               *p != *t;
       ensures \result == strlen(s);
    complete behaviors;
    disjoint behaviors;
 */
size_t strcspn(const char *s, const char *reject);

#endif // __STRCSPN_H__
