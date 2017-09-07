#ifndef __STRCSPN_H__
#define __STRCSPN_H__

#include "kernel_definitions.h"
#include "strspn.h"
#include "strlen.h"

/**
 * strcspn - Calculate the length of the initial substring of @s which does not contain letters in @reject
 * @s: The string to be searched
 * @reject: The string to avoid
 */

/*@ axiomatic StrCSpn {
    logic integer strcspn{L}(char *s, char *reject);

    axiom strcspn_strend:
       \forall char *s, *reject;
          \valid(s) && *s == '\0' ==>
             strcspn(s, reject) == 0;

    axiom strcspn_empty_reject:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *reject == '\0' ==>
             strcspn(s, reject) == strlen(s);

    axiom strcspn_range:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) ==>
             0 <= strcspn(s, reject) <= strlen(s);

    axiom strcspn_shift1:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *s != '\0' &&
          !in_array(reject, *s) ==>
             strcspn(s, reject) == strcspn(s + 1, reject) + 1;

    axiom strcspn_stop_in_reject{L}:
       \forall char *s, *reject;
          valid_str{L}(s) && valid_str{L}(reject) && *s != '\0' &&
          in_array(reject, *s) ==>
             strcspn{L}(s, reject) == 0;
    }
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
