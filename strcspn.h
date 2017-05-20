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
    logic integer strcspn(char *s, char *reject);

    lemma strcspn_strend:
       \forall char *s, *reject;
          *s == '\0' ==>
             strcspn(s, reject) == 0;

    lemma strcspn_empty_reject:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *reject == '\0' ==>
             strcspn(s, reject) == strlen(s);

    lemma strcspn_range:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) ==>
             0 <= strcspn(s, reject) <= strlen(s);

    lemma strcspn_shift:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *s != '\0' &&
          !in_array(reject, *s) ==>
             strcspn(s, reject) == 1 + strcspn(s + 1, reject);
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