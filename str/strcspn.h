#ifndef __STRCSPN_H__
#define __STRCSPN_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ requires valid_str(s);
    requires valid_str(reject);
    assigns \nothing;
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