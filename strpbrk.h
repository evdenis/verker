#ifndef __STRPBRK_H__
#define __STRPBRK_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strspn.h"

/*@ axiomatic StrPBrk {
    logic char *strpbrk(char *cs, char *ct);

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
