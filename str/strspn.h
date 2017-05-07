#ifndef __STRSPN_H__
#define __STRSPN_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ requires valid_str(s);
    requires valid_str(accept);
    assigns \nothing;
    ensures 0 <= \result <= strlen(s);
    ensures \forall char *t; accept <= t < accept + strlen(accept) ==> s[\result] != *t;
    ensures \forall char *p; s <= p < s + \result ==>
            (\exists char *t; accept <= t < accept + strlen(accept) && *p == *t);
 */
size_t strspn(const char *s, const char *accept);

#endif // __STRSPN_H__