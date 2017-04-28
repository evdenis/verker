#ifndef __STRCHR_H__
#define __STRCHR_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ requires valid_str(s);
    requires c == ((char %) c);
    assigns \nothing;
    behavior not_exists:
       assumes \forall integer i; 0 <= i <= strlen(s) ==> s[i] != c;
       ensures \result == \null;
    behavior exists:
       assumes \exists integer i; 0 <= i <= strlen(s) && s[i] == c;
       ensures \base_addr(\result) == \base_addr(s);
       ensures s <= \result <= s + strlen(s);
       ensures *\result == c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchr(const char *s, int c);

#endif // __STRCHR_H__