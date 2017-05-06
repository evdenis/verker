#ifndef __STRCHRNUL_H__
#define __STRCHRNUL_H__

#include "strlen.h"

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \base_addr(\result) == \base_addr(s);
    ensures s <= \result <= s + strlen(s);
    behavior not_exists:
       assumes \forall integer i; 0 <= i < strlen(s) ==> s[i] != (char %) c;
       ensures \result == s + strlen(s);
       ensures *\result == '\0';
    behavior exists:
       assumes \exists integer i; 0 <= i < strlen(s) && s[i] == (char %) c;
       ensures *\result == (char %) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchrnul(const char *s, int c);

#endif // __STRCHRNUL_H__