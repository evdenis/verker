#ifndef __STRCASECMP_H__
#define __STRCASECMP_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "../ctype.h"

/*@ requires valid_str(s1);
    requires valid_str(s2);
    assigns \nothing;
    behavior equal:
       assumes \forall integer i; 0 <= i <= strlen(s1) ==> tolower(s1[i]) == tolower(s2[i]);
       ensures \result == 0;
    behavior not_equal:
       assumes \exists integer i; 0 <= i <= strlen(s1) && tolower(s1[i]) != tolower(s2[i]);
       ensures \result != 0;
       ensures \exists integer i; 0 <= i <= strlen(s1) &&
               (\forall integer j; 0 <= j < i ==> tolower(s1[j]) == tolower(s2[j])) &&
               tolower(s1[i]) != tolower(s2[i]) &&
               \result == tolower(s1[i]) - tolower(s2[i]);
    complete behaviors;
    disjoint behaviors;
 */
int strcasecmp(const char *s1, const char *s2);

#endif // __STRCASECMP_H__
