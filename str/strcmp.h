#ifndef __STRCMP_H__
#define __STRCMP_H__

#include "strlen.h"

/*@ requires valid_string(cs);
    requires valid_string(ct);
    assigns \nothing;
    ensures \result == -1 || \result == 0 || \result == 1;
    behavior equal:
       assumes \forall size_t i; i <= strlen(cs) ==> cs[i] == ct[i];
       ensures \result == 0;
    behavior ne:
       assumes \exists size_t i; i <= strlen(cs) && cs[i] != ct[i];
       ensures \result == -1 || \result == 1;
       ensures \result == -1 ==> \exists size_t i; i <= strlen(cs) && cs[i] < ct[i];
       ensures \result == 1 ==> \exists size_t i; i <= strlen(cs) && cs[i] >= ct[i];
 */
int strcmp(const char *cs, const char *ct);

#endif // __STRCMP_H__