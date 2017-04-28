#ifndef __SKIP_SPACES_H__
#define __SKIP_SPACES_H__

#include "kernel_definitions.h"
#include "../ctype.h"
#include "strlen.h"


/*@ axiomatic SkipSpaces {
    logic char *skip_spaces(char *str) ;//=
       //isspace(*str) ? skip_spaces(str + 1) : str;
    lemma order:
       \forall char *str; str <= skip_spaces(str);
    lemma same:
       \forall char *str; !isspace(*str) ==>
          str == skip_spaces(str);
    lemma shift:
       \forall char *str, integer i;
          0 <= i < skip_spaces(str) - str ==> isspace(str[i]);
    }
 */

/*@ requires valid_str(str);
    assigns \nothing;
    ensures \base_addr(\result) == \base_addr(str);
    ensures \result == skip_spaces(str);
 */
char *skip_spaces(const char *str);

#endif // __SKIP_SPACES_H__