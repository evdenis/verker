#ifndef __SKIP_SPACES_H__
#define __SKIP_SPACES_H__

#include "kernel_definitions.h"
#include "ctype.h"
#include "strlen.h"


/*@ axiomatic SkipSpaces {
    logic char *skip_spaces{L}(char *str) ;//=
       //isspace(*str) ? skip_spaces(str + 1) : str;
    axiom defn{L}:
       \forall char *str, size_t i;
       valid_str(str) && i <= strlen(str) &&
       (\forall size_t j; j < i ==> isspace(str[j])) &&
       !isspace(str[i]) ==>
          str + i == skip_spaces{L}(str);
    axiom deref{L}:
       \forall char *str; valid_str(str) ==>
          !isspace(*skip_spaces(str));
    axiom range{L}:
       \forall char *str;
       valid_str(str) ==>
          str <= skip_spaces(str) <= str + strlen(str);
    axiom iter_one{L}:
       \forall char *str;
       valid_str(str) && !isspace(*str) ==>
       skip_spaces(str) == skip_spaces(str+1);
    axiom base_addr{L}:
       \forall char *str;
       valid_str(str) ==>
          \base_addr(str) == \base_addr(skip_spaces(str));
    axiom same{L}:
       \forall char *str;
       \valid(str) && !isspace(*str) ==>
          str == skip_spaces(str);
    axiom skipped_are_spaces{L}:
       \forall char *str, size_t i;
       valid_str{L}(str) &&
       i < skip_spaces{L}(str) - str ==>
          isspace(str[i]);
    }
 */

/**
 * skip_spaces - Removes leading whitespace from @str.
 * @str: The string to be stripped.
 *
 * Returns a pointer to the first non-whitespace character in @str.
 */

/*@ requires valid_str(str);
    assigns \nothing;
    ensures \result == skip_spaces(str);
    ensures \base_addr(\result) == \base_addr(str);
    ensures str <= \result <= str + strlen(str);
    ensures !isspace(*\result);
    ensures \forall char *p; str <= p < \result ==> isspace(*p);
    ensures valid_str(\result);
 */
char *skip_spaces(const char *str);

#endif // __SKIP_SPACES_H__
