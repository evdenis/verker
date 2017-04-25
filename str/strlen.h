#ifndef __STRLEN_H__
#define __STRLEN_H__

#include "kernel_definitions.h"

/*@ axiomatic Strings {
    predicate valid_string(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    lemma strlen_before_null:
       \forall char* s, integer i;
          valid_string(s) &&
          0 <= i < strlen(s) ==> s[i] != '\0';

    lemma strlen_at_null:
       \forall char* s;
          valid_string(s) ==> s[strlen(s)] == '\0';

    lemma strlen_shift:
       \forall char *s, size_t i;
          valid_string(s) &&
          i <= strlen(s)  ==>
          strlen(s+i) == strlen(s) + i;
    }
 */

/*@ requires valid_string(s);
    assigns \nothing;
    ensures \result == strlen(s);
 */
size_t strlen(const char *s);

#endif // __STRLEN_H__