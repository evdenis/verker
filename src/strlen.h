#ifndef __STRLEN_H__
#define __STRLEN_H__

#include "kernel_definitions.h"

/*@ axiomatic Strlen {
    predicate valid_str(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    lemma valid_str_shift1:
       \forall char *s;
          *s != '\0' &&
          valid_str(s) ==>
             valid_str(s+1);

    lemma valid_str_strend:
       \forall char *s;
          \valid(s) && *s == '\0' ==>
             valid_str(s);

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    lemma strlen_before_null:
       \forall char* s, integer i;
          valid_str(s) &&
          0 <= i < strlen(s) ==> s[i] != '\0';

    lemma strlen_at_null:
       \forall char* s;
          valid_str(s) ==> s[strlen(s)] == '\0';

    lemma strlen_shift:
       \forall char *s, size_t i;
          valid_str(s) &&
          i <= strlen(s) ==>
          strlen(s+i) == strlen(s)-i;

    lemma strlen_shift_ex:
       \forall char *s, size_t i;
          valid_str(s) &&
          0 < i <= strlen(s) ==>
          strlen(s+i) < strlen(s);

    lemma strlen_shift1:
       \forall char *s;
          valid_str(s) && *s != '\0' ==>
          strlen(s) == 1 + strlen(s+1);

    lemma strlen_pointers:
       \forall char *s, *sc;
          valid_str(s)  &&
          valid_str(sc) &&
          \base_addr(s) == \base_addr(sc) &&
          s <= sc &&
          (\forall integer i; 0 <= i <= sc - s ==> s[i] != '\0') ==>
             strlen(sc) <= strlen(s);

    lemma strlen_main:
       \forall char *s, size_t n;
       valid_str(s) &&
       s[n] == '\0' &&
       (\forall integer i; 0 <= i < n ==> s[i] != '\0') ==>
           strlen(s) == n;

    lemma valid_str_shiftn:
       \forall char *s, integer i;
          valid_str(s) &&
          (0 <= i < strlen(s)) ==>
             valid_str(s+i);
    }
 */

/**
 * strlen - Find the length of a string
 * @s: The string to be sized
 */

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \result == strlen(s);
    ensures s[\result] == '\0';
    ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';
 */
size_t strlen(const char *s);

#endif // __STRLEN_H__
