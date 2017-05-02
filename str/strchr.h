#ifndef __STRCHR_H__
#define __STRCHR_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ axiomatic Strchr {
    logic char *strchr(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? (char *) \null : strchr(str+1, c));

    lemma mem:
       \forall char *str, c;
       valid_str(str) ==>
          ((str <= strchr(str, c) <= str + strlen(str))  &&
          \base_addr(str) == \base_addr(strchr(str, c))) ^^
          strchr(str, c) == \null;
    lemma iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
       strchr(str, c) == strchr(str+1, c);
    lemma at_end:
       \forall char *str, c;
       valid_str(str) ==>
          strchr(str, c) == \null ^^ *strchr(str, c) == c;

    lemma defn:
       \forall char *str, c, size_t i;
       valid_str(str) && i <= strlen(str) &&
       (\forall size_t j; j < i ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strchr(str, c);
    lemma skipped:
       \forall char *str, c, size_t i;
       valid_str(str) &&
       i < strchr(str, c) - str <= strlen(str) ==>
          str[i] != c;
    }
 */

/*@ requires valid_str(s);
    requires c == ((char %) c);
    assigns \nothing;
    ensures \result == strchr(s, (char %) c);
 */
char *strchr(const char *s, int c);

#endif // __STRCHR_H__