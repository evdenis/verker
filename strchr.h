#ifndef __STRCHR_H__
#define __STRCHR_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ axiomatic Strchr {
    logic char *strchr(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? (char *) \null : strchr(str+1, c));

    axiom mem:
       \forall char *str, c;
       valid_str(str) ==>
          (str <= strchr(str, c) <= str + strlen(str)) ^^
          strchr(str, c) == \null;
    axiom iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchr(str, c) == strchr(str+1, c);
    axiom res:
       \forall char *str, c;
       valid_str(str) ==>
          strchr(str, c) == \null ^^ *strchr(str, c) == c;
    axiom at_end_zero:
       \forall char *str, c;
       \valid(str) && *str == '\0' ==>
          strchr(str, c) == \null;
    axiom at_end_char:
       \forall char *str, c;
       \valid(str) && *str == c ==>
          strchr(str, c) == str;

    axiom defn:
       \forall char *str, c, integer i;
       valid_str(str) && 0 <= i <= strlen(str) &&
       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strchr(str, c);
    axiom skipped:
       \forall char *str, c, integer i;
       valid_str(str) &&
       0 <= i < strchr(str, c) - str <= strlen(str) ==>
          str[i] != c;
    }
 */

/**
 * strchr - Find the first occurrence of a character in a string
 * @s: The string to be searched
 * @c: The character to search for
 */

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \result == strchr(s, (char %) c);
    behavior not_exists:
       assumes \forall char *p; s <= p <= s + strlen(s) ==> *p != (char %) c;
       ensures \result == \null;
    behavior exists:
       assumes \exists char *p; s <= p <= s + strlen(s) && *p == (char %) c;
       ensures s <= \result <= s + strlen(s);
       ensures *\result == (char %) c;
       ensures \forall char *p; s <= p < \result ==> *p != (char %) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchr(const char *s, int c);

#endif // __STRCHR_H__