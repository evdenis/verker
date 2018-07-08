#ifndef __STRCHR_H__
#define __STRCHR_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ axiomatic Strchr {
    logic char *strchr(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? (char *) \null : strchr(str+1, c));

    lemma strchr_mem:
       \forall char *str, c;
       valid_str(str) ==>
          (str <= strchr(str, c) <= str + strlen(str)) ^^
          strchr(str, c) == \null;
    lemma strchr_iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchr(str, c) == strchr(str+1, c);
    lemma strchr_res:
       \forall char *str, c;
       valid_str(str) ==>
          strchr(str, c) == \null ^^ *strchr(str, c) == c;
    lemma strchr_at_end_zero:
       \forall char *str, c;
       \valid(str) && *str == '\0' ==>
          strchr(str, c) == \null;
    lemma strchr_at_end_char:
       \forall char *str, c;
       \valid(str) && *str == c ==>
          strchr(str, c) == str;

    lemma strchr_defn:
       \forall char *str, c, integer i;
       valid_str(str) && 0 <= i <= strlen(str) &&
       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strchr(str, c);
    lemma strchr_skipped:
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
    ensures \result == strchr(s, (char AENO) c);
    behavior not_exists:
       assumes \forall char *p; s <= p <= s + strlen(s) ==> *p != (char AENO) c;
       ensures \result == \null;
    behavior exists:
       assumes \exists char *p; s <= p <= s + strlen(s) && *p == (char AENO) c;
       ensures s <= \result <= s + strlen(s);
       ensures *\result == (char AENO) c;
       ensures \forall char *p; s <= p < \result ==> *p != (char AENO) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchr(const char *s, int c);

#endif // __STRCHR_H__
