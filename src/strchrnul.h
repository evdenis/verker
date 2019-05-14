#ifndef __STRCHRNUL_H__
#define __STRCHRNUL_H__

#include "strlen.h"

/*@ axiomatic Strchrnul {
    logic char *strchrnul(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? str : strchrnul(str+1, c));

    lemma strchrnul_mem:
       \forall char *str, c;
       valid_str(str) ==>
          (str <= strchrnul(str, c) <= str + strlen(str));
    lemma strchrnul_iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchrnul(str, c) == strchrnul(str+1, c);
    lemma strchrnul_res:
       \forall char *str, c;
       valid_str(str) ==>
          *strchrnul(str, c) == '\0' ^^ *strchrnul(str, c) == c;
    lemma strchrnul_strlen:
       \forall char *str;
       valid_str(str) ==>
          strlen(str) == strchrnul(str, (char)'\0') - str;
    lemma strchrnul_at_end:
       \forall char *str, c;
       \valid(str) && (*str == '\0' || *str == c) ==>
          strchrnul(str, c) == str;

    lemma strchrnul_defn:
       \forall char *str, c, integer i;
       valid_str(str) && 0 <= i <= strlen(str) &&
       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strchrnul(str, c);
    lemma strchrnul_skipped:
       \forall char *str, c, integer i;
       valid_str(str) &&
       0 <= i < strchrnul(str, c) - str <= strlen(str) ==>
          str[i] != c;
    }
 */

/**
 * strchrnul - Find and return a character in a string, or end of string
 * @s: The string to be searched
 * @c: The character to search for
 *
 * Returns pointer to first occurrence of 'c' in s. If c is not found, then
 * return a pointer to the null byte at the end of s.
 */

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \base_addr(\result) == \base_addr(s);
    ensures \result == strchrnul(s, (char AENO) c);
    ensures s <= \result <= s + strlen(s);
    behavior not_exists:
       assumes \forall integer i; 0 <= i < strlen(s) ==> s[i] != (char AENO) c;
       ensures \result == s + strlen(s);
       ensures *\result == '\0';
    behavior exists:
       assumes \exists integer i; 0 <= i < strlen(s) && s[i] == (char AENO) c;
       ensures *\result == (char AENO) c;
       ensures \forall char *p; s <= p < \result ==> *p != (char AENO) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchrnul(const char *s, int c);

#endif // __STRCHRNUL_H__
