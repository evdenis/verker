#ifndef __STRCHRNUL_H__
#define __STRCHRNUL_H__

#include "strlen.h"

/*@ axiomatic Strchrnull {
    logic char *strchrnull(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? str : strchrnull(str+1, c));

    lemma mem:
       \forall char *str, c;
       valid_str(str) ==>
          (str <= strchrnull(str, c) <= str + strlen(str));
    lemma iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchrnull(str, c) == strchrnull(str+1, c);
    lemma res:
       \forall char *str, c;
       valid_str(str) ==>
          *strchrnull(str, c) == '\0' ^^ *strchrnull(str, c) == c;
    lemma strchrnull_strlen:
       \forall char *str;
       valid_str(str) ==>
          strlen(str) == strchrnull(str, (char)'\0') - str;
    lemma at_end:
       \forall char *str, c;
       (*str == '\0' || *str == c) ==>
          strchrnull(str, c) == str;

    lemma defn:
       \forall char *str, c, integer i;
       valid_str(str) && 0 <= i <= strlen(str) &&
       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strchrnull(str, c);
    lemma skipped:
       \forall char *str, c, integer i;
       valid_str(str) &&
       0 <= i < strchrnull(str, c) - str <= strlen(str) ==>
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
    ensures \result == strchrnull(s, (char %) c);
    ensures s <= \result <= s + strlen(s);
    behavior not_exists:
       assumes \forall integer i; 0 <= i < strlen(s) ==> s[i] != (char %) c;
       ensures \result == s + strlen(s);
       ensures *\result == '\0';
    behavior exists:
       assumes \exists integer i; 0 <= i < strlen(s) && s[i] == (char %) c;
       ensures *\result == (char %) c;
       ensures \forall char *p; s <= p < \result ==> *p != (char %) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchrnul(const char *s, int c);

#endif // __STRCHRNUL_H__