#ifndef __STRCHRNUL_H__
#define __STRCHRNUL_H__

#include "strlen.h"

/*@ axiomatic Strchrnul {
    logic char *strchrnul(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? str : strchrnul(str+1, c));

//    lemma strchrnul_mem:
//       \forall char *str, c;
//       valid_str(str) ==>
//          (str <= strchrnul(str, c) <= str + strlen(str));
//    lemma strchrnul_iter_one:
//       \forall char *str, c;
//       valid_str(str) && *str != c && *str != '\0' ==>
//          strchrnul(str, c) == strchrnul(str+1, c);
//    lemma strchrnul_res:
//       \forall char *str, c;
//       valid_str(str) ==>
//          *strchrnul(str, c) == '\0' ^^ *strchrnul(str, c) == c;
//    lemma strchrnul_strlen:
//       \forall char *str;
//       valid_str(str) ==>
//          strlen(str) == strchrnul(str, (char)'\0') - str;
//    lemma strchrnul_at_end:
//       \forall char *str, c;
//       \valid(str) && (*str == '\0' || *str == c) ==>
//          strchrnul(str, c) == str;

//    lemma strchrnul_defn:
//       \forall char *str, c, integer i;
//       valid_str(str) && 0 <= i <= strlen(str) &&
//       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
//       str[i] == c ==>
//          str + i == strchrnul(str, c);
//    lemma strchrnul_skipped:
//       \forall char *str, c, integer i;
//       valid_str(str) &&
//       0 <= i < strchrnul(str, c) - str <= strlen(str) ==>
//          str[i] != c;
    }
 */

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ decreases strlen(str);
  @  @ ensures   str <= strchrnul(str, c) <= str + strlen(str);
  @  @/
  @ void strchrnul_mem(char *str, char c)
  @ {
  @   if (*str != '\0' && *str != c)
  @     strchrnul_mem(str + 1, c);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  c != '\0';
  @  @ decreases strlen(str);
  @  @ ensures   *strchrnul(str, c) == '\0' ^^ *strchrnul(str, c) == c;
  @  @/
  @ void strchrnul_res(char *str, char c)
  @ {
  @   if (*str != '\0' && *str != c)
  @     strchrnul_res(str + 1, c);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ decreases strlen(str);
  @  @ ensures   strlen(str) == strchrnul(str, (char)'\0') - str;
  @  @/
  @ void strchrnul_strlen(char *str)
  @ {
  @   if (*str != '\0')
  @     strchrnul_strlen(str + 1);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  0 <= i <= strlen(str);
  @  @ requires  \forall integer j; 0 <= j < i ==> str[j] != c;
  @  @ requires  str[i] == c;
  @  @ decreases strlen(str);
  @  @ ensures   strchrnul(str, c) == str + i;
  @  @/
  @ void strchrnul_defn(char *str, char c, size_t i)
  @ {
  @   if (*str != '\0' && *str != c)
  @     strchrnul_defn(str + 1, c, i - 1);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  0 <= i < strchrnul(str, c) - str;
  @  @ decreases i;
  @  @ ensures   str[i] != c;
  @  @/
  @ void strchrnul_skipped(char *str, char c, size_t i)
  @ {
  @   if (i > 0)
  @     strchrnul_skipped(str + 1, c, i - 1);
  @ }
  @*/

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
