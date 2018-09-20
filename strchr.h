#ifndef __STRCHR_H__
#define __STRCHR_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ axiomatic Strchr {
    logic char *strchr(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? (char *) \null : strchr(str+1, c));

//    lemma strchr_mem:
//       \forall char *str, c;
//       valid_str(str) ==>
//          (str <= strchr(str, c) <= str + strlen(str)) ^^
//          strchr(str, c) == \null;
//    lemma strchr_iter_one:
//       \forall char *str, c;
//       valid_str(str) && *str != c && *str != '\0' ==>
//          strchr(str, c) == strchr(str+1, c);
//    lemma strchr_res:
//       \forall char *str, c;
//       valid_str(str) ==>
//          strchr(str, c) == \null ^^ *strchr(str, c) == c;
//    lemma strchr_at_end_zero:
//       \forall char *str, c;
//       \valid(str) && *str == '\0' ==>
//          strchr(str, c) == \null;
//    lemma strchr_at_end_char:
//       \forall char *str, c;
//       \valid(str) && *str == c ==>
//          strchr(str, c) == str;

//    lemma strchr_defn:
//       \forall char *str, c, integer i;
//       valid_str(str) && 0 <= i <= strlen(str) &&
//       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
//       str[i] == c ==>
//          str + i == strchr(str, c);
//    lemma strchr_skipped:
//       \forall char *str, c, integer i;
//       valid_str(str) &&
//       0 <= i < strchr(str, c) - str <= strlen(str) ==>
//          str[i] != c;
    }
 */

/*@ axiomatic Strchr_skipped {
  @   // Lemmas from the lemma functions won't be imported, so defining them explicitly
  @   lemma Valid_str_shift:
  @     \forall char *s;
  @       valid_str(s) && s[0] != '\0' ==>
  @       valid_str(s + 1) && strlen(s + 1) == strlen(s) - 1;
  @   lemma Strchr_same_block:
  @     \forall char *s, c; strchr(s, c) != \null ==> \base_addr(strchr(s, c)) == \base_addr(s);
  @   lemma Strchr_skipped:
  @     \forall char *str, char c, size_t i;
  @       valid_str(str) &&
  @       strchr(str, c) != \null && 
  @       0 <= i < strchr(str, c) - str <= strlen(str) ==>
  @       str[i] != c;
  @ }
  @*/

// Lemmas from the axiomatic won't be imported as there are no used
// symbols defined in the axiomatic

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(s);
  @  @ requires  strchr(s, c) != \null;
  @  @ decreases strlen(s);
  @  @ ensures   \base_addr(strchr(s, c)) == \base_addr(s);
  @  @/
  @  void strchr_same_block(char *s, char c)
  @  {
  @    if (*s != c && *s != '\0')
  @     strchr_same_block(s + 1, c);
  @  }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  strchr(str, c) != \null;
  @  @ requires  0 <= i < strchr(str, c) - str <= strlen(str);
  @  @ decreases i;
  @  @ ensures   str[i] != c;
  @  @/
  @ void strchr_skipped(char *str, char c, size_t i)
  @ {
  @   if (i > 0 && *str != '\0' && *str != c) {
  @     strchr_skipped(str + 1, c, i - 1);
  @  }
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ decreases strlen(str);
  @  @ ensures   (str <= strchr(str, c) <= str + strlen(str)) ^^
  @  @           strchr(str, c) == \null;
  @  @/
  @ void strchr_mem(char *str, char c)
  @ {
  @    if (*str != c && *str != '\0')
  @      strchr_mem(str + 1, c);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  c != '\0';
  @  @ decreases strlen(str);
  @  @ ensures   strchr(str, c) == \null ^^
  @  @           (\valid(strchr(str,c)) && *strchr(str, c) == c);
  @  @/
  @ void strchr_res(char *str, char c)
  @ {
  @    if (*str != c && *str != '\0')
  @      strchr_res(str + 1, c);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  0 <= i <= strlen(str);
  @  @ requires  \forall integer j; 0 <= j < i ==> str[j] != c;
  @  @ requires  str[i] == c;
  @  @ decreases strlen(str);
  @  @ ensures   strchr(str, c) == str + i;
  @  @/
  @ void strchr_defn(char *str, char c, size_t i)
  @ {
  @    if (*str != c && *str != '\0')
  @      strchr_defn(str + 1, c, i - 1);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  \exists char * p; str <= p < str + strlen(str) && *p == c;
  @  @ decreases strlen(str);
  @  @ ensures   strchr(str, c) != \null && \base_addr(strchr(str, c)) == \base_addr(str);
  @  @/
  @ void strchr_not_null(char *str, char c)
  @ {
  @   if (*str != c && *str != '\0')
  @     strchr_not_null(str + 1, c);
  @ }
  @*/

/* ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  strchr(str, c) != \null;
  @  @ requires  0 <= i < strchr(str, c) - str <= strlen(str);
  @  @ decreases i;
  @  @ ensures   str[i] != c;
  @  @/
  @ void strchr_skipped(char *str, char c, size_t i)
  @ {
  @   if (i > 0 && *str != '\0' && *str != c) {
  @     strchr_skipped(str + 1, c, i - 1);
  @  }
  @ }
  @*/

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
