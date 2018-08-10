#ifndef __SKIP_SPACES_H__
#define __SKIP_SPACES_H__

#include "kernel_definitions.h"
#include "ctype.h"
#include "strlen.h"


/*@ axiomatic SkipSpaces {
    logic char *skip_spaces(char *str) =
       isspace(*str) ? skip_spaces(str + 1) : str;
//    lemma skip_spaces_defn{L}:
//       \forall char *str, size_t i;
//       valid_str(str) && i <= strlen(str) &&
//       (\forall size_t j; j < i ==> isspace(str[j])) &&
//       !isspace(str[i]) ==>
//          str + i == skip_spaces(str);
//    lemma skip_spaces_deref:
//       \forall char *str; valid_str(str) ==>
//          !isspace(*skip_spaces(str));
//    lemma skip_spaces_range:
//       \forall char *str;
//       valid_str(str) ==>
//          str <= skip_spaces(str) <= str + strlen(str);
//    lemma skip_spaces_iter_one:
//       \forall char *str;
//       valid_str(str) && !isspace(*str) ==>
//       skip_spaces(str) == skip_spaces(str+1);
//    lemma skip_spaces_base_addr:
//       \forall char *str;
//       valid_str(str) ==>
//          \base_addr(str) == \base_addr(skip_spaces(str));
//    lemma skip_spaces_same:
//       \forall char *str;
//       \valid(str) && !isspace(*str) ==>
//          str == skip_spaces(str);
//    lemma skipped_are_spaces:
//       \forall char *str, size_t i;
//       valid_str(str) &&
//       i < skip_spaces(str) - str ==>
//          isspace(str[i]);
    }
 */

/*@ ghost
  @ //@ ensures \result <==> isspace(c);
  @ int is_space(char c)
  @ {
  @   return c == ' '  || c == '\f' || c == '\n'
  @      ||  c == '\r' || c == '\t' || c == '\v';
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  str <= res <= str + strlen(str);
  @  @ requires  \forall char *p; str <= p < res ==> isspace(*p);
  @  @ requires  !isspace(*res);
  @  @ decreases strlen(str);
  @  @ ensures   skip_spaces(str) == res;
  @  @/
  @ void skip_spaces_defn(char *str, char* res)
  @ {
  @    if (isspace(*str)) {
  @      //@ assert str <= res || str == res;
  @      //@ assert str + strlen(str) == str + 1 + strlen(str + 1);
  @      skip_spaces_defn(str + 1, res);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ decreases strlen(str);
  @  @ ensures   str <= skip_spaces(str) <= str + strlen(str);
  @  @/
  @ void skip_spaces_range(char *str)
  @ {
  @    if (isspace(*str)) {
  @      skip_spaces_range(str + 1);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(str);
  @  @ requires  i < skip_spaces(str) - str;
  @  @ decreases i;
  @  @ ensures   isspace(str[i]);
  @  @/
  @ void skipped_are_spaces(char *str, size_t i)
  @ {
  @   if (i > 0)
  @    skipped_are_spaces(str + 1, i - 1);
  @ }
  @*/

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
