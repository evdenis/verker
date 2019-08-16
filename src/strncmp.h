#ifndef __STRNCMP_H__
#define __STRNCMP_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strnlen.h"

/**
 * strncmp - Compare two length-limited strings
 * @cs: One string
 * @ct: Another string
 * @count: The maximum number of bytes to compare
 */

/*@ axiomatic StrnCmp {
    logic int strncmp(char *s1, char *s2, size_t n) =
       n == 0 ? 0 :
          (s1[0] == s2[0] ?
	     (s1[0] == '\0' ? 0 : strncmp(s1 + 1, s2 + 1, (size_t)(n - 1)))
          :
	     (int)(s1[0] - s2[0])
	  );

    predicate strnequal(char *s1, char *s2, size_t n) =
       strncmp(s1, s2, n) == 0;

    lemma strncmp_shift1:
       \forall char *s1, char *s2, size_t n;
          valid_strn(s1, n) ==>
          valid_strn(s2, n) ==>
          n > 0 ==>
          strnequal(s1, s2, n) ==>
          strnequal(s1 + 1, s2 + 1, (size_t)(n - 1));

    lemma strncmp_equal:
       \forall char *s1, char *s2, size_t n;
          valid_strn(s1, n) ==>
          valid_strn(s2, n) ==>
          (\forall size_t i; 0 <= i < n ==> s1[i] == s2[i]) ==>
          strnequal(s1, s2, n);
    }
 */

/*@ requires valid_strn(cs, count);
    requires valid_strn(ct, count);
    assigns \nothing;
    ensures \result == -1 || \result == 0 || \result == 1;
    behavior equal:
       assumes count == 0 ||
               count > 0  &&
               (\forall integer i; 0 <= i < strnlen(cs, count) ==> (cs[i] == ct[i])) &&
               strnlen(cs, count) == strnlen(ct, count);
       ensures \result == 0;
    behavior len_diff:
       assumes count > 0;
       assumes \forall integer i; 0 <= i < strnlen(cs, count) ==> (cs[i] == ct[i]);
       assumes strnlen(cs, count) != strnlen(ct, count);
       ensures strnlen(cs, count) < strnlen(ct, count) ==> \result == -1;
       ensures strnlen(cs, count) > strnlen(ct, count) ==> \result == 1;
    behavior not_equal:
       assumes count > 0;
       assumes \exists integer i; 0 <= i < strnlen(cs, count) && cs[i] != ct[i];
       ensures \exists integer i; 0 <= i < strnlen(cs, count) &&
               (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
               (cs[i] != ct[i]) &&
               ((u8 AENO)cs[i] < (u8 AENO)ct[i] ? \result == -1 : \result == 1);
    complete behaviors;
    disjoint behaviors;
 */
int strncmp(const char *cs, const char *ct, size_t count);

#endif // __STRNCMP_H__
