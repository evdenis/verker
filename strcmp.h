#ifndef __STRCMP_H__
#define __STRCMP_H__

#include "strlen.h"

/* axiomatic StrCmp {
    logic integer cmp(unsigned char a, unsigned char b) =
       a == b ? 0 : a < b ? -1 : 1;

    logic integer strncmp(char *cs, char *ct, integer n) =
       n == -1 ? 0 : (cs[n] == ct[n] ? strncmp(cs+1, ct+1, n-1) : cmp((u8 %)cs[n], (u8 %)ct[n]));
    logic integer strcmp(char *cs, char *ct) = strncmp(cs, ct, strlen(cs));
    predicate equaln(char *cs, char *ct, size_t n) = strncmp(cs, ct, n) == 0;
    predicate equal(char *cs, char *ct) = strcmp(cs, ct) == 0;

    lemma range:
       \forall char *cs, *ct, size_t n;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) ==>
          -1 <= strncmp(cs, ct, n) <= 1;

    lemma defn_equal:
       \forall char *cs, *ct, size_t n;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) &&
       (\forall size_t i; i <= n ==> cs[i] == ct[i]) ==>
          strncmp(cs, ct, n) == 0;
    lemma defn_less:
       \forall char *cs, *ct, size_t n, k;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) && k <= n &&
       (\forall size_t i; i < k ==> cs[i] == ct[i]) &&
       (u8 %)cs[k] < (u8 %)ct[k] ==>
          strncmp(cs, ct, n) == -1;
    lemma defn_greater:
       \forall char *cs, *ct, size_t n, k;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) && k <= n &&
       (\forall size_t i; i < k ==> cs[i] == ct[i]) &&
       (u8 %)cs[k] > (u8 %)ct[k] ==>
          strncmp(cs, ct, n) == 1;

    lemma iter_one:
       \forall char *cs, *ct, size_t n;
       \valid(cs+(0..n)) && \valid(ct+(0..n)) &&
       n > 0 && *cs == *ct ==>
          strncmp(cs, ct, n) == strncmp(cs+1, ct+1, n-1);
    lemma at_end:
       \forall char *cs, *ct;
       \valid(cs) && \valid(ct) ==>
       strncmp(cs, ct, 0) == cmp((u8 %)*cs, (u8 %)*ct);
    }
 */

/**
 * strcmp - Compare two strings
 * @cs: One string
 * @ct: Another string
 */

/*@ requires valid_str(cs);
    requires valid_str(ct);
    assigns \nothing;
    //ensures \result == strcmp(cs, ct);
    behavior equal:
       assumes \forall integer i; 0 <= i <= strlen(cs) ==> cs[i] == ct[i];
       ensures \result == 0;
    behavior not_equal:
       assumes \exists integer i; 0 <= i <= strlen(cs) && cs[i] != ct[i];
       ensures \result == -1 || \result == 1;
       ensures \exists integer i; 0 <= i <= strlen(cs) &&
               (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
               (cs[i] != ct[i]) &&
               ((u8 %)cs[i] < (u8 %)ct[i] ? \result == -1 : \result == 1);
    complete behaviors;
    disjoint behaviors;
 */
int strcmp(const char *cs, const char *ct);

#endif // __STRCMP_H__
