#ifndef __STRSPN_H__
#define __STRSPN_H__

#include "kernel_definitions.h"
#include "strlen.h"

/**
 * strspn - Calculate the length of the initial substring of @s which only contain letters in @accept
 * @s: The string to be searched
 * @accept: The string to search for
 */

/*@ axiomatic StrSpn {
    predicate in_array(char *s, char c) = \exists char *p; s <= p < s + strlen(s) && *p == c;

    axiom in_array_shift1:
       \forall char *s, c;
          valid_str(s) && s != '\0' && *s != c ==>
             in_array(s, c) <==> in_array(s + 1, c);
    axiom in_array_true:
       \forall char *s, c;
          valid_str(s) && s != '\0' && *s == c ==>
             in_array(s, c);
    axiom in_array_false:
       \forall char *s, c;
          valid_str(s) && s == '\0' ==>
             !in_array(s, c);

    logic integer strspn{L}(char *s, char *accept) reads s, accept;

    axiom strspn_strend:
       \forall char *s, *accept;
          \valid(s) && *s == '\0' ==>
             strspn(s, accept) == 0;

    axiom strspn_empty_accept:
       \forall char *s, *accept;
          \valid(accept) && *accept == '\0' ==>
             strspn(s, accept) == 0;

    axiom strspn_range{L}:
       \forall char* s, *accept;
          valid_str{L}(s) && valid_str{L}(accept) ==>
             0 <= strspn{L}(s, accept) <= strlen{L}(s);

    axiom strspn_shift1:
       \forall char *s, *accept;
          valid_str(s) && valid_str(accept) && *s != '\0' &&
          in_array(accept, *s) ==>
             strspn(s, accept) == strspn(s + 1, accept) + 1;

    axiom strspn_stop_not_in_accept{L}:
       \forall char *s, *accept;
          valid_str{L}(s) && valid_str{L}(accept) && *s != '\0' &&
          !in_array{L}(accept, *s) ==>
             strspn{L}(s, accept) == 0;
    }
 */

/*@ requires valid_str(s);
    requires valid_str(accept);
    assigns \nothing;
    ensures 0 <= \result <= strlen(s);
    ensures \forall char *t; accept <= t < accept + strlen(accept) ==> s[\result] != *t;
    ensures \forall char *p; s <= p < s + \result ==>
            (\exists char *t; accept <= t < accept + strlen(accept) && *p == *t);
    ensures \result == strspn(s, accept);
 */
size_t strspn(const char *s, const char *accept);

#endif // __STRSPN_H__
