#ifndef __STRNSTR_H__
#define __STRNSTR_H__

#include "kernel_definitions.h"
#include "memcmp.h"
#include "strlen.h"

/**
 * strnstr - Find the first substring in a length-limited string
 * @s1: The string to be searched
 * @s2: The string to search for
 * @len: the maximum number of characters to search
 *
 * All len bytes are searched, including bytes after an embedded NUL.
 */

/*@ predicate strnstr_match{L}(char *haystack, char *needle, integer offset) =
       \forall integer i; 0 <= i < strlen(needle) ==>
                          haystack[offset + i] == needle[i];
 */

/*@ requires haystack: \valid_read(s1 + (0..len-1));
    requires needle: valid_str(s2);
    requires needle_length: strlen(s2) <= LONG_MAX;
    terminates \true;
    exits \false;
    assigns \result \from s1, s2, len, s1[0..len-1], s2[0..strlen(s2)];

    behavior empty:
       assumes empty_needle: strlen(s2) == 0;
       ensures result: \result == s1;

    behavior nonempty:
       assumes nonempty_needle: strlen(s2) > 0;
       ensures found: \result != \null ==>
          (\exists integer i; 0 <= i <= len - strlen(s2) &&
             \result == s1 + i && strnstr_match(s1, s2, i) &&
             (\forall integer j; 0 <= j < i ==> !strnstr_match(s1, s2, j)));
       ensures missing: (\result == \null) <==>
          (\forall integer i; 0 <= i <= len - strlen(s2) ==>
                              !strnstr_match(s1, s2, i));

    complete behaviors;
    disjoint behaviors;
 */
char *strnstr(const char *s1, const char *s2, size_t len);

#endif // __STRNSTR_H__
