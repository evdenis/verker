#ifndef __STRSEP_H__
#define __STRSEP_H__

#include "kernel_definitions.h"
#include "strpbrk.h"

/**
 * strsep - Split a string into tokens
 * @s: The string to be searched
 * @ct: The characters to search for
 *
 * strsep() updates @s to point after the token, ready for the next call.
 *
 * It returns empty tokens, too, behaving exactly like the libc function
 * of that name. In fact, it was stolen from glibc2 and de-fancy-fied.
 * Same semantics, slimmer shape. ;)
 */

/*@ requires valid_str(ct);
    requires \valid(s);
    requires valid_str(*s) ^^ *s == \null;
    behavior input_null:
       assumes *s == \null;
       assigns \nothing;
       ensures \result == \null;
    behavior input_strpbrk_null:
       assumes valid_str(*s);
       assumes strpbrk(*s, ct) == \null;
       assigns *s;
       ensures \result == \old(*s);
       ensures *s == \null;
    behavior input_strpbrk_not_null:
       assumes valid_str(*s);
       assumes strpbrk(*s, ct) != \null;
       assigns *strpbrk(\old(*s), ct);
       assigns *s;
       ensures \result == \old(*s);
       ensures *s == strpbrk(\old(*s), ct) + 1;
       ensures *strpbrk(\old(*s), ct) == '\0';
       ensures valid_str(\result);
       //ensures strlen(\result) == strpbrk(\old(*s), ct) - \old(*s);
    complete behaviors;
    disjoint behaviors;
 */
char *strsep(char **s, const char *ct);

#endif // __STRSEP_H__
