#ifndef __STRNCASECMP_H__
#define __STRNCASECMP_H__

#define CTYPE_H

#include "kernel_definitions.h"
#include "strnlen.h"
//#include "ctype.h"

#ifdef SPEC
/*@ axiomatic Ctype {
    predicate islower(integer c) = 'a' <= c <= 'z';
    predicate isupper(integer c) = 'A' <= c <= 'Z';
    predicate isalpha(integer c) = isupper(c) || islower(c);
    predicate isdigit(integer c)  = '0' <= c <= '9';
    predicate isodigit(integer c) = '0' <= c <= '7';
    predicate isalnum(integer c)  = isdigit(c) || isalpha(c);
    predicate isspace(integer c)  = c == ' '  || c == '\f' || c == '\n' ||
                                    c == '\r' || c == '\t' || c == '\v';
    predicate isxdigit(integer c) = isdigit(c)        ||
                                    ('a' <= c <= 'f') ||
                                    ('A' <= c <= 'F');

    logic integer tolower(integer c);
    logic integer toupper(integer c);
    axiom a: tolower('A') == 'a'; axiom b: tolower('B') == 'b'; axiom c: tolower('C') == 'c';
    axiom d: tolower('D') == 'd'; axiom e: tolower('E') == 'e'; axiom f: tolower('F') == 'f';
    axiom g: tolower('G') == 'g'; axiom h: tolower('H') == 'h'; axiom i: tolower('I') == 'i';
    axiom j: tolower('J') == 'j'; axiom k: tolower('K') == 'k'; axiom l: tolower('L') == 'l';
    axiom m: tolower('M') == 'm'; axiom n: tolower('N') == 'n'; axiom o: tolower('O') == 'o';
    axiom p: tolower('P') == 'p'; axiom q: tolower('Q') == 'q'; axiom r: tolower('R') == 'r';
    axiom s: tolower('S') == 's'; axiom t: tolower('T') == 't'; axiom u: tolower('U') == 'u';
    axiom v: tolower('V') == 'v'; axiom w: tolower('W') == 'w'; axiom x: tolower('X') == 'x';
    axiom y: tolower('Y') == 'y'; axiom z: tolower('Z') == 'z';

    axiom pl: \forall integer c; !isupper(c) ==> tolower(c) == c;
    axiom pu: \forall integer c; !islower(c) ==> toupper(c) == c;
    axiom tl: \forall integer c; !islower(c) ==> toupper(tolower(c)) == c;
    axiom tu: \forall integer c; !isupper(c) ==> tolower(toupper(c)) == c;
    }
 */

//@ ensures \result == tolower(c);
unsigned char tolower(const unsigned char c);
#endif

/**
 * strncasecmp - Case insensitive, length-limited string comparison
 * @s1: One string
 * @s2: The other string
 * @len: the maximum number of characters to compare
 */

int strncasecmp(const char *s1, const char *s2, size_t len);

#endif // __STRNCASECMP_H__
