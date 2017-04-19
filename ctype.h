#ifndef CTYPE_H
#define CTYPE_H

/*
 * NOTE! This ctype does not handle EOF like the standard C
 * library is required to.
 */

#ifndef SPEC
extern const unsigned char _ctype[];
#else
extern const unsigned char *_ctype;
#endif
#define __ismask(x) (_ctype[(int)(unsigned char)(x)])

#ifndef SPEC
#define isalnum(c)	((__ismask(c)&(_U|_L|_D)) != 0)
#define isalpha(c)	((__ismask(c)&(_U|_L)) != 0)
#define iscntrl(c)	((__ismask(c)&(_C)) != 0)
#define isgraph(c)	((__ismask(c)&(_P|_U|_L|_D)) != 0)
#define islower(c)	((__ismask(c)&(_L)) != 0)
#define isprint(c)	((__ismask(c)&(_P|_U|_L|_D|_SP)) != 0)
#define ispunct(c)	((__ismask(c)&(_P)) != 0)
/* Note: isspace() must return false for %NUL-terminator */
#define isspace(c)	((__ismask(c)&(_S)) != 0)
#define isupper(c)	((__ismask(c)&(_U)) != 0)
#define isxdigit(c)	((__ismask(c)&(_D|_X)) != 0)

#define isascii(c) (((unsigned char)(c))<=0x7f)
#define toascii(c) (((unsigned char)(c))&0x7f)
#else

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


//@ ensures \result <==> isalnum(c);
bool isalnum(char c);
//@ ensures \result <==> isalpha(c);
bool isalpha(char c);
bool iscntrl(char c);
bool isgraph(char c);
//@ ensures \result <==> islower(c);
bool islower(char c);
bool isprint(char c);
bool ispunct(char c);
//@ ensures \result <==> isspace(c);
bool isspace(char c);
//@ ensures \result <==> isupper(c);
bool isupper(char c);
//@ ensures \result <==> isxdigit(c);
bool isxdigit(char c);

//@ ensures \result <==> (0 <= c <= 127);
bool isascii(char c);
bool toascii(char c);
#endif

//@ ensures \result <==> isdigit(c);
int isdigit(int c);

//@ ensures \result == tolower(c);
unsigned char __tolower(unsigned char c);

//@ ensures \result == toupper(c);
unsigned char __toupper(unsigned char c);

#ifndef SPEC
#define tolower(c) __tolower(c)
#define toupper(c) __toupper(c)
#else
//@ ensures \result == tolower(c);
char tolower(const char c);
//@ ensures \result == toupper(c);
char toupper(const char c);
#endif

/*
 * Fast implementation of tolower() for internal usage. Do not use in your
 * code.
 */
//@ ensures \result == tolower(c);
char _tolower(const char c);

/* Fast check for octal digit */
//@ ensures \result <==> isodigit(c);
int isodigit(const char c);

#endif
