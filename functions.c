#define SPEC 1

#define EINVAL 1

#define bool _Bool
#define true  1
#define false 0

/*
 * NOTE! This ctype does not handle EOF like the standard C
 * library is required to.
 */

#define _U	0x01	/* upper */
#define _L	0x02	/* lower */
#define _D	0x04	/* digit */
#define _C	0x08	/* cntrl */
#define _P	0x10	/* punct */
#define _S	0x20	/* white space (space/lf/tab) */
#define _X	0x40	/* hex digit */
#define _SP	0x80	/* hard space (0x20) */

#ifndef SPEC
const unsigned char _ctype[] = {
_C,_C,_C,_C,_C,_C,_C,_C,				/* 0-7 */
_C,_C|_S,_C|_S,_C|_S,_C|_S,_C|_S,_C,_C,			/* 8-15 */
_C,_C,_C,_C,_C,_C,_C,_C,				/* 16-23 */
_C,_C,_C,_C,_C,_C,_C,_C,				/* 24-31 */
_S|_SP,_P,_P,_P,_P,_P,_P,_P,				/* 32-39 */
_P,_P,_P,_P,_P,_P,_P,_P,				/* 40-47 */
_D,_D,_D,_D,_D,_D,_D,_D,				/* 48-55 */
_D,_D,_P,_P,_P,_P,_P,_P,				/* 56-63 */
_P,_U|_X,_U|_X,_U|_X,_U|_X,_U|_X,_U|_X,_U,		/* 64-71 */
_U,_U,_U,_U,_U,_U,_U,_U,				/* 72-79 */
_U,_U,_U,_U,_U,_U,_U,_U,				/* 80-87 */
_U,_U,_U,_P,_P,_P,_P,_P,				/* 88-95 */
_P,_L|_X,_L|_X,_L|_X,_L|_X,_L|_X,_L|_X,_L,		/* 96-103 */
_L,_L,_L,_L,_L,_L,_L,_L,				/* 104-111 */
_L,_L,_L,_L,_L,_L,_L,_L,				/* 112-119 */
_L,_L,_L,_P,_P,_P,_P,_C,				/* 120-127 */
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,			/* 128-143 */
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,			/* 144-159 */
_S|_SP,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,	/* 160-175 */
_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,	/* 176-191 */
_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,	/* 192-207 */
_U,_U,_U,_U,_U,_U,_U,_P,_U,_U,_U,_U,_U,_U,_U,_L,	/* 208-223 */
_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,	/* 224-239 */
_L,_L,_L,_L,_L,_L,_L,_P,_L,_L,_L,_L,_L,_L,_L,_L};	/* 240-255 */
#else
const unsigned char *_ctype = /*@ ctype_tbl = */
"\x08\x08\x08\x08\x08\x08\x08\x08\x08\x28\x28\x28\x28\x28\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\x08\xa0\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x04\x04\x04\x04\x04\x04\x04\x04\x04\x04\x10\x10\x10\x10\x10\x10\x10\x41\x41\x41\x41\x41\x41\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x10\x10\x10\x10\x10\x10\x42\x42\x42\x42\x42\x42\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x10\x10\x10\x10\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x10\x01\x01\x01\x01\x01\x01\x01\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x10\x02\x02\x02\x02\x02\x02\x02\x02";
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


/*@ requires (char *) _ctype == ctype_tbl;
    ensures \result <==> isalnum(c);
 */
static inline bool isalnum(char c) { return ((__ismask(c)&(_U|_L|_D)) != 0); }
//@ ensures \result <==> isalpha(c);
static inline bool isalpha(char c) { return ((__ismask(c)&(_U|_L)) != 0); }
static inline bool iscntrl(char c) { return ((__ismask(c)&(_C)) != 0); }
static inline bool isgraph(char c) { return ((__ismask(c)&(_P|_U|_L|_D)) != 0); }
//@ ensures \result <==> islower(c);
static inline bool islower(char c) { return ((__ismask(c)&(_L)) != 0); }
static inline bool isprint(char c) { return ((__ismask(c)&(_P|_U|_L|_D|_SP)) != 0); }
static inline bool ispunct(char c) { return ((__ismask(c)&(_P)) != 0); }
static inline bool isspace(char c) { return ((__ismask(c)&(_S)) != 0); }
//@ ensures \result <==> isupper(c);
static inline bool isupper(char c) { return ((__ismask(c)&(_U)) != 0); }
static inline bool isxdigit(char c) { return ((__ismask(c)&(_D|_X)) != 0); }

static inline bool isascii(char c) { return (((unsigned char)(c))<=0x7f); }
static inline bool toascii(char c) { return (((unsigned char)(c))&0x7f); }
#endif

//@ ensures \result <==> isdigit(c);
static inline int isdigit(int c)
{
	return '0' <= c && c <= '9';
}

//@ ensures \result == tolower(c);
static inline unsigned char __tolower(unsigned char c)
{
	if (isupper(c))
		c -= 'A'-'a';
	return c;
}

//@ ensures \result == toupper(c);
static inline unsigned char __toupper(unsigned char c)
{
	if (islower(c))
		c -= 'a'-'A';
	return c;
}

#ifndef SPEC
#define tolower(c) __tolower(c)
#define toupper(c) __toupper(c)
#else
static inline char tolower(const char c) { return __tolower(c); }
static inline char toupper(const char c) { return __toupper(c); }
#endif

/*
 * Fast implementation of tolower() for internal usage. Do not use in your
 * code.
 */
//@ ensures \result == tolower(c);
static inline char _tolower(const char c)
{
	return c | 0x20;
}

/* Fast check for octal digit */
//@ ensures \result <==> isodigit(c);
static inline int isodigit(const char c)
{
	return c >= '0' && c <= '7';
}

/*@ predicate kstrtobool_fmt_false(char *s) =
       s[0] == 'N' || s[0] == 'n' || s[0] == '0' ||
       ((s[0] == 'o' || s[0] == 'O') &&
        (s[1] == 'F' || s[1] == 'f'));
 */

/*@ predicate kstrtobool_fmt_true(char *s) =
       s[0] == 'Y' || s[0] == 'y' || s[0] == '1' ||
       ((s[0] == 'o' || s[0] == 'O') &&
        (s[1] == 'N' || s[1] == 'n'));
 */

/*@ predicate kstrtobool_fmt(char *s) =
       kstrtobool_fmt_true(s) ||
       kstrtobool_fmt_false(s);
 */

/**
 * kstrtobool - convert common user inputs into boolean values
 * @s: input string
 * @res: result
 *
 * This routine returns 0 iff the first character is one of 'Yy1Nn0', or
 * [oO][NnFf] for "on" and "off". Otherwise it will return -EINVAL.  Value
 * pointed to by res is updated upon finding a match.
 */

/*@ requires s == \null || \valid(s+(0..1));
    requires \valid(res);
    ensures \result == 0 || \result == -EINVAL;
    ensures \result == -EINVAL ==> res == \old(res);
    behavior INVAL:
       assumes s == \null || !kstrtobool_fmt(s);
       assigns \nothing;
       ensures \result == -EINVAL;
    behavior CORRECT:
       assumes s != \null && kstrtobool_fmt(s);
       assigns *res;
       ensures kstrtobool_fmt_true(s)  ==> *res == 1;
       ensures kstrtobool_fmt_false(s) ==> *res == 0;
       ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
 */
int kstrtobool(const char *s, bool *res)
{
	if (!s)
		return -EINVAL;

	switch (s[0]) {
	case 'y':
	case 'Y':
	case '1':
		*res = true;
		return 0;
	case 'n':
	case 'N':
	case '0':
		*res = false;
		return 0;
	case 'o':
	case 'O':
		switch (s[1]) {
		case 'n':
		case 'N':
			*res = true;
			return 0;
		case 'f':
		case 'F':
			*res = false;
			return 0;
		default:
			break;
		}
	default:
		break;
	}

	return -EINVAL;
}
//EXPORT_SYMBOL(kstrtobool);



