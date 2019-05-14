#include "ctype.h"

#if !defined(SPEC) || !defined(ASTRAVER_TOOLCHAIN)
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
//@ global invariant ctype: (char *) _ctype == ctype_tbl;
#endif

#ifdef SPEC
//@ ensures \result == tolower(c);
char tolower(const char c) { return __tolower(c); }
//@ ensures \result == toupper(c);
char toupper(const char c) { return __toupper(c); }

#define __ismask(x) (_ctype[(int)(unsigned char)(x)])

bool isalnum(char c) { return ((__ismask(c)&(_U|_L|_D)) != 0); }
bool isalpha(char c) { return ((__ismask(c)&(_U|_L)) != 0); }
bool iscntrl(char c) { return ((__ismask(c)&(_C)) != 0); }
bool isgraph(char c) { return ((__ismask(c)&(_P|_U|_L|_D)) != 0); }
bool islower(char c) { return ((__ismask(c)&(_L)) != 0); }
bool isprint(char c) { return ((__ismask(c)&(_P|_U|_L|_D|_SP)) != 0); }
bool ispunct(char c) { return ((__ismask(c)&(_P)) != 0); }
bool isspace(char c) { return ((__ismask(c)&(_S)) != 0); }
bool isupper(char c) { return ((__ismask(c)&(_U)) != 0); }
bool isxdigit(char c) { return ((__ismask(c)&(_D|_X)) != 0); }

bool isascii(char c) { return (((unsigned char)(c))<=0x7f); }
bool toascii(char c) { return (((unsigned char)(c))&0x7f); }
#endif

int isdigit(int c)
{
	return '0' <= c && c <= '9';
}

unsigned char __tolower(unsigned char c)
{
	if (isupper(c))
		c -= 'A'-'a';
	return c;
}

unsigned char __toupper(unsigned char c)
{
	if (islower(c))
		c -= 'a'-'A';
	return c;
}

char _tolower(const char c)
{
	return c | 0x20;
}

int isodigit(const char c)
{
	return c >= '0' && c <= '7';
}
