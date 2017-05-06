#include "strnchr.h"

char *strnchr(const char *s, size_t count, int c)
{
	//@ ghost char *os = s;
	//@ ghost size_t ocount = count;
	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant os <= s <= os + strnlen(os, ocount);
	    loop invariant s - os == ocount - count;
	    loop invariant valid_strn(s, count);
	    loop invariant strnlen(os, ocount) == s - os + strnlen(s, count);
	    loop invariant \forall char *p; os <= p < s ==> *p != (char %) c;
	    loop variant count;
	 */
	for (; count-- /*@%*/ && *s != '\0'; ++s)
		if (*s == (char)/*@%*/c)
			return (char *)s;
	return NULL;
}