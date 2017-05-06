#include "strchr.h"

char *strchr(const char *s, int c)
{
	//@ ghost char *os = s;
	/*@ loop invariant valid_str(s);
	    loop invariant os <= s <= os + strlen(os);
	    loop invariant \forall char *p; os <= p < s ==> *p != (char %)c;
	    loop variant strlen(os) - (s - os);
	 */
	for (; *s != (char)/*@%*/c; ++s)
		if (*s == '\0')
			return NULL;
	//@ assert (char %)c != '\0' <==> s < os + strlen(os);
	//@ assert (char %)c == '\0' <==> s == os + strlen(os);
	return (char *)s;
}