#include "memset.h"

void *memset(void *s, int c, size_t count)
{
	char *xs = s;
	//@ ghost size_t ocount = count;

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant (char *)s <= xs <= (char *)s + ocount;
	    loop invariant xs - s == ocount - count;
	    loop invariant \forall char *p; (char *)s <= p < xs ==> *p == (char AENO) c;
	    loop variant count;
	 */
	while (count-- AENOC)
		*xs++ = (char) AENOC c; // CODE_CHANGE:
	//@ assert count == (size_t AENO)(-1);
	return s;
}

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int buf[10];

	memset(buf, 3, 10 * sizeof(int));

	return 0;
}
#endif
