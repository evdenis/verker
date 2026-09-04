#include "memset.h"

void *memset(void *s, int c, size_t count)
{
	char *xs = s;
	//@ ghost size_t ocount = count;

	/*@ loop invariant bound:   0 <= count <= ocount;
	    loop invariant offset:  xs == (char *)s + (ocount - count);
	    loop invariant written: \forall integer i; 0 <= i < ocount - count ==> ((char *)s)[i] == (char) c;
	    loop assigns count, xs, ((char *)s)[0..ocount-1];
	    loop variant count;
	 */
	while (count--)
		*xs++ = (char) c; // CODE_CHANGE:
	//@ assert count == (size_t)(-1);
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
