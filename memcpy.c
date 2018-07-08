#include "memcpy.h"

void *memcpy(void *dest, const void *src, size_t count)
{
	char *tmp = dest;
	const char *s = src;
	//@ ghost size_t ocount = count;

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant (char *)dest <= tmp <= (char *)dest + ocount;
	    loop invariant (char *)src <= s <= (char *)src + ocount;
	    loop invariant tmp - dest == s - src == ocount - count;
	    loop invariant \forall integer i; 0 <= i < ocount - count ==>
	                   ((char *)dest)[i] == ((char *)src)[i];
	    loop variant count;
	 */
	while (count-- AENOC)
		*tmp++ = *s++;
	//@ assert count == (size_t AENO)(-1);
	return dest;
}

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int src[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
	int dest[ARRAY_SIZE(src)];

	memcpy(dest, src, sizeof(src));

	return 0;
}
#endif
