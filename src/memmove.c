#include "memmove.h"

void *memmove(void *dest, const void *src, size_t count)
{
	//@ ghost size_t ocount = count;
	char *tmp;
	const char *s;

	if (dest <= src) {
		tmp = dest;
		s = src;
		/*@ loop invariant 0 <= count <= ocount;
		    loop invariant tmp - dest == ocount - count == s - src;
		    loop invariant (char *)dest <= tmp <= (char *)dest + ocount;
		    loop invariant (char *)src <= s <= (char *)src + ocount;
		    loop invariant \forall integer i; ocount - count <= i < ocount ==> ((char *)src)[i] == \at(((char *)src)[i], Pre);
		    loop invariant \forall integer i; 0 <= i < ocount - count ==> ((char *)dest)[i] == \at(((char *)src)[i], Pre);
		    loop assigns count, s, ((char *)dest)[0..ocount-1];
		    loop variant count; */
		while (count-- AENOC) {
			*tmp++ = *s++;
			//@ assert ((char *)dest)[ocount - count - 1] == ((char *)src)[ocount - count - 1];
		}
	} else {
		tmp = dest;
		tmp += count;
		s = src;
		s += count;
		/*@ loop invariant 0 <= count <= ocount;
		    loop invariant tmp - dest == count == s - src;
		    loop invariant (char *)dest <= tmp <= (char *)dest + ocount;
		    loop invariant (char *)src <= s <= (char *)src + ocount;
		    loop invariant \forall integer i; 0 <= i < count ==> ((char *)src)[i] == \at(((char *)src)[i], Pre);
		    loop invariant \forall integer i; count <= i < ocount ==> ((char *)dest)[i] == \at(((char *)src)[i], Pre);
		    loop assigns count, s, ((char *)dest)[0..ocount-1];
		    loop variant count; */
		while (count-- AENOC) {
			*--tmp = *--s;
			//@ assert ((char *)dest)[count] == ((char *)src)[count];
		}
	}
	//@ assert count == (size_t AENO)(-1);
	return dest;
}


#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int src[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
	int dest[ARRAY_SIZE(src)];

	memmove(dest, src, sizeof(src));
	memmove(dest, dest, sizeof(dest));

	return 0;
}
#endif
