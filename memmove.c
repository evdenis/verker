#include "memmove.h"

void *memmove(void *dest, const void *src, size_t count)
{
	//@ ghost size_t orig_count = count;
	char *tmp;
	const char *s;

	if (dest <= src) {
		tmp = dest;
		s = src;
		/*@ loop invariant 0 <= count <= orig_count;
		    loop invariant tmp - dest == orig_count - count == s - src;
		    loop invariant (char *)dest <= tmp <= (char *)dest + orig_count;
		    loop invariant (char *)src <= s <= (char *)src + orig_count;
		    loop invariant \forall integer i; orig_count - count <= i < orig_count ==> ((char *)src)[i] == \at(((char *)src)[i], Pre);
		    loop invariant \forall integer i; 0 <= i < orig_count - count ==> ((char *)dest)[i] == \at(((char *)src)[i], Pre);
		    loop variant count; */
		while (count-- ACSL_EXT_NO_OVERFLOW_CMNT) {
			*tmp++ = *s++;
			//@ assert ((char *)dest)[orig_count - count - 1] == ((char *)src)[orig_count - count - 1];
		}
	} else {
		tmp = dest;
		tmp += count;
		s = src;
		s += count;
		/*@ loop invariant 0 <= count <= orig_count;
		    loop invariant tmp - dest == count == s - src;
		    loop invariant (char *)dest <= tmp <= (char *)dest + orig_count;
		    loop invariant (char *)src <= s <= (char *)src + orig_count;
		    loop invariant \forall integer i; 0 <= i < count ==> ((char *)src)[i] == \at(((char *)src)[i], Pre);
		    loop invariant \forall integer i; count <= i < orig_count ==> ((char *)dest)[i] == \at(((char *)src)[i], Pre);
		    loop variant count; */
		while (count-- ACSL_EXT_NO_OVERFLOW_CMNT) {
			*--tmp = *--s;
			//@ assert ((char *)dest)[count] == ((char *)src)[count];
		}
	}
	//@ assert count == (size_t ACSL_EXT_NO_OVERFLOW)(-1);
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
