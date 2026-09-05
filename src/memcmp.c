#include "memcmp.h"

/* axiomatic Mem {
    logic integer memcmp(char *cs, char *ct, integer count);
    lemma eq:
         \forall integer i, char *cs, *ct;
         0 <= i && \valid(cs+(0..i)) && \valid(ct+(0..i)) &&
         cs[i] == ct[i] <==>
            memcmp(cs, ct, i) == 0;
    lemma lt:
         \exists integer i, char *cs, *ct;
         0 <= i && \valid(cs+(0..i)) && \valid(ct+(0..i)) &&
         (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
         cs[i] < ct[i] <==>
            memcmp(cs, ct, i) < 0;
    lemma gt:
         \exists integer i, char *cs, *ct;
         0 <= i && \valid(cs+(0..i)) && \valid(ct+(0..i)) &&
         (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
         cs[i] > ct[i] <==>
            memcmp(cs, ct, i) > 0;
    }
 */

__visible int memcmp(const void *cs, const void *ct, size_t count)
{
	const char *su1, *su2; /*CODE_CHANGE*/
	int res = 0;

	/*@ loop invariant bound: 0 <= count <= \at(count,Pre);
	    loop invariant off1:  su1 == (char *)cs + (\at(count,Pre) - count);
	    loop invariant off2:  su2 == (char *)ct + (\at(count,Pre) - count);
	    loop invariant equal: \forall integer i; 0 <= i < \at(count,Pre) - count ==>
	                          (unsigned char)((char *)cs)[i] == (unsigned char)((char *)ct)[i];
	    //loop invariant memcmp((char *)cs, (char *)ct, \at(count,Pre)) ==
	    //               memcmp((char *)su1, (char *)su2, count);
	    loop invariant res == 0;
	    loop assigns su1, su2, count, res;
	    loop variant count;
	 */
	for (su1 = cs, su2 = ct; 0 < count; ++su1, ++su2, count--)
		if ((res = /*CODE_CHANGE:*/(unsigned char)*su1 - (unsigned char)*su2) != 0)
			break;

	return res;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size % 2 == 0) {
		memcmp(data, data + size / 2, size / 2);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int src[]  = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
	int dest[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
	int res;

	res = memcmp(dest, src, sizeof(src));
	dest[ARRAY_SIZE(dest)-1]--;

	res = memcmp(dest, src, sizeof(src));
	dest[ARRAY_SIZE(dest)-1]+=2;

	res = memcmp(dest, src, sizeof(src));
	res = res;

	return 0;
}
#endif
