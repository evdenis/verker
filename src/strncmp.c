#include "strncmp.h"

int strncmp(const char *cs, const char *ct, size_t count)
{
	unsigned char c1, c2;
	//@ ghost char *ocs = (char *)cs;
	//@ ghost char *oct = (char *)ct;
	//@ ghost size_t ocount = count;
	//@ ghost size_t k = 0;
	//@ ghost valid_strn_len(ocs, ocount);
	//@ ghost valid_strn_len(oct, ocount);

	/*@ loop invariant bound: 0 <= count <= ocount;
	    loop invariant off:   k == ocount - count;
	    loop invariant idx1:  cs == ocs + k;
	    loop invariant idx2:  ct == oct + k;
	    loop invariant valid: valid_strn(cs, count) && valid_strn(ct, count);
	    loop invariant len1:  strnlen(ocs, ocount) == strnlen(cs, count) + k;
	    loop invariant len2:  strnlen(oct, ocount) == strnlen(ct, count) + k;
	    loop invariant eq:    \forall integer i; 0 <= i < k ==> ocs[i] == oct[i];
	    loop assigns cs, ct, count, c1, c2, k;
	    loop variant count;
	*/
	while (count) {
		c1 = /*CODE_CHANGE:*/(unsigned char) *cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char) *ct++;
		if (c1 != c2) {
			//@ ghost int res = c1 < c2 ? -1 : 1;
			/*@ for not_equal:
			    assert \exists integer i; 0 <= i < strnlen(ocs, ocount) &&
			      (\forall integer j; 0 <= j < i ==> ocs[j] == oct[j]) &&
			      (ocs[i] != oct[i]) &&
			      ((u8)ocs[i] < (u8)oct[i] ? res == -1 : res == 1) &&
			      i == k;
			 */
			return c1 < c2 ? -1 : 1;
		}
		if (!c1)
			break;
		//@ ghost valid_strn_shift(ocs + k, count);
		//@ ghost valid_strn_shift(oct + k, count);
		count--;
		//@ ghost k++;
	}

	return 0;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strncmp((const char *)data, (const char *)(data + size / 2), size / 2);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	int res;
	const char *s1 = "1234567895";
	const char *s2 = "123456789";
	const char *s3 = "1234567899";
	const char *s4 = "1234567890";

	res = strncmp(s1, s1, strlen(s1)+10);
	res = strncmp(s1, s1, strlen(s1) / 2);
	res = strncmp(s1, s2, strlen(s1)+10);
	res = strncmp(s1, s3, strlen(s1)+10);
	res = strncmp(s1, s4, strlen(s1)+10);
	res = res;

	return 0;
}
#endif
