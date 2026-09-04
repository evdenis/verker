#include "strcmp.h"

int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	//@ ghost char *ocs = (char *)cs;
	//@ ghost char *oct = (char *)ct;
	//@ ghost size_t k = 0;
	//@ ghost size_t n = elim_valid_str(ocs);
	//@ ghost intro_valid_str_len(ocs, n);

	/*@ loop invariant validcs: valid_str(cs);
	    loop invariant validct: valid_str(ct);
	    loop invariant idxcs:   cs == ocs + k;
	    loop invariant idxct:   ct == oct + k;
	    loop invariant bound:   0 <= k <= n;
	    loop invariant lencs:   n == strlen(cs) + k;
	    loop invariant eq:      \forall integer i; 0 <= i < k ==> ocs[i] == oct[i];
	    loop assigns cs, ct, c1, c2, k;
	    loop variant n - k;
	*/
	while (1) {
		c1 = /*CODE_CHANGE:*/(unsigned char) *cs++;
		c2 = /*CODE_CHANGE:*/(unsigned char) *ct++;
		if (c1 != c2) {
			//@ ghost if (c1 < c2) strncmp_defn_less(ocs, oct, n, k);
			//@ ghost if (c1 > c2) strncmp_defn_greater(ocs, oct, n, k);
			return c1 < c2 ? -1 : 1;
		}

		if (!c1) {
			//@ ghost strncmp_defn_equal(ocs, oct, n);
			break;
		}
		//@ ghost valid_str_shift(ocs + k);
		//@ ghost valid_str_shift(oct + k);
		//@ ghost k++;
	}

	return 0;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strcmp((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int res;
	const char *s1 = "1234567895";
	const char *s2 = "123456789";
	const char *s3 = "1234567899";
	const char *s4 = "1234567890";

	res = strcmp(s1, s1);
	res = strcmp(s1, s2);
	res = strcmp(s1, s3);
	res = strcmp(s1, s4);
	res = res;

	return 0;
}
#endif
