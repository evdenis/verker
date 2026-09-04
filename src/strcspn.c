#include "strcspn.h"

size_t strcspn(const char *s, const char *reject)
{
	const char *p;
	const char *r;
	size_t count = 0;

	//@ ghost size_t k = 0;
	//@ ghost size_t m = 0;
	/*@ loop invariant idx:      p == s + k;
	    loop invariant bound:    0 <= k <= strlen(s);
	    loop invariant len:      strlen(s) == strlen(p) + k;
	    loop invariant valid:    valid_str(p);
	    loop invariant cnt:      count == k;
	    loop invariant rejected: \forall integer i; 0 <= i < k ==> !in_array(reject, s[i]);
	    loop invariant span:     strcspn(s, reject) == strcspn(p, reject) + k;
	    loop assigns p, r, count, k, m;
	    loop variant strlen(s) - k;
	 */
	for (p = s; *p != '\0'; ++p) {
		//@ ghost m = 0;
		/*@ loop invariant iidx:   r == reject + m;
		    loop invariant ibound: 0 <= m <= strlen(reject);
		    loop invariant ilen:   strlen(reject) == strlen(r) + m;
		    loop invariant ivalid: valid_str(r);
		    loop invariant inone:  \forall integer i; 0 <= i < m ==> reject[i] != *p;
		    loop assigns r, m;
		    loop variant strlen(reject) - m;
		 */
		for (r = reject; *r != '\0'; ++r) {
			if (*p == *r) {
				//@ ghost valid_str_len((char *)r);
				//@ assert m < strlen(reject);
				//@ ghost in_array_intro((char *)reject, *p, m);
				//@ assert in_array(reject, *p);
				return count;
			}
			//@ ghost valid_str_shift((char *)r);
			//@ ghost m++;
		}
		//@ assert !in_array(reject, *p);
		//@ ghost valid_str_shift((char *)p);
		//@ ghost k++;
		++count;
	}
	//@ ghost valid_str_len((char *)s);
	//@ ghost valid_str_len((char *)reject);
	//@ ghost strcspn_range((char *)s, (char *)reject);
	return count;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strcspn((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	size_t res;
	const char *reject = "1234567890";

	res = strcspn("abcbcd", reject);
	res = strcspn("123456", reject);
	res = strcspn("abc023", reject);
	res = strcspn("",       reject);
	res = strcspn("abcbcd", "");
	res = res;

	return 0;
}
#endif
