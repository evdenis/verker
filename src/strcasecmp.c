#include "strcasecmp.h"

int strcasecmp(const char *s1, const char *s2)
{
	int c1, c2;
	//@ ghost char *os1 = (char *)s1;
	//@ ghost char *os2 = (char *)s2;
	//@ ghost size_t k = 0;
	//@ ghost valid_str_len(os1);
	//@ ghost valid_str_len(os2);

	/*@ loop invariant valid: valid_str(s1) && valid_str(s2);
	    loop invariant idx1:  s1 == os1 + k;
	    loop invariant idx2:  s2 == os2 + k;
	    loop invariant bound: 0 <= k <= strlen(os1);
	    loop invariant len:   strlen(os1) == strlen(s1) + k;
	    loop invariant lower: \forall integer i; 0 <= i < k ==>
	                          tolower(os1[i]) == tolower(os2[i]);
	    loop assigns s1, s2, c1, c2, k;
	    loop variant strlen(os1) - k;
	*/
	do {
		c1 = tolower(*s1++);
		c2 = tolower(*s2++);
		/*@ ghost if (c1 == c2 && c1 != 0) {
		  @   valid_str_shift(os1 + k);
		  @   valid_str_shift(os2 + k);
		  @   k++;
		  @ }
		  @*/
	} while (c1 == c2 && c1 != 0);
	//@ ghost int res = c1 - c2;
	//@ assert c1 == c2 ==> c1 == 0 && res == 0;
	/*@ assert c1 != c2 ==>
	    \exists integer i; 0 <= i <= strlen(os1) &&
	            (\forall integer j; 0 <= j < i ==> tolower(os1[j]) == tolower(os2[j])) &&
	            tolower(os1[i]) != tolower(os2[i]) &&
	       res == tolower(os1[i]) - tolower(os2[i]) &&
	       i == k;
	 */
	return c1 - c2;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strcasecmp((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int res;
	const char *s1 = "123ABCDEFG";
	const char *s2 = "123ABCDEF";
	const char *s3 = "123abcdefg";
	const char *s4 = "123abcdeff";
	const char *s5 = "123abcdefz";

	res = strcasecmp(s1, s1);
	res = strcasecmp(s1, s2);
	res = strcasecmp(s1, s3);
	res = strcasecmp(s1, s4);
	res = strcasecmp(s1, s5);
	res = res;

	return 0;
}
#endif
