#include "strspn.h"

size_t strspn(const char *s, const char *accept)
{
	const char *p;
	const char *a;
	size_t count = 0;

	//@ ghost size_t k = 0;
	//@ ghost size_t m = 0;
	/*@ loop invariant idx:      p == s + k;
	    loop invariant bound:    0 <= k <= strlen(s);
	    loop invariant len:      strlen(s) == strlen(p) + k;
	    loop invariant valid:    valid_str(p);
	    loop invariant cnt:      count == k;
	    loop invariant accepted: \forall integer i; 0 <= i < k ==> in_array(accept, s[i]);
	    loop invariant span:     strspn(s, accept) == strspn(p, accept) + k;
	    loop assigns p, a, count, k, m;
	    loop variant strlen(s) - k;
	 */
	for (p = s; *p != '\0'; ++p) {
		//@ ghost m = 0;
		/*@ loop invariant iidx:   a == accept + m;
		    loop invariant ibound: 0 <= m <= strlen(accept);
		    loop invariant ilen:   strlen(accept) == strlen(a) + m;
		    loop invariant ivalid: valid_str(a);
		    loop invariant inone:  \forall integer i; 0 <= i < m ==> accept[i] != *p;
		    loop assigns a, m;
		    loop variant strlen(accept) - m;
		 */
		for (a = accept; *a != '\0'; ++a) {
			if (*p == *a)
				break;
			//@ ghost valid_str_shift((char *)a);
			//@ ghost m++;
		}
		if (*a == '\0')
			//@ assert !in_array(accept, *p);
			return count;
		//@ ghost valid_str_len((char *)a);
		//@ assert strlen(a) > 0;
		//@ assert m < strlen(accept);
		//@ ghost in_array_intro((char *)accept, *p, m);
		//@ assert in_array(accept, *p);
		//@ ghost valid_str_shift((char *)p);
		//@ ghost k++;
		++count;
	}
	//@ ghost valid_str_len((char *)s);
	//@ ghost valid_str_len((char *)accept);
	//@ ghost strspn_range((char *)s, (char *)accept);
	return count;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strspn((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	size_t res;
	const char *accept = "1234567890";

	res = strspn("098765", accept);
	res = strspn("098abc", accept);
	res = strspn("abc",    accept);
	res = strspn("",       accept);
	res = res;

	return 0;
}
#endif
