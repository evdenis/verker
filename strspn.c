#include "strspn.h"

size_t strspn(const char *s, const char *accept)
{
	const char *p;
	const char *a;
	size_t count = 0;

	/*@ loop invariant s <= p <= s + strlen(s);
	    loop invariant 0 <= count <= strlen(s);
	    loop invariant count == p - s;
	    loop invariant \forall char *c; s <= c < p ==>
	                   (\exists char *t; accept <= t < accept + strlen(accept) && *c == *t);
	    loop invariant valid_str(p);
	    loop invariant strspn(s, accept) == strspn(p, accept) + count;
	    loop variant strlen(s) - (p - s);
	 */
	for (p = s; *p != '\0'; ++p) {
		/*@ loop invariant accept <= a <= accept + strlen(accept);
		    loop invariant \forall char *c; accept <= c < a ==> *c != *p;
		    loop invariant valid_str(a);
		    loop invariant in_array(accept, *p) ==> in_array(a, *p);
		    loop variant strlen(accept) - (a - accept);
		 */
		for (a = accept; *a != '\0'; ++a) {
			if (*p == *a)
				break;
		}
		if (*a == '\0')
			//@ assert !in_array(accept, *p);
			return count;
		//@ assert in_array(accept, *p);
		++count;
	}
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
