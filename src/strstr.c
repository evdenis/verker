#include "strstr.h"

/*@ axiomatic StrStr {
    logic char *strstr(char *s1, char *s2);

    // plain character equality: the same relation memcmp's postcondition
    // gives on (unsigned char) values
    predicate strmatch(char *s1, char *s2) =
       \forall integer i;
          0 <= i < strlen(s2) ==>
             s1[i] == s2[i];
    }
 */

/*@ requires valid_str(s1);
    requires valid_str(s2);
    requires strlen(s1) <= LONG_MAX;
    requires strlen(s2) <= LONG_MAX;
    terminates \true;
    assigns \result \from s1, s2;
    exits \false;
    behavior exists:
       assumes \exists integer i; 0 <= i <= strlen(s1) && strmatch(s1 + i, s2);
       ensures 0 <= \result - s1 <= strlen(s1);
    behavior not_exists:
       assumes \forall integer i; 0 <= i <= strlen(s1) ==> !strmatch(s1 + i, s2);
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strstr(const char *s1, const char *s2)
{
	size_t l1, l2;

	l2 = strlen(s2);
	if (!l2)
		return (char *)s1;
	//@ assert strlen(s2) > 0;
	l1 = strlen(s1);
	//@ ghost char *os1 = (char *)s1;
	//@ ghost size_t ol1 = l1;
	//@ ghost size_t k = 0;
	//@ ghost valid_str_len(os1);
	/*@ loop invariant bound:   l1 <= ol1;
	    loop invariant idx:     s1 == os1 + k;
	    loop invariant offset:  k == ol1 - l1;
	    loop invariant len:     ol1 == strlen(os1);
	    loop invariant valid:   valid_str(s1);
	    loop invariant lens1:   strlen(os1) == strlen(s1) + k;
	    loop invariant nomatch: \forall integer i; 0 <= i < k ==> !strmatch(os1 + i, s2);
	    loop assigns l1, s1, k;
	    loop variant l1;
	 */
	while (l1 >= l2) {
		l1--;
		int c = /*CODE_CHANGE:*/memcmp(s1, s2, l2);
		if (!c) {
			//@ assert \forall integer i; 0 <= i < l2 ==> s1[i] == s2[i];
			//@ assert strmatch(s1, s2);
			//@ assert \exists integer i; 0 <= i <= strlen(os1) && strmatch(os1 + i, s2);
			return (char *)s1;
		}
		//@ assert c != 0;
		//@ assert l2 == strlen(s2);
		//@ assert exists_diff: \exists integer i; 0 <= i < l2 && s1[i] != s2[i];
		//@ assert !strmatch(s1, s2);
		//@ ghost valid_str_shift((char *)s1);
		s1++;
		//@ ghost k++;
	}
	return NULL;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strstr((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	const char *s1 = "1234567890";
	char *ptr;

	ptr = strstr(s1, "789");
	ptr = strstr(s1, "000");
	ptr = ptr;

	return 0;
}
#endif
