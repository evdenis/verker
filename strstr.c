#include "strstr.h"

/*@ axiomatic StrStr {
    logic char *strstr(char *s1, char *s2);

    predicate strmatch(char *s1, char *s2) =
       (strlen(s1) == strlen(s2)) &&
       (\forall integer i;
          0 <= i <= strlen(s1) ==>
             s1[i] == s2[i]);
    }
 */

/*@ requires valid_str(s1);
    requires valid_str(s2);
    assigns \nothing;
    behavior exists:
       assumes \exists char *s; s1 <= s <= s1 + strlen(s1) && strmatch(s, s2);
       ensures s1 <= \result <= s1 + strlen(s1);
    behavior not_exists:
       assumes \forall char *s; s1 <= s <= s1 + strlen(s1) ==> !strmatch(s, s2);
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
	//@ ghost char *os1 = s1;
	//@ ghost size_t ol1 = l1;
	/*@ loop invariant l1 <= ol1;
	    loop invariant ol1 - l1 == s1 - os1;
	    loop invariant os1 <= s1 <= os1 + strlen(os1);
	    loop invariant valid_str(s1);
	    loop invariant \forall char *s; os1 <= s < s1 ==> !strmatch(s, s2);
	    loop variant l1;
	 */
	while (l1 >= l2) {
		l1--;
		if (!memcmp(s1, s2, l2))
			return (char *)s1;
		s1++;
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
