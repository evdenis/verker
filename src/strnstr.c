#include "strnstr.h"

/*@ predicate eqstr{L1, L2}(char *str1, char *str2, integer n) =
		\forall integer i; 0 <= i < n ==> \at(str1[i], L1) == \at(str2[i], L2);
*/

/*@ requires valid_str(s1);
	requires valid_str(s2);
	requires len <= strlen(s1);
	assigns \nothing;

	behavior empty:
		assumes strlen(s2) == 0;
		ensures \result == s1;
	behavior len_l_l2:
		assumes strlen(s2) != 0;
		assumes len < strlen(s2);
		ensures \result == NULL;
	behavior not_found:
		assumes strlen(s2) != 0;
		assumes len >= strlen(s2);
		assumes \forall integer j; 0 <= j <= len - strlen(s2) ==> !eqstr{Pre, Pre}(s1 + j, s2, strlen(s2));
		ensures \result == NULL;
	behavior found:
		assumes strlen(s2) != 0;
		assumes len >= strlen(s2);
		assumes \exists integer j; 0 <= j <= len - strlen(s2)  && eqstr{Pre, Pre}(s1 + j, s2, strlen(s2));
		ensures eqstr{Post, Pre}(\result, s2, strlen(s2));
	disjoint behaviors;
	complete behaviors;
*/

char *strnstr(const char *s1, const char *s2, size_t len)
{
	size_t l2;
	//@ ghost char* os1 = s1;
	//@ ghost size_t olen = len;
	//@ ghost bool t = false;

	l2 = strlen(s2);
	//@ assert strlen(s2) == l2;
	if (!l2)
		return (char *)s1;
	/*@
		//loop invariant valid_str(os1);
		//loop invariant s1 - olen >= os1 - len;
		//loop invariant s1 - os1 == olen - len;
		loop invariant os1 <= s1 <= os1 + strlen(os1);
		loop invariant s1 + len == os1 + olen;
		loop invariant len <= strlen(s1);
		loop invariant valid_str(s1);
		loop invariant valid_str(s2);
		loop assigns len, s1;
		//loop invariant eqstr{Pre, Pre}(\at(s1, Pre), s2, l2) ^^ !eqstr{Pre, Pre}(\at(s1, Pre), s2, l2);
		//loop invariant s1 == os1 || !eqstr{Here, Pre}(s1 - 1, s2, l2);
		//loop invariant eqstr{Pre, Pre}(\at(s1, Pre), s2, l2) ^^ (\forall integer j; 0 <= j <= s1 - os1 ==> !eqstr{Here, Pre}(\at(s1, Pre) + j, s2, l2));
		//loop invariant (s1 != os1) ==> (\forall integer j; 0 <= j <= s1 - os1 ==> !eqstr{Pre, Pre}(os1 + j, s2, l2));
		loop invariant \forall integer j; 0 <= j < s1 - os1 ==> !eqstr{Pre, Pre}(os1 + j, s2, l2);
		loop variant len;
	*/
	while (len >= l2) {
		//@ ghost t = false;
		//@ assert \at(len, Pre) >= strlen(s2);
		len--;
		if (!memcmp(s1, s2, l2))
			//@ assert eqstr{Here, Pre}(s1, s2, l2);
			//@ assert strlen(os1) == strlen{Pre}(\at(s1, Pre));
			//@ assert \forall integer i; 0 <= i < strlen{Pre}(\at(s1, Pre)) ==> \at(os1[i], Here) == \at(s1[i], Pre);
			//@ assert eqstr{Here, Pre}(os1, \at(s1, Pre), strlen{Pre}(\at(s1, Pre)));
			//@ assert \exists integer j; eqstr{Here, Pre}(os1 + j, s2, l2) && j == s1 - os1;
			return (char *)s1;
		s1++;
	}
	//@ assert len < strlen(s2);
	//@ assert \forall integer j; 0 <= j <= len - l2 ==> !eqstr{Pre, Pre}(\at(s1, Pre) + j, s2, l2);
	return NULL;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		strnstr((const char *)data, (const char *)(data + size / 2), size / 2);
	}
	return 0;
}
#endif


#ifdef DUMMY_MAIN

#include <string.h>

int main(int argc, char *argv[])
{
	const char *s1 = "1234567890";
	char *ptr;

	ptr = strnstr(s1, "789", strlen(s1));
	ptr = strnstr(s1, "789", strlen(s1) / 2);
	ptr = strnstr(s1, "000", strlen(s1));
	ptr = ptr;

	return 0;
}
#endif
