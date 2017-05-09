#include "match_string.h"


/*@ requires valid_str(string);
    requires n <= INT_MAX;
    //requires \valid(array+(0..n-1));
    //requires \forall integer i;
    assigns \nothing;
 */
int match_string(const char * const *array, size_t n, const char *string)
{
	//int index; CODE_CHANGE:
	int index;
	const char *item;

	/*@ loop invariant 0 <= index <= n;
	    loop variant n - index;
	 */
	for (index = 0; index < n; index++) {
		item = array[index];
		if (!item)
			break;
		if (!strcmp(item, string))
			return index;
	}

	return -EINVAL;
}
