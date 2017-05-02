#include "match_string.h"

/*@
    assigns \nothing;
 */
int match_string(const char * const *array, size_t n, const char *string)
{
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
