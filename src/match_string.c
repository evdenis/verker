#include "match_string.h"


int match_string(const char * const *array, size_t n, const char *string)
{
	int index;
	const char *item;

    /*@
        loop invariant 0 <= index <= n;
        loop invariant \forall integer k; 0 <= k < index ==>
            strcmp(array[k], string) != 0;
		loop invariant \forall integer k; 0 <= k < index ==>
            array[k] != NULL;
        loop assigns index;
		loop assigns item;
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