#include "match_string.h"


int match_string(const char * const *array, size_t n, const char *string)
{
	int index;
	const char *item;

	/*@ loop invariant bounds: 0 <= index <= n && index <= INT_MAX;
	    loop invariant limit: \forall integer length;
	       match_string_array(array, n, length) ==> index <= length;
	    loop invariant skipped: \forall integer i; 0 <= i < index ==>
	       array[i] != \null && valid_str(array[i]) && strcmp(array[i], string) != 0;
	    loop assigns index, item;
	    loop variant INT_MAX - index;
	 */
	for (index = 0; index < n; index++) {
		item = array[index];
		if (!item) {
			/*@ assert end: \forall integer length;
			       match_string_array(array, n, length) ==> index == length;
			 */
			break;
		}
		/*@ assert next: \forall integer length;
		       match_string_array(array, n, length) ==> index < length;
		 */
		//@ assert valid_item: valid_str(item);
		if (!strcmp(item, string)) {
			return index;
		}

		//@ ghost strcmp_corollary((char *)item, (char *)string);
		/*@ assert differs: \exists integer i;
		       0 <= i <= \min(strlen(item), strlen(string)) &&
		       item[i] != string[i];
		 */
	}

	return -EINVAL;
}


#ifdef DUMMY_MAIN
#include <assert.h>

int main(void)
{
	const char *items[] = {"first", "match", "match", NULL, "late"};
	const char *empty[] = {NULL};

	assert(match_string(NULL, 0, "match") == -EINVAL);
	assert(match_string(empty, (size_t)-1, "match") == -EINVAL);
	assert(match_string(items, 1, "first") == 0);
	assert(match_string(items, 1, "match") == -EINVAL);
	assert(match_string(items, 3, "match") == 1);
	assert(match_string(items, (size_t)-1, "match") == 1);
	assert(match_string(items, 5, "late") == -EINVAL);
	assert(match_string(items, (size_t)-1, "missing") == -EINVAL);
	return 0;
}
#endif
