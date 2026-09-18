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

int main(int argc, char *argv[])
{
	const char *str = "12345";
	const char *list[] = {
		"TEST",
		"TST",
		"TS",
		"T",
		"12345",
		NULL
	};

	match_string(list, -1, str);
	match_string(list, 3, str);

	return 0;
}
#endif
