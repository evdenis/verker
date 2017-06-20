#include "match_string.h"


/*@ requires valid_str(string);
    requires n <= INT_MAX;
    requires \valid(array + (0 .. n - 1));
    requires \forall integer i; 0 <= i < n - 1 ==> valid_str(array[i]);
    requires array[n - 1] == \null || valid_str(array[n - 1]);
    assigns \nothing;
    //behavior b1:
    //behavior b2:
    //complete behaviors;
    //disjoint behaviors;
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
}
#endif
