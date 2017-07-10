#include "match_string.h"

/*@ predicate null_terminator(char **array) =
       \exists integer i;
          0 <= i &&
          array[i] == \null &&
          (\forall integer j; 0 <= j < i ==> array[j] != \null);
    logic integer null_at(char **array) =
       *array == \null ? 1 : 1 + null_at(array + 1);
 */

/*@ requires valid_str(string);
    requires n <= INT_MAX;
    requires (null_terminator(array) &&
             null_at(array) <= n     &&
             \valid(array + (0 .. null_at(array))) &&
             (\forall integer i; 0 <= i < null_at(array) ==> valid_str(array[i])))
             ||
             (\valid(array + (0 .. n - 1)) &&
             (\forall integer i; 0 <= i < n ==> valid_str(array[i])));
    assigns \nothing;
 */
int match_string(const char * const *array, size_t n, const char *string)
{
	int index;
	const char *item;

	/*@ loop invariant 0 <= index;
	    loop invariant null_terminator(array) ==> index <= null_at(array);
	    loop invariant !null_terminator(array) ==> index <= n;
	    loop variant n - index;
	 */
	for (index = 0; index < n; index++) {
		item = array[index];
		//@ assert item == \null || valid_str(item);
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
