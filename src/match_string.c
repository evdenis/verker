#include "match_string.h"


int match_string(const char * const *array, size_t n, const char *string)
{
	int index;
	const char *item;
	
  /*@
		loop invariant 0 <= index <= real_len(array, n) <= n;
		loop invariant
			\forall size_t k;
				0 <= k < index ==>
					strcmp(array[k], string) != 0;
		loop invariant
			\forall size_t k;
				0 <= k < index ==>
					array[k] != NULL;
		loop invariant
			\forall size_t k;
					0 <= k < index ==>
						valid_str(array[k]);
		loop assigns index;
		loop assigns item;
		loop variant real_len(array, n) - index;
  */
	for (index = 0; index < n; index++) {
		item = array[index];
		if (!item)
			break;
		//@ assert valid_str(array[index]);
		if (!strcmp(item, string))
			//@ assert strlen(item) == strlen(string);
			/*@
				assert \forall size_t i;
					0 < i <= strlen(item) ==> item[i] == string[i];
			 */
			return index;

		/*@
			assert
				\exists size_t i;
					(
						0 <= i <= \min(strlen(item), strlen(string)) &&
						item[i] != string[i]
					);
		*/
		/*@ assert \forall size_t i;
			0 <= i <= index ==> strcmp(array[i], string) != 0;
		*/
	}

	/*@ assert \forall size_t i;
		0 <= i < real_len(array, n) ==> strcmp(array[i], string) != 0;
	*/

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