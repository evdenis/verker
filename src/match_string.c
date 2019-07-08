#include "match_string.h"


int match_string(const char * const *array, size_t n, const char *string)
{
	int index;
	const char *item;


    /*@
        loop invariant 0 <= index < real_len(array, n);
        loop invariant \forall integer k; 0 <= k < index ==> (
            array[k] != NULL &&
            strcmp(array[k], string) != 0
		);
        loop assigns index;
		loop assigns item;
        loop variant real_len(array, n) - index;
    */

	for (index = 0; index < n; index++) {
		item = array[index];
		if (!item)
			break;
		//@ assert array[index] != NULL;
		if (!strcmp(item, string))
			return index;
		//@ assert strcmp(array[index], string) != 0;
		//@ assert checked_head(array, string, index);
	}

	//@ assert checked_head(array, string, n);

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