#include "match_string.h"


int match_string(const char * const *array, size_t n, const char *string)
{
	int index;
	const char *item;

	/*@ assert 0 == 1; */

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