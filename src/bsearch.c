#include "bsearch.h"

/*@ requires \typeof(key) <: \type(char *);
    requires \typeof(elt) <: \type(char *);
    requires \valid_read((char *)key) && \valid_read((char *)elt);
    assigns \nothing;
    ensures \result > 0  <==> *((char *)key) > *((char *)elt);
    ensures \result < 0  <==> *((char *)key) < *((char *)elt);
    ensures \result == 0 <==> *((char *)key) == *((char *)elt);
 */
int ccmp(const void *key, const void *elt)
{
   return *((char *)key) > *((char *)elt) ? 1 : *((char *)key) - *((char *)elt);
}

//@ lemma Dummy: ccmp == \null || ccmp != \null;

/*@ requires \typeof(key) <: \type(char *);
    requires \typeof(base) <: \type(char *);
    requires size == 1;
    requires \valid_read((char *)key+(0..size));
    requires \valid_read((char *)base+(0..num*size));
    requires cmp == ccmp;
    assigns \nothing;
    //behavior NOT_EXISTS:
    //   assumes \forall integer i; 0 <= i < n ==> a[i] != key;
    //   ensures \result == \null;
    //behavior EXISTS:
    //   assumes \exists integer i; 0 <= i < n && a[i] == key;
    //   ensures \exists integer i; 0 <= i < n && \result == (a + i);
    //   ensures (*\result) == key;
    //complete behaviors;
    //disjoint behaviors;
 */
void *bsearch(const void *key, const void *base, size_t num, size_t size,
	      int (*cmp)(const void *key, const void *elt))
{
	size_t start = 0, end = num;
	int result;

	/* loop invariant 0 <= start;
	    loop invariant end <= num;
	    loop invariant \forall integer i;
	                      0 <= i < num && a[i] == *((char *)key) ==>
	                         start <= i <= end;
	    loop invariant \forall integer i;
	                      0 <= i < num && a[i] == *((char *)key) ==>
	                         a[start] <= key <= a[end];
	    loop variant end - start;
	 */
	while (start < end) {
		size_t mid = start + (end - start) / 2;

		result = cmp(key, base + mid * size);
		if (result < 0)
			end = mid;
		else if (result > 0)
			start = mid + 1;
		else
			return (void *)base + mid * size;
	}

	return NULL;
}
