#define CONFIG_HAVE_EFFICIENT_UNALIGNED_ACCESS 1

#define ___config_enabled(__ignored,val,...) val

#define __config_enabled(arg1_or_junk) ___config_enabled(arg1_or_junk 1, 0)

#define _config_enabled(value) __config_enabled(__ARG_PLACEHOLDER_ ##value)

#define config_enabled(cfg) _config_enabled(cfg)

#define IS_BUILTIN(option) config_enabled(option)

#define IS_MODULE(option) config_enabled(option ##_MODULE)

#define IS_ENABLED(option) (IS_BUILTIN(option) || IS_MODULE(option))

typedef unsigned long __kernel_ulong_t;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_size_t size_t;
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------


//------------------------------------------------------------------------------

/*@ requires size > 0;
    requires \forall integer i; 0 <= i < size ==> \typeof(a + i) <: \type(char *);
    requires \forall integer i; 0 <= i < size ==> \typeof(b + i) <: \type(char *);
    requires \valid((char *)a + (0..size-1));
    requires \valid((char *)b + (0..size-1));
    requires \base_addr(a) == \base_addr(b) || \base_addr(a) != \base_addr(b);
    assigns ((char *)a)[0..size-1];
    assigns ((char *)b)[0..size-1];
    ensures \forall integer i; 0 <= i < size ==> *((char *)a + i) == \old(*((char *)b + i));
    ensures \forall integer i; 0 <= i < size ==> *((char *)b + i) == \old(*((char *)a + i));
 */
static void generic_swap(void *a, void *b, int size)
{
	char t;

   /*@ loop invariant size >= 0;
       loop invariant 0 <= a - \at(a, Pre) < \at(size, Pre);
       loop invariant \base_addr(a) == \base_addr(\at(a,Pre));
       loop invariant \base_addr(b) == \base_addr(\at(b,Pre));
       //loop invariant a - \at(a, Pre) == \at(size, Pre) - size;
       //loop invariant 0 <= b - \at(b, Pre) <= size;
       //loop invariant \forall integer i; 0 <= i <= (\at(size, Pre) - size) ==>
       //   *((char *)b + i) == \at(*((char *)a + i), Pre);
       loop variant size;
    */
	do {
		t = *(char *)a;
		*(char *)a++ = *(char *)b;
		*(char *)b++ = t;
	} while (--size > 0);
}

/*@ requires \typeof(a) <: \type(u32 *);
    requires \typeof(b) <: \type(u32 *);
    requires \valid((u32 *)a);
    requires \valid((u32 *)b);
    assigns *((u32 *)a), *((u32 *)b);
    ensures *((u32 *)a) == \old(*((u32 *)b));
    ensures *((u32 *)b) == \old(*((u32 *)a));
 */
static void u32_swap(void *a, void *b, int size)
{
	u32 t = *(u32 *)a;
	*(u32 *)a = *(u32 *)b;
	*(u32 *)b = t;
}

/*@ requires \typeof(a) <: \type(u64 *);
    requires \typeof(b) <: \type(u64 *);
    requires \valid((u64 *)a);
    requires \valid((u64 *)b);
    assigns *((u64 *)a), *((u64 *)b);
    ensures *((u64 *)a) == \old(*((u64 *)b));
    ensures *((u64 *)b) == \old(*((u64 *)a));
 */
static void u64_swap(void *a, void *b, int size)
{
	u64 t = *(u64 *)a;
	*(u64 *)a = *(u64 *)b;
	*(u64 *)b = t;
}

static int alignment_ok(const void *base, int align)
{
	return IS_ENABLED(CONFIG_HAVE_EFFICIENT_UNALIGNED_ACCESS) ||
		((unsigned long)base & (align - 1)) == 0;
}

void sort(void *base, size_t num, size_t size,
	  int (*cmp_func)(const void *, const void *),
	  void (*swap_func)(void *, void *, int size))
{
	/* pre-scale counters for performance */
	int i = (num/2 - 1) * size, n = num * size, c, r;

	if (!swap_func) {
		if (size == 4 && alignment_ok(base, 4))
			swap_func = u32_swap;
		else if (size == 8 && alignment_ok(base, 8))
			swap_func = u64_swap;
		else
			swap_func = generic_swap;
	}

	/* heapify */
	for ( ; i >= 0; i -= size) {
		for (r = i; r * 2 + size < n; r  = c) {
			c = r * 2 + size;
			if (c < n - size &&
					cmp_func(base + c, base + c + size) < 0)
				c += size;
			if (cmp_func(base + r, base + c) >= 0)
				break;
			swap_func(base + r, base + c, size);
		}
	}

	/* sort */
	for (i = n - size; i > 0; i -= size) {
		swap_func(base, base + i, size);
		for (r = 0; r * 2 + size < i; r = c) {
			c = r * 2 + size;
			if (c < i - size &&
					cmp_func(base + c, base + c + size) < 0)
				c += size;
			if (cmp_func(base + r, base + c) >= 0)
				break;
			swap_func(base + r, base + c, size);
		}
	}
}
