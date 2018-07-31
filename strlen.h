#ifndef __STRLEN_H__
#define __STRLEN_H__

#include "kernel_definitions.h"

/*@ axiomatic Strlen {
    predicate valid_str(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    //lemma valid_str_shift1:
    //   \forall char *s;
    //      *s != '\0' &&
    //      valid_str(s) ==>
    //         valid_str(s+1);

    //lemma valid_str_strend:
    //   \forall char *s;
    //      \valid(s) && *s == '\0' ==>
    //         valid_str(s);

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    //lemma strlen_before_null:
    //   \forall char* s, integer i;
    //      valid_str(s) &&                        // <-- should be `==>' (!)
    //      0 <= i < strlen(s) ==> s[i] != '\0';

    // lemma strlen_at_null:
    //   \forall char* s;
    //      valid_str(s) ==> s[strlen(s)] == '\0';

    // lemma strlen_shift:
    //   \forall char *s, size_t i;
    //      valid_str(s) &&
    //      i <= strlen(s) ==>
    //      strlen(s+i) == strlen(s)-i;

    // lemma strlen_shift_ex:
    //   \forall char *s, size_t i;
    //      valid_str(s) &&
    //      0 < i <= strlen(s) ==>
    //      strlen(s+i) < strlen(s);

    // lemma strlen_shift1:
    //   \forall char *s;
    //      valid_str(s) && *s != '\0' ==>
    //      strlen(s) == 1 + strlen(s+1);

    // lemma strlen_pointers:
    //   \forall char *s, *sc;
    //      valid_str(s)  &&
    //      valid_str(sc) &&
    //      \base_addr(s) == \base_addr(sc) &&
    //      s <= sc &&
    //      (\forall integer i; 0 <= i <= sc - s ==> s[i] != '\0') ==>
    //         strlen(sc) <= strlen(s);

    // lemma strlen_main:
    //   \forall char *s, size_t n;
    //   valid_str(s) &&
    //   s[n] == '\0' &&
    //   (\forall integer i; 0 <= i < n ==> s[i] != '\0') ==>
    //       strlen(s) == n;

    // lemma valid_str_shiftn:
    //   \forall char *s, integer i;
    //      valid_str(s) &&
    //      (0 <= i < strlen(s)) ==>
    //         valid_str(s+i);
    }
 */

/**
 * strlen - Find the length of a string
 * @s: The string to be sized
 */

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ ensures s[\result] == '\0';
  @  @ ensures \valid(s+(0..\result));
  @  @ ensures \forall size_t j; j < \result ==> s[j] != '\0';
  @  @/
  @ size_t elim_valid_str(char *s)
  @ {
  @    /@ loop invariant \forall size_t j; j < i ==> s[j] != '\0';
  @     @ loop variant ULLONG_MAX - i;
  @     @/ 
  @    for (size_t i = 0; i <= ULLONG_MAX; i++) {
  @      if (s[i] == '\0') return i;
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ ensures s[\result] == '\0';
  @  @ ensures \valid(s+(0..\result));
  @  @ ensures \forall size_t j; j < \result ==> s[j] != '\0';
  @  @ ensures strlen(s) == \result;
  @  @/
  @ size_t elim_valid_str_full(char *s)
  @ {
  @    size_t size = elim_valid_str(s);
  @    /@ loop invariant strlen(&s[i]) + i <= size ==> strlen(s) == strlen(&s[i]) + i;
  @     @ loop invariant 0 <= i <= size;
  @     @ loop variant size - i;
  @     @/ 
  @    for (size_t i = 0; i <= size; i++) {
  @      if (s[i] == '\0') return i;
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires \valid(s+(0..n));
  @  @ requires s[n] == '\0';
  @  @ requires \forall size_t j; j < n ==> s[j] != '\0';
  @  @ ensures valid_str(s);
  @  @ ensures strlen(s) == n;
  @  @/
  @  void intro_valid_str_full(char *s, size_t n)
  @  {
  @    //@ assert valid_str(s);
  @    elim_valid_str_full(s);
  @  }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ ensures s[0] == '\0' ==> strlen(s) == 0;
  @  @ ensures s[0] != '\0' ==> strlen(s) == 1 + strlen(s + 1);
  @  @/
  @ void elim_strlen(char *s)
  @ {
  @   size_t size = elim_valid_str_full(s);
  @    if (s[0] != '\0') {
  @      //@ assert (s + 1)[size -% 1] == '\0';
  @      size_t size1 = elim_valid_str_full(s + 1);
  @      //@ assert size1 >= size - 1;
  @      //@ assert size1 <= size - 1; 
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires valid_str(s) && 0 <= i < strlen(s);
  @  @ ensures valid_str(s + i);
  @  @ lemmafn \true;
  @  @/
  @  void valid_str_shiftn(char *s, size_t i) {
  @    elim_valid_str_full(s);
  @    /@ loop invariant valid_str(s + j);
  @     @ loop invariant 0 <= j <= i;
  @     @ loop variant i - j;
  @     @/
  @    for (size_t j = 0; j < i; j++) {
  @      size_t size = elim_valid_str_full(s + j);
  @      if ((s + j)[0] != '\0') {
  @        //@ assert \forall size_t k; k < size - 1 ==> (s + j + 1)[k] == (s + j)[k +% 1];
  @        intro_valid_str_full(s + j + 1, size - 1);
  @      }
  @    }
  @  }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ ensures \forall integer i; 0 <= i < strlen(s) ==> valid_str(s + i);
  @  @ lemmafn \true;
  @  @/
  @  void valid_str_shiftn_full(char *s) {
  @    size_t size = elim_valid_str_full(s);
  @    /@ loop invariant 0 <= i <= size;
  @     @ loop invariant \forall integer j; 0 <= j < i ==> valid_str(s + j);
  @     @ loop variant size - i;
  @     @/
  @    for (size_t i = 0; i < size; i++)
  @      valid_str_shiftn(s, i);
  @  }
  @*/

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires 0 <= i < strlen(s); 
  @  @ ensures s[i] != '\0';
  @  @ lemmafn \true;
  @  @/
  @ void strlen_before_null(char *s, size_t i) {
  @   elim_valid_str_full(s);
  @ }
  @*/
  
/*@ ghost
  @ /@ requires valid_str(s);
  @  @ ensures \forall integer i; 0 <= i < strlen(s) ==> s[i] != '\0';
  @  @ lemmafn \true;
  @  @/
  @ void strlen_before_null_full(char *s) {
  @   size_t size = elim_valid_str_full(s);
  @    /@ loop invariant 0 <= i <= size;
  @     @ loop invariant \forall integer j; 0 <= j < i ==> s[j] != '\0';
  @     @ loop variant size - i;
  @     @/
  @    for (size_t i = 0; i < size; i++)
  @      strlen_before_null(s, i);
  @ }
  @*/  

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ ensures s[strlen(s)] == '\0';
  @  @ lemmafn \true;
  @  @/
  @ void strlen_at_null(char *s, size_t i) {
  @   elim_valid_str_full(s);
  @ }
  @*/ 

/*@ ghost
  @ /@ requires valid_str(s);
  @  @ requires s[n] == '\0';
  @  @ requires \forall integer i; 0 <= i < n ==> s[i] != '\0';
  @  @ ensures  strlen(s) == n;
  @  @ lemmafn \true;
  @  @/
  @ void strlen_main(char *s, size_t n) {
  @   elim_valid_str_full(s);
  @ }
  @*/

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \result == strlen(s);
    ensures s[\result] == '\0';
    ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';
 */
size_t strlen(const char *s);

#endif // __STRLEN_H__
