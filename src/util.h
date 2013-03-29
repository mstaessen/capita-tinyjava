#ifndef UTIL_H
#define UTIL_H

int add_truncating(int x, int y);
  //@ requires true;
  //@ ensures true;

int sub_truncating(int x, int y);
  //@ requires true;
  //@ ensures true;

int times_truncating(int x, int y);
  //@ requires true;
  //@ ensures true;

short unsigned_chars_to_short(unsigned char b1, unsigned char b2);
  //@ requires true;
  //@ ensures true;

#endif