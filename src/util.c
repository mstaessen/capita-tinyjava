#include "util.h"

int add_truncating(int x, int y)
  //@ requires true;
  //@ ensures true;
{
  return x + y;
}

int sub_truncating(int x, int y)
  //@ requires true;
  //@ ensures true;
{
  return x - y;
}

int times_truncating(int x, int y)
  //@ requires true;
  //@ ensures true;
{
  return x * y;
}

short unsigned_chars_to_short(unsigned char b1, unsigned char b2)
  //@ requires true;
  //@ ensures true;
{
  return (short) ((b1 << 8) | b2);
}

