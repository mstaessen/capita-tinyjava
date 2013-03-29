#ifndef CHARS_READER_H
#define CHARS_READER_H

//#include <malloc.h>

/*@
predicate chars_reader(struct chars_reader* r, char* buffer, int size, real f);
@*/

struct chars_reader;

struct chars_reader* create_chars_reader_from_file(char* path);
  //@ requires [?f]string(path, ?cs);
  //@ ensures chars_reader(result, ?buffer, ?size, 1) &*& [f]string(path, cs);

struct chars_reader* create_chars_reader(char* buffer, int size);
  //@ requires [?f]chars(buffer, size, ?cs) &*& [f]malloc_block(buffer, size);
  //@ ensures chars_reader(result, buffer, size, f);

char reader_next_int8(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
  
unsigned char reader_next_uint8(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
  
unsigned char reader_get_uint8_at(struct chars_reader* r, int offset);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

short reader_next_int16(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

unsigned short reader_next_uint16(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

int reader_next_int32(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

unsigned int reader_next_uint32(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

char* reader_next_chars(struct chars_reader* r, int length);
    //@ requires chars_reader(r, ?buffer, ?size, ?f) &*& 0 <= length;
  //@ ensures chars_reader(r, buffer, size, f) &*& result != 0 &*& chars(result, length, ?cs) &*& malloc_block(result, length);

int reader_get_offset(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f) &*& 0 <= result &*& result <= size;

void reader_set_offset(struct chars_reader* r, int offset);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

void reader_skip(struct chars_reader* r, int nb);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);

char* reader_get_buffer(struct chars_reader* r);
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f) &*& result == buffer;

void reader_dispose(struct chars_reader* r);
  //@ requires  chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures [f]chars(buffer, size, ?cs) &*& [f]malloc_block(buffer, size);

#endif
