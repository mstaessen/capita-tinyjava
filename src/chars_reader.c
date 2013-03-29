#include "chars_reader.h"

#include <stdlib.h>
#include <stdio.h>
//@ #include "arrays.gh"

struct chars_reader {
  char *buffer;
  int size;
  int offset;
  //@ real frac;
};

/*@
predicate chars_reader(struct chars_reader* r, char* buffer, int size, real f) =
  r->buffer |-> buffer &*& r->size |-> size &*& r->offset |-> ?offset &*& malloc_block_chars_reader(r) &*& 
  0 <= size &*& 0 <= offset &*& offset <= size &*& r->frac |-> f &*&
  [f]buffer[0..size] |-> ?cs &*& [f]malloc_block(buffer, size);
@*/

struct chars_reader* create_chars_reader_from_file(char* path)
  //@ requires [?f]string(path, ?cs);
  //@ ensures chars_reader(result, ?buffer, ?size, 1) &*& [f]string(path, cs);
{ 
  int filesize;
  struct chars_reader* r = malloc(sizeof(struct chars_reader));
  FILE* file = fopen(path, "rb");
  if(r == 0) {
    abort();
  } else if(file == 0) {
    abort();
  } else {
    char* buffer; 
    long file_size;
    fseek(file, 0, 2 /* SEEK_END*/);
    file_size = ftell(file);
    if(file_size < 0) {
      abort();
    }
    r->size = file_size;
    rewind(file);
    buffer = malloc(sizeof(char) * (r->size));
    if(buffer == 0) {
      abort();
    }
    r->buffer = buffer;
    r->offset = 0;
    //@ r->frac = 1;
    fread(buffer, r->size, 1, file);
    fclose(file);
    //@ close chars_reader(r, buffer, file_size, 1);
    return r; 
  }
}

struct chars_reader* create_chars_reader(char* buffer, int size)
  //@ requires [?f]buffer[0..size] |-> ?cs &*& [f]malloc_block(buffer, size);
  //@ ensures chars_reader(result, buffer, size, f);
{
  struct chars_reader* r = malloc(sizeof(struct chars_reader));
  if(r == 0) {
    abort();
  }
  r->buffer = buffer;
  r->size = size;
  r->offset = 0;
  //@ r->frac = f;
  //@ close chars_reader(r, buffer, size, f);
  return r;
}

char reader_next_int8(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  char res;
  //@ open chars_reader(r, buffer, size, f);
  if (r->offset < 0 || r->size <= r->offset) {
    abort();
  }
  res = r->buffer[r->offset];
  r->offset++;
  return res;
  //@ close chars_reader(r, buffer, size, f);
}

unsigned char reader_next_uint8(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  char res;
  //@ open chars_reader(r, buffer, size, f);
  if (r->offset < 0 || r->size <= r->offset) {
    abort();
  }
  res = r->buffer[r->offset];
  r->offset++;
  return (unsigned char) res;
  //@ close chars_reader(r, buffer, size, f);
}

unsigned char reader_get_uint8_at(struct chars_reader* r, int offset)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  char res;
  //@ open chars_reader(r, buffer, size, f);
  if (offset < 0 || r->size <= offset) {
    abort();
  }
  res = r->buffer[offset];
  return (unsigned char) res;
  //@ close chars_reader(r, buffer, size, f);
}

short reader_next_int16(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  unsigned char low, high;
  //@ open chars_reader(r, buffer, size, f);
  if (r->offset < 0 || r->size - r->offset < sizeof(short)) {
   abort();
  }
  low = (unsigned char) r->buffer[r->offset + 1];
  //@ produce_limits(low);
  high = (unsigned char) r->buffer[r->offset];
  //@ produce_limits(high);
  r->offset += 2;
  return /*@ truncating @*/ (short) ((unsigned int) low + (unsigned int) 256 * high);
  //@ close chars_reader(r, buffer, size, f);
}

unsigned short reader_next_uint16(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  unsigned char low, high;
  //@ open chars_reader(r, buffer, size, f);
  if (r->offset < 0 || r->size - r->offset < sizeof(unsigned short)) {
   abort();
  }
  low = (unsigned char) r->buffer[r->offset + 1];
  //@ produce_limits(low);
  high = (unsigned char) r->buffer[r->offset];
  //@ produce_limits(high);
  r->offset += 2;
  return (unsigned short) ((unsigned int) low + (unsigned int) 256 * high);
  //@ close chars_reader(r, buffer, size, f);
}

int reader_next_int32(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  unsigned short low, high;
  //@ open chars_reader(r, buffer, size, f);
  if (r->offset < 0 || r->size - r->offset < sizeof(int)) {
    abort();
  }
  //@ close chars_reader(r, buffer, size, f);
  high = reader_next_uint16(r);
  //@ produce_limits(high);
  low = reader_next_uint16(r);
  //@ produce_limits(low);
  return  (high << 16) | low; //todo: check if + is equal to | here
}

unsigned int reader_next_uint32(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  unsigned short low, high;
  //@ open chars_reader(r, buffer, size, f);
  if (r->offset < 0 || r->size - r->offset < sizeof(unsigned int)) {
    abort();
  }
  //@ close chars_reader(r, buffer, size, f);
  high = reader_next_uint16(r);
  low = reader_next_uint16(r);
  return (unsigned int) ((unsigned int) low + (unsigned int) 65536 * high);
}

char* reader_next_chars(struct chars_reader* r, int length)
  //@ requires chars_reader(r, ?buffer, ?size, ?f) &*& 0 <= length;
  //@ ensures chars_reader(r, buffer, size, f) &*& result != 0 &*& result[0..length] |-> _ &*& malloc_block(result, length);
{
  int i;
  char* res = malloc(length);
  if(res == 0 ) { abort(); }
  for(i = 0; i < length; i++)
     //@ invariant 0 <= i && i <= length &*& res[0..length] |-> _ &*& chars_reader(r, buffer, size, f);
  {
    char c = reader_next_int8(r);
    res[i] = c;
  }
  return res;
}

int reader_get_offset(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f) &*& 0 <= result &*& result <= size;
{
  //@ open chars_reader(r, buffer, size, f);
  return r->offset;
  //@ close chars_reader(r, buffer, size, f);
}

void reader_set_offset(struct chars_reader* r, int offset)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  //@ open chars_reader(r, buffer, size, f);
  if(offset < 0 || offset > r->size) {
    abort();
  }  
  r->offset = offset;
  //@ close chars_reader(r, buffer, size, f);
}

void reader_skip(struct chars_reader* r, int nb)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f);
{
  //@ open chars_reader(r, buffer, size, f);
  if(nb < 0 && r->offset + nb < 0) {
    abort();
  }
  if(nb > 0 && r->size - r->offset < nb) {
    abort();
  }
  r->offset += nb;
  //@ close chars_reader(r, buffer, size, f);
}

char* reader_get_buffer(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures chars_reader(r, buffer, size, f) &*& result == buffer;
{
  //@ open chars_reader(r, buffer, size, f);
  return r->buffer;
  //@ close chars_reader(r, buffer, size, f);
}

void reader_dispose(struct chars_reader* r)
  //@ requires chars_reader(r, ?buffer, ?size, ?f);
  //@ ensures [f]buffer[0..size] |-> _ &*& [f]malloc_block(buffer, size);
{
  //@ open chars_reader(r, buffer, size, f);
  free(r);
}
