#include "stdlib.h"
#include "threading.h"
#include "chars_reader.h"
#include "bool.h"
#include "stdio.h"
#include "limits.h"
#include "string.h"
#include "util.h"

void error(char *msg)
//@ requires [?f]string(msg, ?cs);
//@ ensures false;
{
    puts(msg);
    abort();
}

enum CONSTANT_TYPE { STRING = 1, INT = 3, CLASS = 7, METHODREF = 10, NAME_AND_TYPE = 12 };

/*@
    predicate constants(struct constant *constant, list<void *> values) =
        constant == 0 ?
            values == nil<void *> :
                malloc_block_constant(constant)
                    &*& constant->tag |-> ?tag
                    &*& constant->info |-> ?info
                    &*& constant->next |-> ?next
                    &*& const_info(info, tag)
                    &*& constants(next, ?tail)
                    &*& values == cons<void *>(constant, tail);
@*/
struct constant {
    int tag;
    void *info;
    struct constant *next;
};

/*@
    predicate const_info(void *info, int tag) =
        info != 0
            &*& (tag == STRING ?
                string_constant(info, _, _) :
                    (tag == INT ? int_constant(info, _) :
                        (tag == CLASS ? class_constant(info, _) :
                            (tag == METHODREF ? methodref_constant(info, _, _) :
                                nat_constant(info, _, _)))));
    predicate string_constant(struct string_constant *c, unsigned short length, char* string) =
        malloc_block_string_constant(c)
            &*& malloc_block(string, length)
            &*& c->length |-> length
            &*& length >= 0
            &*& c->string |-> string
            &*& chars(string, length, ?cs);
@*/
struct string_constant {
    unsigned short length;
    char *string;
};

/*@
    predicate int_constant(struct int_constant *c, int value) =
        malloc_block_int_constant(c)
            &*& c->value |-> value;
@*/
struct int_constant {
    int value;
};

/*@
    predicate class_constant(struct class_constant *c, unsigned short name_index) =
        malloc_block_class_constant(c)
            &*& c->name_index |-> name_index;
@*/
struct class_constant {
    unsigned short name_index;
};

/*@
    predicate methodref_constant(struct methodref_constant *c, unsigned short class_index, unsigned short nat_index) =
        malloc_block_methodref_constant(c)
            &*& c->class_index |-> class_index
            &*& c->name_and_type_index |-> nat_index;
@*/
struct methodref_constant {
    unsigned short class_index;
    unsigned short name_and_type_index;
};

/*@
    predicate nat_constant(struct name_and_type_constant *c, unsigned short name_index, unsigned short descriptor_index) =
        malloc_block_name_and_type_constant(c)
            &*& c->name_index |-> name_index
            &*& c->descriptor_index |-> descriptor_index;
@*/
struct name_and_type_constant {
    unsigned short name_index;
    unsigned short descriptor_index;
};

/*@
    lemma_auto(reverse(xs)) void reverse_length<t>(list<t> xs);
        requires true;
        ensures length(reverse(xs)) == length(xs);
@*/
struct constant *constants_reverse(struct constant *c)
//@ requires constants(c, ?values);
//@ ensures constants(result, reverse<void *>(values)) &*& length(values) == length(reverse(values));
{
    struct constant *res = 0;
    struct constant *curr = c;
    //@ close constants(res, nil<void *>);
    //@ append_nil<void *>(reverse<void *>(values));
    while(curr != 0)
        /*@
            invariant constants(res, ?res_values)
                &*& constants(curr, ?curr_values)
                &*& reverse<void *>(values) == append<void *>(reverse<void *>(curr_values), res_values);
        @*/
    {
        //@ open constants(curr, curr_values);
        struct constant *tmp = curr->next;
        //@ assert constants(tmp, ?tmp_values);
        curr->next = res;
        res = curr;
        curr = tmp;
        //@ close constants(res, cons<void *>(head(curr_values), res_values));
        //@ append_assoc<void *>(reverse<void *>(tmp_values), cons<void *>(head(curr_values), nil<void *>), res_values);
    }
    //@ open constants(curr, _);
    return res;
}

void *constants_clone_info(struct constant *c, int expected_tag, int index)
//@ requires constants(c, ?values) &*& 1 <= index &*& index < length(values);
//@ ensures constants(c, values) &*& const_info(result, expected_tag);
{
    //@ open constants(c, values);
    if(index == 1) {
        void *res;

        if(c->tag != expected_tag) {
            error("ERROR: bad tag");
        }

        //@ open const_info(?inf, ?tag);
        switch(c->tag) {
        case STRING:
            char *string;
            struct string_constant *info = c->info;
            //@ open string_constant(info, ?length, ?str);
            struct string_constant *sc = malloc(sizeof(struct string_constant));
            if(sc == 0) {
                error("ERROR: insufficient memory");
            }
            sc->length = info->length;
            string = malloc(info->length);
            if(string == 0) {
                error("ERROR: insufficient memory");
            }
            memcpy(string, info->string, info->length);
            sc->string = string;
            //@ close string_constant(sc, length, string);
            //@ close string_constant(info, length, str);
            res = sc;
            break;
        case INT:
            struct int_constant *info = c->info;
            //@ open int_constant(info, ?value);
            struct int_constant *ic = malloc(sizeof(struct int_constant));
            if(ic == 0) {
                error("ERROR: insufficient memory");
            }
            ic->value = info->value;
            //@ close int_constant(ic, value);
            //@ close int_constant(info, value);
            res = ic;
            break;
        case CLASS:
            struct class_constant *info = c->info;
            //@ open class_constant(info, ?name_index);
            struct class_constant *cc = malloc(sizeof(struct class_constant));
            if(cc == 0) {
                error("ERROR: insufficient memory");
            }
            cc->name_index = info->name_index;
            //@ close class_constant(cc, name_index);
            //@ close class_constant(info, name_index);
            res = cc;
            break;
        case METHODREF:
            struct methodref_constant *info = c->info;
            //@ open methodref_constant(info, ?class_index, ?nat_index);
            struct methodref_constant *mrc = malloc(sizeof(struct methodref_constant));
            if(mrc == 0) {
                error("ERROR: insufficient memory");
            }
            mrc->class_index = info->class_index;
            mrc->name_and_type_index = info->name_and_type_index;
            //@ close methodref_constant(mrc, class_index, nat_index);
            //@ close methodref_constant(info, class_index, nat_index);
            res = mrc;
            break;
        case NAME_AND_TYPE:
            struct name_and_type_constant *info = c->info;
            //@ open nat_constant(info, ?name_index, ?descriptor_index);
            struct name_and_type_constant *ntc = malloc(sizeof(struct name_and_type_constant));
            if(ntc == 0) {
                error("ERROR: insufficient memory");
            }
            ntc->name_index = info->name_index;
            ntc->descriptor_index = info->descriptor_index;
            //@ close nat_constant(ntc, name_index, descriptor_index);
            //@ close nat_constant(info, name_index, descriptor_index);
            res = ntc;
            break;
        default:
            error("ERROR: bad label");
        }
        //@ close const_info(res, tag);
        //@ close const_info(inf, tag);
        //@ close constants(c, values);
        return res;
    } else {
        return constants_clone_info(c->next, expected_tag, index - 1);
        //@ close constants(c, values);
    }
}

void *constants_clone_info_checked(struct constant *c, int expected_tag, int index, int constant_count)
//@ requires constants(c, ?values) &*& 0 < index &*& index < length(values);
//@ ensures constants(c, values) &*& const_info(result, expected_tag);
{
    if(index < 1 || index >= constant_count)
        error("ERROR: bad index");
    return constants_clone_info(c, expected_tag, index);
}

/*@
    predicate method(struct method *method, char *name, int name_length, int name_index, int max_locals, int max_stack, char *code, int code_length, struct method* next) =
        malloc_block_method(method)
            &*& method->name |-> name
            &*& method->name_length |-> name_length
            &*& method->name_index |-> name_index
            &*& method->max_locals |-> max_locals
            &*& method->max_stack |-> max_stack
            &*& method->code |-> code
            &*& method->code_length |-> code_length
            &*& method->next |-> next;
    predicate methods(struct method *method, int count) =
        method == 0 ?
            count == 0 :
                method(method, ?name, ?name_length, ?name_index, ?max_locals, ?max_stack, ?code, ?code_length, ?next)
                    &*& methods(next, count - 1);
@*/
struct method {
    char *name;
    int name_length;
    int name_index;
    int max_locals;
    int max_stack;
    char *code;
    int code_length;
    struct method *next;
};

/*@
    predicate_family method_predicate_data(void *p)(void *data);
@*/
typedef bool method_predicate(struct method *method, void *data);
//@ requires method_predicate_data(this)(data);
//@ ensures method_predicate_data(this)(data);

// bool has_name(struct method* method, void* data) //@ : method_predicate
//     //@ requires method_predicate_data(has_name)(name_index) &*& method(method, ?m_name, ?m_name_length, ?m_name_index, ?m_max_locals, ?m_max_stack, ?m_code, ?m_code_length, ?m_next);
//     //@ ensures method_predicate_data(has_name)(name_index) &*& method(method, m_name, m_name_length, m_name_index, m_max_locals, m_max_stack, m_code, m_code_length, m_next);
// {
//     char* string = (char*) data;
//     int string_length = strlen((char*)string);
//     bool res;
//     if(method->name_length != string_length) {
//         res = false;
//     } else {
//         int memcmpres = memcmp(method->name, string, method->name_length);
//         res = memcmpres == 0;
//     }
//     return res;
// }


// /*@
//     predicate_family_instance method_predicate_data(has_name_index)(void *data) =
//         method_name_index(data, _);
// @*/
// bool has_name_index(struct method *method, void *name_index) //@ : method_predicate
//     //@ requires method(method, ?m_name, ?m_name_length, ?m_name_index, ?m_max_locals, ?m_max_stack, ?m_code, ?m_code_length, ?m_next) &*& method_predicate_data(has_name_index)(name_index);
//     //@ ensures method(method, m_name, m_name_length, m_name_index, m_max_locals, m_max_stack, m_code, m_code_length, m_next) &*& method_predicate_data(has_name_index)(name_index) &*& result == (m_name_index == *(int *)name_index);
// {
//     //@ open method(method, m_name, m_name_length, m_name_index, m_max_locals, m_max_stack, m_code, m_code_length, m_next);
//     return method->name_index == *(int *)name_index;
//     //@ close method(method, m_name, m_name_length, m_name_index, m_max_locals, m_max_stack, m_code, m_code_length, m_next);
// }

// void get_method_info(struct method* method, int count, int* max_locals, int* max_stack, char** code, int* code_length, method_predicate* p, void* data)
// {
//     if(count == 0) {
//         error("ERROR: no such method");
//     } else {
//         bool found = p(method, data);
//         if(found) {
//             char* my_code = malloc(method->code_length);
//             if(my_code == 0) {
//                 error("ERROR: insufficient memory");
//             }
//             *max_locals = method->max_locals;
//             *max_stack = method->max_stack;
//             memcpy(my_code, method->code, method->code_length);
//             *code = my_code;
//             *code_length = method->code_length;
//         } else {
//             get_method_info(method->next, count - 1, max_locals, max_stack, code, code_length, p, data);
//         }
//     }
// }


//             FIXME: removed from class_file_with_constants
//             &*& constant_count == length(constant_values)
/*@
    predicate empty_class_file(struct class_file *class_file) =
        malloc_block_class_file(class_file)
            &*& class_file->constant_count |-> ?constant_count
            &*& class_file->constants |-> ?constants
            &*& class_file->field_count |-> ?field_count
            &*& class_file->method_count |-> ?method_count
            &*& class_file->methods |-> ?methods;

    predicate class_file_with_constants(struct class_file *class_file) = 
        malloc_block_class_file(class_file)
            &*& class_file->constant_count |-> ?constant_count
            &*& class_file->constants |-> ?constants
            &*& constants(constants, ?constant_values)
            &*& constant_count == length(constant_values) + 1
            &*& class_file->field_count |-> ?field_count
            &*& class_file->method_count |-> ?method_count
            &*& class_file->methods |-> ?methods;

    predicate class_file_with_methods(struct class_file *class_file) = 
        malloc_block_class_file(class_file)
            &*& class_file->constant_count |-> ?constant_count
            &*& class_file->constants |-> ?constants
            &*& constants(constants, ?values)
            &*& class_file->field_count |-> ?field_count
            &*& class_file->method_count |-> ?method_count
            &*& class_file->methods |-> ?methods
            &*& methods(methods, method_count);
@*/
struct class_file {
    int constant_count;
    struct constant *constants;
    int field_count;
    int method_count;
    struct method *methods;
};

void parse_constant_pool(struct chars_reader *reader, struct class_file *class_file)
//@ requires chars_reader(reader,?buffer,?size,?f) &*& empty_class_file(class_file);
//@ ensures chars_reader(reader,buffer,size,f) &*& class_file_with_constants(class_file);
{
    struct constant *constants;
    int i;
    unsigned short constant_count = 0;
    constant_count = reader_next_uint16(reader);
    if(constant_count < (unsigned short) 1)
        error("ERROR: constant count must be at least one");
    constants = 0;
    //@ close constants(0,nil<void*>);

    for(i = 1; i < constant_count; i++)
    	//@ invariant chars_reader(reader,buffer,size,f) &*& 1<=i &*& i<= constant_count &*&  constants(constants, ?values) &*& length(values) == i-1;
        
    {

        unsigned char tag;

        struct constant *constant = malloc(sizeof(struct constant));
        if(constant == 0) {
            error("ERROR: insufficient memory");
        }
        tag = reader_next_uint8(reader);
        constant->tag = tag;
        switch((int) tag) {
        case STRING:
        {
            unsigned short length;
            char *string;

            struct string_constant *string_constant = malloc(sizeof(struct string_constant));
            if(string_constant == 0) {
                error("ERROR: insufficient memory");
            }
            length = reader_next_uint16(reader);
            string_constant->length = length;
            string = reader_next_chars(reader, length);

            string_constant->string = string;
            constant->info = string_constant;
            //@ close string_constant(string_constant, length, string);
            break;
        }
        case INT:
        {
            int value;
            struct int_constant *int_constant = malloc(sizeof(struct int_constant));
            if(int_constant == 0) {
                error("ERROR: insufficient memory");
            }
            value = reader_next_int32(reader);
            int_constant->value = value;
            constant->info = int_constant;
            //@ close int_constant(int_constant, value);
            break;
        }
        case CLASS:
        {
            unsigned short name_index;
            struct class_constant *class_constant = malloc(sizeof(struct class_constant));
            if(class_constant == 0) {
                error("ERROR: insufficient memory");
            }
            name_index = reader_next_uint16(reader);
            class_constant->name_index = name_index;
            if(name_index < 1 || name_index >= constant_count) {
                error("ERROR: bad index");
            }
            constant->info = class_constant;
            //@ close class_constant(class_constant, name_index);
            break;
        }
        case METHODREF:
        {
            unsigned short class_index;
            unsigned short name_and_type_index;
            struct methodref_constant *methodref_constant = malloc(sizeof(struct methodref_constant));
            if(methodref_constant == 0) {
                error("ERROR: insufficient memory");
            }
            class_index = reader_next_uint16(reader);
            methodref_constant->class_index = class_index;
            if(class_index < 1 ||  class_index >= constant_count) {
                error("ERROR: bad index");
            }
            name_and_type_index = reader_next_uint16(reader);
            if(name_and_type_index < 1 ||  name_and_type_index >= constant_count) {
                error("ERROR: bad index");
            }
            methodref_constant->name_and_type_index = name_and_type_index;
            constant->info = methodref_constant;
            //@ close methodref_constant(methodref_constant, class_index, name_and_type_index);
            break;
        }
        case NAME_AND_TYPE:
        {
            unsigned short name_index;
            unsigned short descriptor_index;
            struct name_and_type_constant *name_and_type_constant = malloc(sizeof(struct name_and_type_constant));
            if(name_and_type_constant == 0) {
                error("ERROR: insufficient memory");
            }
            name_index = reader_next_uint16(reader);
            if(name_index < 1 ||  name_index >= constant_count) {
                error("ERROR: bad index");
            }
            name_and_type_constant->name_index = name_index;
            descriptor_index = reader_next_uint16(reader);
            if(descriptor_index < 1 ||  descriptor_index >= constant_count) {
                error("ERROR: bad index");
            }
            name_and_type_constant->descriptor_index = descriptor_index;
            constant->info = name_and_type_constant;
            //@ close nat_constant(name_and_type_constant, name_index, descriptor_index);
            break;
        }
        default:
            error("Unsupported constant pool tag");
        }
        constant->next = constants;
        constants = constant;
        //@ close const_info(constant->info,tag);
        //@ close constants(constants,cons<void*>(constant,values));
    }

    //@ open empty_class_file(class_file);
    constants = constants_reverse(constants);
    class_file->constant_count = constant_count;
    class_file->constants = constants;
    //@ close class_file_with_constants(class_file);
}

 int parse_attributes(struct chars_reader* reader)
     //@ requires chars_reader(reader, ?buffer, ?size, ?f);
     //@ ensures chars_reader(reader, buffer, size, f);
 {
     int i;
     unsigned short attributes_count = reader_next_uint16(reader);
     for(i = 0; i < attributes_count; i++)
     //@ invariant chars_reader(reader, buffer, size, f);
     {
         unsigned short attribute_name_index = reader_next_uint16(reader);
         unsigned int length = reader_next_uint32(reader);
         if(length > (unsigned int) INT_MAX) {
             error("ERROR: unsupported attribute length");
         }
         reader_skip(reader, (int) length);
     }
     return attributes_count;
 }

 void parse_fields(struct chars_reader* reader, struct class_file* class_file)
 //@ requires chars_reader(reader,?buffer,?size,?f) &*& class_file_with_constants(class_file);
 //@ ensures chars_reader(reader,buffer,size,f) &*& class_file_with_constants(class_file);

 {
     int i;
     unsigned short field_count = reader_next_uint16(reader);
     //@ open class_file_with_constants(class_file);
     class_file->field_count = field_count;
     for(i = 0; i < field_count; i++)
     //@ invariant chars_reader(reader,buffer,size,f) &*& i >= 0 &*& i <= field_count;
     {
         unsigned short access_flags = reader_next_uint16(reader);
         unsigned short name_index = reader_next_uint16(reader);
         unsigned short descriptor_index = reader_next_uint16(reader);
         int attributes_count = parse_attributes(reader);
     }
     //@ close class_file_with_constants(class_file);
 }

 void parse_methods(struct chars_reader* reader, struct class_file* class_file)
 //@ requires chars_reader(reader,?buffer,?size,?f) &*& class_file_with_constants(class_file);
 //@ ensures chars_reader(reader,buffer,size,f) &*& class_file_with_methods(class_file);
 {
     int i;
     unsigned short method_count = reader_next_uint16(reader);
     //@open class_file_with_constants(class_file);
     class_file->method_count = method_count;
     class_file->methods = 0;
     //@close class_file_with_constants(class_file);
     for(i = 0; i < method_count; i++)
     //@ invariant i>= 0 &*& i<= method_count &*& class_file_with_constants(class_file) &*& chars_reader(reader,buffer,size,f);
     {
         unsigned short access_flags, name_index, descriptor_index, max_stack, max_locals;
         int pre_attrib_offset, offset, code_length, code_offset, attributes_count;
         unsigned int ucode_length;
         char* code;
         struct string_constant* name_constant;
         struct method* method = malloc(sizeof(struct method));
         if(method == 0) error("Insufficient memory");
	//@open class_file_with_constants(class_file);
         method->next = class_file->methods;
         access_flags = reader_next_uint16(reader);
         name_index = reader_next_uint16(reader);
         method->name_index= name_index;
         if(name_index < 1 ||  name_index >= class_file->constant_count) {
             error("ERROR: bad index");
         }
   
   	//@ open constants(_,?values);
         //@ assert name_index >= 1 &*& name_index < length(values);
         name_constant = constants_clone_info(class_file->constants, STRING, name_index);
         method->name = name_constant->string;
         method->name_length = name_constant->length;
         free(name_constant);
         descriptor_index = reader_next_uint16(reader);
         pre_attrib_offset = reader_get_offset(reader);
         reader_skip(reader, 8);
         max_stack = reader_next_uint16(reader);
         method->max_stack = max_stack;
         max_locals = reader_next_uint16(reader);
         method->max_locals = max_locals;
         offset = reader_get_offset(reader);
         ucode_length = reader_next_uint32(reader);
         if(ucode_length > (unsigned int) INT_MAX) {
             error("ERROR: code length not supported yet");
         }
         code_length = (int) ucode_length;
         method->code_length = code_length;
         code_offset = reader_get_offset(reader);
         code = reader_next_chars(reader, code_length);
         method->code = code;
         reader_set_offset(reader, pre_attrib_offset);
         attributes_count = parse_attributes(reader);
         class_file->methods = method;
     }
 }

struct class_file* parse_class_file(struct chars_reader* reader)
    //@ requires chars_reader(reader, ?buffer, ?size, ?f);
    //@ ensures chars_reader(reader, buffer, size, f) &*& class_file_with_constants(result);
{
    unsigned short minor_version, major_version, access_flags, this_class, super_class, interfaces_count;
    unsigned int magic;
    struct class_file* class_file = malloc(sizeof(struct class_file));
    int offset = 0;
    int i, attributes_count;
    if(class_file == 0)
        error("ERROR: insufficient memory");
    //@ close empty_class_file(class_file);
    magic = reader_next_uint32(reader);
    minor_version = reader_next_uint16(reader);
    major_version = reader_next_uint16(reader);
    parse_constant_pool(reader, class_file);
    access_flags = reader_next_uint16(reader);
    this_class = reader_next_uint16(reader);
    super_class = reader_next_uint16(reader);
    interfaces_count = reader_next_uint16(reader);
    for(i = 0; i < interfaces_count; i++)
    	//@ invariant chars_reader(reader,buffer,size,f) &*& i >= 0 &*& i <= interfaces_count ;
    {
        unsigned short interfaces_index = reader_next_uint16(reader);
    }
    parse_fields(reader, class_file);
    parse_methods(reader, class_file);
    //attributes_count = parse_attributes(reader);
    return class_file;
}

//              FIXME: Removed from predicate node
//              &*& (thread != 0 ? thread(thread, ?thread_run, ?data, ?info) : thread == 0)
/*@
    predicate node(struct node *node, int value, struct thread *thread, struct node *next) =
            malloc_block_node(node)
                &*& node->value |-> value
                &*& node->thread |-> thread
                &*& node->next |-> next;
    predicate nodes(struct node *node, list<int> values) =
        values == nil<int> ?
            node == 0 :
                node(node, ?value, ?thread, ?next)
                    &*& nodes(next, ?tail)
                    &*& values == cons<int>(value, tail);
@*/
struct node {
    int value;
    struct thread *thread;
    struct node *next;
};

int node_get_value(struct node *n)
//@ requires node(n, ?value, ?thread, ?next);
//@ ensures node(n, value, 0, next) &*& result == value;
{
    //@ open node(n, value, thread, next);
    // if(n->thread != 0) {
    //     thread_join(n->thread);
    // }
    n->thread = 0;
    return n->value;
    //@ close node(n, value, 0, next);
}

void node_set_value(struct node *n, int value)
//@ requires node(n, _, ?thread, ?next);
//@ ensures node(n, value, 0, next);
{
    //@ open node(n, _, thread, next);
    // if(n->thread != 0) {
    //     thread_join(n->thread);
    // }
    n->thread = 0;
    n->value = value;
    //@ close node(n, value, 0, next);
}

/*@
    predicate lseg(struct node *first, struct node *last, list<int> values) =
        values == nil<int> ?
            first == last :
                node(first, ?value, ?thread, ?next)
                    &*& lseg(next, last, ?tail)
                    &*& values == cons<int>(value, tail);

    lemma void nodes_to_lseg_lemma(struct node *first)
        requires nodes(first, ?values);
        ensures lseg(first, 0, values);
    {
        open nodes(first, values);
        if (values != nil<int>) {
            open node(first, ?value, ?thread, ?next);
            nodes_to_lseg_lemma(first->next);
            close node(first, value, thread, next);
        }
        close lseg(first, 0, values);
    }

    lemma void lseg_to_nodes_lemma(struct node *first)
        requires lseg(first, 0, ?values);
        ensures nodes(first, values);
    {
        open lseg(first, 0, values);
        if (values != nil<int>) {
            open node(first, ?value, ?thread, ?next);
            lseg_to_nodes_lemma(first->next);
            close node(first, value, thread, next);
        }
        close nodes(first, values);
    }

    lemma void lseg_append_lemma(struct node *first)
        requires lseg(first, ?last, ?first_values) &*& lseg(last, 0, ?last_values);
        ensures lseg(first, 0, append<int>(first_values, last_values));
    {
        open lseg(first, last, first_values);
        if (first_values != nil<int>) {
            open node(first, ?value, ?thread, ?next);
            lseg_append_lemma(first->next);
            close node(first, value, thread, next);
            close lseg(first, 0, append<int>(first_values, last_values));
        }
    }
@*/
struct node *node_at(struct node *n, int index)
//@ requires nodes(n, ?values) &*& index >= 0 &*& index < length(values);
//@ ensures lseg(result, 0, drop<int>(index, values)) &*& lseg(n, result, take<int>(index, values));
{
    if(index == 0) {
        //@ nodes_to_lseg_lemma(n);
        //@ close lseg(n, n, nil<int>);
        return n;
    } else {
        //@ open nodes(n, values);
        //@ open node(n, ?value, ?thread, ?next);
        struct node *res = node_at(n->next, index - 1);
        //@ close node(n, value, thread, next);
        //@ close lseg(n, res, take<int>(index, values));
        return res;
    }
}

/*@
    predicate stack(struct stack *stack, list<int> values) =
        malloc_block_stack(stack)
            &*& stack->top |-> ?top
            &*& stack->count |-> ?count
            &*& count == length(values)
            &*& nodes(top, values);
@*/
struct stack {
    struct node *top;
    int count;
};

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, nil<int>);
{
    int i;
    struct stack *s = malloc(sizeof(struct stack));
    if(s == 0) {
        error("ERROR: insufficient memory");
    }
    s->top = 0;
    s->count = 0;
    //@ close nodes(0, nil<int>);
    //@ close stack(s, nil<int>);
    return s;
}

void stack_dispose(struct stack *s)
//@ requires stack(s, nil<int>);
//@ ensures true;
{
    //@ open stack(s, nil<int>);
    //@ open nodes(_, _);
    free(s);
}

void stack_push(struct stack *s, int value)
//@ requires stack(s, ?values);
//@ ensures stack(s, cons<int>(value, values));
{
    //@ open stack(s, values);
    struct node *new_node = malloc(sizeof(struct node));
    if(new_node == 0) {
        error("ERROR: insufficient memory");
    }
    new_node->next = s->top;
    new_node->value = value;
    new_node->thread = 0;
    //@ close node(new_node, value, 0, s->top);
    s->top = new_node;
    if(s->count == INT_MAX) {
        error("ERROR: stack overflow");
    }
    s->count += 1;
    //@ close nodes(new_node, cons<int>(value, values));
    //@ close stack(s, cons<int>(value, values));
}

int stack_pop(struct stack *s)
//@ requires stack(s, ?values) &*& length(values) != 0;
//@ ensures stack(s, tail(values)) &*& result == head(values);
{
    //@ open stack(s, values);
    struct node *n;
    int res;
    if(s->count == 0) {
        error("ERROR: stack underflow");
    }
    n = s->top;
    //@ open nodes(n, values);
    //@ open node(n, ?value, ?thread, ?next);
    s->top = s->top->next;
    //@ close node(n, value, thread, next);
    s->count--;
    res = node_get_value(n);
    //@ open node(n, value, 0, next);
    free(n);
    //@ close stack(s, tail(values));
    return res;
}

int stack_count(struct stack *s)
//@ requires stack(s, ?values);
//@ ensures stack(s, values) &*& result == length(values);
{
    //@ open stack(s, values);
    return s->count;
    //@ close stack(s, values);
}

// int stack_get(struct stack* s, int index_from_bottom)
//     //@ requires stack(s, ?values) &*& index_from_bottom >= 0 &*& index_from_bottom < length(values);
//     //@ ensures stack(s, values) &*& result == nth(length(values) - index_from_bottom, values);
// {
//     struct node* n;
//     //@ open stack(s, values);
//     if(s->count <= index_from_bottom) {
//         error("ERROR: bad stack index");
//     }
//     n = node_at(s->top, s->count - index_from_bottom - 1);
//     //@ lseg_to_nodes_lemma(n);
//     //@ open nodes(n, ?values2);
//     return node_get_value(n);
//     //@ close nodes(n, values2);
//     //@ close stack(s, values);
// }

// void stack_set(struct stack* s, int index_from_bottom, int value)
//     //@ requires stack(s, ?values) &*& index_from_bottom >= 0 &*& index_from_bottom < length(values);
//     //@ ensures stack(s, values) &*& value == nth(length(values) - index_from_bottom, values);
// {
//     struct node* n;
//     //@ open stack(s, values);
//     if(s->count <= index_from_bottom) {
//         error("ERROR: bad stack index");
//     }
//     n = node_at(s->top, s->count - index_from_bottom - 1);
//     //@ close stack(s, values);
//     node_set_value(n, value);
// }

// void execute_code(struct class_file* class_file, struct stack* s, char* code, int code_length, int max_locals, int args_size);

// TODO: check declaration, not sure whether right...
/*@
    predicate new_thread_info(struct new_thread_info *new_thread_info, struct class_file *class_file, struct stack *stack, char *code, int code_length, int max_locals, int args_size, struct node *node) =
        malloc_block_new_thread_info(new_thread_info)
            &*& new_thread_info->class_file |-> class_file
            &*& new_thread_info->stack |-> stack
            &*& stack(stack, ?stack_count)
            &*& new_thread_info->code |-> code
            &*& new_thread_info->code_length |-> code_length
            &*& new_thread_info->max_locals |-> max_locals
            &*& new_thread_info->args_size |-> args_size
            &*& new_thread_info->node |-> node
            &*& nodes(node, ?values);
@*/
struct new_thread_info {
    struct class_file *class_file;
    struct stack *stack;
    char *code;
    int code_length;
    int max_locals;
    int args_size;
    struct node *node;
};

// void execute_thread(struct new_thread_info* info)
// {
//     int return_value;
//     execute_code(info->class_file, info->stack, info->code, info->code_length, info->max_locals, info->args_size);
//     return_value = stack_pop(info->stack);
//     info->node->value = return_value;
//     stack_dispose(info->stack);
//     free(info);
// }
//
//
// void stack_start_thread(struct stack* s, int index_from_bottom, struct new_thread_info* info)
// {
//     struct thread* thread;
//     struct node* n;
//     if(s->count <= index_from_bottom) {
//         error("ERROR: bad stack index");
//     }
//     n = node_at(s->top, s->count - index_from_bottom - 1);
//     node_get_value(n);
//     info->node = n;
//     thread = thread_start_joinable(execute_thread, info);
//     n->thread = thread;
// }

// bool chars_equals(char* c, int clength, char* string)
//     //@ requires chars(c, clength, ?cs) &*& string(string, ?string_cs);
//     //@ ensures chars(c, clength, cs) &*& string(string, string_cs) &*& result == (cs == string_cs);
// {
//     int res;
//     int string_length = strlen(string);
//     if(string_length != clength) return false;
//     //@ string_to_chars(string);
//     res = memcmp(c, string, clength);
//     //@ chars_to_string(string);
//     return res == 0;
// }

// void parse_method_type(char* descriptor, int dlength, int* args_size)
// {
//     struct chars_reader* reader = create_chars_reader(descriptor, dlength);
//     char c = reader_next_int8(reader);
//     bool closingparen = false;
//     int arg_count = 0;
//     if(c != '(')
//         error("Expected (");
//     while(!closingparen)
//     {
//         c = reader_next_int8(reader);
//         switch(c) {
//         case 'I':
//             if(arg_count == INT_MAX) {
//                 error("ERROR: arithmetic overflow");
//             }
//             arg_count++;
//             break;
//         case ')':
//             closingparen = true;
//             break;
//         default:
//             error("Expected ) or I");
//         }
//     }
//     c = reader_next_int8(reader);
//     if( c != 'I')
//         error("Expected I");
//     *args_size = arg_count;
//     reader_dispose(reader);
// }
//
// bool chars_starts_with(char* c, int clength, char* string)
// {
//     int string_length = strlen(string);
//     if(string_length == 0) {
//         return true;
//     } else {
//         if(0 < clength && *c == *string) {
//             return chars_starts_with(c + 1, clength - 1, string + 1);
//         } else {
//             return false;
//         }
//     }
// }
//
// void execute_code(struct class_file* class_file, struct stack* s, char* code, int code_length, int max_locals, int args_size)
// {
//     int i, preinstr_count;
//     int pre_stack_count = stack_count(s);
//     int locals_offset = pre_stack_count - args_size;
//     struct chars_reader* reader = create_chars_reader(code, code_length);
//     for(i = 0; i < max_locals; i++)
//     {
//         stack_push(s, 0);
//     }
//     preinstr_count = stack_count(s);
//     for(;;)
//     {
//         unsigned char opcode = reader_next_uint8(reader);
//         switch((int) opcode) {
//         case 0x00: // nop
//         {
//             break;
//         }
//         case 0x03: // iconst_0
//         {
//             stack_push(s, 0);
//             break;
//         }
//         case 0x04: // iconst_1
//         {
//             stack_push(s, 1);
//             break;
//         }
//         case 0x05: // iconst_2
//         {
//             stack_push(s, 2);
//             break;
//         }
//         case 0x06: // iconst_3
//         {
//             stack_push(s, 3);
//             break;
//         }
//         case 0x07: // iconst_4
//         {
//             stack_push(s, 4);
//             break;
//         }
//         case 0x08: // iconst_5
//         {
//             stack_push(s, 5);
//             break;
//         }
//         case 0x10: // bipush
//         {
//             unsigned char number = reader_next_uint8(reader);
//             stack_push(s, number);
//             break;
//         }
//         case 0x11: // sipush
//         {
//             unsigned short number = reader_next_uint16(reader);
//             stack_push(s, number);
//             break;
//         }
//         case 0x12: // ldc
//         {
//             unsigned char index = reader_next_uint8(reader);
//             struct int_constant* info = constants_clone_info_checked(class_file->constants, INT, index, class_file->constant_count);
//             stack_push(s, info->value);
//             free(info);
//             break;
//         }
//         case 0x15: // iload
//         {
//             int value;
//             unsigned char index = reader_next_uint8(reader);
//             if(index >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             value = stack_get(s, locals_offset + (int) index);
//             stack_push(s, value);
//             break;
//         }
//         case 0x1a: // iload_0
//         {
//             int value = stack_get(s, locals_offset + 0);
//             stack_push(s, value);
//             break;
//         }
//         case 0x1b: // iload_1
//         {
//             int value;
//             if(1 >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             value = stack_get(s, locals_offset + 1);
//             stack_push(s, value);
//             break;
//         }
//         case 0x1c: // iload_2
//         {
//             int value;
//             if(2 >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             value = stack_get(s, locals_offset + 2);
//             stack_push(s, value);
//             break;
//         }
//         case 0x1d: // iload_3
//         {
//             int value;
//             if(3 >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             value = stack_get(s, locals_offset + 3);
//             stack_push(s, value);
//             break;
//         }
//         case 0x36: // istore
//         {
//             int value = stack_pop(s);
//             unsigned char index = reader_next_uint8(reader);
//             if(index >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             stack_set(s, locals_offset + (int) index, value);
//             break;
//         }
//         case 0x3b: // istore_0
//         {
//             int value = stack_pop(s);
//             stack_set(s, locals_offset + 0, value);
//             break;
//         }
//         case 0x3c: // istore_1
//         {
//             int value = stack_pop(s);
//             if(1 >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             stack_set(s, locals_offset + 1, value);
//             break;
//         }
//         case 0x3d: // istore_2
//         {
//             int value = stack_pop(s);
//             if(2 >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             stack_set(s, locals_offset + 2, value);
//             break;
//         }
//         case 0x3e: // istore_3
//         {
//             int value = stack_pop(s);
//             if(3 >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             stack_set(s, locals_offset + 3, value);
//             break;
//         }
//         case 0x57: // pop
//         {
//             int value = stack_pop(s);
//             break;
//         }
//         case 0x60: // iadd
//         {
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             int res = add_truncating(value1, value2);
//             stack_push(s, res);
//             break;
//         }
//         case 0x64: // isub
//         {
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             int res = sub_truncating(value1, value2);
//             stack_push(s, res);
//             break;
//         }
//         case 0x68: // imul
//         {
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             int res = times_truncating(value1, value2);
//             stack_push(s, res);
//             break;
//         }
//         case 0x70: //irem
//         {
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             stack_push(s, value1 % value2);
//             break;
//         }
//         case 0x84: // iinc
//         {
//             unsigned char index = reader_next_uint8(reader);
//             char amount = reader_next_int8(reader);
//             int value;
//             if(index >= args_size + max_locals) {
//                 error("ERROR: illegal variable index");
//             }
//             value = stack_get(s, locals_offset + index);
//             if(0 <= value && 0 <= amount && INT_MAX - value < amount)
//                 error("Arithmetic overflow.");
//             else if(value < 0 && amount < 0 && INT_MIN - value > amount)
//                 error("Arithmetic overflow.");
//             else
//                 stack_set(s, locals_offset + index, value + amount);
//             break;
//         }
//         case 0x99: // ifeq
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value = stack_pop(s);
//             if(value == 0) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0x9a: // ifne
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value = stack_pop(s);
//             if(value != 0) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0x9e: // ifle
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value = stack_pop(s);
//             if(value <= 0) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0xa0: // if_icmpne
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             if(value1 != value2) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0xa1: // if_icmplt
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             if(value1 < value2) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0xa2: // if_icmpge
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             if(value1 >= value2) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0xa4: // if_icmple
//         {
//             short branchoffset = reader_next_int16(reader);
//             int value2 = stack_pop(s);
//             int value1 = stack_pop(s);
//             if(value1 <= value2) {
//                 reader_skip(reader, branchoffset - 3);
//             }
//             break;
//         }
//         case 0xa7: // goto
//         {
//             short branchoffset = reader_next_int16(reader);
//             reader_skip(reader, branchoffset - 3);
//             break;
//         }
//         case 0xac: // ireturn
//         {
//             int returnvalue = stack_pop(s);
//             int new_count = stack_count(s);
//             int k;
//             if(new_count != pre_stack_count + max_locals) {
//                 error("ERROR: stack corrupt");
//             }
//             for(k = 0; k < max_locals + args_size; k++)
//             {
//                 stack_pop(s);
//             }
//             stack_push(s, returnvalue);
//             reader_dispose(reader);
//             free(code);
//             return;
//         }
//         case 0xb8: // invokestatic
//         {
//             bool execute_async;
//             int callee_args_size, callee_max_locals, callee_code_length, callee_max_stack, callee_name_index;
//             char* callee_code;
//             short method_reference_index = reader_next_int16(reader);
//             struct methodref_constant* methodref = constants_clone_info_checked(class_file->constants, METHODREF, method_reference_index, class_file->constant_count);
//             struct class_constant* class = constants_clone_info(class_file->constants, CLASS, methodref->class_index);
//             struct string_constant* class_name = constants_clone_info(class_file->constants, STRING, class->name_index);
//             struct name_and_type_constant* name_and_type = constants_clone_info(class_file->constants, NAME_AND_TYPE, methodref->name_and_type_index);
//             struct string_constant* method_name = constants_clone_info(class_file->constants, STRING, name_and_type->name_index);
//             struct string_constant* descriptor = constants_clone_info(class_file->constants, STRING, name_and_type->descriptor_index);
//             if(chars_equals(class_name->string, class_name->length, "BuiltIn")) {
//                 if(chars_equals(method_name->string, method_name->length, "printInt")) {
//                     int value = stack_pop(s);
//                     printf("%i", value);
//                 } else if(chars_equals(method_name->string, method_name->length, "newLine")) {
//                     puts("");
//                 } else if(chars_equals(method_name->string, method_name->length, "readInt")) {
//                     int value;
//                     int scan_result = scanf("%i", &value);
//                     if(scan_result != 1) {
//                         error("Error: you did not enter a number");
//                     }
//                     stack_push(s, value);
//                 } else if(chars_equals(method_name->string, method_name->length, "assertEq")) {
//                     int value1 = stack_pop(s);
//                     int value2 = stack_pop(s);
//                     if(value1 != value2) {
//                         error("Assertion violation");
//                     }
//                 } else {
//                     error("No such builtin method");
//                 }
//                 goto end;
//             }
//             execute_async = chars_starts_with(method_name->string, method_name->length, "async_");
//             parse_method_type(descriptor->string, descriptor->length, &callee_args_size);
//             callee_name_index = name_and_type->name_index;
//             get_method_info(class_file->methods, class_file->method_count, &callee_max_locals, &callee_max_stack, &callee_code, &callee_code_length, has_name_index, &callee_name_index);
//             if(! execute_async) {
//                 int current_stack_size = stack_count(s);
//                 if(callee_args_size > current_stack_size)
//                     error("ERROR: insufficient arguments");
//                 execute_code(class_file, s, callee_code, callee_code_length, callee_max_locals, callee_args_size);
//             } else {
//                 int current_offset, var_offset;
//                 struct new_thread_info* info;
//                 unsigned char nextopcode;
//                 struct stack* new_stack = create_stack();
//                 int current_stack_size = stack_count(s);
//                 int nb_args = callee_args_size;
//                 if(nb_args > current_stack_size)
//                     error("ERROR: insufficient arguments");
//                 for(i = 0; i < nb_args; i++)
//                 {
//
//                     int val = stack_get(s, current_stack_size - nb_args + i );
//                     stack_push(new_stack, val);
//                 }
//                 for(i = 0; i < nb_args; i++)
//                 {
//                     stack_pop(s);
//                 }
//                 info = malloc(sizeof(struct new_thread_info));
//                 if(info == 0)
//                     error("Insufficient memory");
//                 info->class_file = class_file;
//                 info->stack = new_stack;
//                 info->code = callee_code;
//                 info->code_length = callee_code_length;
//                 info->max_locals = callee_max_locals;
//                 info->args_size = callee_args_size;
//                 info->node = 0;
//                 current_offset = reader_get_offset(reader);
//                 nextopcode = reader_get_uint8_at(reader, current_offset);
//                 switch((int) nextopcode) {
//                 case 0x36: // istore
//                 {
//                     unsigned char index;
//                     reader_next_uint8(reader);
//                     index = reader_next_uint8(reader);
//                     if(index >= args_size + max_locals) {
//                         error("ERROR: illegal variable index");
//                     }
//                     var_offset = locals_offset + index;
//                     break;
//                 }
//                 case 0x3b: // istore_0
//                 {
//                     var_offset =  locals_offset +  0;
//                     reader_skip(reader, 1);
//                     break;
//                 }
//                 case 0x3c: // istore_1
//                 {
//                     if(1 >= args_size + max_locals) {
//                         error("ERROR: illegal variable index");
//                     }
//                     var_offset =  locals_offset + 1;
//                     reader_skip(reader, 1);
//                     break;
//                 }
//                 case 0x3d: // istore_2
//                 {
//                     if(2 >= args_size + max_locals) {
//                         error("ERROR: illegal variable index");
//                     }
//                     var_offset =  locals_offset + 2;
//                     reader_skip(reader, 1);
//                     break;
//                 }
//                 case 0x3e: // istore_3
//                 {
//                     if(3 >= args_size + max_locals) {
//                         error("ERROR: illegal variable index");
//                     }
//                     var_offset =  locals_offset + 3;
//                     reader_skip(reader, 1);
//                     break;
//                 }
//                 default:
//                 {
//                     int stack_size = stack_count(s);
//                     stack_push(s, 0);
//                     var_offset = stack_size;
//                 }
//                 }
//                 stack_start_thread(s, var_offset, info);
//             }
// end:
//             free(class);
//             free(method_name->string);
//             free(method_name);
//             free(class_name->string);
//             free(class_name);
//             free(name_and_type);
//             free(descriptor->string);
//             free(descriptor);
//             free(methodref);
//             break;
//         }
//         default:
//             //printf("%hhx", opcode);
//             error("\nUnsupported opcode");
//         }
//     }
// }
//
// int execute_class_file(struct class_file* class_file)
// {
//     int max_locals;
//     int max_stack;
//     char* code;
//     int code_length;
//     struct stack* s = create_stack();
//     char* main_method_name = "main";
//     int exit_value;
//     get_method_info(class_file->methods, class_file->method_count, &max_locals, &max_stack, &code, &code_length, has_name, main_method_name);
//     execute_code(class_file, s, code, code_length, max_locals, 0);
//     exit_value = stack_pop(s);
//     stack_dispose(s);
//     return exit_value;
// }
//
// int main(int argc, char** argv)
// {
//     char* buffer;
//     int exit_value;
//     int filesize;
//     struct chars_reader* reader;
//     struct class_file* class_file;
//     if(argc < 2)
//         error("Usage: tinyjava classfile");
//     reader = create_chars_reader_from_file(argv[1]);
//     class_file = parse_class_file(reader);
//     buffer = reader_get_buffer(reader);
//     reader_dispose(reader);
//     free(buffer);
//     exit_value = execute_class_file(class_file);
//     exit(exit_value);
// }
