#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include "bool.h"
#include "threading.h"
#include "chars_reader.h"
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
    inductive constant_list = empty_constant_list | constant_list_el(int tag, void *info, constant_list);

    fixpoint constant_list constant_list_append(constant_list first, constant_list last) { 
        switch (first) {
            case empty_constant_list: return last;
            case constant_list_el(tag, info, tail): return constant_list_el(tag, info, constant_list_append(tail, last)); 
        }
    }
    
    lemma void constant_list_append_nil_lemma(constant_list values) 
        requires true;
        ensures constant_list_append(values, empty_constant_list) == values;
    {
        switch (values) {
            case empty_constant_list:
            case constant_list_el(tag, info, tail):
                constant_list_append_nil_lemma(tail);
        }
    }

    lemma void constant_list_append_assoc_lemma(constant_list one, constant_list two, constant_list three) 
        requires true;
        ensures constant_list_append(constant_list_append(one, two), three) 
            == constant_list_append(one, constant_list_append(two, three));
    {
        switch (one) {
            case empty_constant_list:
            case constant_list_el(tag, info, tail):
                constant_list_append_assoc_lemma(tail, two, three);
        }
    }

    fixpoint constant_list constant_list_reverse(constant_list values) {
        switch (values) {
            case empty_constant_list: return empty_constant_list;
            case constant_list_el(tag, info, tail): return constant_list_append(constant_list_reverse(tail), constant_list_el(tag, info, empty_constant_list)); 
        }
    }

    predicate constant(struct constant *c, constant_list values, int count) = 
        c == 0 ? 
            values == empty_constant_list &*& count == 0 : 
                (   
                    malloc_block_constant(c) 
                        &*& c->tag |-> ?tag
                        &*& c->info |-> ?info
                        &*& constant_inf(info, tag)
                        &*& c->next |-> ?next 
                        &*& constant(next, ?next_values, count - 1)
                        &*& values == constant_list_el(tag, info, next_values)
                );
@*/
struct constant {
    int tag;
    void *info;
    struct constant *next;
};

/*@
    predicate constant_inf(void *info, int tag) = info != 0
        &*& (tag == 1 ? 
            string_constant(info, _, _) : 
                (tag == 3 ? int_constant(info, _) : 
                    (tag == 7 ? class_constant(info, _) :
                        (tag == 10 ? methodref_constant(info, _, _) :
                            nat_constant(info, _, _)))));
    predicate string_constant(struct string_constant *c, unsigned short length, char* string) = malloc_block_string_constant(c)
        &*& c->length |-> length
        &*& length >= 0
        &*& c->string |-> string
        &*& chars(string, length, _);
@*/
struct string_constant {
    unsigned short length;
    char *string;
};

/*@
    predicate int_constant(struct int_constant *c, int value) = malloc_block_int_constant(c)
        &*& c->value |-> value;
@*/
struct int_constant {
    int value;
};

/*@
    predicate class_constant(struct class_constant *c, unsigned short name_index) = malloc_block_class_constant(c)
        &*& c->name_index |-> name_index;
@*/
struct class_constant {
    unsigned short name_index;
};

/*@
    predicate methodref_constant(struct methodref_constant *c, unsigned short class_index, unsigned short nat_index) = malloc_block_methodref_constant(c)
        &*& c->class_index |-> class_index
        &*& c->name_and_type_index |-> nat_index;
@*/
struct methodref_constant {
    unsigned short class_index;
    unsigned short name_and_type_index;
};

/*@
    predicate nat_constant(struct name_and_type_constant *c, unsigned short name_index, unsigned short descriptor_index) = malloc_block_name_and_type_constant(c)
        &*& c->name_index |-> name_index
        &*& c->descriptor_index |-> descriptor_index;
@*/
struct name_and_type_constant {
    unsigned short name_index;
    unsigned short descriptor_index;
};

// struct constant *constants_reverse(struct constant *c)
//     //@ requires constant(c, ?values, ?count);
//     //@ ensures constant(result, constant_list_reverse(values), count);
// {
//     struct constant *res = 0;
//     //@ close constant(res, empty_constant_list, 0);
//     struct constant *curr = c;
//     //@ constant_list_append_nil_lemma(constant_list_reverse(values));
//     while(curr != 0)
//         /*@ 
//             invariant constant(res, ?res_val, ?res_count) 
//                 &*& constant(curr, ?curr_val, count - res_count) 
//                 &*& constant_list_reverse(values) 
//                     == constant_list_append(constant_list_reverse(curr_val), res_val);
//         @*/
//     {
//         //@ open constant(curr, curr_val, ?curr_count);
//         struct constant *tmp = curr->next;
//         //@ assert constant(tmp, ?tmp_val, curr_count - 1) &*& curr->tag |-> ?tag &*& curr->info |-> ?info;
//         curr->next = res;
//         res = curr;
//         curr = tmp;
//         //@ close constant(res, constant_list_el(tag, info, res_val), count - curr_count);
//         //@ constant_list_append_assoc_lemma(constant_list_reverse(tmp_val), constant_list_el(tag, info, empty_constant_list), res_val);
//     }
//     //@ open constant(curr, _, _);
//     return res;
// }

void *constants_clone_info(struct constant *c, int expected_tag, int index)
    //@ requires constant(c, constant_list_el(?tag, ?inf, ?tail), ?count) &*& 1 <= index &*& index < count;
    //@ ensures constant(c, constant_list_el(tag, inf, tail), count) &*& constant_inf(result, expected_tag);
{
    //@ open constant(c, constant_list_el(tag, inf, tail), count);
    if(index == 1) {
        void *res;

        if(c->tag != expected_tag) {
            error("ERROR: bad tag");
        }
        
        //@ open constant_inf(inf, tag);        
        switch(c->tag) {
            // FIXME: 
            // case STRING:
                // char *string;
                // struct string_constant *info = c->info;
                // //@ open string_constant(info, ?length, ?str);
                // struct string_constant *sc = malloc(sizeof(struct string_constant));
                // if(sc == 0) {
                //     error("ERROR: insufficient memory");
                // }
                // sc->length = info->length;
                // string = malloc(info->length);
                // if(string == 0) {
                //     error("ERROR: insufficient memory");
                // }
                // memcpy(string, info->string, info->length);
                // sc->string = string;
                // //@ close string_constant(sc, length, str);
                // //@ close string_constant(info, length, str);
                // res = sc;
                // break;
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
        //@ close constant_inf(res, tag);
        //@ close constant_inf(inf, tag);
        //@ close constant(c, constant_list_el(tag, inf, tail), count);
        return res;
    } else {
        //@ open constant(?next, ?next_values, count - 1);
        //@ close constant(next, next_values, count - 1);
        return constants_clone_info(c->next, expected_tag, index - 1);
        //@ close constant(c, constant_list_el(tag, inf, tail), count);
    }
}

void *constants_clone_info_checked(struct constant *c, int expected_tag, int index, int constant_count)
    //@ requires constant(c, constant_list_el(?tag, ?info, ?tail), constant_count);
    //@ ensures constant(c, constant_list_el(tag, info, tail), constant_count) &*& constant_inf(result, expected_tag);
{
    if(index < 1 || index >= constant_count)
        error("ERROR: bad index");
    return constants_clone_info(c, expected_tag, index);
}

/*@
    predicate method(struct method *m) = m == 0 ?
        false :
            malloc_block_method(m)
                &*& m->name |-> _
                &*& m->name_length |-> _
                &*& m->name_index |-> _
                &*& m->max_locals |-> _
                &*& m->code |-> _
                &*& m->code_length |-> _
                &*& m->next |-> _;
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

// //@ predicate_family method_predicate_data(void *p)(void *data)
// typedef bool method_predicate(struct method *method, void *data);
//     //@ requires method_predicate_data(this)(data);
//     //@ ensures method_predicate_data(this)(data);
// 
// /*@
//     predicate_family_instance method_predicate_data(has_name)(void *data) = 
// @*/
// bool has_name(struct method *method, void *data) //@ : method_predicate
//     //@ requires method_predicate_data(has_name)(data);
//     //@ ensures method_predicate_data(has_name)(data);
// {
//     char *string = (char *) data;
//     int string_length = strlen((char *)string);
//     bool res;
//     if(method->name_length != string_length) {
//         res = false;
//     } else {
//         int memcmpres = memcmp(method->name, string, method->name_length);
//         res = memcmpres == 0;
//     }
//     return res;
// }
// 
// /*@
//     predicate_family_instance method_predicate_data(has_name_index)(void *data) = 
// @*/
// bool has_name_index(struct method *method, void *name_index) //@ : method_predicate
//     //@ requires method_predicate_data(has_name_index)(data);
//     //@ ensures method_predicate_data(has_name_index)(data);
// {
//     return method->name_index == * (int *)name_index;
// }
// 
// void get_method_info(struct method *method, int count, int *max_locals, int *max_stack, char **code, int *code_length, method_predicate *p, void *data)
//     //@ requires true;
//     //@ ensures true;
// {
//     if(count == 0) {
//         error("ERROR: no such method");
//     } else {
//         bool found = p(method, data);
//         if(found) {
//             char *my_code = malloc(method->code_length);
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

// struct class_file {
//     int constant_count;
//     struct constant *constants;
//     int field_count;
//     int method_count;
//     struct method *methods;
// };
// 
// void parse_constant_pool(struct chars_reader *reader, struct class_file *class_file)
//     //@ requires true;
//     //@ ensures true;
// {
//     struct constant *constants;
//     int i;
//     unsigned short constant_count = 0;
//     constant_count = reader_next_uint16(reader);
//     if(constant_count < (unsigned short) 1)
//         error("ERROR: constant count must be at least one");
//     constants = 0;
//     for(i = 1; i < constant_count; i++)
//     {
//         unsigned char tag;
//         struct constant *constant = malloc(sizeof(struct constant));
//         if(constant == 0) {
//             error("ERROR: insufficient memory");
//         }
//         tag = reader_next_uint8(reader);
//         constant->tag = tag;
//         switch((int) tag) {
//         case STRING:
//         {
//             unsigned short length;
//             char *string;
//             struct string_constant *string_constant = malloc(sizeof(struct string_constant));
//             if(string_constant == 0) {
//                 error("ERROR: insufficient memory");
//             }
//             length = reader_next_uint16(reader);
//             string_constant->length = length;
//             string = reader_next_chars(reader, length);
//             string_constant->string = string;
//             constant->info = string_constant;
//             break;
//         }
//         case INT:
//         {
//             int value;
//             struct int_constant *int_constant = malloc(sizeof(struct int_constant));
//             if(int_constant == 0) {
//                 error("ERROR: insufficient memory");
//             }
//             value = reader_next_int32(reader);
//             int_constant->value = value;
//             constant->info = int_constant;
//             break;
//         }
//         case CLASS:
//         {
//             unsigned short name_index;
//             struct class_constant *class_constant = malloc(sizeof(struct class_constant));
//             if(class_constant == 0) {
//                 error("ERROR: insufficient memory");
//             }
//             name_index = reader_next_uint16(reader);
//             class_constant->name_index = name_index;
//             if(name_index < 1 || name_index >= constant_count) {
//                 error("ERROR: bad index");
//             }
//             constant->info = class_constant;
//             break;
//         }
//         case METHODREF:
//         {
//             unsigned short class_index;
//             unsigned short name_and_type_index;
//             struct methodref_constant *methodref_constant = malloc(sizeof(struct methodref_constant));
//             if(methodref_constant == 0) {
//                 error("ERROR: insufficient memory");
//             }
//             class_index = reader_next_uint16(reader);
//             methodref_constant->class_index = class_index;
//             if(class_index < 1 ||  class_index >= constant_count) {
//                 error("ERROR: bad index");
//             }
//             name_and_type_index = reader_next_uint16(reader);
//             if(name_and_type_index < 1 ||  name_and_type_index >= constant_count) {
//                 error("ERROR: bad index");
//             }
//             methodref_constant->name_and_type_index = name_and_type_index;
//             constant->info = methodref_constant;
//             break;
//         }
//         case NAME_AND_TYPE:
//         {
//             unsigned short name_index;
//             unsigned short descriptor_index;
//             struct name_and_type_constant *name_and_type_constant = malloc(sizeof(struct name_and_type_constant));
//             if(name_and_type_constant == 0) {
//                 error("ERROR: insufficient memory");
//             }
//             name_index = reader_next_uint16(reader);
//             if(name_index < 1 ||  name_index >= constant_count) {
//                 error("ERROR: bad index");
//             }
//             name_and_type_constant->name_index = name_index;
//             descriptor_index = reader_next_uint16(reader);
//             if(descriptor_index < 1 ||  descriptor_index >= constant_count) {
//                 error("ERROR: bad index");
//             }
//             name_and_type_constant->descriptor_index = descriptor_index;
//             constant->info = name_and_type_constant;
//             break;
//         }
//         default:
//             error("Unsupported constant pool tag");
//         }
//         constant->next = constants;
//         constants = constant;
//     }
//     constants = constants_reverse(constants);
//     class_file->constant_count = constant_count;
//     class_file->constants = constants;
// }
// 
// int parse_attributes(struct chars_reader *reader)
//     //@ requires true;
//     //@ ensures true;
// {
//     int i;
//     unsigned short attributes_count = reader_next_uint16(reader);
//     for(i = 0; i < attributes_count; i++)
//     {
//         unsigned short attribute_name_index = reader_next_uint16(reader);
//         unsigned int length = reader_next_uint32(reader);
//         if(length > (unsigned int) INT_MAX) {
//             error("ERROR: unsupported attribute length");
//         }
//         reader_skip(reader, (int) length);
//     }
//     return attributes_count;
// }
// 
// void parse_fields(struct chars_reader *reader, struct class_file *class_file)
//     //@ requires true;
//     //@ ensures true;
// {
//     int i;
//     unsigned short field_count = reader_next_uint16(reader);
//     class_file->field_count = field_count;
//     for(i = 0; i < field_count; i++)
//     {
//         unsigned short access_flags = reader_next_uint16(reader);
//         unsigned short name_index = reader_next_uint16(reader);
//         unsigned short descriptor_index = reader_next_uint16(reader);
//         int attributes_count = parse_attributes(reader);
//     }
// }
// 
// void parse_methods(struct chars_reader *reader, struct class_file *class_file)
//     //@ requires true;
//     //@ ensures true;
// {
//     int i;
//     unsigned short method_count = reader_next_uint16(reader);
//     class_file->method_count = method_count;
//     class_file->methods = 0;
//     for(i = 0; i < method_count; i++)
//     {
//         unsigned short access_flags, name_index, descriptor_index, max_stack, max_locals;
//         int pre_attrib_offset, offset, code_length, code_offset, attributes_count;
//         unsigned int ucode_length;
//         char *code;
//         struct string_constant *name_constant;
//         struct method *method = malloc(sizeof(struct method));
//         if(method == 0) error("Insufficient memory");
//         method->next = class_file->methods;
//         access_flags = reader_next_uint16(reader);
//         name_index = reader_next_uint16(reader);
//         method->name_index= name_index;
//         if(name_index < 1 ||  name_index >= class_file->constant_count) {
//             error("ERROR: bad index");
//         }
//         name_constant = constants_clone_info(class_file->constants, STRING, name_index);
//         method->name = name_constant->string;
//         method->name_length = name_constant->length;
//         free(name_constant);
//         descriptor_index = reader_next_uint16(reader);
//         pre_attrib_offset = reader_get_offset(reader);
//         reader_skip(reader, 8);
//         max_stack = reader_next_uint16(reader);
//         method->max_stack = max_stack;
//         max_locals = reader_next_uint16(reader);
//         method->max_locals = max_locals;
//         offset = reader_get_offset(reader);
//         ucode_length = reader_next_uint32(reader);
//         if(ucode_length > (unsigned int) INT_MAX) {
//             error("ERROR: code length not supported yet");
//         }
//         code_length = (int) ucode_length;
//         method->code_length = code_length;
//         code_offset = reader_get_offset(reader);
//         code = reader_next_chars(reader, code_length);
//         method->code = code;
//         reader_set_offset(reader, pre_attrib_offset);
//         attributes_count = parse_attributes(reader);
//         class_file->methods = method;
//     }
// }
// 
// struct class_file *parse_class_file(struct chars_reader *reader)
//     //@ requires true;
//     //@ ensures true;
// {
//     unsigned short minor_version, major_version, access_flags, this_class, super_class, interfaces_count;
//     unsigned int magic;
//     struct class_file *class_file = malloc(sizeof(struct class_file));
//     int offset = 0;
//     int i, attributes_count;
//     if(class_file == 0)
//         error("ERROR: insufficient memory");
//     magic = reader_next_uint32(reader);
//     minor_version = reader_next_uint16(reader);
//     major_version = reader_next_uint16(reader);
//     parse_constant_pool(reader, class_file);
//     access_flags = reader_next_uint16(reader);
//     this_class = reader_next_uint16(reader);
//     super_class = reader_next_uint16(reader);
//     interfaces_count = reader_next_uint16(reader);
//     for(i = 0; i < interfaces_count; i++)
//     {
//         unsigned short interfaces_index = reader_next_uint16(reader);
//     }
//     parse_fields(reader, class_file);
//     parse_methods(reader, class_file);
//     attributes_count = parse_attributes(reader);
//     return class_file;
// }

/*@
    predicate node(struct node *node, int value, struct thread *thread, struct node *next) = 
        node != 0
            &*& malloc_block_node(node)
            &*& node->value |-> value
            &*& node->thread |-> thread
            &*& node->next |-> next;
    predicate nodes(struct node *node, int count) = 
        node == 0 ?
            count == 0 :
                0 < count
                    &*& node(node, ?value, ?thread, ?next)
                    &*& nodes(next, count - 1);
    predicate lseg(struct node *first, struct node *last, int count) = 
        first == last ?
            count == 0 :
                0 < count 
                    &*& node(first, ?value, ?thread, ?next)
                    &*& lseg(next, last, count - 1);
    lemma void nodes_to_lseg_lemma(struct node *first)
        requires nodes(first, ?count);
        ensures lseg(first, 0, count);
    {
        open nodes(first, count);
        if (first != 0) {
            open node(first, ?value, ?thread, ?next);
            nodes_to_lseg_lemma(first->next);
            close node(first, value, thread, next);
        }
        close lseg(first, 0, count);
    }
    lemma void lseg_to_nodes_lemma(struct node *first)
        requires lseg(first, 0, ?count);
        ensures nodes(first, count);
    {
        open lseg(first, 0, count);
        if (first != 0) {
            open node(first, ?value, ?thread, ?next);
            lseg_to_nodes_lemma(first->next);
            close node(first, value, thread, next);
        }
        close nodes(first, count);
    }
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
    if(n->thread != 0) {
         // FIXME thread_join(n->thread);
    }
    n->thread = 0;
    return n->value;
    //@ close node(n, value, 0, next);
}

void node_set_value(struct node *n, int value)
    //@ requires node(n, _, ?thread, ?next);
    //@ ensures node(n, value, 0, next);
{
    //@ open node(n, _, thread, next);
    if(n->thread != 0) {
        // FIXME thread_join(n->thread);
    }
    n->thread = 0;
    n->value = value;
    //@ close node(n, value, 0, next);
}

struct node *node_at(struct node *n, int index)
    //@ requires nodes(n, ?count) &*& 0 <= index &*& index < count;
    //@ ensures lseg(n, result, index + 1) &*& lseg(result, 0, count - index);
{
    //@ nodes_to_lseg_lemma(n);
    if(index == 0) {
        return n;
    } else {
        //@ open lseg(n, 0, count);
        //@ open node(n, ?value, ?thread, ?next);
        struct node *res = node_at(n->next, index - 1);
        //@ close node(n, value, thread, next);
        //@ close lseg(n, count);
        return res;
    }
}

// /*@
//     predicate stack(struct stack *stack, node_list values, int count) = 
//         malloc_block_stack(stack)
//             &*& stack->top |-> ?top
//             &*& stack->count |-> count
//             &*& 0 <= count
//             &*& nodes(top, values, count);
// @*/
// struct stack {
//     struct node *top;
//     int count;
// };
// 
// struct stack *create_stack()
//     //@ requires true;
//     //@ ensures stack(result, empty_node_list, 0);
// {
//     int i;
//     struct stack *s = malloc(sizeof(struct stack));
//     if(s == 0) {
//         error("ERROR: insufficient memory");
//     }
//     s->top = 0;
//     s->count = 0;
//     //@ close nodes(s->top, empty_node_list, 0);
//     //@ close stack(s, empty_node_list, 0);
//     return s;
// }
// 
// void stack_dispose(struct stack *s)
//     //@ requires stack(s, empty_node_list, 0);
//     //@ ensures true;
// {
//     //@ open stack(s, empty_node_list, 0);
//     //@ open nodes(s->top, empty_node_list, 0);
//     free(s);
// }
// 
// void stack_push(struct stack *s, int value)
//     //@ requires stack(s, ?values, ?count);
//     //@ ensures stack(s, node_list_el(value, 0, values), count + 1);
// {
//     //@ open stack(s, values, count);
//     struct node *new_node = malloc(sizeof(struct node));
//     if(new_node == 0) {
//         error("ERROR: insufficient memory");
//     }
//     new_node->next = s->top;
//     new_node->value = value;
//     new_node->thread = 0;
//     //@ close nodes(new_node, node_list_el(value, 0, values), count + 1);
//     s->top = new_node;
//     if(s->count == INT_MAX) {
//         error("ERROR: stack overflow");
//     }
//     s->count += 1;
//     //@ close stack(s, node_list_el(value, 0, values), count + 1);
// }

// int stack_pop(struct stack *s)
//     //@ requires stack(s, node_list_el(?value, ?thread, ?tail), ?count);
//     //@ ensures stack(s, tail, count - 1) &*& result == value;
// {
//     //@ open stack(s, node_list_el(value, thread, tail), count);
//     struct node *n;
//     int res;
//     if(s->count == 0) {
//         error("ERROR: stack underflow");
//     }
//     n = s->top;
//     //@ open nodes(n, node_list_el(value, thread, tail), count);
//     s->top = s->top->next;
//     s->count--;
//     //@ close nodes(n, node_list_el(value, thread, tail), count);
//     res = node_get_value(n);
//     //@ open nodes(n, node_list_el(_, _, tail), count);
//     free(n);
//     //@ close stack(s, tail, count - 1);
//     return res;
// }

// int stack_count(struct stack *s)
//     //@ requires stack(s, ?values, ?count);
//     //@ ensures stack(s, values, count) &*& result == count;
// {
//     //@ open stack(s, values, count);
//     return s->count;
//     //@ close stack(s, values, count);
// }
// 
// int stack_get(struct stack *s, int index_from_bottom)
//     //@ requires stack(s, ?values, ?count);
//     //@ ensures stack(s, values, count);
// {
//     //@ open stack(s, values, count);
//     struct node *n;
//     if(s->count <= index_from_bottom) {
//         error("ERROR: bad stack index");
//     }
//     n = node_at(s->top, s->count - index_from_bottom - 1);
//     return node_get_value(n);
//     //@ close stack(s, values, count);
// }
// 
// void stack_set(struct stack *s, int index_from_bottom, int value)
//     //@ requires stack(s, ?values, ?count);
//     //@ ensures stack(s, values, count);
// {
//     struct node *n;
//     if(s->count <= index_from_bottom) {
//         error("ERROR: bad stack index");
//     }
//     n = node_at(s->top, s->count - index_from_bottom - 1);
//     node_set_value(n, value);
// }

// void execute_code(struct class_file *class_file, struct stack *s, char *code, int code_length, int max_locals, int args_size);
//     //@ requires true;
//     //@ ensures true;

// struct new_thread_info {
//     struct class_file *class_file;
//     struct stack *stack;
//     char *code;
//     int code_length;
//     int max_locals;
//     int args_size;
//     struct node *node;
// };

// void execute_thread(struct new_thread_info *info)
//     //@ requires true;
//     //@ ensures true;
// {
//     int return_value;
//     execute_code(info->class_file, info->stack, info->code, info->code_length, info->max_locals, info->args_size);
//     return_value = stack_pop(info->stack);
//     info->node->value = return_value;
//     stack_dispose(info->stack);
//     free(info);
// }


// void stack_start_thread(struct stack *s, int index_from_bottom, struct new_thread_info *info)
//     //@ requires true;
//     //@ ensures true;
// {
//     struct thread *thread;
//     struct node *n;
//     if(s->count <= index_from_bottom) {
//         error("ERROR: bad stack index");
//     }
//     n = node_at(s->top, s->count - index_from_bottom - 1);
//     node_get_value(n);
//     info->node = n;
//     thread = thread_start_joinable(execute_thread, info);
//     n->thread = thread;
// }

// bool chars_equals(char *c, int clength, char *string)
//     //@ requires true;
//     //@ ensures true;
// {
//     int res;
//     int string_length = strlen(string);
//     if(string_length != clength) return false;
//     res = memcmp(c, string, clength);
//     return res == 0;
// }
// 
// void parse_method_type(char *descriptor, int dlength, int *args_size)
//     //@ requires true;
//     //@ ensures true;
// {
//     struct chars_reader *reader = create_chars_reader(descriptor, dlength);
//     char c = reader_next_int8(reader);
//     bool closingparen = false;
//     int arg_count = 0;
//     if(c != '(')
//         error("Expected (");
//     while(! closingparen)
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
// bool chars_starts_with(char *c, int clength, char *string)
//     //@ requires true;
//     //@ ensures true;
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

// void execute_code(struct class_file *class_file, struct stack *s, char *code, int code_length, int max_locals, int args_size)
//     //@ requires true;
//     //@ ensures true;
// {
//     int i, preinstr_count;
//     int pre_stack_count = stack_count(s);
//     int locals_offset = pre_stack_count - args_size;
//     struct chars_reader *reader = create_chars_reader(code, code_length);
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
//             struct int_constant *info = constants_clone_info_checked(class_file->constants, INT, index, class_file->constant_count);
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
//             char *callee_code;
//             short method_reference_index = reader_next_int16(reader);
//             struct methodref_constant *methodref = constants_clone_info_checked(class_file->constants, METHODREF, method_reference_index, class_file->constant_count);
//             struct class_constant *class = constants_clone_info(class_file->constants, CLASS, methodref->class_index);
//             struct string_constant *class_name = constants_clone_info(class_file->constants, STRING, class->name_index);
//             struct name_and_type_constant *name_and_type = constants_clone_info(class_file->constants, NAME_AND_TYPE, methodref->name_and_type_index);
//             struct string_constant *method_name = constants_clone_info(class_file->constants, STRING, name_and_type->name_index);
//             struct string_constant *descriptor = constants_clone_info(class_file->constants, STRING, name_and_type->descriptor_index);
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
//                 struct new_thread_info *info;
//                 unsigned char nextopcode;
//                 struct stack *new_stack = create_stack();
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

// int execute_class_file(struct class_file *class_file)
//     //@ requires true;
//     //@ ensures true;
// {
//     int max_locals;
//     int max_stack;
//     char *code;
//     int code_length;
//     struct stack *s = create_stack();
//     char *main_method_name = "main";
//     int exit_value;
//     get_method_info(class_file->methods, class_file->method_count, &max_locals, &max_stack, &code, &code_length, has_name, main_method_name);
//     execute_code(class_file, s, code, code_length, max_locals, 0);
//     exit_value = stack_pop(s);
//     stack_dispose(s);
//     return exit_value;
// }

int main(int argc, char **argv)
    //@ requires true;
    //@ ensures true;
{
    char *buffer;
    int exit_value;
    int filesize;
    struct chars_reader *reader;
    struct class_file *class_file;
    if(argc < 2)
        error("Usage: tinyjava classfile");
    reader = create_chars_reader_from_file(argv[1]);
    class_file = parse_class_file(reader);
    buffer = reader_get_buffer(reader);
    reader_dispose(reader);
    free(buffer);
    exit_value = execute_class_file(class_file);
    exit(exit_value);
}
