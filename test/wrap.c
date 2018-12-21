#include <stdio.h>
#include <string.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/callback.h>
#include "dummy_skills.h"

/*
  type return_enum = Runn | Fail | Succ
  (corresponding C values: int 0,1,2)
 */

/* C interface to OCaml functions readbt, tick */

value readbt(const char *filename) {
  CAMLparam0();
  static value *readbt_closure = NULL;
  if (readbt_closure == NULL) readbt_closure = caml_named_value("readbt");
  CAMLreturn (caml_callback(*readbt_closure, caml_copy_string(filename)));
}

int tick(value bt) {
  CAMLparam1(bt);
  static value *tick_closure = NULL;
  if (tick_closure == NULL) tick_closure = caml_named_value("tick");
  return Int_val(caml_callback(*tick_closure, bt));
}

/* OCaml interface to the C functions ExecuteSkill, ResetSkill */

CAMLprim value exec(value v) {
  return Val_int(ExecuteSkill(String_val(v)));
}

CAMLprim value reset(value v) {
  ResetSkill(String_val(v));
  return Val_true;
}
