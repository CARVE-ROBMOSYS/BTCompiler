#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>
#include "dummy_skills.h"

/* from wrap.c */
extern value readbt(char *filename);
extern value tick(value bt);

int main(int argc, char *argv[]) {

  if (argc == 1) {
    printf("Please specify an input file\n");
    exit(1);
  }

  caml_startup(argv);

  for (int i = 1; i < argc; i++) {
    value bt = readbt(argv[i]);
    int result = tick(bt);
    printf("Result of %s is: ",argv[i]);
    if (result == 0) {
      printf("Running\n");
    } else if (result == 1) {
      printf("Failed\n");
    } else if (result == 2) {
      printf("Success\n");
    } else {
      printf("Error!\n");
    }
  }

  return 0;
}
