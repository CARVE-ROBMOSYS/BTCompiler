#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>

/* from wrap.c */
extern value readbt(char *filename);
extern value tick(value bt);

/* from dummy_skills.c */
extern int ExecuteSkill(const char *name);

int main(int argc, char **argv) {
  int result;

  caml_startup(argv);
  value bt = readbt(argv[1]);
  result = tick(bt);

  printf("Result is: ");
  if (result == 0) {
    printf("Running\n");
  } else if (result == 1) {
    printf("Failed\n");
  } else if (result == 2) {
    printf("Success\n");
  } else {
    printf("Error!\n");
  }

  return 0;
}
