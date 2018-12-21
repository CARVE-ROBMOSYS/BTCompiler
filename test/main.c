#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>
#include "dummy_skills.h"

#define MAX 10000     // maximum length of a line in the results file

/* from wrap.c */ 
extern value readbt(const char *filename);
extern value tick(value bt);

int main(int argc, char *argv[]) {

  /* initialization */
  
  if (argc == 1) {
    printf("Please specify an input file\n");
    exit(1);
  }

  caml_startup(argv);

  FILE *ft;

  if ((ft = fopen("expected-results.txt", "r"))==NULL) {
    printf("Cannot open results file.\n");
    exit(1);
  }

  int all_ok = 1;

  for (int i = 1; i < argc; i++) {      // main test loop
    const char *filename = argv[i];
    printf("Testing file %s\n",filename);

    value bt = readbt(filename);
    int result = tick(bt);

    char res[8];
    switch (result) {
    case 0:
      strcpy(res, "Running");
      break;
    case 1:
      strcpy(res, "Failure");
      break;
    case 2:
      strcpy(res, "Success");
      break;
    default:
      printf("BT execution returned an error.\n");
      exit(1);
    }
    
    // Execution was successful, now compare the return value with the
    // expected one

    char line[MAX];
    
    while (fgets(line, sizeof line, ft) != NULL) {
      char *s = strstr(line, filename);    // look for filename
      if (s != NULL) {
        s = strpbrk(s, "RFS");     // look for R[unning], F[ailure], S[uccess]
        if (s != NULL) {
          char expected[8];
          strncpy(expected, s, 7);
          expected[7] = '\0';
          if (strcmp(expected, res) == 0) {
            printf("Return value is %s, test is passed.\n", res);
          } else {
            printf("Return value is %s, test is NOT passed (expected result: %s).\n", res, expected);
            all_ok = 0;
          }
        } else {
          printf("Could not find expected result for test %s\n",filename);
        }
        break;
      }
    }
    // notice that if filename is not present in the expected results file,
    // the check is silently skipped

    rewind(ft);
  }
  
  if (all_ok == 1) {
    printf("\nAll tests OK.\n");
  } else {
    printf("\nSome test failed.\n");
  }

  fclose(ft);
  return 0;
}



