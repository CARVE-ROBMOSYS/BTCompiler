#include "dummy_skills.h"
#include <string.h>
#include <stdio.h>

#if defined(POSIX)
#include <unistd.h>
#elif defined(_WIN32)
#include <windows.h>
#endif

void PortableSleep(unsigned int MSec)
{
#if defined(POSIX)
usleep((useconds_t)MSec * 1000);
#elif defined(_WIN32)
Sleep((DWORD)MSec);
#endif
}


int DoDummySkill(int status, int elapsed_time_milliseconds)
{
    //PortableSleep(elapsed_time_milliseconds);
    return status;
}

int ExecuteOrResetSkill(const char *name, int is_tick) {

  if (is_tick == 1) {
    printf ("Ticking the skill: %s \n", name);
  } else {
    printf ("Halting the skill: %s \n", name);
    return SUCCESS;
  }

  if (strcmp(name,"Action1SecondSuccess") == 0) {
    int return_status = DoDummySkill(SUCCESS, 1000);
    //    printf ("I am returning %d \n", return_status);
    
    return return_status;
  }
  else if (strcmp(name, "Action1SecondFailure") == 0) {
    int return_status = DoDummySkill(FAILURE, 1000);
    //    printf ("I am returning %d \n", return_status);
    
    return return_status;
  }
  else if (strcmp(name, "ConditionTrue") == 0) {
    int return_status = DoDummySkill(SUCCESS, 0);
    //    printf ("I am returning %d \n", return_status);
    
    return return_status;
  }
  else if (strcmp(name, "ConditionFalse") == 0) {
    int return_status = DoDummySkill(FAILURE, 0);
    //    printf ("I am returning %d \n", return_status);

    return return_status;
  }
  else if (strcmp(name, "ActionRunning") == 0) {
    int return_status = DoDummySkill(RUNNING, 1000);
    //    printf ("I am returning %d \n", return_status);
    
    return return_status;
  }
  else {
    printf ("Node %s not known \n", name);
    return ERROR;
  }

}

int ExecuteSkill(const char *name) {
  return ExecuteOrResetSkill(name,1);
}

void ResetSkill(const char *name) {
  ExecuteOrResetSkill(name,0);
  return;
}
