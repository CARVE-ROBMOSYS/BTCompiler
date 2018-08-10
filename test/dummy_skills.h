#ifndef DUMMY_SKILLS_H
#define DUMMY_SKILLS_H

enum Status {RUNNING, FAILURE, SUCCESS, ERROR};

int ExecuteSkill(const char *name);
void ResetSkill(const char *name);


#endif // DUMMY_SKILLS_H
