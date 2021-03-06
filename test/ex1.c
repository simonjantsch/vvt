#include "benchmarks.h"

int main () {

  int x;
  int y;
  int xa;
  int ya;
  
  xa = ya = 0;
  
  while (__nondet_bool()) {
    x = xa + 2*ya;
    y = -2*xa + ya;

    x++;
    if (__nondet_bool()) y = y+x;
    else y = y-x;
    
    xa = x - 2*y;
    ya = 2*x + y;
  }

  assert (xa + 2*ya >= 0);
  return 0;
}

