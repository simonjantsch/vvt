#include "benchmarks.h"

int main()
{
  NONDET_INT(n);
  NONDET_INT(m);
  int x; 
  int y;
  x = 0;
  y = m;
  if(n < 0)
    return 0;
  if(m < 0)
    return 0;
  if(m > n-1)
    return 0;
  while(x<=n-1) {
    x++;
    if(x>=m+1) y++;
    else if(x > m) return 0;
    x = x;
  }
  if(x < n)
    return 0;
  assert(y < n+1);
}
