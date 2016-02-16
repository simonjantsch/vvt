/* Testcase from Threader's distribution. For details see:
   http://www.model.in.tum.de/~popeea/research/threader

   This file is adapted from the Promela code introduced in the paper:
   Using Promela and Spin to verify parallel algorithms
   by Paul McKenney
*/

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int idx=0; // boolean to control which of the two elements will be used by readers
  // (idx <= 0) then ctr1 is used
  // (idx >= 1) then ctr2 is used
int ctr1=1, ctr2=0; 
int readerprogress1=0, readerprogress2=0; // the progress is indicated by an integer:
  // 0: reader not yet started
  // 1: reader withing QRCU read-side critical section
  // 2: reader finished with QRCU read-side critical section
pthread_mutex_t mutex; // used to serialize updaters' slowpaths

/* sums the pair of counters forcing weak memory ordering */
#define sum_unordered				\
  if (__nondet_bool()) {			\
    sum = ctr1;					\
    sum = sum + ctr2;				\
  } else {					\
    sum = ctr2;					\
    sum = sum + ctr1;				\
  }

void __VERIFIER_atomic_use1(int myidx) {
  __atomic_begin();
  assume(myidx <= 0 && ctr1>0);
  ctr1++;
  __atomic_end();
}

void __VERIFIER_atomic_use2(int myidx) {
  __atomic_begin();
  assume(myidx >= 1 && ctr2>0);
  ctr2++;
  __atomic_end();
}

void __VERIFIER_atomic_use_done(int myidx) {
  __atomic_begin();
  if (myidx <= 0) { ctr1--; }
  else { ctr2--; }
  __atomic_end();
}

void __VERIFIER_atomic_take_snapshot(int *readerstart1, int *readerstart2) {
  /* Snapshot reader state. */
  __atomic_begin();
  *readerstart1 = readerprogress1;
  *readerstart2 = readerprogress2;
  __atomic_end();
}

void __VERIFIER_atomic_check_progress1(int readerstart1) {
  /* Verify reader progress. */
  __atomic_begin();
  if (__nondet_bool()) {
    assume(readerstart1 == 1 && readerprogress1 == 1);
    __error();
  }
  __atomic_end();
}

void __VERIFIER_atomic_check_progress2(int readerstart2) {
  __atomic_begin();
  if (__nondet_bool()) {
    assume(readerstart2 == 1 && readerprogress2 == 1);
    __error();
  }
  __atomic_end();
}

void *qrcu_reader1(void* arg) {
  int myidx;
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (__nondet_bool()) {
      __VERIFIER_atomic_use1(myidx);
      break;
    } else {
      if (__nondet_bool()) {
	__VERIFIER_atomic_use2(myidx);
	break;
      } else {}
    }
  }
  readerprogress1 = 1;
  readerprogress1 = 2;
  /* rcu_read_unlock */
  __VERIFIER_atomic_use_done(myidx);
  return 0;
}

void *qrcu_reader2(void* arg) {
  int myidx;
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (__nondet_bool()) {
      __VERIFIER_atomic_use1(myidx);
      break;
    } else {
      if (__nondet_bool()) {
	__VERIFIER_atomic_use2(myidx);
	break;
      } else {}
    }
  }
  readerprogress2 = 1;
  readerprogress2 = 2;
  /* rcu_read_unlock */
  __VERIFIER_atomic_use_done(myidx);
  return 0;
}

void* qrcu_updater(void* arg) {
  int i;
  int readerstart1, readerstart2;
  int sum;
  __VERIFIER_atomic_take_snapshot(&readerstart1, &readerstart2);
  sum_unordered;
  if (sum <= 1) { sum_unordered; }
  else {}
  if (sum > 1) {
    pthread_mutex_lock(&mutex);
    if (idx <= 0) { ctr2++; idx = 1; ctr1--; }
    else { ctr1++; idx = 0; ctr2--; }
    if (idx <= 0) { while (ctr1 > 0); }
    else { while (ctr2 > 0); }
    pthread_mutex_unlock(&mutex);
  } else {}
  __VERIFIER_atomic_check_progress1(readerstart1);
  __VERIFIER_atomic_check_progress2(readerstart2);
  return 0;
}

int main() {
  pthread_t t1, t2, t3;
  pthread_mutex_init(&mutex, 0);
  pthread_create(&t1, 0, qrcu_reader1, 0);
  pthread_create(&t2, 0, qrcu_reader2, 0);
  pthread_create(&t3, 0, qrcu_updater, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_mutex_destroy(&mutex);
  return 0;
}
