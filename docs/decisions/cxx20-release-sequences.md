Under strict RC11, the following would be considered race-free:
```c
#include <pthread.h>
#include <stdatomic.h>
atomic_int x;
int d;
void *w(void *_) {
  d = 1;
  atomic_store_explicit(&x, 1, memory_order_release);
  atomic_store_explicit(&x, 2,
                        memory_order_relaxed); // same thread, later in mo
  return 0;
}
void *r(void *_) {
  if (atomic_load_explicit(&x, memory_order_acquire) == 2) {
    int v = d;
    (void)v;
  }
  return 0;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&a, 0, w, 0);
  pthread_create(&b, 0, r, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
}
```
The two stores in the writer create a release sequence which synchronizes with the load in the reader. [P0982R0](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p0982r0.html), which was later implemented in C++20 rejects such constructs as containing a data race and thus is UB; specifically, same-thread stores can *not* participate in release sequences. This is different to the formalization outlined in RC11, which allowed any modifications to a memory location to extend release sequences (given that it was synchronized with another thread). The GenMC model checker will also reject such constructs; to stay consistent with both GenMC and the C++ standard the checker will also reject this.