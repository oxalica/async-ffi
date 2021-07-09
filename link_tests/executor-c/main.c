#include <assert.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <threads.h>

// Data structures.

struct FfiWakerVTable {
    struct FfiWaker const *(*clone)(struct FfiWaker const *);
    void (*wake)(struct FfiWaker *);
    void (*wake_by_ref)(struct FfiWaker const *);
    void (*drop)(struct FfiWaker *);
};

struct FfiWaker {
    struct FfiWakerVTable const *vtable;

    // Store some extra trailing data to wake up the executor loop.
    mtx_t *mutex;
    cnd_t *condvar;
    int *awake;
};

struct FfiContext {
    struct FfiWaker const *waker_ref;
};

struct PollU32 {
    uint8_t is_pending;
    union { uint32_t value; };
};

struct FfiFutureU32 {
    void *fut;
    struct PollU32 (*poll)(void *fut, struct FfiContext *context);
    void (*drop)(void *fut);
};

// Waker virtual functions.

struct FfiWaker const *waker_clone(struct FfiWaker const *w) {
    struct FfiWaker *p = malloc(sizeof(struct FfiWaker));
    assert(p);
    *p = *w;
    return p;
}

void waker_wake_by_ref(struct FfiWaker const *w) {
    puts("Wake");
    mtx_lock(w->mutex);
    *w->awake = 1;
    cnd_signal(w->condvar);
    mtx_unlock(w->mutex);
}

void waker_drop(struct FfiWaker *w) {
    free(w);
}

void waker_wake(struct FfiWaker *w) {
    waker_wake_by_ref(w);
    waker_drop(w);
}

struct FfiWakerVTable waker_vtable = {
    .clone = &waker_clone,
    .wake = &waker_wake,
    .wake_by_ref = &waker_wake_by_ref,
    .drop = &waker_drop,
};

// Executor.

typedef struct FfiFutureU32 (*plugin_run_fn_t)(uint32_t, uint32_t);

void execute(plugin_run_fn_t fn) {
    // Waker may outlive the executor itself, so data referenced by waker need to be reference-counted.
    // Here we simply use global one since the executor is run only once.
    static mtx_t mutex;
    static cnd_t condvar;
    static int awake = 0;
    mtx_init(&mutex, mtx_plain);
    cnd_init(&condvar);

    struct FfiWaker waker = {
        .vtable = &waker_vtable,
        .mutex = &mutex,
        .condvar = &condvar,
        .awake = &awake,
    };
    struct FfiContext ctx = { .waker_ref = &waker };

    puts("Calling future");
    struct FfiFutureU32 fut = fn(42, 1);

    struct PollU32 ret;
    while (1) {
        puts("Polling future");
        ret = (fut.poll)(fut.fut, &ctx);
        printf("-> is_pending: %d\n", ret.is_pending);
        if (!ret.is_pending)
            break;

        // When `poll` returns `Pending`, it automatically hook the waker to some reactor, which will
        // be called `wake` or `wake_by_ref` if the future is ready to be `poll`ed again.
        // So we wait on the condvar until someone wake us again.
        mtx_lock(&mutex);
        while (!awake)
            cnd_wait(&condvar, &mutex);
        awake = 0;
        mtx_unlock(&mutex);
    }
    // Drop the future when finished or canceled.
    (fut.drop)(fut.fut);

    printf("42 + 1 = %" PRIu32 "\n", ret.value);
}

int main (int argc, char const **argv) {
    assert(argc == 2);
    char const *lib_path = argv[1];

    void *dl = dlopen(lib_path, RTLD_LAZY);
    if (!dl) {
        fprintf(stderr, "dlopen failed: %s\n", dlerror());
        exit(1);
    }
    dlerror(); // Clear errno.

    plugin_run_fn_t fn = dlsym(dl, "plugin_run");
    char *dlerr;
    if ((dlerr = dlerror()) != 0) {
        fprintf(stderr, "dlsym failed: %s\n", dlerr);
        dlclose(dl);
        exit(1);
    }

    execute(fn);

    dlclose(dl);
    return 0;
}
