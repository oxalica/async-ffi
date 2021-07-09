#include <assert.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

struct FfiWakerVTable {
    struct FfiWaker const *(*clone)(struct FfiWaker const *);
    void (*wake)(struct FfiWaker const *);
    void (*wake_by_ref)(struct FfiWaker const *);
    void (*drop)(struct FfiWaker const *);
};

struct FfiWaker {
    struct FfiWakerVTable const *vtable;
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

struct my_data {
    uint32_t state;
    uint32_t a, b, ret;
    pthread_t handle;
    struct FfiWaker const *waker;
};

static void *handler (void *data_raw) {
    struct my_data *data = (struct my_data *)data_raw;
    usleep(500000);
    data->ret = data->a + data->b;
    atomic_store(&data->state, 2);
    (data->waker->vtable->wake)(data->waker);
}

static struct PollU32 fut_poll (void *fut, struct FfiContext *context) {
    struct my_data *data = (struct my_data *)fut;
    pthread_t handle;
    switch (atomic_load(&data->state)) {
        case 0:
            data->waker = (context->waker_ref->vtable->clone)(context->waker_ref);
            data->state = 1;
            pthread_create(&data->handle, NULL, handler, (void *)data);
        case 1:
            return (struct PollU32) { .is_pending = 1 };
        case 2:
            pthread_join(data->handle, NULL);
            data->handle = 0;
            return (struct PollU32) { .is_pending = 0, .value = data->ret };
    }
}

static void fut_drop(void *fut) {
    struct my_data *data = (struct my_data *)fut;
    if (data->handle != 0) {
        pthread_kill(data->handle, SIGKILL);
        pthread_join(data->handle, NULL);
    }
    free(data);
}

struct FfiFutureU32 plugin_run (uint32_t a, uint32_t b) {
    struct my_data *data = malloc(sizeof(struct my_data));
    data->handle = 0;
    data->state = 0;
    data->a = a;
    data->b = b;
    struct FfiFutureU32 fut = {
        .fut = (void *)data,
        .poll = fut_poll,
        .drop = fut_drop,
    };
    return fut;
}
