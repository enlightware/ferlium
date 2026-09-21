// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

// Callgrind client requests for the Node benchmark runner. Both the Rust compiler and the
// generated Ferlium code are Wasm, so neither can issue the native requests itself. Outside
// Valgrind every request is a no-op.

#include <callgrind.h>
#include <node_api.h>

static napi_value start_instrumentation(napi_env env, napi_callback_info info) {
    CALLGRIND_START_INSTRUMENTATION;
    return NULL;
}

static napi_value zero_stats(napi_env env, napi_callback_info info) {
    CALLGRIND_ZERO_STATS;
    return NULL;
}

static napi_value toggle_collect(napi_env env, napi_callback_info info) {
    CALLGRIND_TOGGLE_COLLECT;
    return NULL;
}

static napi_value dump_stats_at(napi_env env, napi_callback_info info) {
    size_t argc = 1;
    napi_value argv[1];
    char label[256] = "range";
    napi_get_cb_info(env, info, &argc, argv, NULL, NULL);
    if (argc >= 1) {
        size_t written;
        napi_get_value_string_utf8(env, argv[0], label, sizeof(label), &written);
    }
    CALLGRIND_DUMP_STATS_AT(label);
    return NULL;
}

static napi_value running_on_valgrind(napi_env env, napi_callback_info info) {
    napi_value result;
    napi_get_boolean(env, RUNNING_ON_VALGRIND != 0, &result);
    return result;
}

static void export_fn(napi_env env, napi_value exports, const char* name, napi_callback fn) {
    napi_value value;
    napi_create_function(env, NULL, 0, fn, NULL, &value);
    napi_set_named_property(env, exports, name, value);
}

NAPI_MODULE_INIT() {
    export_fn(env, exports, "startInstrumentation", start_instrumentation);
    export_fn(env, exports, "zero", zero_stats);
    export_fn(env, exports, "toggleCollect", toggle_collect);
    export_fn(env, exports, "dump", dump_stats_at);
    export_fn(env, exports, "runningOnValgrind", running_on_valgrind);
    return exports;
}
