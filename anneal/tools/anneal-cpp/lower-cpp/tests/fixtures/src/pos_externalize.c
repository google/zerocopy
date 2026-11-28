// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `get_ctx` reaches a record with a variadic function-pointer field and
// takes the address of a global. Extracted with
// `--externalize-callee=get_ctx`, it becomes an external declaration and the
// record is only ever named as a pointee.
struct ctx {
  int (*log)(const char *fmt, ...);
  int level;
};

static struct ctx g_ctx;

struct ctx *get_ctx(void) {
  g_ctx.level = g_ctx.level + 1;
  return &g_ctx;
}

int use_ctx(struct ctx *c, int v);

int pos_externalize(int v) { return use_ctx(get_ctx(), v) == 0; }
