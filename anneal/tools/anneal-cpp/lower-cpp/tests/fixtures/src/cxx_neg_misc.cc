// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Constructs the lowerer must refuse; each function is lowered as its own
// entry from one bundle.
int read_ref(const int &r);

// A reference bound to an array element makes the array memory, so the
// store through `r` conflicts with the read of `a[0]`.
int ref_elem_unseq() {
  int a[2] = {1, 2};
  int &r = a[0];
  return (r = 99) + a[0];
}

// C++17 sequences the right operand of `=` first; the store to `a[0]`
// conflicts with the call that reads it through `r`.
int assign_lvalue_order() {
  int a[1] = {10};
  const int &r = a[0];
  (a[0] = 1) = read_ref(r);
  return a[0];
}

// The address of the static array escapes through a reference.
int static_ref_escape(const int *prev) {
  static const int kArr[1] = {42};
  const int &r = kArr[0];
  return prev ? (prev == &r) : static_ref_escape(&r);
}

struct Base {
  int x;
};
struct Derived : Base {
  int y;
};

// A base-class reference aliases the derived object.
int base_ref_alias() {
  Derived d;
  d.x = 0;
  d.y = 0;
  Base &r = d;
  return (r.x = 2) + d.x;
}

// The address of an assignment is the address of its left operand.
int addr_of_assign() {
  int x = 1;
  int *p = &(x = 2);
  return (*p = 3) + x;
}

// The side effect inside the null pointer constant must not be dropped.
int null_with_side_effect() {
  int x = 0;
  int *q = static_cast<decltype(nullptr)>((x = 77, nullptr));
  return x + (q == nullptr);
}

// Returning a record that is not trivially copyable needs the result to be
// constructed in place, which a by-value `_0` cannot model.
struct Pinned {
  Pinned *self;
  Pinned() : self(this) {}
  Pinned(const Pinned &) = delete;
  ~Pinned() {}
};
Pinned make_pinned() { return Pinned(); }

// A temporary with a destructor wraps the initializer in a full-expression
// cleanup; the reference still aliases `a`, `kArr`, or `x`.
struct Idx {
  ~Idx() {}
  int get() const { return 0; }
};

int unseq_cleanup_ref() {
  int a[2] = {1, 2};
  int &r = a[Idx{}.get()];
  return (r = 99) + a[0];
}

int static_cleanup_escape(const int *prev) {
  static const int kArr[1] = {42};
  const int &r = kArr[Idx{}.get()];
  return prev ? (prev == &r) : static_cleanup_escape(&r);
}

int cleanup_assign_ref() {
  int arr[4] = {0, 0, 0, 99};
  int x = 0;
  int &r = (x = Idx{}.get());
  arr[x = 3] = read_ref(r);
  return arr[3];
}

// A non-trivial constructor receives the object's address, here through a
// converting copy-initialization and through an aggregate member.
struct Box {
  int val;
  Box(Box **out) : val(0) { *out = this; }
};
struct Outer {
  Box b;
};

int ctor_conversion_escape() {
  Box *alias = nullptr;
  Box b = &alias;
  return (alias->val = 7) + b.val;
}

int aggregate_ctor_escape() {
  Box *alias = nullptr;
  Outer o = {Box(&alias)};
  return (alias->val = 7) + o.b.val;
}

// Indexing the array a call returns by reference still lets the call bind
// `x` by reference.
using Arr2 = int[2];
Arr2 &get_arr(int &x);

int ref_array_call_escape() {
  int x = 0;
  return (get_arr(x)[0] = 5) + x;
}
