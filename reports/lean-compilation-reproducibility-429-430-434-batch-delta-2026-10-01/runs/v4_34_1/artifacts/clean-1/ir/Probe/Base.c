// Lean compiler output
// Module: Probe.Base
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_compilation__probe_Probe_inc(lean_object*);
LEAN_EXPORT lean_object* lp_compilation__probe_Probe_inc___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_compilation__probe_Probe_inc(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_add(v_n_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_compilation__probe_Probe_inc___boxed(lean_object* v_n_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_compilation__probe_Probe_inc(v_n_4_);
lean_dec(v_n_4_);
return v_res_5_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_compilation__probe_Probe_Base(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
