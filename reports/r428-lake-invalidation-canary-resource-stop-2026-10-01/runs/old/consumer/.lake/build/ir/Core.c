// Lean compiler output
// Module: Core
// Imports: public import Init public meta import Init public import Dep
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
LEAN_EXPORT lean_object* lp_probe__consumer_coreValue;
static lean_object* _init_lp_probe__consumer_coreValue(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(8u);
return v___x_1_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_probe__dep_Dep(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_probe__consumer_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_probe__dep_Dep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_probe__consumer_coreValue = _init_lp_probe__consumer_coreValue();
lean_mark_persistent(lp_probe__consumer_coreValue);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
