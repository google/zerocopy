// Lean compiler output
// Module: Alien
// Imports: public import Init public meta import Init public import Lean
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
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Alien_2630635079____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Alien_2630635079____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Alien_2630635079____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Alien_2630635079____hygCtx___hyg_2____boxed(lean_object* v_a_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_plugin__probe_initFn_00___x40_Alien_2630635079____hygCtx___hyg_2_();
return v_res_5_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_plugin__probe_Alien(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = lp_plugin__probe_initFn_00___x40_Alien_2630635079____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
