// Lean compiler output
// Module: Current.Funs
// Imports: public import Init public meta import Init public import Aeneas public import Current.Types
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_aeneas_Aeneas_Std_core_num_U32_wrapping__add(lean_object*, lean_object*);
lean_object* lp_aeneas_Aeneas_Std_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_inc(lean_object*);
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_inc___boxed(lean_object*);
static const lean_closure_object lp_r48__probe_pipeline__workload_twice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_r48__probe_pipeline__workload_inc___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_r48__probe_pipeline__workload_twice___closed__0 = (const lean_object*)&lp_r48__probe_pipeline__workload_twice___closed__0_value;
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_twice(lean_object*);
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_twice___boxed(lean_object*);
static lean_once_cell_t lp_r48__probe_pipeline__workload_choose___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_r48__probe_pipeline__workload_choose___closed__0;
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_choose(lean_object*);
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_choose___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_inc(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lp_aeneas_Aeneas_Std_core_num_U32_wrapping__add(v_x_1_, v___x_2_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_inc___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_r48__probe_pipeline__workload_inc(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_twice(lean_object* v_x_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = ((lean_object*)(lp_r48__probe_pipeline__workload_twice___closed__0));
v___x_10_ = lp_r48__probe_pipeline__workload_inc(v_x_8_);
v___x_11_ = lp_aeneas_Aeneas_Std_bind___redArg(v___x_10_, v___f_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_twice___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_r48__probe_pipeline__workload_twice(v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
static lean_object* _init_lp_r48__probe_pipeline__workload_choose___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lp_r48__probe_pipeline__workload_twice(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_choose(lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_nat_dec_eq(v_x_16_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = lp_r48__probe_pipeline__workload_inc(v_x_16_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&lp_r48__probe_pipeline__workload_choose___closed__0, &lp_r48__probe_pipeline__workload_choose___closed__0_once, _init_lp_r48__probe_pipeline__workload_choose___closed__0);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_r48__probe_pipeline__workload_choose___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_r48__probe_pipeline__workload_choose(v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_aeneas_Aeneas(uint8_t builtin);
lean_object* initialize_r48__probe_Current_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_r48__probe_Current_Funs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_aeneas_Aeneas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_r48__probe_Current_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
