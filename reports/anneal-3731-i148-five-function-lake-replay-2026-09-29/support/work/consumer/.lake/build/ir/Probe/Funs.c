// Lean compiler output
// Module: Probe.Funs
// Imports: public import Init public meta import Init public import Aeneas public import Probe.Types
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
lean_object* lp_aeneas_Aeneas_Std_UScalar_add(uint8_t, lean_object*, lean_object*);
lean_object* lp_aeneas_Aeneas_Std_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_add__one(lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_add__one___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_choose(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_choose___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_pair__sum(lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_pair__sum___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_make__pair(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_i148__replay_i148__corpus_combine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_i148__replay_i148__corpus_add__one___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_i148__replay_i148__corpus_combine___closed__0 = (const lean_object*)&lp_i148__replay_i148__corpus_combine___closed__0_value;
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_add__one(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = 3;
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lp_aeneas_Aeneas_Std_UScalar_add(v___x_2_, v_x_1_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_add__one___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_i148__replay_i148__corpus_add__one(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_choose(uint8_t v_flag_7_, lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
if (v_flag_7_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v_y_9_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
lean_dec(v_y_9_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v_x_8_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_choose___boxed(lean_object* v_flag_12_, lean_object* v_x_13_, lean_object* v_y_14_){
_start:
{
uint8_t v_flag_boxed_15_; lean_object* v_res_16_; 
v_flag_boxed_15_ = lean_unbox(v_flag_12_);
v_res_16_ = lp_i148__replay_i148__corpus_choose(v_flag_boxed_15_, v_x_13_, v_y_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_pair__sum(lean_object* v_pair_17_){
_start:
{
lean_object* v_left_18_; lean_object* v_right_19_; uint8_t v___x_20_; lean_object* v___x_21_; 
v_left_18_ = lean_ctor_get(v_pair_17_, 0);
v_right_19_ = lean_ctor_get(v_pair_17_, 1);
v___x_20_ = 3;
v___x_21_ = lp_aeneas_Aeneas_Std_UScalar_add(v___x_20_, v_left_18_, v_right_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_pair__sum___boxed(lean_object* v_pair_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_i148__replay_i148__corpus_pair__sum(v_pair_22_);
lean_dec_ref(v_pair_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_make__pair(lean_object* v_x_24_, lean_object* v_y_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_x_24_);
lean_ctor_set(v___x_26_, 1, v_y_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine___lam__0(uint8_t v_flag_28_, lean_object* v___f_29_, lean_object* v_p_30_){
_start:
{
lean_object* v_left_31_; lean_object* v_right_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_left_31_ = lean_ctor_get(v_p_30_, 0);
lean_inc(v_left_31_);
v_right_32_ = lean_ctor_get(v_p_30_, 1);
lean_inc(v_right_32_);
lean_dec_ref(v_p_30_);
v___x_33_ = lp_i148__replay_i148__corpus_choose(v_flag_28_, v_left_31_, v_right_32_);
v___x_34_ = lp_aeneas_Aeneas_Std_bind___redArg(v___x_33_, v___f_29_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine___lam__0___boxed(lean_object* v_flag_35_, lean_object* v___f_36_, lean_object* v_p_37_){
_start:
{
uint8_t v_flag_boxed_38_; lean_object* v_res_39_; 
v_flag_boxed_38_ = lean_unbox(v_flag_35_);
v_res_39_ = lp_i148__replay_i148__corpus_combine___lam__0(v_flag_boxed_38_, v___f_36_, v_p_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine(uint8_t v_flag_41_, lean_object* v_x_42_, lean_object* v_y_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___f_44_ = ((lean_object*)(lp_i148__replay_i148__corpus_combine___closed__0));
v___x_45_ = lean_box(v_flag_41_);
v___f_46_ = lean_alloc_closure((void*)(lp_i148__replay_i148__corpus_combine___lam__0___boxed), 3, 2);
lean_closure_set(v___f_46_, 0, v___x_45_);
lean_closure_set(v___f_46_, 1, v___f_44_);
v___x_47_ = lp_i148__replay_i148__corpus_make__pair(v_x_42_, v_y_43_);
v___x_48_ = lp_aeneas_Aeneas_Std_bind___redArg(v___x_47_, v___f_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_i148__replay_i148__corpus_combine___boxed(lean_object* v_flag_49_, lean_object* v_x_50_, lean_object* v_y_51_){
_start:
{
uint8_t v_flag_boxed_52_; lean_object* v_res_53_; 
v_flag_boxed_52_ = lean_unbox(v_flag_49_);
v_res_53_ = lp_i148__replay_i148__corpus_combine(v_flag_boxed_52_, v_x_50_, v_y_51_);
return v_res_53_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_aeneas_Aeneas(uint8_t builtin);
lean_object* initialize_i148__replay_Probe_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_i148__replay_Probe_Funs(uint8_t builtin) {
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
res = initialize_i148__replay_Probe_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
