// Lean compiler output
// Module: Plugin
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
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
static const lean_string_object lp_plugin__probe_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PLUGIN_MARKER"};
static const lean_object* lp_plugin__probe_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2_ = (const lean_object*)&lp_plugin__probe_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2__value;
static const lean_string_object lp_plugin__probe_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "plugin-v1"};
static const lean_object* lp_plugin__probe_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2_ = (const lean_object*)&lp_plugin__probe_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2__value;
static const lean_string_object lp_plugin__probe_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_plugin__probe_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2_ = (const lean_object*)&lp_plugin__probe_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___y_8_; 
v___x_5_ = ((lean_object*)(lp_plugin__probe_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2_));
v___x_6_ = lean_io_getenv(v___x_5_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_object* v___x_16_; 
v___x_16_ = ((lean_object*)(lp_plugin__probe_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2_));
v___y_8_ = v___x_16_;
goto v___jp_7_;
}
else
{
lean_object* v_val_17_; 
v_val_17_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v___x_6_);
v___y_8_ = v_val_17_;
goto v___jp_7_;
}
v___jp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_string_utf8_byte_size(v___y_8_);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_nat_dec_eq(v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = ((lean_object*)(lp_plugin__probe_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2_));
v___x_13_ = l_IO_FS_writeFile(v___y_8_, v___x_12_);
lean_dec_ref(v___y_8_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec_ref(v___y_8_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_plugin__probe_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2____boxed(lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_plugin__probe_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_();
return v_res_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_plugin__probe_Plugin(uint8_t builtin) {
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
res = lp_plugin__probe_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
