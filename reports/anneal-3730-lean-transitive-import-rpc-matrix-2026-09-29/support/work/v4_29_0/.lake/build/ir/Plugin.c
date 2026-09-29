// Lean compiler output
// Module: Plugin
// Imports: public import Init public import Lean
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
static const lean_string_object lp_rpc__matrix_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PLUGIN_MARKER"};
static const lean_object* lp_rpc__matrix_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2_ = (const lean_object*)&lp_rpc__matrix_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2__value;
static const lean_string_object lp_rpc__matrix_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "plugin-v1"};
static const lean_object* lp_rpc__matrix_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2_ = (const lean_object*)&lp_rpc__matrix_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2__value;
static const lean_string_object lp_rpc__matrix_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_rpc__matrix_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2_ = (const lean_object*)&lp_rpc__matrix_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2__value;
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_rpc__matrix_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* lp_rpc__matrix_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* lp_rpc__matrix_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(lp_rpc__matrix_initFn___closed__0_00___x40_Plugin_3463931333____hygCtx___hyg_2_));
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; 
x_13 = ((lean_object*)(lp_rpc__matrix_initFn___closed__2_00___x40_Plugin_3463931333____hygCtx___hyg_2_));
x_4 = x_13;
goto block_12;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec_ref(x_3);
x_4 = x_14;
goto block_12;
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(lp_rpc__matrix_initFn___closed__1_00___x40_Plugin_3463931333____hygCtx___hyg_2_));
x_9 = l_IO_FS_writeFile(x_4, x_8);
lean_dec_ref(x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* lp_rpc__matrix_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_rpc__matrix_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rpc__matrix_Plugin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = lp_rpc__matrix_initFn_00___x40_Plugin_3463931333____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
