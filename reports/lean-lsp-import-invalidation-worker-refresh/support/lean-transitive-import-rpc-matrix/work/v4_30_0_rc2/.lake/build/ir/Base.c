// Lean compiler output
// Module: Base
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_rpc__matrix_tacticProbe__tac___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "tacticProbe_tac"};
static const lean_object* lp_rpc__matrix_tacticProbe__tac___closed__0 = (const lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__0_value;
static const lean_ctor_object lp_rpc__matrix_tacticProbe__tac___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 219, 198, 218, 250, 60, 21, 133)}};
static const lean_object* lp_rpc__matrix_tacticProbe__tac___closed__1 = (const lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__1_value;
static const lean_string_object lp_rpc__matrix_tacticProbe__tac___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "probe_tac"};
static const lean_object* lp_rpc__matrix_tacticProbe__tac___closed__2 = (const lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__2_value;
static const lean_ctor_object lp_rpc__matrix_tacticProbe__tac___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_rpc__matrix_tacticProbe__tac___closed__3 = (const lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__3_value;
static const lean_ctor_object lp_rpc__matrix_tacticProbe__tac___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__3_value)}};
static const lean_object* lp_rpc__matrix_tacticProbe__tac___closed__4 = (const lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__4_value;
LEAN_EXPORT const lean_object* lp_rpc__matrix_tacticProbe__tac = (const lean_object*)&lp_rpc__matrix_tacticProbe__tac___closed__4_value;
static const lean_string_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__0 = (const lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__0_value;
static const lean_string_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__1 = (const lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__1_value;
static const lean_string_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__2 = (const lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__2_value;
static const lean_string_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__3 = (const lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__3_value;
static const lean_ctor_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value_aux_0),((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value_aux_1),((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value_aux_2),((lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 42, 145, 170, 145, 147, 228, 105)}};
static const lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4 = (const lean_object*)&lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4_value;
LEAN_EXPORT lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_rpc__matrix_selected;
LEAN_EXPORT lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1(lean_object* v_x_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = ((lean_object*)(lp_rpc__matrix_tacticProbe__tac___closed__1));
v___x_26_ = l_Lean_Syntax_isOfKind(v_x_22_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(1);
v___x_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_a_24_);
return v___x_28_;
}
else
{
lean_object* v_ref_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_ref_29_ = lean_ctor_get(v_a_23_, 5);
v___x_30_ = 0;
v___x_31_ = l_Lean_SourceInfo_fromRef(v_ref_29_, v___x_30_);
v___x_32_ = ((lean_object*)(lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__3));
v___x_33_ = ((lean_object*)(lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___closed__4));
lean_inc(v___x_31_);
v___x_34_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_31_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
v___x_35_ = l_Lean_Syntax_node1(v___x_31_, v___x_33_, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v_a_24_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1___boxed(lean_object* v_x_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_rpc__matrix___aux__Base______macroRules__tacticProbe__tac__1(v_x_37_, v_a_38_, v_a_39_);
lean_dec_ref(v_a_38_);
return v_res_40_;
}
}
static lean_object* _init_lp_rpc__matrix_selected(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(9u);
return v___x_41_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rpc__matrix_Base(uint8_t builtin) {
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
lp_rpc__matrix_selected = _init_lp_rpc__matrix_selected();
lean_mark_persistent(lp_rpc__matrix_selected);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
