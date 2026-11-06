// Lean compiler output
// Module: Macro
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_prune__producer_tacticNew__tac___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticNew_tac"};
static const lean_object* lp_prune__producer_tacticNew__tac___closed__0 = (const lean_object*)&lp_prune__producer_tacticNew__tac___closed__0_value;
static const lean_ctor_object lp_prune__producer_tacticNew__tac___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_prune__producer_tacticNew__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 62, 48, 252, 119, 122, 170, 53)}};
static const lean_object* lp_prune__producer_tacticNew__tac___closed__1 = (const lean_object*)&lp_prune__producer_tacticNew__tac___closed__1_value;
static const lean_string_object lp_prune__producer_tacticNew__tac___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "new_tac"};
static const lean_object* lp_prune__producer_tacticNew__tac___closed__2 = (const lean_object*)&lp_prune__producer_tacticNew__tac___closed__2_value;
static const lean_ctor_object lp_prune__producer_tacticNew__tac___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_prune__producer_tacticNew__tac___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_prune__producer_tacticNew__tac___closed__3 = (const lean_object*)&lp_prune__producer_tacticNew__tac___closed__3_value;
static const lean_ctor_object lp_prune__producer_tacticNew__tac___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_prune__producer_tacticNew__tac___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_prune__producer_tacticNew__tac___closed__3_value)}};
static const lean_object* lp_prune__producer_tacticNew__tac___closed__4 = (const lean_object*)&lp_prune__producer_tacticNew__tac___closed__4_value;
LEAN_EXPORT const lean_object* lp_prune__producer_tacticNew__tac = (const lean_object*)&lp_prune__producer_tacticNew__tac___closed__4_value;
static const lean_string_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__0 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__0_value;
static const lean_string_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__1 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__1_value;
static const lean_string_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__2 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__2_value;
static const lean_string_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__3 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__3_value;
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value_aux_0),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value_aux_1),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value_aux_2),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4_value;
static const lean_string_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__5 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__5_value;
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value_aux_0),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value_aux_1),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value_aux_2),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6_value;
static const lean_string_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__7 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__7_value;
static const lean_ctor_object lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__8 = (const lean_object*)&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__8_value;
static lean_once_cell_t lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__9;
LEAN_EXPORT lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__9(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Array_mkArray0(lean_box(0));
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1(lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = ((lean_object*)(lp_prune__producer_tacticNew__tac___closed__1));
v___x_36_ = l_Lean_Syntax_isOfKind(v_x_32_, v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(1);
v___x_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
return v___x_38_;
}
else
{
lean_object* v_ref_39_; uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_ref_39_ = lean_ctor_get(v_a_33_, 5);
v___x_40_ = 0;
v___x_41_ = l_Lean_SourceInfo_fromRef(v_ref_39_, v___x_40_);
v___x_42_ = ((lean_object*)(lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__3));
v___x_43_ = ((lean_object*)(lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__4));
lean_inc_n(v___x_41_, 3);
v___x_44_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_41_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
v___x_45_ = ((lean_object*)(lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__6));
v___x_46_ = ((lean_object*)(lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__8));
v___x_47_ = lean_obj_once(&lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__9, &lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__9_once, _init_lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___closed__9);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_41_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_47_);
v___x_49_ = l_Lean_Syntax_node1(v___x_41_, v___x_45_, v___x_48_);
v___x_50_ = l_Lean_Syntax_node2(v___x_41_, v___x_43_, v___x_44_, v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_a_34_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1___boxed(lean_object* v_x_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_prune__producer___aux__Macro______macroRules__tacticNew__tac__1(v_x_52_, v_a_53_, v_a_54_);
lean_dec_ref(v_a_53_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_prune__producer_Macro(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
