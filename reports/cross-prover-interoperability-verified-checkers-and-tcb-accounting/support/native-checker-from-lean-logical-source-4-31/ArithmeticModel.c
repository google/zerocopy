// Lean compiler output
// Module: ArithmeticModel
// Imports: public import Init public meta import Init import Lean
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_add8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_add8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_mul8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_mul8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_input_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_input_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_literal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_literal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingAdd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingAdd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingMul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingMul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqSource_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqSource_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqSource(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqSource___boxed(lean_object*, lean_object*);
static const lean_string_object l_ArithmeticPrototype_instReprSource_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ArithmeticPrototype.Source.input"};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__0 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__0_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__0_value)}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__1 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__1_value;
static lean_once_cell_t l_ArithmeticPrototype_instReprSource_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__2;
static lean_once_cell_t l_ArithmeticPrototype_instReprSource_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__3;
static const lean_string_object l_ArithmeticPrototype_instReprSource_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "ArithmeticPrototype.Source.literal"};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__4 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__4_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__4_value)}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__5 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__5_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__6 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__6_value;
static const lean_string_object l_ArithmeticPrototype_instReprSource_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "ArithmeticPrototype.Source.wrappingAdd"};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__7 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__7_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__7_value)}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__8 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__8_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__9 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__9_value;
static const lean_string_object l_ArithmeticPrototype_instReprSource_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "ArithmeticPrototype.Source.wrappingMul"};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__10 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__10_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__10_value)}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__11 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__11_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprSource_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_ArithmeticPrototype_instReprSource_repr___closed__12 = (const lean_object*)&l_ArithmeticPrototype_instReprSource_repr___closed__12_value;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprSource_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprSource_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ArithmeticPrototype_instReprSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ArithmeticPrototype_instReprSource_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ArithmeticPrototype_instReprSource___closed__0 = (const lean_object*)&l_ArithmeticPrototype_instReprSource___closed__0_value;
LEAN_EXPORT const lean_object* l_ArithmeticPrototype_instReprSource = (const lean_object*)&l_ArithmeticPrototype_instReprSource___closed__0_value;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_parameter_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_parameter_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_immediate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_immediate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_addByte_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_addByte_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_mulByte_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_mulByte_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqIR_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqIR_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqIR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqIR___boxed(lean_object*, lean_object*);
static const lean_string_object l_ArithmeticPrototype_instReprIR_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ArithmeticPrototype.IR.parameter"};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__0 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__0_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__0_value)}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__1 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__1_value;
static const lean_string_object l_ArithmeticPrototype_instReprIR_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ArithmeticPrototype.IR.immediate"};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__2 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__2_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__2_value)}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__3 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__3_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__4 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__4_value;
static const lean_string_object l_ArithmeticPrototype_instReprIR_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ArithmeticPrototype.IR.addByte"};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__5 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__5_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__5_value)}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__6 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__6_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__7 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__7_value;
static const lean_string_object l_ArithmeticPrototype_instReprIR_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ArithmeticPrototype.IR.mulByte"};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__8 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__8_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__8_value)}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__9 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__9_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprIR_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_ArithmeticPrototype_instReprIR_repr___closed__10 = (const lean_object*)&l_ArithmeticPrototype_instReprIR_repr___closed__10_value;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprIR_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprIR_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ArithmeticPrototype_instReprIR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ArithmeticPrototype_instReprIR_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ArithmeticPrototype_instReprIR___closed__0 = (const lean_object*)&l_ArithmeticPrototype_instReprIR___closed__0_value;
LEAN_EXPORT const lean_object* l_ArithmeticPrototype_instReprIR = (const lean_object*)&l_ArithmeticPrototype_instReprIR___closed__0_value;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalSource(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalSource___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalIR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalIR___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_decode(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_construct(lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprIR_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprIR_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalSource_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalSource_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalIR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalIR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprSource_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprSource_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_checkPosthoc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_checkPosthoc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00ArithmeticPrototype_instReprRow_repr_spec__0(lean_object*);
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__0 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__0_value;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "input"};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__1 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__1_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__1_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__2 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__2_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__2_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__3 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__3_value;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__4 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__4_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__4_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__5 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__5_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__3_value),((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__5_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__6 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__6_value;
static lean_once_cell_t l_ArithmeticPrototype_instReprRow_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__7;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__8 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__8_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__8_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__9 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__9_value;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__10 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__10_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__10_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__11 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__11_value;
static lean_once_cell_t l_ArithmeticPrototype_instReprRow_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__12;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__13 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__13_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__13_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__14 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__14_value;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "output"};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__15 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__15_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__15_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__16 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__16_value;
static lean_once_cell_t l_ArithmeticPrototype_instReprRow_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__17;
static const lean_string_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__18 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__18_value;
static lean_once_cell_t l_ArithmeticPrototype_instReprRow_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__19;
static lean_once_cell_t l_ArithmeticPrototype_instReprRow_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__20;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__0_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__21 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__21_value;
static const lean_ctor_object l_ArithmeticPrototype_instReprRow_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__18_value)}};
static const lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg___closed__22 = (const lean_object*)&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprRow_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprRow_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ArithmeticPrototype_instReprRow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ArithmeticPrototype_instReprRow_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ArithmeticPrototype_instReprRow___closed__0 = (const lean_object*)&l_ArithmeticPrototype_instReprRow___closed__0_value;
LEAN_EXPORT const lean_object* l_ArithmeticPrototype_instReprRow = (const lean_object*)&l_ArithmeticPrototype_instReprRow___closed__0_value;
static lean_once_cell_t l_ArithmeticPrototype_instInhabitedRow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instInhabitedRow___closed__0;
static lean_once_cell_t l_ArithmeticPrototype_instInhabitedRow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ArithmeticPrototype_instInhabitedRow___closed__1;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instInhabitedRow;
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateA(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateA___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateB(lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateB___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_checkInstrumented___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_checkInstrumented___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ArithmeticPrototype_checkInstrumented(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_checkInstrumented___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ArithmeticPrototype_add8(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_unsigned_to_nat(256u);
v___x_4_ = lean_nat_add(v_a_1_, v_b_2_);
v___x_5_ = lean_nat_mod(v___x_4_, v___x_3_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_add8___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_ArithmeticPrototype_add8(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_mul8(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_unsigned_to_nat(256u);
v___x_12_ = lean_nat_mul(v_a_9_, v_b_10_);
v___x_13_ = lean_nat_mod(v___x_12_, v___x_11_);
lean_dec(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_mul8___boxed(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_ArithmeticPrototype_mul8(v_a_14_, v_b_15_);
lean_dec(v_b_15_);
lean_dec(v_a_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorIdx(lean_object* v_x_17_){
_start:
{
switch(lean_obj_tag(v_x_17_))
{
case 0:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(0u);
return v___x_18_;
}
case 1:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(1u);
return v___x_19_;
}
case 2:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(2u);
return v___x_20_;
}
default: 
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(3u);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorIdx___boxed(lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_ArithmeticPrototype_Source_ctorIdx(v_x_22_);
lean_dec(v_x_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorElim___redArg(lean_object* v_t_24_, lean_object* v_k_25_){
_start:
{
switch(lean_obj_tag(v_t_24_))
{
case 0:
{
return v_k_25_;
}
case 1:
{
lean_object* v_v_26_; lean_object* v___x_27_; 
v_v_26_ = lean_ctor_get(v_t_24_, 0);
lean_inc(v_v_26_);
lean_dec_ref_known(v_t_24_, 1);
v___x_27_ = lean_apply_1(v_k_25_, v_v_26_);
return v___x_27_;
}
default: 
{
lean_object* v_a_28_; lean_object* v_b_29_; lean_object* v___x_30_; 
v_a_28_ = lean_ctor_get(v_t_24_, 0);
lean_inc(v_a_28_);
v_b_29_ = lean_ctor_get(v_t_24_, 1);
lean_inc(v_b_29_);
lean_dec(v_t_24_);
v___x_30_ = lean_apply_2(v_k_25_, v_a_28_, v_b_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorElim(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_33_, v_k_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_ctorElim___boxed(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_ArithmeticPrototype_Source_ctorElim(v_motive_37_, v_ctorIdx_38_, v_t_39_, v_h_40_, v_k_41_);
lean_dec(v_ctorIdx_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_input_elim___redArg(lean_object* v_t_43_, lean_object* v_input_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_43_, v_input_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_input_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_input_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_47_, v_input_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_literal_elim___redArg(lean_object* v_t_51_, lean_object* v_literal_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_51_, v_literal_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_literal_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_literal_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_55_, v_literal_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingAdd_elim___redArg(lean_object* v_t_59_, lean_object* v_wrappingAdd_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_59_, v_wrappingAdd_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingAdd_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_wrappingAdd_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_63_, v_wrappingAdd_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingMul_elim___redArg(lean_object* v_t_67_, lean_object* v_wrappingMul_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_67_, v_wrappingMul_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_Source_wrappingMul_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_wrappingMul_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_ArithmeticPrototype_Source_ctorElim___redArg(v_t_71_, v_wrappingMul_73_);
return v___x_74_;
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqSource_decEq(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
if (lean_obj_tag(v_x_76_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
case 1:
{
lean_object* v_v_79_; uint8_t v___x_80_; 
v_v_79_ = lean_ctor_get(v_x_75_, 0);
v___x_80_ = 0;
switch(lean_obj_tag(v_x_76_))
{
case 0:
{
return v___x_80_;
}
case 1:
{
lean_object* v_v_81_; uint8_t v___x_82_; 
v_v_81_ = lean_ctor_get(v_x_76_, 0);
v___x_82_ = lean_nat_dec_eq(v_v_79_, v_v_81_);
if (v___x_82_ == 0)
{
return v___x_80_;
}
else
{
return v___x_82_;
}
}
default: 
{
return v___x_80_;
}
}
}
case 2:
{
lean_object* v_a_83_; lean_object* v_b_84_; uint8_t v___x_85_; 
v_a_83_ = lean_ctor_get(v_x_75_, 0);
v_b_84_ = lean_ctor_get(v_x_75_, 1);
v___x_85_ = 0;
switch(lean_obj_tag(v_x_76_))
{
case 0:
{
return v___x_85_;
}
case 2:
{
lean_object* v_a_86_; lean_object* v_b_87_; uint8_t v_inst_88_; 
v_a_86_ = lean_ctor_get(v_x_76_, 0);
v_b_87_ = lean_ctor_get(v_x_76_, 1);
v_inst_88_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v_a_83_, v_a_86_);
if (v_inst_88_ == 0)
{
return v___x_85_;
}
else
{
uint8_t v_inst_89_; 
v_inst_89_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v_b_84_, v_b_87_);
if (v_inst_89_ == 0)
{
return v___x_85_;
}
else
{
return v_inst_89_;
}
}
}
default: 
{
return v___x_85_;
}
}
}
default: 
{
lean_object* v_a_90_; lean_object* v_b_91_; uint8_t v___x_92_; 
v_a_90_ = lean_ctor_get(v_x_75_, 0);
v_b_91_ = lean_ctor_get(v_x_75_, 1);
v___x_92_ = 0;
switch(lean_obj_tag(v_x_76_))
{
case 0:
{
return v___x_92_;
}
case 3:
{
lean_object* v_a_93_; lean_object* v_b_94_; uint8_t v_inst_95_; 
v_a_93_ = lean_ctor_get(v_x_76_, 0);
v_b_94_ = lean_ctor_get(v_x_76_, 1);
v_inst_95_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v_a_90_, v_a_93_);
if (v_inst_95_ == 0)
{
return v___x_92_;
}
else
{
uint8_t v_inst_96_; 
v_inst_96_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v_b_91_, v_b_94_);
if (v_inst_96_ == 0)
{
return v___x_92_;
}
else
{
return v_inst_96_;
}
}
}
default: 
{
return v___x_92_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqSource_decEq___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v_x_97_, v_x_98_);
lean_dec(v_x_98_);
lean_dec(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqSource(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v_x_101_, v_x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqSource___boxed(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_ArithmeticPrototype_instDecidableEqSource(v_x_104_, v_x_105_);
lean_dec(v_x_105_);
lean_dec(v_x_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprSource_repr___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(2u);
v___x_112_ = lean_nat_to_int(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprSource_repr___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_to_int(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprSource_repr(lean_object* v_x_133_, lean_object* v_prec_134_){
_start:
{
lean_object* v___y_136_; 
switch(lean_obj_tag(v_x_133_))
{
case 0:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_134_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_136_ = v___x_144_;
goto v___jp_135_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_136_ = v___x_145_;
goto v___jp_135_;
}
}
case 1:
{
lean_object* v_v_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_166_; 
v_v_146_ = lean_ctor_get(v_x_133_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_166_ == 0)
{
v___x_148_ = v_x_133_;
v_isShared_149_ = v_isSharedCheck_166_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_v_146_);
lean_dec(v_x_133_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_166_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___y_151_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1024u);
v___x_163_ = lean_nat_dec_le(v___x_162_, v_prec_134_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_151_ = v___x_164_;
goto v___jp_150_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_151_ = v___x_165_;
goto v___jp_150_;
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_152_ = ((lean_object*)(l_ArithmeticPrototype_instReprSource_repr___closed__6));
v___x_153_ = l_Nat_reprFast(v_v_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set_tag(v___x_148_, 3);
lean_ctor_set(v___x_148_, 0, v___x_153_);
v___x_155_ = v___x_148_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_161_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_152_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
lean_inc(v___y_151_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_151_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = 0;
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_prec_134_);
return v___x_160_;
}
}
}
}
case 2:
{
lean_object* v_a_167_; lean_object* v_b_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_191_; 
v_a_167_ = lean_ctor_get(v_x_133_, 0);
v_b_168_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_191_ == 0)
{
v___x_170_ = v_x_133_;
v_isShared_171_ = v_isSharedCheck_191_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_b_168_);
lean_inc(v_a_167_);
lean_dec(v_x_133_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_191_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___y_174_; uint8_t v___x_188_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_188_ = lean_nat_dec_le(v___x_172_, v_prec_134_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_174_ = v___x_189_;
goto v___jp_173_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_174_ = v___x_190_;
goto v___jp_173_;
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_175_ = lean_box(1);
v___x_176_ = ((lean_object*)(l_ArithmeticPrototype_instReprSource_repr___closed__9));
v___x_177_ = l_ArithmeticPrototype_instReprSource_repr(v_a_167_, v___x_172_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 5);
lean_ctor_set(v___x_170_, 1, v___x_177_);
lean_ctor_set(v___x_170_, 0, v___x_176_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_187_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_175_);
v___x_181_ = l_ArithmeticPrototype_instReprSource_repr(v_b_168_, v___x_172_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
lean_inc(v___y_174_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___y_174_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = 0;
v___x_185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
v___x_186_ = l_Repr_addAppParen(v___x_185_, v_prec_134_);
return v___x_186_;
}
}
}
}
default: 
{
lean_object* v_a_192_; lean_object* v_b_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_216_; 
v_a_192_ = lean_ctor_get(v_x_133_, 0);
v_b_193_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_216_ == 0)
{
v___x_195_ = v_x_133_;
v_isShared_196_ = v_isSharedCheck_216_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_b_193_);
lean_inc(v_a_192_);
lean_dec(v_x_133_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_216_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___y_199_; uint8_t v___x_213_; 
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_213_ = lean_nat_dec_le(v___x_197_, v_prec_134_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_199_ = v___x_214_;
goto v___jp_198_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_199_ = v___x_215_;
goto v___jp_198_;
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_200_ = lean_box(1);
v___x_201_ = ((lean_object*)(l_ArithmeticPrototype_instReprSource_repr___closed__12));
v___x_202_ = l_ArithmeticPrototype_instReprSource_repr(v_a_192_, v___x_197_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 5);
lean_ctor_set(v___x_195_, 1, v___x_202_);
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_212_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_200_);
v___x_206_ = l_ArithmeticPrototype_instReprSource_repr(v_b_193_, v___x_197_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc(v___y_199_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_199_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_134_);
return v___x_211_;
}
}
}
}
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = ((lean_object*)(l_ArithmeticPrototype_instReprSource_repr___closed__1));
lean_inc(v___y_136_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_134_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprSource_repr___boxed(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_ArithmeticPrototype_instReprSource_repr(v_x_217_, v_prec_218_);
lean_dec(v_prec_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorIdx(lean_object* v_x_222_){
_start:
{
switch(lean_obj_tag(v_x_222_))
{
case 0:
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(0u);
return v___x_223_;
}
case 1:
{
lean_object* v___x_224_; 
v___x_224_ = lean_unsigned_to_nat(1u);
return v___x_224_;
}
case 2:
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(2u);
return v___x_225_;
}
default: 
{
lean_object* v___x_226_; 
v___x_226_ = lean_unsigned_to_nat(3u);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorIdx___boxed(lean_object* v_x_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_ArithmeticPrototype_IR_ctorIdx(v_x_227_);
lean_dec(v_x_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorElim___redArg(lean_object* v_t_229_, lean_object* v_k_230_){
_start:
{
switch(lean_obj_tag(v_t_229_))
{
case 0:
{
return v_k_230_;
}
case 1:
{
lean_object* v_v_231_; lean_object* v___x_232_; 
v_v_231_ = lean_ctor_get(v_t_229_, 0);
lean_inc(v_v_231_);
lean_dec_ref_known(v_t_229_, 1);
v___x_232_ = lean_apply_1(v_k_230_, v_v_231_);
return v___x_232_;
}
default: 
{
lean_object* v_a_233_; lean_object* v_b_234_; lean_object* v___x_235_; 
v_a_233_ = lean_ctor_get(v_t_229_, 0);
lean_inc(v_a_233_);
v_b_234_ = lean_ctor_get(v_t_229_, 1);
lean_inc(v_b_234_);
lean_dec(v_t_229_);
v___x_235_ = lean_apply_2(v_k_230_, v_a_233_, v_b_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorElim(lean_object* v_motive_236_, lean_object* v_ctorIdx_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_k_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_238_, v_k_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_ctorElim___boxed(lean_object* v_motive_242_, lean_object* v_ctorIdx_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_k_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_ArithmeticPrototype_IR_ctorElim(v_motive_242_, v_ctorIdx_243_, v_t_244_, v_h_245_, v_k_246_);
lean_dec(v_ctorIdx_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_parameter_elim___redArg(lean_object* v_t_248_, lean_object* v_parameter_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_248_, v_parameter_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_parameter_elim(lean_object* v_motive_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_parameter_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_252_, v_parameter_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_immediate_elim___redArg(lean_object* v_t_256_, lean_object* v_immediate_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_256_, v_immediate_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_immediate_elim(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_immediate_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_260_, v_immediate_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_addByte_elim___redArg(lean_object* v_t_264_, lean_object* v_addByte_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_264_, v_addByte_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_addByte_elim(lean_object* v_motive_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_addByte_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_268_, v_addByte_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_mulByte_elim___redArg(lean_object* v_t_272_, lean_object* v_mulByte_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_272_, v_mulByte_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_IR_mulByte_elim(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_mulByte_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_ArithmeticPrototype_IR_ctorElim___redArg(v_t_276_, v_mulByte_278_);
return v___x_279_;
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqIR_decEq(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
switch(lean_obj_tag(v_x_280_))
{
case 0:
{
if (lean_obj_tag(v_x_281_) == 0)
{
uint8_t v___x_282_; 
v___x_282_ = 1;
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
case 1:
{
lean_object* v_v_284_; uint8_t v___x_285_; 
v_v_284_ = lean_ctor_get(v_x_280_, 0);
v___x_285_ = 0;
switch(lean_obj_tag(v_x_281_))
{
case 0:
{
return v___x_285_;
}
case 1:
{
lean_object* v_v_286_; uint8_t v___x_287_; 
v_v_286_ = lean_ctor_get(v_x_281_, 0);
v___x_287_ = lean_nat_dec_eq(v_v_284_, v_v_286_);
if (v___x_287_ == 0)
{
return v___x_285_;
}
else
{
return v___x_287_;
}
}
default: 
{
return v___x_285_;
}
}
}
case 2:
{
lean_object* v_a_288_; lean_object* v_b_289_; uint8_t v___x_290_; 
v_a_288_ = lean_ctor_get(v_x_280_, 0);
v_b_289_ = lean_ctor_get(v_x_280_, 1);
v___x_290_ = 0;
switch(lean_obj_tag(v_x_281_))
{
case 0:
{
return v___x_290_;
}
case 2:
{
lean_object* v_a_291_; lean_object* v_b_292_; uint8_t v_inst_293_; 
v_a_291_ = lean_ctor_get(v_x_281_, 0);
v_b_292_ = lean_ctor_get(v_x_281_, 1);
v_inst_293_ = l_ArithmeticPrototype_instDecidableEqIR_decEq(v_a_288_, v_a_291_);
if (v_inst_293_ == 0)
{
return v___x_290_;
}
else
{
uint8_t v_inst_294_; 
v_inst_294_ = l_ArithmeticPrototype_instDecidableEqIR_decEq(v_b_289_, v_b_292_);
if (v_inst_294_ == 0)
{
return v___x_290_;
}
else
{
return v_inst_294_;
}
}
}
default: 
{
return v___x_290_;
}
}
}
default: 
{
lean_object* v_a_295_; lean_object* v_b_296_; uint8_t v___x_297_; 
v_a_295_ = lean_ctor_get(v_x_280_, 0);
v_b_296_ = lean_ctor_get(v_x_280_, 1);
v___x_297_ = 0;
switch(lean_obj_tag(v_x_281_))
{
case 0:
{
return v___x_297_;
}
case 3:
{
lean_object* v_a_298_; lean_object* v_b_299_; uint8_t v_inst_300_; 
v_a_298_ = lean_ctor_get(v_x_281_, 0);
v_b_299_ = lean_ctor_get(v_x_281_, 1);
v_inst_300_ = l_ArithmeticPrototype_instDecidableEqIR_decEq(v_a_295_, v_a_298_);
if (v_inst_300_ == 0)
{
return v___x_297_;
}
else
{
uint8_t v_inst_301_; 
v_inst_301_ = l_ArithmeticPrototype_instDecidableEqIR_decEq(v_b_296_, v_b_299_);
if (v_inst_301_ == 0)
{
return v___x_297_;
}
else
{
return v_inst_301_;
}
}
}
default: 
{
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqIR_decEq___boxed(lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_ArithmeticPrototype_instDecidableEqIR_decEq(v_x_302_, v_x_303_);
lean_dec(v_x_303_);
lean_dec(v_x_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_instDecidableEqIR(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = l_ArithmeticPrototype_instDecidableEqIR_decEq(v_x_306_, v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instDecidableEqIR___boxed(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_ArithmeticPrototype_instDecidableEqIR(v_x_309_, v_x_310_);
lean_dec(v_x_310_);
lean_dec(v_x_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprIR_repr(lean_object* v_x_334_, lean_object* v_prec_335_){
_start:
{
lean_object* v___y_337_; 
switch(lean_obj_tag(v_x_334_))
{
case 0:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_344_ = lean_nat_dec_le(v___x_343_, v_prec_335_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_337_ = v___x_345_;
goto v___jp_336_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_337_ = v___x_346_;
goto v___jp_336_;
}
}
case 1:
{
lean_object* v_v_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_367_; 
v_v_347_ = lean_ctor_get(v_x_334_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_367_ == 0)
{
v___x_349_ = v_x_334_;
v_isShared_350_ = v_isSharedCheck_367_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_v_347_);
lean_dec(v_x_334_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_367_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___y_352_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(1024u);
v___x_364_ = lean_nat_dec_le(v___x_363_, v_prec_335_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_352_ = v___x_365_;
goto v___jp_351_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_352_ = v___x_366_;
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_353_ = ((lean_object*)(l_ArithmeticPrototype_instReprIR_repr___closed__4));
v___x_354_ = l_Nat_reprFast(v_v_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 3);
lean_ctor_set(v___x_349_, 0, v___x_354_);
v___x_356_ = v___x_349_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_362_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
lean_inc(v___y_352_);
v___x_358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_358_, 0, v___y_352_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = 0;
v___x_360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*1, v___x_359_);
v___x_361_ = l_Repr_addAppParen(v___x_360_, v_prec_335_);
return v___x_361_;
}
}
}
}
case 2:
{
lean_object* v_a_368_; lean_object* v_b_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_392_; 
v_a_368_ = lean_ctor_get(v_x_334_, 0);
v_b_369_ = lean_ctor_get(v_x_334_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_392_ == 0)
{
v___x_371_ = v_x_334_;
v_isShared_372_ = v_isSharedCheck_392_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_b_369_);
lean_inc(v_a_368_);
lean_dec(v_x_334_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_392_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___y_375_; uint8_t v___x_389_; 
v___x_373_ = lean_unsigned_to_nat(1024u);
v___x_389_ = lean_nat_dec_le(v___x_373_, v_prec_335_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_375_ = v___x_390_;
goto v___jp_374_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_375_ = v___x_391_;
goto v___jp_374_;
}
v___jp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_376_ = lean_box(1);
v___x_377_ = ((lean_object*)(l_ArithmeticPrototype_instReprIR_repr___closed__7));
v___x_378_ = l_ArithmeticPrototype_instReprIR_repr(v_a_368_, v___x_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 5);
lean_ctor_set(v___x_371_, 1, v___x_378_);
lean_ctor_set(v___x_371_, 0, v___x_377_);
v___x_380_ = v___x_371_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_388_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_376_);
v___x_382_ = l_ArithmeticPrototype_instReprIR_repr(v_b_369_, v___x_373_);
v___x_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
lean_inc(v___y_375_);
v___x_384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_384_, 0, v___y_375_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = 0;
v___x_386_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*1, v___x_385_);
v___x_387_ = l_Repr_addAppParen(v___x_386_, v_prec_335_);
return v___x_387_;
}
}
}
}
default: 
{
lean_object* v_a_393_; lean_object* v_b_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_417_; 
v_a_393_ = lean_ctor_get(v_x_334_, 0);
v_b_394_ = lean_ctor_get(v_x_334_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_417_ == 0)
{
v___x_396_ = v_x_334_;
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_b_394_);
lean_inc(v_a_393_);
lean_dec(v_x_334_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___y_400_; uint8_t v___x_414_; 
v___x_398_ = lean_unsigned_to_nat(1024u);
v___x_414_ = lean_nat_dec_le(v___x_398_, v_prec_335_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__2, &l_ArithmeticPrototype_instReprSource_repr___closed__2_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__2);
v___y_400_ = v___x_415_;
goto v___jp_399_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_obj_once(&l_ArithmeticPrototype_instReprSource_repr___closed__3, &l_ArithmeticPrototype_instReprSource_repr___closed__3_once, _init_l_ArithmeticPrototype_instReprSource_repr___closed__3);
v___y_400_ = v___x_416_;
goto v___jp_399_;
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_401_ = lean_box(1);
v___x_402_ = ((lean_object*)(l_ArithmeticPrototype_instReprIR_repr___closed__10));
v___x_403_ = l_ArithmeticPrototype_instReprIR_repr(v_a_393_, v___x_398_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 5);
lean_ctor_set(v___x_396_, 1, v___x_403_);
lean_ctor_set(v___x_396_, 0, v___x_402_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_413_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_401_);
v___x_407_ = l_ArithmeticPrototype_instReprIR_repr(v_b_394_, v___x_398_);
v___x_408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_inc(v___y_400_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___y_400_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = 0;
v___x_411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v___x_410_);
v___x_412_ = l_Repr_addAppParen(v___x_411_, v_prec_335_);
return v___x_412_;
}
}
}
}
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_338_ = ((lean_object*)(l_ArithmeticPrototype_instReprIR_repr___closed__1));
lean_inc(v___y_337_);
v___x_339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_339_, 0, v___y_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_340_);
v___x_342_ = l_Repr_addAppParen(v___x_341_, v_prec_335_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprIR_repr___boxed(lean_object* v_x_418_, lean_object* v_prec_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_ArithmeticPrototype_instReprIR_repr(v_x_418_, v_prec_419_);
lean_dec(v_prec_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalSource(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
switch(lean_obj_tag(v_x_423_))
{
case 0:
{
lean_inc(v_x_424_);
return v_x_424_;
}
case 1:
{
lean_object* v_v_425_; 
v_v_425_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_v_425_);
return v_v_425_;
}
case 2:
{
lean_object* v_a_426_; lean_object* v_b_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_426_ = lean_ctor_get(v_x_423_, 0);
v_b_427_ = lean_ctor_get(v_x_423_, 1);
v___x_428_ = l_ArithmeticPrototype_evalSource(v_a_426_, v_x_424_);
v___x_429_ = l_ArithmeticPrototype_evalSource(v_b_427_, v_x_424_);
v___x_430_ = l_ArithmeticPrototype_add8(v___x_428_, v___x_429_);
lean_dec(v___x_429_);
lean_dec(v___x_428_);
return v___x_430_;
}
default: 
{
lean_object* v_a_431_; lean_object* v_b_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_a_431_ = lean_ctor_get(v_x_423_, 0);
v_b_432_ = lean_ctor_get(v_x_423_, 1);
v___x_433_ = l_ArithmeticPrototype_evalSource(v_a_431_, v_x_424_);
v___x_434_ = l_ArithmeticPrototype_evalSource(v_b_432_, v_x_424_);
v___x_435_ = l_ArithmeticPrototype_mul8(v___x_433_, v___x_434_);
lean_dec(v___x_434_);
lean_dec(v___x_433_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalSource___boxed(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_ArithmeticPrototype_evalSource(v_x_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec(v_x_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalIR(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
switch(lean_obj_tag(v_x_439_))
{
case 0:
{
lean_inc(v_x_440_);
return v_x_440_;
}
case 1:
{
lean_object* v_v_441_; 
v_v_441_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_v_441_);
return v_v_441_;
}
case 2:
{
lean_object* v_a_442_; lean_object* v_b_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_a_442_ = lean_ctor_get(v_x_439_, 0);
v_b_443_ = lean_ctor_get(v_x_439_, 1);
v___x_444_ = l_ArithmeticPrototype_evalIR(v_a_442_, v_x_440_);
v___x_445_ = l_ArithmeticPrototype_evalIR(v_b_443_, v_x_440_);
v___x_446_ = l_ArithmeticPrototype_add8(v___x_444_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_444_);
return v___x_446_;
}
default: 
{
lean_object* v_a_447_; lean_object* v_b_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_447_ = lean_ctor_get(v_x_439_, 0);
v_b_448_ = lean_ctor_get(v_x_439_, 1);
v___x_449_ = l_ArithmeticPrototype_evalIR(v_a_447_, v_x_440_);
v___x_450_ = l_ArithmeticPrototype_evalIR(v_b_448_, v_x_440_);
v___x_451_ = l_ArithmeticPrototype_mul8(v___x_449_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v___x_449_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_evalIR___boxed(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_ArithmeticPrototype_evalIR(v_x_452_, v_x_453_);
lean_dec(v_x_453_);
lean_dec(v_x_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_decode(lean_object* v_x_455_){
_start:
{
switch(lean_obj_tag(v_x_455_))
{
case 0:
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
case 1:
{
lean_object* v_v_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_v_457_ = lean_ctor_get(v_x_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v_x_455_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_v_457_);
lean_dec(v_x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_v_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
case 2:
{
lean_object* v_a_465_; lean_object* v_b_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_a_465_ = lean_ctor_get(v_x_455_, 0);
v_b_466_ = lean_ctor_get(v_x_455_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v_x_455_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_b_466_);
lean_inc(v_a_465_);
lean_dec(v_x_455_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = l_ArithmeticPrototype_decode(v_a_465_);
v___x_471_ = l_ArithmeticPrototype_decode(v_b_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_471_);
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
default: 
{
lean_object* v_a_476_; lean_object* v_b_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
v_a_476_ = lean_ctor_get(v_x_455_, 0);
v_b_477_ = lean_ctor_get(v_x_455_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_486_ == 0)
{
v___x_479_ = v_x_455_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_b_477_);
lean_inc(v_a_476_);
lean_dec(v_x_455_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_481_ = l_ArithmeticPrototype_decode(v_a_476_);
v___x_482_ = l_ArithmeticPrototype_decode(v_b_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_482_);
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_construct(lean_object* v_x_487_){
_start:
{
switch(lean_obj_tag(v_x_487_))
{
case 0:
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
return v___x_488_;
}
case 1:
{
lean_object* v_v_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_v_489_ = lean_ctor_get(v_x_487_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v_x_487_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_v_489_);
lean_dec(v_x_487_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_v_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
case 2:
{
lean_object* v_a_497_; lean_object* v_b_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v_a_497_ = lean_ctor_get(v_x_487_, 0);
v_b_498_ = lean_ctor_get(v_x_487_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_507_ == 0)
{
v___x_500_ = v_x_487_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_b_498_);
lean_inc(v_a_497_);
lean_dec(v_x_487_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = l_ArithmeticPrototype_construct(v_a_497_);
v___x_503_ = l_ArithmeticPrototype_construct(v_b_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_503_);
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
default: 
{
lean_object* v_a_508_; lean_object* v_b_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_518_; 
v_a_508_ = lean_ctor_get(v_x_487_, 0);
v_b_509_ = lean_ctor_get(v_x_487_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_518_ == 0)
{
v___x_511_ = v_x_487_;
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_b_509_);
lean_inc(v_a_508_);
lean_dec(v_x_487_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = l_ArithmeticPrototype_construct(v_a_508_);
v___x_514_ = l_ArithmeticPrototype_construct(v_b_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_514_);
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprIR_repr_match__1_splitter___redArg(lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_, lean_object* v_h__3_522_, lean_object* v_h__4_523_){
_start:
{
switch(lean_obj_tag(v_x_519_))
{
case 0:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_h__4_523_);
lean_dec(v_h__3_522_);
lean_dec(v_h__2_521_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_apply_1(v_h__1_520_, v___x_524_);
return v___x_525_;
}
case 1:
{
lean_object* v_v_526_; lean_object* v___x_527_; 
lean_dec(v_h__4_523_);
lean_dec(v_h__3_522_);
lean_dec(v_h__1_520_);
v_v_526_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_v_526_);
lean_dec_ref_known(v_x_519_, 1);
v___x_527_ = lean_apply_1(v_h__2_521_, v_v_526_);
return v___x_527_;
}
case 2:
{
lean_object* v_a_528_; lean_object* v_b_529_; lean_object* v___x_530_; 
lean_dec(v_h__4_523_);
lean_dec(v_h__2_521_);
lean_dec(v_h__1_520_);
v_a_528_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_a_528_);
v_b_529_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_b_529_);
lean_dec_ref_known(v_x_519_, 2);
v___x_530_ = lean_apply_2(v_h__3_522_, v_a_528_, v_b_529_);
return v___x_530_;
}
default: 
{
lean_object* v_a_531_; lean_object* v_b_532_; lean_object* v___x_533_; 
lean_dec(v_h__3_522_);
lean_dec(v_h__2_521_);
lean_dec(v_h__1_520_);
v_a_531_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_a_531_);
v_b_532_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_b_532_);
lean_dec_ref_known(v_x_519_, 2);
v___x_533_ = lean_apply_2(v_h__4_523_, v_a_531_, v_b_532_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprIR_repr_match__1_splitter(lean_object* v_motive_534_, lean_object* v_x_535_, lean_object* v_h__1_536_, lean_object* v_h__2_537_, lean_object* v_h__3_538_, lean_object* v_h__4_539_){
_start:
{
switch(lean_obj_tag(v_x_535_))
{
case 0:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v_h__4_539_);
lean_dec(v_h__3_538_);
lean_dec(v_h__2_537_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_apply_1(v_h__1_536_, v___x_540_);
return v___x_541_;
}
case 1:
{
lean_object* v_v_542_; lean_object* v___x_543_; 
lean_dec(v_h__4_539_);
lean_dec(v_h__3_538_);
lean_dec(v_h__1_536_);
v_v_542_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_v_542_);
lean_dec_ref_known(v_x_535_, 1);
v___x_543_ = lean_apply_1(v_h__2_537_, v_v_542_);
return v___x_543_;
}
case 2:
{
lean_object* v_a_544_; lean_object* v_b_545_; lean_object* v___x_546_; 
lean_dec(v_h__4_539_);
lean_dec(v_h__2_537_);
lean_dec(v_h__1_536_);
v_a_544_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_a_544_);
v_b_545_ = lean_ctor_get(v_x_535_, 1);
lean_inc(v_b_545_);
lean_dec_ref_known(v_x_535_, 2);
v___x_546_ = lean_apply_2(v_h__3_538_, v_a_544_, v_b_545_);
return v___x_546_;
}
default: 
{
lean_object* v_a_547_; lean_object* v_b_548_; lean_object* v___x_549_; 
lean_dec(v_h__3_538_);
lean_dec(v_h__2_537_);
lean_dec(v_h__1_536_);
v_a_547_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_a_547_);
v_b_548_ = lean_ctor_get(v_x_535_, 1);
lean_inc(v_b_548_);
lean_dec_ref_known(v_x_535_, 2);
v___x_549_ = lean_apply_2(v_h__4_539_, v_a_547_, v_b_548_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalSource_match__1_splitter___redArg(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_, lean_object* v_h__3_554_, lean_object* v_h__4_555_){
_start:
{
switch(lean_obj_tag(v_x_550_))
{
case 0:
{
lean_object* v___x_556_; 
lean_dec(v_h__4_555_);
lean_dec(v_h__3_554_);
lean_dec(v_h__2_553_);
v___x_556_ = lean_apply_1(v_h__1_552_, v_x_551_);
return v___x_556_;
}
case 1:
{
lean_object* v_v_557_; lean_object* v___x_558_; 
lean_dec(v_h__4_555_);
lean_dec(v_h__3_554_);
lean_dec(v_h__1_552_);
v_v_557_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_v_557_);
lean_dec_ref_known(v_x_550_, 1);
v___x_558_ = lean_apply_2(v_h__2_553_, v_v_557_, v_x_551_);
return v___x_558_;
}
case 2:
{
lean_object* v_a_559_; lean_object* v_b_560_; lean_object* v___x_561_; 
lean_dec(v_h__4_555_);
lean_dec(v_h__2_553_);
lean_dec(v_h__1_552_);
v_a_559_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_a_559_);
v_b_560_ = lean_ctor_get(v_x_550_, 1);
lean_inc(v_b_560_);
lean_dec_ref_known(v_x_550_, 2);
v___x_561_ = lean_apply_3(v_h__3_554_, v_a_559_, v_b_560_, v_x_551_);
return v___x_561_;
}
default: 
{
lean_object* v_a_562_; lean_object* v_b_563_; lean_object* v___x_564_; 
lean_dec(v_h__3_554_);
lean_dec(v_h__2_553_);
lean_dec(v_h__1_552_);
v_a_562_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_a_562_);
v_b_563_ = lean_ctor_get(v_x_550_, 1);
lean_inc(v_b_563_);
lean_dec_ref_known(v_x_550_, 2);
v___x_564_ = lean_apply_3(v_h__4_555_, v_a_562_, v_b_563_, v_x_551_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalSource_match__1_splitter(lean_object* v_motive_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_, lean_object* v_h__3_570_, lean_object* v_h__4_571_){
_start:
{
switch(lean_obj_tag(v_x_566_))
{
case 0:
{
lean_object* v___x_572_; 
lean_dec(v_h__4_571_);
lean_dec(v_h__3_570_);
lean_dec(v_h__2_569_);
v___x_572_ = lean_apply_1(v_h__1_568_, v_x_567_);
return v___x_572_;
}
case 1:
{
lean_object* v_v_573_; lean_object* v___x_574_; 
lean_dec(v_h__4_571_);
lean_dec(v_h__3_570_);
lean_dec(v_h__1_568_);
v_v_573_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_v_573_);
lean_dec_ref_known(v_x_566_, 1);
v___x_574_ = lean_apply_2(v_h__2_569_, v_v_573_, v_x_567_);
return v___x_574_;
}
case 2:
{
lean_object* v_a_575_; lean_object* v_b_576_; lean_object* v___x_577_; 
lean_dec(v_h__4_571_);
lean_dec(v_h__2_569_);
lean_dec(v_h__1_568_);
v_a_575_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_a_575_);
v_b_576_ = lean_ctor_get(v_x_566_, 1);
lean_inc(v_b_576_);
lean_dec_ref_known(v_x_566_, 2);
v___x_577_ = lean_apply_3(v_h__3_570_, v_a_575_, v_b_576_, v_x_567_);
return v___x_577_;
}
default: 
{
lean_object* v_a_578_; lean_object* v_b_579_; lean_object* v___x_580_; 
lean_dec(v_h__3_570_);
lean_dec(v_h__2_569_);
lean_dec(v_h__1_568_);
v_a_578_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_a_578_);
v_b_579_ = lean_ctor_get(v_x_566_, 1);
lean_inc(v_b_579_);
lean_dec_ref_known(v_x_566_, 2);
v___x_580_ = lean_apply_3(v_h__4_571_, v_a_578_, v_b_579_, v_x_567_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalIR_match__1_splitter___redArg(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_, lean_object* v_h__3_585_, lean_object* v_h__4_586_){
_start:
{
switch(lean_obj_tag(v_x_581_))
{
case 0:
{
lean_object* v___x_587_; 
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
v___x_587_ = lean_apply_1(v_h__1_583_, v_x_582_);
return v___x_587_;
}
case 1:
{
lean_object* v_v_588_; lean_object* v___x_589_; 
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__1_583_);
v_v_588_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_v_588_);
lean_dec_ref_known(v_x_581_, 1);
v___x_589_ = lean_apply_2(v_h__2_584_, v_v_588_, v_x_582_);
return v___x_589_;
}
case 2:
{
lean_object* v_a_590_; lean_object* v_b_591_; lean_object* v___x_592_; 
lean_dec(v_h__4_586_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v_a_590_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_590_);
v_b_591_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_b_591_);
lean_dec_ref_known(v_x_581_, 2);
v___x_592_ = lean_apply_3(v_h__3_585_, v_a_590_, v_b_591_, v_x_582_);
return v___x_592_;
}
default: 
{
lean_object* v_a_593_; lean_object* v_b_594_; lean_object* v___x_595_; 
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v_a_593_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_a_593_);
v_b_594_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_b_594_);
lean_dec_ref_known(v_x_581_, 2);
v___x_595_ = lean_apply_3(v_h__4_586_, v_a_593_, v_b_594_, v_x_582_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_evalIR_match__1_splitter(lean_object* v_motive_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_h__1_599_, lean_object* v_h__2_600_, lean_object* v_h__3_601_, lean_object* v_h__4_602_){
_start:
{
switch(lean_obj_tag(v_x_597_))
{
case 0:
{
lean_object* v___x_603_; 
lean_dec(v_h__4_602_);
lean_dec(v_h__3_601_);
lean_dec(v_h__2_600_);
v___x_603_ = lean_apply_1(v_h__1_599_, v_x_598_);
return v___x_603_;
}
case 1:
{
lean_object* v_v_604_; lean_object* v___x_605_; 
lean_dec(v_h__4_602_);
lean_dec(v_h__3_601_);
lean_dec(v_h__1_599_);
v_v_604_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_v_604_);
lean_dec_ref_known(v_x_597_, 1);
v___x_605_ = lean_apply_2(v_h__2_600_, v_v_604_, v_x_598_);
return v___x_605_;
}
case 2:
{
lean_object* v_a_606_; lean_object* v_b_607_; lean_object* v___x_608_; 
lean_dec(v_h__4_602_);
lean_dec(v_h__2_600_);
lean_dec(v_h__1_599_);
v_a_606_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_a_606_);
v_b_607_ = lean_ctor_get(v_x_597_, 1);
lean_inc(v_b_607_);
lean_dec_ref_known(v_x_597_, 2);
v___x_608_ = lean_apply_3(v_h__3_601_, v_a_606_, v_b_607_, v_x_598_);
return v___x_608_;
}
default: 
{
lean_object* v_a_609_; lean_object* v_b_610_; lean_object* v___x_611_; 
lean_dec(v_h__3_601_);
lean_dec(v_h__2_600_);
lean_dec(v_h__1_599_);
v_a_609_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_a_609_);
v_b_610_ = lean_ctor_get(v_x_597_, 1);
lean_inc(v_b_610_);
lean_dec_ref_known(v_x_597_, 2);
v___x_611_ = lean_apply_3(v_h__4_602_, v_a_609_, v_b_610_, v_x_598_);
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprSource_repr_match__1_splitter___redArg(lean_object* v_x_612_, lean_object* v_h__1_613_, lean_object* v_h__2_614_, lean_object* v_h__3_615_, lean_object* v_h__4_616_){
_start:
{
switch(lean_obj_tag(v_x_612_))
{
case 0:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v_h__4_616_);
lean_dec(v_h__3_615_);
lean_dec(v_h__2_614_);
v___x_617_ = lean_box(0);
v___x_618_ = lean_apply_1(v_h__1_613_, v___x_617_);
return v___x_618_;
}
case 1:
{
lean_object* v_v_619_; lean_object* v___x_620_; 
lean_dec(v_h__4_616_);
lean_dec(v_h__3_615_);
lean_dec(v_h__1_613_);
v_v_619_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_v_619_);
lean_dec_ref_known(v_x_612_, 1);
v___x_620_ = lean_apply_1(v_h__2_614_, v_v_619_);
return v___x_620_;
}
case 2:
{
lean_object* v_a_621_; lean_object* v_b_622_; lean_object* v___x_623_; 
lean_dec(v_h__4_616_);
lean_dec(v_h__2_614_);
lean_dec(v_h__1_613_);
v_a_621_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_a_621_);
v_b_622_ = lean_ctor_get(v_x_612_, 1);
lean_inc(v_b_622_);
lean_dec_ref_known(v_x_612_, 2);
v___x_623_ = lean_apply_2(v_h__3_615_, v_a_621_, v_b_622_);
return v___x_623_;
}
default: 
{
lean_object* v_a_624_; lean_object* v_b_625_; lean_object* v___x_626_; 
lean_dec(v_h__3_615_);
lean_dec(v_h__2_614_);
lean_dec(v_h__1_613_);
v_a_624_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_a_624_);
v_b_625_ = lean_ctor_get(v_x_612_, 1);
lean_inc(v_b_625_);
lean_dec_ref_known(v_x_612_, 2);
v___x_626_ = lean_apply_2(v_h__4_616_, v_a_624_, v_b_625_);
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_ArithmeticModel_0__ArithmeticPrototype_instReprSource_repr_match__1_splitter(lean_object* v_motive_627_, lean_object* v_x_628_, lean_object* v_h__1_629_, lean_object* v_h__2_630_, lean_object* v_h__3_631_, lean_object* v_h__4_632_){
_start:
{
switch(lean_obj_tag(v_x_628_))
{
case 0:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v_h__4_632_);
lean_dec(v_h__3_631_);
lean_dec(v_h__2_630_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_apply_1(v_h__1_629_, v___x_633_);
return v___x_634_;
}
case 1:
{
lean_object* v_v_635_; lean_object* v___x_636_; 
lean_dec(v_h__4_632_);
lean_dec(v_h__3_631_);
lean_dec(v_h__1_629_);
v_v_635_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_v_635_);
lean_dec_ref_known(v_x_628_, 1);
v___x_636_ = lean_apply_1(v_h__2_630_, v_v_635_);
return v___x_636_;
}
case 2:
{
lean_object* v_a_637_; lean_object* v_b_638_; lean_object* v___x_639_; 
lean_dec(v_h__4_632_);
lean_dec(v_h__2_630_);
lean_dec(v_h__1_629_);
v_a_637_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_a_637_);
v_b_638_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_b_638_);
lean_dec_ref_known(v_x_628_, 2);
v___x_639_ = lean_apply_2(v_h__3_631_, v_a_637_, v_b_638_);
return v___x_639_;
}
default: 
{
lean_object* v_a_640_; lean_object* v_b_641_; lean_object* v___x_642_; 
lean_dec(v_h__3_631_);
lean_dec(v_h__2_630_);
lean_dec(v_h__1_629_);
v_a_640_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_a_640_);
v_b_641_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_b_641_);
lean_dec_ref_known(v_x_628_, 2);
v___x_642_ = lean_apply_2(v_h__4_632_, v_a_640_, v_b_641_);
return v___x_642_;
}
}
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_checkPosthoc(lean_object* v_s_643_, lean_object* v_p_644_){
_start:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = l_ArithmeticPrototype_decode(v_p_644_);
v___x_646_ = l_ArithmeticPrototype_instDecidableEqSource_decEq(v___x_645_, v_s_643_);
lean_dec(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_checkPosthoc___boxed(lean_object* v_s_647_, lean_object* v_p_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_ArithmeticPrototype_checkPosthoc(v_s_647_, v_p_648_);
lean_dec(v_s_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00ArithmeticPrototype_instReprRow_repr_spec__0(lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_nat_to_int(v_a_651_);
return v___x_652_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(9u);
v___x_667_ = lean_nat_to_int(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(5u);
v___x_675_ = lean_nat_to_int(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(10u);
v___x_683_ = lean_nat_to_int(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__0));
v___x_686_ = lean_string_length(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__19, &l_ArithmeticPrototype_instReprRow_repr___redArg___closed__19_once, _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__19);
v___x_688_ = lean_nat_to_int(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprRow_repr___redArg(lean_object* v_x_693_){
_start:
{
lean_object* v_input_694_; lean_object* v_a_695_; lean_object* v_b_696_; lean_object* v_output_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_input_694_ = lean_ctor_get(v_x_693_, 0);
lean_inc(v_input_694_);
v_a_695_ = lean_ctor_get(v_x_693_, 1);
lean_inc(v_a_695_);
v_b_696_ = lean_ctor_get(v_x_693_, 2);
lean_inc(v_b_696_);
v_output_697_ = lean_ctor_get(v_x_693_, 3);
lean_inc(v_output_697_);
lean_dec_ref(v_x_693_);
v___x_698_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__5));
v___x_699_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__6));
v___x_700_ = lean_obj_once(&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__7, &l_ArithmeticPrototype_instReprRow_repr___redArg___closed__7_once, _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__7);
v___x_701_ = l_Nat_reprFast(v_input_694_);
v___x_702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
v___x_703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_700_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = 0;
v___x_705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_704_);
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_699_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__9));
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_box(1);
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__11));
v___x_712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_698_);
v___x_714_ = lean_obj_once(&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__12, &l_ArithmeticPrototype_instReprRow_repr___redArg___closed__12_once, _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__12);
v___x_715_ = l_Nat_reprFast(v_a_695_);
v___x_716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_714_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v___x_704_);
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_713_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_707_);
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_709_);
v___x_722_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__14));
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_698_);
v___x_725_ = l_Nat_reprFast(v_b_696_);
v___x_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_714_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*1, v___x_704_);
v___x_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_724_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_707_);
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_709_);
v___x_732_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__16));
v___x_733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_698_);
v___x_735_ = lean_obj_once(&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__17, &l_ArithmeticPrototype_instReprRow_repr___redArg___closed__17_once, _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__17);
v___x_736_ = l_Nat_reprFast(v_output_697_);
v___x_737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
v___x_738_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_735_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*1, v___x_704_);
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_734_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_ArithmeticPrototype_instReprRow_repr___redArg___closed__20, &l_ArithmeticPrototype_instReprRow_repr___redArg___closed__20_once, _init_l_ArithmeticPrototype_instReprRow_repr___redArg___closed__20);
v___x_742_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__21));
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_740_);
v___x_744_ = ((lean_object*)(l_ArithmeticPrototype_instReprRow_repr___redArg___closed__22));
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_741_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_704_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprRow_repr(lean_object* v_x_748_, lean_object* v_prec_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_ArithmeticPrototype_instReprRow_repr___redArg(v_x_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_instReprRow_repr___boxed(lean_object* v_x_751_, lean_object* v_prec_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_ArithmeticPrototype_instReprRow_repr(v_x_751_, v_prec_752_);
lean_dec(v_prec_752_);
return v_res_753_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instInhabitedRow___closed__0(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(256u);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_nat_mod(v___x_757_, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instInhabitedRow___closed__1(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_obj_once(&l_ArithmeticPrototype_instInhabitedRow___closed__0, &l_ArithmeticPrototype_instInhabitedRow___closed__0_once, _init_l_ArithmeticPrototype_instInhabitedRow___closed__0);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
lean_ctor_set(v___x_761_, 2, v___x_759_);
lean_ctor_set(v___x_761_, 3, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l_ArithmeticPrototype_instInhabitedRow(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_ArithmeticPrototype_instInhabitedRow___closed__1, &l_ArithmeticPrototype_instInhabitedRow___closed__1_once, _init_l_ArithmeticPrototype_instInhabitedRow___closed__1);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateA(lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(3u);
v___x_765_ = l_ArithmeticPrototype_add8(v_x_763_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateA___boxed(lean_object* v_x_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_ArithmeticPrototype_intermediateA(v_x_766_);
lean_dec(v_x_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateB(lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = l_ArithmeticPrototype_intermediateA(v_x_768_);
v___x_770_ = lean_unsigned_to_nat(5u);
v___x_771_ = l_ArithmeticPrototype_mul8(v___x_769_, v___x_770_);
lean_dec(v___x_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_intermediateB___boxed(lean_object* v_x_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_ArithmeticPrototype_intermediateB(v_x_772_);
lean_dec(v_x_772_);
return v_res_773_;
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_checkInstrumented___lam__0(lean_object* v___x_774_, lean_object* v_rows_775_, lean_object* v_s_776_, lean_object* v_p_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; lean_object* v_input_780_; lean_object* v_a_781_; lean_object* v_b_782_; lean_object* v_output_783_; uint8_t v___x_784_; 
v___x_779_ = lean_array_get_borrowed(v___x_774_, v_rows_775_, v_a_778_);
v_input_780_ = lean_ctor_get(v___x_779_, 0);
v_a_781_ = lean_ctor_get(v___x_779_, 1);
v_b_782_ = lean_ctor_get(v___x_779_, 2);
v_output_783_ = lean_ctor_get(v___x_779_, 3);
v___x_784_ = lean_nat_dec_eq(v_input_780_, v_a_778_);
if (v___x_784_ == 0)
{
return v___x_784_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = l_ArithmeticPrototype_intermediateA(v_a_778_);
v___x_786_ = lean_nat_dec_eq(v_a_781_, v___x_785_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
return v___x_786_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = l_ArithmeticPrototype_intermediateB(v_a_778_);
v___x_788_ = lean_nat_dec_eq(v_b_782_, v___x_787_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
return v___x_788_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = l_ArithmeticPrototype_evalSource(v_s_776_, v_a_778_);
v___x_790_ = lean_nat_dec_eq(v_output_783_, v___x_789_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
return v___x_790_;
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = l_ArithmeticPrototype_evalIR(v_p_777_, v_a_778_);
v___x_792_ = lean_nat_dec_eq(v_output_783_, v___x_791_);
lean_dec(v___x_791_);
return v___x_792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_checkInstrumented___lam__0___boxed(lean_object* v___x_793_, lean_object* v_rows_794_, lean_object* v_s_795_, lean_object* v_p_796_, lean_object* v_a_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_ArithmeticPrototype_checkInstrumented___lam__0(v___x_793_, v_rows_794_, v_s_795_, v_p_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec(v_p_796_);
lean_dec(v_s_795_);
lean_dec_ref(v_rows_794_);
lean_dec_ref(v___x_793_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint8_t l_ArithmeticPrototype_checkInstrumented(lean_object* v_s_800_, lean_object* v_p_801_, lean_object* v_rows_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_array_get_size(v_rows_802_);
v___x_804_ = lean_unsigned_to_nat(256u);
v___x_805_ = lean_nat_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_dec_ref(v_rows_802_);
lean_dec(v_p_801_);
lean_dec(v_s_800_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___f_807_; uint8_t v___x_808_; 
v___x_806_ = l_ArithmeticPrototype_instInhabitedRow;
v___f_807_ = lean_alloc_closure((void*)(l_ArithmeticPrototype_checkInstrumented___lam__0___boxed), 5, 4);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_closure_set(v___f_807_, 1, v_rows_802_);
lean_closure_set(v___f_807_, 2, v_s_800_);
lean_closure_set(v___f_807_, 3, v_p_801_);
v___x_808_ = l_Nat_decidableForallFin___redArg(v___x_804_, v___f_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_ArithmeticPrototype_checkInstrumented___boxed(lean_object* v_s_809_, lean_object* v_p_810_, lean_object* v_rows_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_ArithmeticPrototype_checkInstrumented(v_s_809_, v_p_810_, v_rows_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_ArithmeticModel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ArithmeticPrototype_instInhabitedRow = _init_l_ArithmeticPrototype_instInhabitedRow();
lean_mark_persistent(l_ArithmeticPrototype_instInhabitedRow);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_ArithmeticModel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticModel(uint8_t builtin) {
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
res = runtime_initialize_ArithmeticModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_ArithmeticModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_ArithmeticModel(builtin);
}
#ifdef __cplusplus
}
#endif
