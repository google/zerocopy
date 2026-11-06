// Lean compiler output
// Module: CheckerMain
// Imports: public import Init public meta import Init public import Lean public import ArithmeticModel import all ArithmeticModel
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_ArithmeticPrototype_checkPosthoc(lean_object*, lean_object*);
lean_object* lean_get_stdin();
lean_object* lean_get_stdout();
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
static lean_once_cell_t l_NativeChecker_selectedSource___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__0;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__1;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__2;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__3;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__4;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__5;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__6;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__7;
static lean_once_cell_t l_NativeChecker_selectedSource___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedSource___closed__8;
LEAN_EXPORT lean_object* l_NativeChecker_selectedSource;
static lean_once_cell_t l_NativeChecker_selectedIR___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedIR___closed__0;
static lean_once_cell_t l_NativeChecker_selectedIR___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedIR___closed__1;
static lean_once_cell_t l_NativeChecker_selectedIR___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedIR___closed__2;
static lean_once_cell_t l_NativeChecker_selectedIR___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedIR___closed__3;
static lean_once_cell_t l_NativeChecker_selectedIR___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedIR___closed__4;
static lean_once_cell_t l_NativeChecker_selectedIR___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeChecker_selectedIR___closed__5;
LEAN_EXPORT lean_object* l_NativeChecker_selectedIR;
LEAN_EXPORT uint8_t l_NativeChecker_validate(lean_object*);
LEAN_EXPORT lean_object* l_NativeChecker_validate___boxed(lean_object*);
static const lean_string_object l_NativeChecker_parseIR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unsupported-IR-node"};
static const lean_object* l_NativeChecker_parseIR___closed__0 = (const lean_object*)&l_NativeChecker_parseIR___closed__0_value;
static const lean_ctor_object l_NativeChecker_parseIR___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_NativeChecker_parseIR___closed__0_value)}};
static const lean_object* l_NativeChecker_parseIR___closed__1 = (const lean_object*)&l_NativeChecker_parseIR___closed__1_value;
static const lean_string_object l_NativeChecker_parseIR___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "depth-limit"};
static const lean_object* l_NativeChecker_parseIR___closed__2 = (const lean_object*)&l_NativeChecker_parseIR___closed__2_value;
static const lean_ctor_object l_NativeChecker_parseIR___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_NativeChecker_parseIR___closed__2_value)}};
static const lean_object* l_NativeChecker_parseIR___closed__3 = (const lean_object*)&l_NativeChecker_parseIR___closed__3_value;
static const lean_string_object l_NativeChecker_parseIR___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l_NativeChecker_parseIR___closed__4 = (const lean_object*)&l_NativeChecker_parseIR___closed__4_value;
static const lean_string_object l_NativeChecker_parseIR___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imm"};
static const lean_object* l_NativeChecker_parseIR___closed__5 = (const lean_object*)&l_NativeChecker_parseIR___closed__5_value;
static const lean_string_object l_NativeChecker_parseIR___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_NativeChecker_parseIR___closed__6 = (const lean_object*)&l_NativeChecker_parseIR___closed__6_value;
static const lean_string_object l_NativeChecker_parseIR___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l_NativeChecker_parseIR___closed__7 = (const lean_object*)&l_NativeChecker_parseIR___closed__7_value;
static const lean_string_object l_NativeChecker_parseIR___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "literal-out-of-byte-range"};
static const lean_object* l_NativeChecker_parseIR___closed__8 = (const lean_object*)&l_NativeChecker_parseIR___closed__8_value;
static const lean_ctor_object l_NativeChecker_parseIR___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_NativeChecker_parseIR___closed__8_value)}};
static const lean_object* l_NativeChecker_parseIR___closed__9 = (const lean_object*)&l_NativeChecker_parseIR___closed__9_value;
static const lean_ctor_object l_NativeChecker_parseIR___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_NativeChecker_parseIR___closed__10 = (const lean_object*)&l_NativeChecker_parseIR___closed__10_value;
LEAN_EXPORT lean_object* l_NativeChecker_parseIR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeChecker_parseIR___boxed(lean_object*, lean_object*);
static const lean_string_object l_NativeChecker_answer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "accepted"};
static const lean_object* l_NativeChecker_answer___closed__0 = (const lean_object*)&l_NativeChecker_answer___closed__0_value;
static const lean_ctor_object l_NativeChecker_answer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_NativeChecker_answer___closed__1 = (const lean_object*)&l_NativeChecker_answer___closed__1_value;
static const lean_ctor_object l_NativeChecker_answer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_NativeChecker_answer___closed__0_value),((lean_object*)&l_NativeChecker_answer___closed__1_value)}};
static const lean_object* l_NativeChecker_answer___closed__2 = (const lean_object*)&l_NativeChecker_answer___closed__2_value;
static const lean_string_object l_NativeChecker_answer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reason"};
static const lean_object* l_NativeChecker_answer___closed__3 = (const lean_object*)&l_NativeChecker_answer___closed__3_value;
static const lean_string_object l_NativeChecker_answer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "checked-selected-statement"};
static const lean_object* l_NativeChecker_answer___closed__4 = (const lean_object*)&l_NativeChecker_answer___closed__4_value;
static const lean_ctor_object l_NativeChecker_answer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_NativeChecker_answer___closed__4_value)}};
static const lean_object* l_NativeChecker_answer___closed__5 = (const lean_object*)&l_NativeChecker_answer___closed__5_value;
static const lean_ctor_object l_NativeChecker_answer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_NativeChecker_answer___closed__3_value),((lean_object*)&l_NativeChecker_answer___closed__5_value)}};
static const lean_object* l_NativeChecker_answer___closed__6 = (const lean_object*)&l_NativeChecker_answer___closed__6_value;
static const lean_ctor_object l_NativeChecker_answer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeChecker_answer___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_NativeChecker_answer___closed__7 = (const lean_object*)&l_NativeChecker_answer___closed__7_value;
LEAN_EXPORT lean_object* l_NativeChecker_answer(lean_object*);
LEAN_EXPORT lean_object* l_NativeChecker_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeChecker_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* _lean_main();
LEAN_EXPORT lean_object* l_main___boxed(lean_object*);
static lean_object* _init_l_NativeChecker_selectedSource___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(256u);
v___x_2_ = lean_unsigned_to_nat(3u);
v___x_3_ = lean_nat_mod(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__0, &l_NativeChecker_selectedSource___closed__0_once, _init_l_NativeChecker_selectedSource___closed__0);
v___x_5_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__1, &l_NativeChecker_selectedSource___closed__1_once, _init_l_NativeChecker_selectedSource___closed__1);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_unsigned_to_nat(256u);
v___x_10_ = lean_unsigned_to_nat(5u);
v___x_11_ = lean_nat_mod(v___x_10_, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__3, &l_NativeChecker_selectedSource___closed__3_once, _init_l_NativeChecker_selectedSource___closed__3);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__5(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__4, &l_NativeChecker_selectedSource___closed__4_once, _init_l_NativeChecker_selectedSource___closed__4);
v___x_15_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__2, &l_NativeChecker_selectedSource___closed__2_once, _init_l_NativeChecker_selectedSource___closed__2);
v___x_16_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__6(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(256u);
v___x_18_ = lean_unsigned_to_nat(7u);
v___x_19_ = lean_nat_mod(v___x_18_, v___x_17_);
return v___x_19_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__7(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__6, &l_NativeChecker_selectedSource___closed__6_once, _init_l_NativeChecker_selectedSource___closed__6);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource___closed__8(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__7, &l_NativeChecker_selectedSource___closed__7_once, _init_l_NativeChecker_selectedSource___closed__7);
v___x_23_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__5, &l_NativeChecker_selectedSource___closed__5_once, _init_l_NativeChecker_selectedSource___closed__5);
v___x_24_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_NativeChecker_selectedSource(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__8, &l_NativeChecker_selectedSource___closed__8_once, _init_l_NativeChecker_selectedSource___closed__8);
return v___x_25_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__0, &l_NativeChecker_selectedSource___closed__0_once, _init_l_NativeChecker_selectedSource___closed__0);
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_NativeChecker_selectedIR___closed__0, &l_NativeChecker_selectedIR___closed__0_once, _init_l_NativeChecker_selectedIR___closed__0);
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR___closed__2(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__3, &l_NativeChecker_selectedSource___closed__3_once, _init_l_NativeChecker_selectedSource___closed__3);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_NativeChecker_selectedIR___closed__2, &l_NativeChecker_selectedIR___closed__2_once, _init_l_NativeChecker_selectedIR___closed__2);
v___x_34_ = lean_obj_once(&l_NativeChecker_selectedIR___closed__1, &l_NativeChecker_selectedIR___closed__1_once, _init_l_NativeChecker_selectedIR___closed__1);
v___x_35_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR___closed__4(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_NativeChecker_selectedSource___closed__6, &l_NativeChecker_selectedSource___closed__6_once, _init_l_NativeChecker_selectedSource___closed__6);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR___closed__5(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_obj_once(&l_NativeChecker_selectedIR___closed__4, &l_NativeChecker_selectedIR___closed__4_once, _init_l_NativeChecker_selectedIR___closed__4);
v___x_39_ = lean_obj_once(&l_NativeChecker_selectedIR___closed__3, &l_NativeChecker_selectedIR___closed__3_once, _init_l_NativeChecker_selectedIR___closed__3);
v___x_40_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_NativeChecker_selectedIR(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_NativeChecker_selectedIR___closed__5, &l_NativeChecker_selectedIR___closed__5_once, _init_l_NativeChecker_selectedIR___closed__5);
return v___x_41_;
}
}
LEAN_EXPORT uint8_t l_NativeChecker_validate(lean_object* v_p_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = l_NativeChecker_selectedSource;
v___x_44_ = l_ArithmeticPrototype_checkPosthoc(v___x_43_, v_p_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_NativeChecker_validate___boxed(lean_object* v_p_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_NativeChecker_validate(v_p_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_NativeChecker_parseIR(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_zero_67_; uint8_t v_isZero_68_; 
v_zero_67_ = lean_unsigned_to_nat(0u);
v_isZero_68_ = lean_nat_dec_eq(v_x_63_, v_zero_67_);
if (v_isZero_68_ == 1)
{
lean_object* v___x_69_; 
lean_dec(v_x_64_);
v___x_69_ = ((lean_object*)(l_NativeChecker_parseIR___closed__3));
return v___x_69_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Json_getArr_x3f(v_x_64_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_80_; 
v_a_79_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_70_, 1);
v___x_80_ = lean_array_to_list(v_a_79_);
if (lean_obj_tag(v___x_80_) == 1)
{
lean_object* v_head_81_; 
v_head_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_head_81_);
if (lean_obj_tag(v_head_81_) == 3)
{
lean_object* v_tail_82_; lean_object* v_s_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_169_; 
v_tail_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_tail_82_);
lean_dec_ref_known(v___x_80_, 2);
v_s_83_ = lean_ctor_get(v_head_81_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_head_81_);
if (v_isSharedCheck_169_ == 0)
{
v___x_85_ = v_head_81_;
v_isShared_86_ = v_isSharedCheck_169_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_s_83_);
lean_dec(v_head_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_169_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_NativeChecker_parseIR___closed__4));
v___x_88_ = lean_string_dec_eq(v_s_83_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l_NativeChecker_parseIR___closed__5));
v___x_90_ = lean_string_dec_eq(v_s_83_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v_one_91_; lean_object* v_n_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
lean_del_object(v___x_85_);
v_one_91_ = lean_unsigned_to_nat(1u);
v_n_92_ = lean_nat_sub(v_x_63_, v_one_91_);
v___x_93_ = ((lean_object*)(l_NativeChecker_parseIR___closed__6));
v___x_94_ = lean_string_dec_eq(v_s_83_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = ((lean_object*)(l_NativeChecker_parseIR___closed__7));
v___x_96_ = lean_string_dec_eq(v_s_83_, v___x_95_);
lean_dec_ref(v_s_83_);
if (v___x_96_ == 0)
{
lean_dec(v_n_92_);
lean_dec(v_tail_82_);
goto v___jp_65_;
}
else
{
if (lean_obj_tag(v_tail_82_) == 1)
{
lean_object* v_tail_97_; 
v_tail_97_ = lean_ctor_get(v_tail_82_, 1);
lean_inc(v_tail_97_);
if (lean_obj_tag(v_tail_97_) == 1)
{
lean_object* v_tail_98_; 
v_tail_98_ = lean_ctor_get(v_tail_97_, 1);
if (lean_obj_tag(v_tail_98_) == 0)
{
lean_object* v_head_99_; lean_object* v_head_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_118_; 
v_head_99_ = lean_ctor_get(v_tail_82_, 0);
lean_inc(v_head_99_);
lean_dec_ref_known(v_tail_82_, 2);
v_head_100_ = lean_ctor_get(v_tail_97_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_tail_97_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v_tail_97_, 1);
lean_dec(v_unused_119_);
v___x_102_ = v_tail_97_;
v_isShared_103_ = v_isSharedCheck_118_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_head_100_);
lean_dec(v_tail_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_118_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; 
v___x_104_ = l_NativeChecker_parseIR(v_n_92_, v_head_99_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_del_object(v___x_102_);
lean_dec(v_head_100_);
lean_dec(v_n_92_);
return v___x_104_;
}
else
{
lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = l_NativeChecker_parseIR(v_n_92_, v_head_100_);
lean_dec(v_n_92_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_dec(v_a_105_);
lean_del_object(v___x_102_);
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_117_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_117_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 3);
lean_ctor_set(v___x_102_, 1, v_a_107_);
lean_ctor_set(v___x_102_, 0, v_a_105_);
v___x_112_ = v___x_102_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_105_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_a_107_);
v___x_112_ = v_reuseFailAlloc_116_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_114_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_112_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_97_, 2);
lean_dec_ref_known(v_tail_82_, 2);
lean_dec(v_n_92_);
goto v___jp_65_;
}
}
else
{
lean_dec(v_tail_97_);
lean_dec_ref_known(v_tail_82_, 2);
lean_dec(v_n_92_);
goto v___jp_65_;
}
}
else
{
lean_dec(v_n_92_);
lean_dec(v_tail_82_);
goto v___jp_65_;
}
}
}
else
{
lean_dec_ref(v_s_83_);
if (lean_obj_tag(v_tail_82_) == 1)
{
lean_object* v_tail_120_; 
v_tail_120_ = lean_ctor_get(v_tail_82_, 1);
lean_inc(v_tail_120_);
if (lean_obj_tag(v_tail_120_) == 1)
{
lean_object* v_tail_121_; 
v_tail_121_ = lean_ctor_get(v_tail_120_, 1);
if (lean_obj_tag(v_tail_121_) == 0)
{
lean_object* v_head_122_; lean_object* v_head_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_141_; 
v_head_122_ = lean_ctor_get(v_tail_82_, 0);
lean_inc(v_head_122_);
lean_dec_ref_known(v_tail_82_, 2);
v_head_123_ = lean_ctor_get(v_tail_120_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_tail_120_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_tail_120_, 1);
lean_dec(v_unused_142_);
v___x_125_ = v_tail_120_;
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_head_123_);
lean_dec(v_tail_120_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; 
v___x_127_ = l_NativeChecker_parseIR(v_n_92_, v_head_122_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_del_object(v___x_125_);
lean_dec(v_head_123_);
lean_dec(v_n_92_);
return v___x_127_;
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
v___x_129_ = l_NativeChecker_parseIR(v_n_92_, v_head_123_);
lean_dec(v_n_92_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_dec(v_a_128_);
lean_del_object(v___x_125_);
return v___x_129_;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_140_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_140_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set_tag(v___x_125_, 2);
lean_ctor_set(v___x_125_, 1, v_a_130_);
lean_ctor_set(v___x_125_, 0, v_a_128_);
v___x_135_ = v___x_125_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_128_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_a_130_);
v___x_135_ = v_reuseFailAlloc_139_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_135_);
v___x_137_ = v___x_132_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_120_, 2);
lean_dec_ref_known(v_tail_82_, 2);
lean_dec(v_n_92_);
goto v___jp_65_;
}
}
else
{
lean_dec(v_tail_120_);
lean_dec_ref_known(v_tail_82_, 2);
lean_dec(v_n_92_);
goto v___jp_65_;
}
}
else
{
lean_dec(v_n_92_);
lean_dec(v_tail_82_);
goto v___jp_65_;
}
}
}
else
{
lean_dec_ref(v_s_83_);
if (lean_obj_tag(v_tail_82_) == 1)
{
lean_object* v_tail_143_; 
v_tail_143_ = lean_ctor_get(v_tail_82_, 1);
if (lean_obj_tag(v_tail_143_) == 0)
{
lean_object* v_head_144_; lean_object* v___x_145_; 
v_head_144_ = lean_ctor_get(v_tail_82_, 0);
lean_inc(v_head_144_);
lean_dec_ref_known(v_tail_82_, 2);
v___x_145_ = l_Lean_Json_getNat_x3f(v_head_144_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_del_object(v___x_85_);
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_167_; 
v_a_154_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_167_ == 0)
{
v___x_156_ = v___x_145_;
v_isShared_157_ = v_isSharedCheck_167_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_145_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_167_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(256u);
v___x_159_ = lean_nat_dec_lt(v_a_154_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_del_object(v___x_156_);
lean_dec(v_a_154_);
lean_del_object(v___x_85_);
v___x_160_ = ((lean_object*)(l_NativeChecker_parseIR___closed__9));
return v___x_160_;
}
else
{
lean_object* v___x_162_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 1);
lean_ctor_set(v___x_85_, 0, v_a_154_);
v___x_162_ = v___x_85_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_154_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_162_);
v___x_164_ = v___x_156_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_82_, 2);
lean_del_object(v___x_85_);
goto v___jp_65_;
}
}
else
{
lean_del_object(v___x_85_);
lean_dec(v_tail_82_);
goto v___jp_65_;
}
}
}
else
{
lean_del_object(v___x_85_);
lean_dec_ref(v_s_83_);
if (lean_obj_tag(v_tail_82_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_NativeChecker_parseIR___closed__10));
return v___x_168_;
}
else
{
lean_dec(v_tail_82_);
goto v___jp_65_;
}
}
}
}
else
{
lean_dec(v_head_81_);
lean_dec_ref_known(v___x_80_, 2);
goto v___jp_65_;
}
}
else
{
lean_dec(v___x_80_);
goto v___jp_65_;
}
}
}
v___jp_65_:
{
lean_object* v___x_66_; 
v___x_66_ = ((lean_object*)(l_NativeChecker_parseIR___closed__1));
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_NativeChecker_parseIR___boxed(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_NativeChecker_parseIR(v_x_170_, v_x_171_);
lean_dec(v_x_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_NativeChecker_answer(lean_object* v_line_189_){
_start:
{
lean_object* v_a_191_; lean_object* v___x_201_; 
v___x_201_ = l_Lean_Json_parse(v_line_189_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v_a_191_ = v_a_202_;
goto v___jp_190_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_a_203_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_201_, 1);
v___x_204_ = lean_unsigned_to_nat(32u);
v___x_205_ = l_NativeChecker_parseIR(v___x_204_, v_a_203_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v_a_191_ = v_a_206_;
goto v___jp_190_;
}
else
{
lean_object* v_a_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_a_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_205_, 1);
v___x_208_ = ((lean_object*)(l_NativeChecker_answer___closed__0));
v___x_209_ = l_NativeChecker_validate(v_a_207_);
v___x_210_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_210_, 0, v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_208_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = ((lean_object*)(l_NativeChecker_answer___closed__7));
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = l_Lean_Json_mkObj(v___x_213_);
lean_dec_ref_known(v___x_213_, 2);
v___x_215_ = l_Lean_Json_compress(v___x_214_);
return v___x_215_;
}
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_192_ = ((lean_object*)(l_NativeChecker_answer___closed__2));
v___x_193_ = ((lean_object*)(l_NativeChecker_answer___closed__3));
v___x_194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_194_, 0, v_a_191_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_192_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_Json_mkObj(v___x_198_);
lean_dec_ref_known(v___x_198_, 2);
v___x_200_ = l_Lean_Json_compress(v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_NativeChecker_loop(lean_object* v_input_216_, lean_object* v_output_217_){
_start:
{
lean_object* v_getLine_219_; lean_object* v___x_220_; 
v_getLine_219_ = lean_ctor_get(v_input_216_, 3);
lean_inc_ref(v_getLine_219_);
v___x_220_ = lean_apply_1(v_getLine_219_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_235_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_235_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_string_utf8_byte_size(v_a_221_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_del_object(v___x_223_);
v___x_228_ = l_NativeChecker_answer(v_a_221_);
lean_inc_ref(v_output_217_);
v___x_229_ = l_IO_FS_Stream_putStrLn(v_output_217_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_dec_ref_known(v___x_229_, 1);
goto _start;
}
else
{
lean_dec_ref(v_output_217_);
lean_dec_ref(v_input_216_);
return v___x_229_;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_a_221_);
lean_dec_ref(v_output_217_);
lean_dec_ref(v_input_216_);
v___x_231_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_231_);
v___x_233_ = v___x_223_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v_output_217_);
lean_dec_ref(v_input_216_);
v_a_236_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_220_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_220_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NativeChecker_loop___boxed(lean_object* v_input_244_, lean_object* v_output_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_NativeChecker_loop(v_input_244_, v_output_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* _lean_main(){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_get_stdin();
v___x_250_ = lean_get_stdout();
v___x_251_ = l_NativeChecker_loop(v___x_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = _lean_main();
return v_res_253_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean(uint8_t builtin);
lean_object* runtime_initialize_ArithmeticModel(uint8_t builtin);
lean_object* runtime_initialize_ArithmeticModel(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_CheckerMain(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_ArithmeticModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_ArithmeticModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_NativeChecker_selectedSource = _init_l_NativeChecker_selectedSource();
lean_mark_persistent(l_NativeChecker_selectedSource);
l_NativeChecker_selectedIR = _init_l_NativeChecker_selectedIR();
lean_mark_persistent(l_NativeChecker_selectedIR);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_CheckerMain(uint8_t builtin) {
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
lean_object* initialize_ArithmeticModel(uint8_t builtin);
lean_object* initialize_ArithmeticModel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CheckerMain(uint8_t builtin) {
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
res = initialize_ArithmeticModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_CheckerMain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_CheckerMain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_CheckerMain(builtin);
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    return _lean_main();
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = runtime_initialize_CheckerMain(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = 0;
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
