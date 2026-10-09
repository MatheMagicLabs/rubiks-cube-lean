// Lean compiler output
// Module: Cube.SquareThm
// Imports: Init Cube.Square
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
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___sqEntryOk_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* l_sqBfs;
static lean_object* l_farCheck___closed__0;
static uint64_t l_farCheck___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
extern uint8_t l_sqCheck;
LEAN_EXPORT uint8_t l_farCheck;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_farCheck___lam__0___boxed(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static uint64_t l_farCheck___closed__4;
uint64_t l_hashSt____x40_Cube_Model___hyg_48_(lean_object*);
extern lean_object* l_half;
static size_t l_farCheck___closed__6;
lean_object* l_parseAlg(lean_object*);
lean_object* l_eval(lean_object*);
LEAN_EXPORT lean_object* l_farWord;
LEAN_EXPORT uint8_t l_farCheck___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_sqCheck__true___nativeDecide__1__1;
static lean_object* l_farWord___closed__0;
LEAN_EXPORT uint8_t l_farCheck__true___nativeDecide__1__1;
static uint64_t l_farCheck___closed__3;
static lean_object* l_farCheck___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_farWord___closed__1;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static uint64_t l_farCheck___closed__2;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static uint8_t l_farCheck___closed__8;
lean_object* lean_array_get_size(lean_object*);
static uint64_t l_farCheck___closed__5;
size_t lean_usize_land(size_t, size_t);
static uint8_t _init_l_sqCheck__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_sqCheck;
return x_1;
}
}
static lean_object* _init_l_farWord___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("U2 R2 U2 R2 F2 R2 F2 L2 F2 U2 R2 F2 U2 B2 U2", 44, 44);
return x_1;
}
}
static lean_object* _init_l_farWord___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_farWord___closed__0;
x_2 = l_parseAlg(x_1);
return x_2;
}
}
static lean_object* _init_l_farWord() {
_start:
{
lean_object* x_1; 
x_1 = l_farWord___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_farCheck___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_half;
x_3 = l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_farCheck___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_farWord;
x_2 = l_eval(x_1);
return x_2;
}
}
static uint64_t _init_l_farCheck___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_farCheck___closed__0;
x_2 = l_hashSt____x40_Cube_Model___hyg_48_(x_1);
return x_2;
}
}
static uint64_t _init_l_farCheck___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 32;
x_2 = l_farCheck___closed__1;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_farCheck___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_farCheck___closed__2;
x_2 = l_farCheck___closed__1;
x_3 = lean_uint64_xor(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_farCheck___closed__4() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 16;
x_2 = l_farCheck___closed__3;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_farCheck___closed__5() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_farCheck___closed__4;
x_2 = l_farCheck___closed__3;
x_3 = lean_uint64_xor(x_2, x_1);
return x_3;
}
}
static size_t _init_l_farCheck___closed__6() {
_start:
{
uint64_t x_1; size_t x_2; 
x_1 = l_farCheck___closed__5;
x_2 = lean_uint64_to_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_farCheck___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_farWord;
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
static uint8_t _init_l_farCheck___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = l_farCheck___closed__7;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_farCheck() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_1 = l_sqBfs;
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = l_farWord;
x_4 = l_farCheck___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = l_farCheck___closed__6;
x_7 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_8 = 1;
x_9 = lean_usize_sub(x_7, x_8);
x_10 = lean_usize_land(x_6, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_dec_ref(x_2);
x_12 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___sqEntryOk_spec__0___redArg(x_4, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_alloc_closure((void*)(l_farCheck___lam__0___boxed), 1, 0);
x_19 = l_List_lengthTR___redArg(x_14);
lean_dec(x_14);
x_20 = lean_unsigned_to_nat(15u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
x_16 = x_21;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = l_farCheck___closed__8;
x_16 = x_22;
goto block_18;
}
block_18:
{
if (x_16 == 0)
{
lean_dec_ref(x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_List_all___redArg(x_3, x_15);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_farCheck___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_farCheck___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l_farCheck__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_farCheck;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Square(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_SquareThm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Square(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_sqCheck__true___nativeDecide__1__1 = _init_l_sqCheck__true___nativeDecide__1__1();
l_farWord___closed__0 = _init_l_farWord___closed__0();
lean_mark_persistent(l_farWord___closed__0);
l_farWord___closed__1 = _init_l_farWord___closed__1();
lean_mark_persistent(l_farWord___closed__1);
l_farWord = _init_l_farWord();
lean_mark_persistent(l_farWord);
l_farCheck___closed__0 = _init_l_farCheck___closed__0();
lean_mark_persistent(l_farCheck___closed__0);
l_farCheck___closed__1 = _init_l_farCheck___closed__1();
l_farCheck___closed__2 = _init_l_farCheck___closed__2();
l_farCheck___closed__3 = _init_l_farCheck___closed__3();
l_farCheck___closed__4 = _init_l_farCheck___closed__4();
l_farCheck___closed__5 = _init_l_farCheck___closed__5();
l_farCheck___closed__6 = _init_l_farCheck___closed__6();
l_farCheck___closed__7 = _init_l_farCheck___closed__7();
lean_mark_persistent(l_farCheck___closed__7);
l_farCheck___closed__8 = _init_l_farCheck___closed__8();
l_farCheck = _init_l_farCheck();
l_farCheck__true___nativeDecide__1__1 = _init_l_farCheck__true___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
