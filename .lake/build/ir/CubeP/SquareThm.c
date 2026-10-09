// Lean compiler output
// Module: CubeP.SquareThm
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
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___sqEntryOkW_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_farCheckW___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_farCheckW___boxed(lean_object*);
uint64_t l_hashSt____x40_Cube_Model___hyg_48_(lean_object*);
extern lean_object* l_half;
uint8_t l_sqCheckF(lean_object*);
lean_object* l_parseAlg(lean_object*);
lean_object* l_eval(lean_object*);
LEAN_EXPORT lean_object* l_farWord;
LEAN_EXPORT uint8_t l_sqCheck__true___nativeDecide__1__1;
lean_object* l_sqTableF(lean_object*);
LEAN_EXPORT uint8_t l_farCheck__true___nativeDecide__1__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_farCheckF(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_farCheckW(lean_object*);
LEAN_EXPORT lean_object* l_farCheckF___boxed(lean_object*);
LEAN_EXPORT lean_object* l_farCheckW___lam__0___boxed(lean_object*);
size_t lean_usize_land(size_t, size_t);
static uint8_t _init_l_sqCheck__true___nativeDecide__1__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = l_sqCheckF(x_1);
return x_2;
}
}
static lean_object* _init_l_farWord() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("U2 R2 U2 R2 F2 R2 F2 L2 F2 U2 R2 F2 U2 B2 U2", 44, 44);
x_2 = l_parseAlg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_farCheckW___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_half;
x_3 = l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_farCheckW(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_farWord;
x_4 = l_eval(x_3);
x_5 = lean_array_get_size(x_2);
x_6 = l_hashSt____x40_Cube_Model___hyg_48_(x_4);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_2, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___sqEntryOkW_spec__0___redArg(x_4, x_18);
lean_dec(x_18);
lean_dec_ref(x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_farCheckW___lam__0___boxed), 1, 0);
x_26 = l_List_lengthTR___redArg(x_21);
lean_dec(x_21);
x_27 = lean_unsigned_to_nat(15u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
x_23 = x_28;
goto block_25;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_List_lengthTR___redArg(x_3);
x_30 = lean_nat_dec_eq(x_29, x_27);
lean_dec(x_29);
x_23 = x_30;
goto block_25;
}
block_25:
{
if (x_23 == 0)
{
lean_dec_ref(x_22);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = l_List_all___redArg(x_3, x_22);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_farCheckW___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_farCheckW___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_farCheckW___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_farCheckW(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_farCheckF(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = l_sqTableF(x_2);
x_4 = l_farCheckW(x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_farCheckF___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_farCheckF(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l_farCheck__true___nativeDecide__1__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = l_farCheckF(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Square(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CubeP_SquareThm(uint8_t builtin, lean_object* w) {
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
l_farWord = _init_l_farWord();
lean_mark_persistent(l_farWord);
l_farCheck__true___nativeDecide__1__1 = _init_l_farCheck__true___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
