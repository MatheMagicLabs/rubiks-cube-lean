// Lean compiler output
// Module: Cube.Phase4Thm
// Imports: Init Cube.Phase4
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
static size_t l_pairId__true___nativeDecide__1__1___closed__4;
extern lean_object* l_idE;
static uint8_t l_pairId__true___nativeDecide__1__1___closed__3;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_pairId__true___nativeDecide__1__1___closed__0;
static uint8_t l_fiberCheck__true___nativeDecide__1__1___closed__0;
static uint8_t l_pairId__true___nativeDecide__1__1___closed__7;
extern lean_object* l_idMS;
LEAN_EXPORT uint8_t l_sliceOk__true___nativeDecide__1__1;
static uint64_t l_pairId__true___nativeDecide__1__1___closed__10;
static size_t l_pairId__true___nativeDecide__1__1___closed__9;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_St_id;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static uint8_t l_pairId__true___nativeDecide__1__1___closed__8;
static uint8_t l_pairId__true___nativeDecide__1__1___closed__2;
extern lean_object* l_cpSet;
extern lean_object* l_pairSet;
extern uint8_t l_sliceOk;
LEAN_EXPORT uint8_t l_cpId__true___nativeDecide__1__1;
static uint64_t l_pairId__true___nativeDecide__1__1___closed__5;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___solveTable___at___k2TableF_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_fiberCheckF(lean_object*);
static lean_object* l_pairId__true___nativeDecide__1__1___closed__6;
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___hashSt____x40_Cube_Model___hyg_48__spec__0(lean_object*, size_t, size_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT uint8_t l_fiberCheck__true___nativeDecide__1__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_pairId__true___nativeDecide__1__1___closed__1;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___solveTable___at___eoTable_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_pairId__true___nativeDecide__1__1;
size_t lean_usize_land(size_t, size_t);
static uint8_t _init_l_fiberCheck__true___nativeDecide__1__1___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = l_fiberCheckF(x_1);
return x_2;
}
}
static uint8_t _init_l_fiberCheck__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_fiberCheck__true___nativeDecide__1__1___closed__0;
return x_1;
}
}
static uint8_t _init_l_sliceOk__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_sliceOk;
return x_1;
}
}
static uint8_t _init_l_cpId__true___nativeDecide__1__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_1 = l_cpSet;
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = l_St_id;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_array_get_size(x_2);
x_21 = 7;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_4);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
x_6 = x_21;
goto block_20;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
x_6 = x_21;
goto block_20;
}
else
{
size_t x_26; size_t x_27; uint64_t x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___hashSt____x40_Cube_Model___hyg_48__spec__0(x_4, x_26, x_27, x_21);
x_6 = x_28;
goto block_20;
}
}
block_20:
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
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
lean_dec_ref(x_2);
x_19 = l_Std_DHashMap_Internal_AssocList_contains___at___solveTable___at___eoTable_spec__1_spec__1___redArg(x_4, x_18);
lean_dec(x_18);
lean_dec_ref(x_4);
return x_19;
}
}
}
static lean_object* _init_l_pairId__true___nativeDecide__1__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_idMS;
x_2 = l_idE;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_pairId__true___nativeDecide__1__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_idMS;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_pairId__true___nativeDecide__1__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_pairId__true___nativeDecide__1__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_pairId__true___nativeDecide__1__1___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_pairId__true___nativeDecide__1__1___closed__1;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_pairId__true___nativeDecide__1__1___closed__4() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_pairId__true___nativeDecide__1__1___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_pairId__true___nativeDecide__1__1___closed__5() {
_start:
{
uint64_t x_1; size_t x_2; size_t x_3; lean_object* x_4; uint64_t x_5; 
x_1 = 7;
x_2 = l_pairId__true___nativeDecide__1__1___closed__4;
x_3 = 0;
x_4 = l_idMS;
x_5 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___hashSt____x40_Cube_Model___hyg_48__spec__0(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_pairId__true___nativeDecide__1__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_idE;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_pairId__true___nativeDecide__1__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_pairId__true___nativeDecide__1__1___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_pairId__true___nativeDecide__1__1___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_pairId__true___nativeDecide__1__1___closed__6;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_pairId__true___nativeDecide__1__1___closed__9() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_pairId__true___nativeDecide__1__1___closed__6;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_pairId__true___nativeDecide__1__1___closed__10() {
_start:
{
uint64_t x_1; size_t x_2; size_t x_3; lean_object* x_4; uint64_t x_5; 
x_1 = 7;
x_2 = l_pairId__true___nativeDecide__1__1___closed__9;
x_3 = 0;
x_4 = l_idE;
x_5 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___hashSt____x40_Cube_Model___hyg_48__spec__0(x_4, x_3, x_2, x_1);
return x_5;
}
}
static uint8_t _init_l_pairId__true___nativeDecide__1__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_22; uint64_t x_28; uint8_t x_29; 
x_1 = l_pairSet;
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = l_pairId__true___nativeDecide__1__1___closed__0;
x_4 = lean_array_get_size(x_2);
x_28 = 7;
x_29 = l_pairId__true___nativeDecide__1__1___closed__7;
if (x_29 == 0)
{
x_22 = x_28;
goto block_27;
}
else
{
uint8_t x_30; 
x_30 = l_pairId__true___nativeDecide__1__1___closed__8;
if (x_30 == 0)
{
x_22 = x_28;
goto block_27;
}
else
{
uint64_t x_31; 
x_31 = l_pairId__true___nativeDecide__1__1___closed__10;
x_22 = x_31;
goto block_27;
}
}
block_21:
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_2, x_18);
lean_dec_ref(x_2);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___solveTable___at___k2TableF_spec__0_spec__0___redArg(x_3, x_19);
lean_dec(x_19);
return x_20;
}
block_27:
{
uint64_t x_23; uint8_t x_24; 
x_23 = 7;
x_24 = l_pairId__true___nativeDecide__1__1___closed__2;
if (x_24 == 0)
{
x_5 = x_22;
x_6 = x_23;
goto block_21;
}
else
{
uint8_t x_25; 
x_25 = l_pairId__true___nativeDecide__1__1___closed__3;
if (x_25 == 0)
{
x_5 = x_22;
x_6 = x_23;
goto block_21;
}
else
{
uint64_t x_26; 
x_26 = l_pairId__true___nativeDecide__1__1___closed__5;
x_5 = x_22;
x_6 = x_26;
goto block_21;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Phase4(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_Phase4Thm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Phase4(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_fiberCheck__true___nativeDecide__1__1___closed__0 = _init_l_fiberCheck__true___nativeDecide__1__1___closed__0();
l_fiberCheck__true___nativeDecide__1__1 = _init_l_fiberCheck__true___nativeDecide__1__1();
l_sliceOk__true___nativeDecide__1__1 = _init_l_sliceOk__true___nativeDecide__1__1();
l_cpId__true___nativeDecide__1__1 = _init_l_cpId__true___nativeDecide__1__1();
l_pairId__true___nativeDecide__1__1___closed__0 = _init_l_pairId__true___nativeDecide__1__1___closed__0();
lean_mark_persistent(l_pairId__true___nativeDecide__1__1___closed__0);
l_pairId__true___nativeDecide__1__1___closed__1 = _init_l_pairId__true___nativeDecide__1__1___closed__1();
lean_mark_persistent(l_pairId__true___nativeDecide__1__1___closed__1);
l_pairId__true___nativeDecide__1__1___closed__2 = _init_l_pairId__true___nativeDecide__1__1___closed__2();
l_pairId__true___nativeDecide__1__1___closed__3 = _init_l_pairId__true___nativeDecide__1__1___closed__3();
l_pairId__true___nativeDecide__1__1___closed__4 = _init_l_pairId__true___nativeDecide__1__1___closed__4();
l_pairId__true___nativeDecide__1__1___closed__5 = _init_l_pairId__true___nativeDecide__1__1___closed__5();
l_pairId__true___nativeDecide__1__1___closed__6 = _init_l_pairId__true___nativeDecide__1__1___closed__6();
lean_mark_persistent(l_pairId__true___nativeDecide__1__1___closed__6);
l_pairId__true___nativeDecide__1__1___closed__7 = _init_l_pairId__true___nativeDecide__1__1___closed__7();
l_pairId__true___nativeDecide__1__1___closed__8 = _init_l_pairId__true___nativeDecide__1__1___closed__8();
l_pairId__true___nativeDecide__1__1___closed__9 = _init_l_pairId__true___nativeDecide__1__1___closed__9();
l_pairId__true___nativeDecide__1__1___closed__10 = _init_l_pairId__true___nativeDecide__1__1___closed__10();
l_pairId__true___nativeDecide__1__1 = _init_l_pairId__true___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
