// Lean compiler output
// Module: Cube.Parity
// Imports: Init Cube.Model
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
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__swapAt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_swapAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__swapAt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_inv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ltCount___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_swapAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_inv(lean_object*);
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ltCount(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___swaps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_swaps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___swaps_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_swaps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ltCount(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_lt(x_4, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(0u);
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(1u);
x_6 = x_12;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_ltCount(x_1, x_5);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_ltCount___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ltCount(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_inv(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_ltCount(x_3, x_4);
x_6 = l_inv(x_4);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_inv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_inv(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_swapAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_ctor_set(x_5, 0, x_7);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_1, x_22);
x_24 = l_swapAt(x_23, x_21);
lean_dec(x_23);
lean_ctor_set(x_2, 1, x_24);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_1, x_27);
x_29 = l_swapAt(x_28, x_26);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_swapAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_swapAt(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__swapAt_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = lean_apply_3(x_3, x_11, x_12, x_13);
return x_14;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_1, x_18);
lean_dec(x_1);
x_20 = lean_apply_3(x_4, x_19, x_16, x_17);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__swapAt_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Cube_Parity_0__swapAt_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Cube_Parity_0__ltCount_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Cube_Parity_0__ltCount_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Cube_Parity_0__ltCount_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Cube_Parity_0__ltCount_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___swaps_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_swapAt(x_3, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_swaps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___swaps_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___swaps_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___swaps_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_swaps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_swaps(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Model(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_Parity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Model(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
