// Lean compiler output
// Module: Cube.BenchDefs
// Imports: Init Cube.Kph1
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_TS;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_benchNext(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_NN;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_TC;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_TE;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___distF_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_benchScan(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_12 = lean_nat_dec_lt(x_5, x_6);
if (x_12 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_byte_array_get(x_1, x_5);
x_14 = 255;
x_15 = lean_uint8_dec_eq(x_13, x_14);
if (x_15 == 0)
{
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_16; 
x_16 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_8 = x_16;
goto block_11;
}
}
block_11:
{
lean_object* x_9; 
x_9 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_8;
x_5 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_benchScan(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_empty_byte_array(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
x_6 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___distF_spec__3___redArg(x_5, x_2, x_3);
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg(x_6, x_4, x_5, x_3, x_3);
lean_dec_ref(x_5);
lean_dec_ref(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchScan_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_8 = lean_unsigned_to_nat(7919u);
x_9 = lean_nat_mul(x_1, x_8);
x_10 = l_NN;
x_11 = lean_nat_mod(x_9, x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_TE;
x_14 = lean_unsigned_to_nat(2187u);
x_15 = lean_unsigned_to_nat(495u);
x_16 = lean_nat_mul(x_14, x_15);
x_17 = lean_nat_div(x_11, x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(18u);
x_19 = lean_nat_mul(x_17, x_18);
lean_dec(x_17);
x_20 = lean_nat_add(x_19, x_4);
lean_dec(x_19);
x_21 = lean_array_get(x_12, x_13, x_20);
lean_dec(x_20);
x_22 = lean_nat_mul(x_21, x_14);
lean_dec(x_21);
x_23 = l_TC;
x_24 = lean_nat_div(x_11, x_15);
x_25 = lean_nat_mod(x_24, x_14);
lean_dec(x_24);
x_26 = lean_nat_mul(x_25, x_18);
lean_dec(x_25);
x_27 = lean_nat_add(x_26, x_4);
lean_dec(x_26);
x_28 = lean_array_get(x_12, x_23, x_27);
lean_dec(x_27);
x_29 = lean_nat_add(x_22, x_28);
lean_dec(x_28);
lean_dec(x_22);
x_30 = lean_nat_mul(x_29, x_15);
lean_dec(x_29);
x_31 = l_TS;
x_32 = lean_nat_mod(x_11, x_15);
lean_dec(x_11);
x_33 = lean_nat_mul(x_32, x_18);
lean_dec(x_32);
x_34 = lean_nat_add(x_33, x_4);
lean_dec(x_33);
x_35 = lean_array_get(x_12, x_31, x_34);
lean_dec(x_34);
x_36 = lean_nat_add(x_30, x_35);
lean_dec(x_35);
lean_dec(x_30);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_mod(x_36, x_37);
lean_dec(x_36);
x_39 = lean_nat_add(x_3, x_38);
lean_dec(x_38);
lean_dec(x_3);
x_40 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_39;
x_4 = x_40;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(18u);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_2);
lean_inc(x_1);
x_11 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg(x_5, x_10, x_4, x_1);
lean_dec_ref(x_10);
x_12 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_11;
x_5 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(18u);
lean_inc(x_2);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_2);
lean_inc(x_1);
x_11 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg(x_5, x_10, x_4, x_1);
lean_dec_ref(x_10);
x_12 = lean_nat_add(x_5, x_7);
x_13 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg(x_1, x_2, x_3, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_benchNext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
x_5 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg(x_2, x_3, x_4, x_2, x_2);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at_____private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___benchNext_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Kph1(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_BenchDefs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Kph1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
