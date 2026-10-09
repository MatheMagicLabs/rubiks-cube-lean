// Lean compiler output
// Module: CubeG.Lower
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
LEAN_EXPORT lean_object* l_lipCell___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_TS;
extern lean_object* l_i0;
LEAN_EXPORT lean_object* l_k1Witness;
lean_object* l_rank(lean_object*);
LEAN_EXPORT uint8_t l_lipFrom(lean_object*, lean_object*);
extern lean_object* l_NN;
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT uint8_t l_k1WitnessValid___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_superflip;
LEAN_EXPORT uint8_t l_k1LowF(lean_object*);
LEAN_EXPORT uint8_t l_lipCell(lean_object*, lean_object*);
lean_object* l_parseAlg(lean_object*);
lean_object* l_eval(lean_object*);
extern lean_object* l_TC;
extern lean_object* l_TE;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_lipCell___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_k1WitnessValid;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_lipCell___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_distF(lean_object*);
LEAN_EXPORT lean_object* l_k1WitnessValid___lam__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_lipFrom___boxed(lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_k1LowF___boxed(lean_object*);
LEAN_EXPORT uint8_t l_lipCell___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_4 = lean_byte_array_get(x_1, x_2);
x_5 = lean_uint8_to_nat(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_TE;
x_8 = lean_unsigned_to_nat(2187u);
x_9 = lean_unsigned_to_nat(495u);
x_10 = lean_nat_mul(x_8, x_9);
x_11 = lean_nat_div(x_2, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(18u);
x_13 = lean_nat_mul(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
x_15 = lean_array_get(x_6, x_7, x_14);
lean_dec(x_14);
x_16 = lean_nat_mul(x_15, x_8);
lean_dec(x_15);
x_17 = l_TC;
x_18 = lean_nat_div(x_2, x_9);
x_19 = lean_nat_mod(x_18, x_8);
lean_dec(x_18);
x_20 = lean_nat_mul(x_19, x_12);
lean_dec(x_19);
x_21 = lean_nat_add(x_20, x_3);
lean_dec(x_20);
x_22 = lean_array_get(x_6, x_17, x_21);
lean_dec(x_21);
x_23 = lean_nat_add(x_16, x_22);
lean_dec(x_22);
lean_dec(x_16);
x_24 = lean_nat_mul(x_23, x_9);
lean_dec(x_23);
x_25 = l_TS;
x_26 = lean_nat_mod(x_2, x_9);
x_27 = lean_nat_mul(x_26, x_12);
lean_dec(x_26);
x_28 = lean_nat_add(x_27, x_3);
lean_dec(x_27);
x_29 = lean_array_get(x_6, x_25, x_28);
lean_dec(x_28);
x_30 = lean_nat_add(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
x_31 = lean_byte_array_get(x_1, x_30);
lean_dec(x_30);
x_32 = lean_uint8_to_nat(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_32, x_33);
lean_dec(x_32);
x_35 = lean_nat_dec_le(x_5, x_34);
lean_dec(x_34);
lean_dec(x_5);
return x_35;
}
}
LEAN_EXPORT uint8_t l_lipCell(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_alloc_closure((void*)(l_lipCell___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_List_range(x_4);
x_6 = l_List_all___redArg(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_lipCell___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_lipCell___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_lipCell___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_lipCell(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_lipFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l_lipCell(x_1, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_1);
return x_7;
}
else
{
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_lipFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_lipFrom(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_superflip() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2", 50, 50);
x_2 = l_parseAlg(x_1);
return x_2;
}
}
static lean_object* _init_l_k1Witness() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("L2 D2 B2 R2 D2 B2 R2 D2 R2 U2 D' B2 U' F2 U' L2 U R2 U2 B' R' F2 U2 F L2 R' D U2 L' R' U'", 89, 89);
x_2 = l_parseAlg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_k1WitnessValid___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_k1WitnessValid() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_alloc_closure((void*)(l_k1WitnessValid___lam__0___boxed), 1, 0);
x_2 = l_k1Witness;
x_3 = l_List_all___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_k1WitnessValid___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_k1WitnessValid___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_k1LowF(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_13; uint8_t x_14; 
x_2 = lean_box(0);
x_3 = l_distF(x_2);
x_13 = l_NN;
lean_inc_ref(x_3);
x_14 = l_lipFrom(x_3, x_13);
if (x_14 == 0)
{
x_4 = x_14;
goto block_12;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = l_i0;
x_16 = lean_byte_array_get(x_3, x_15);
x_17 = lean_uint8_to_nat(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
x_4 = x_19;
goto block_12;
}
block_12:
{
if (x_4 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_k1Witness;
x_6 = l_eval(x_5);
x_7 = l_rank(x_6);
x_8 = lean_byte_array_get(x_3, x_7);
lean_dec(x_7);
lean_dec_ref(x_3);
x_9 = lean_uint8_to_nat(x_8);
x_10 = lean_unsigned_to_nat(12u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_k1LowF___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_k1LowF(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Kph1(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CubeG_Lower(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Kph1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_superflip = _init_l_superflip();
lean_mark_persistent(l_superflip);
l_k1Witness = _init_l_k1Witness();
lean_mark_persistent(l_k1Witness);
l_k1WitnessValid = _init_l_k1WitnessValid();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
