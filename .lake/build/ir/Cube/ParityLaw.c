// Lean compiler output
// Module: Cube.ParityLaw
// Imports: Init Cube.SwapLemmas
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
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t l_ksOk___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_ksOk___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ksOk___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ksOk___lam__0___boxed(lean_object*);
extern lean_object* l_ksC;
extern lean_object* l_ksE;
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ksOk___lam__0(lean_object*);
static lean_object* l_ksOk___closed__0;
lean_object* l_List_range(lean_object*);
LEAN_EXPORT uint8_t l_ksOk___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ksOk;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ksOk___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_unsigned_to_nat(12u);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ksOk___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_ksOk___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_ksC;
lean_inc(x_1);
x_19 = lean_array_get(x_1, x_18, x_4);
x_20 = l_List_all___redArg(x_19, x_2);
if (x_20 == 0)
{
lean_dec_ref(x_3);
x_5 = x_20;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_ksE;
lean_inc(x_1);
x_22 = lean_array_get(x_1, x_21, x_4);
x_23 = l_List_all___redArg(x_22, x_3);
x_5 = x_23;
goto block_17;
}
block_17:
{
if (x_5 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = l_ksC;
lean_inc(x_1);
x_7 = lean_array_get(x_1, x_6, x_4);
x_8 = l_List_lengthTR___redArg(x_7);
lean_dec(x_7);
x_9 = l_ksE;
x_10 = lean_array_get(x_1, x_9, x_4);
x_11 = l_List_lengthTR___redArg(x_10);
lean_dec(x_10);
x_12 = lean_nat_add(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_mod(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
return x_16;
}
}
}
}
static lean_object* _init_l_ksOk___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(18u);
x_2 = l_List_range(x_1);
return x_2;
}
}
static uint8_t _init_l_ksOk() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_alloc_closure((void*)(l_ksOk___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_ksOk___lam__1___boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_alloc_closure((void*)(l_ksOk___lam__2___boxed), 4, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
x_5 = l_ksOk___closed__0;
x_6 = l_List_all___redArg(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ksOk___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ksOk___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ksOk___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_ksOk___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ksOk___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_ksOk___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_SwapLemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_ParityLaw(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_SwapLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ksOk___closed__0 = _init_l_ksOk___closed__0();
lean_mark_persistent(l_ksOk___closed__0);
l_ksOk = _init_l_ksOk();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
