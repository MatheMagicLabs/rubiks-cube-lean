// Lean compiler output
// Module: Cube.Phase34Thm
// Imports: Init Cube.Phase34
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
uint8_t l_k3CheckF(lean_object*);
LEAN_EXPORT uint8_t l_g2Keep__true___nativeDecide__1__1;
LEAN_EXPORT uint8_t l_pairClosed__true___nativeDecide__1__1;
extern uint8_t l_pairClosed;
static uint8_t l_k3Check__true___nativeDecide__1__1___closed__0;
LEAN_EXPORT uint8_t l_k3Check__true___nativeDecide__1__1;
extern uint8_t l_g2Keep;
LEAN_EXPORT uint8_t l_cpClosed__true___nativeDecide__1__1;
extern uint8_t l_hEven;
extern uint8_t l_cpClosed;
LEAN_EXPORT uint8_t l_hEven__true___nativeDecide__1__1;
static uint8_t _init_l_cpClosed__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_cpClosed;
return x_1;
}
}
static uint8_t _init_l_pairClosed__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_pairClosed;
return x_1;
}
}
static uint8_t _init_l_k3Check__true___nativeDecide__1__1___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = l_k3CheckF(x_1);
return x_2;
}
}
static uint8_t _init_l_k3Check__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_k3Check__true___nativeDecide__1__1___closed__0;
return x_1;
}
}
static uint8_t _init_l_g2Keep__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_g2Keep;
return x_1;
}
}
static uint8_t _init_l_hEven__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_hEven;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Phase34(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_Phase34Thm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Phase34(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_cpClosed__true___nativeDecide__1__1 = _init_l_cpClosed__true___nativeDecide__1__1();
l_pairClosed__true___nativeDecide__1__1 = _init_l_pairClosed__true___nativeDecide__1__1();
l_k3Check__true___nativeDecide__1__1___closed__0 = _init_l_k3Check__true___nativeDecide__1__1___closed__0();
l_k3Check__true___nativeDecide__1__1 = _init_l_k3Check__true___nativeDecide__1__1();
l_g2Keep__true___nativeDecide__1__1 = _init_l_g2Keep__true___nativeDecide__1__1();
l_hEven__true___nativeDecide__1__1 = _init_l_hEven__true___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
