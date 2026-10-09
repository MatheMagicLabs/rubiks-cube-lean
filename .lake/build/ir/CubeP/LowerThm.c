// Lean compiler output
// Module: CubeP.LowerThm
// Imports: Init CubeG.Lower
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
LEAN_EXPORT uint8_t l_k1Witness__valid___nativeDecide__1__1;
uint8_t l_k1LowF(lean_object*);
static uint8_t l_k1Low__true___nativeDecide__1__1___closed__0;
extern uint8_t l_k1WitnessValid;
LEAN_EXPORT uint8_t l_k1Low__true___nativeDecide__1__1;
static uint8_t _init_l_k1Witness__valid___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_k1WitnessValid;
return x_1;
}
}
static uint8_t _init_l_k1Low__true___nativeDecide__1__1___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = l_k1LowF(x_1);
return x_2;
}
}
static uint8_t _init_l_k1Low__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_k1Low__true___nativeDecide__1__1___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_CubeG_Lower(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CubeP_LowerThm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CubeG_Lower(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_k1Witness__valid___nativeDecide__1__1 = _init_l_k1Witness__valid___nativeDecide__1__1();
l_k1Low__true___nativeDecide__1__1___closed__0 = _init_l_k1Low__true___nativeDecide__1__1___closed__0();
l_k1Low__true___nativeDecide__1__1 = _init_l_k1Low__true___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
