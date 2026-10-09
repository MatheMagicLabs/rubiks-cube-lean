// Lean compiler output
// Module: Cube.Phase12Thm
// Imports: Init Cube.Phase12
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
LEAN_EXPORT uint8_t l_g1KeepsEO__true___nativeDecide__1__1;
LEAN_EXPORT uint8_t l_k2Check__true___nativeDecide__1__1;
extern uint8_t l_g1KeepsEO;
extern uint8_t l_eoCheck;
LEAN_EXPORT uint8_t l_eoCheck__true___nativeDecide__1__1;
extern uint8_t l_k2Check;
static uint8_t _init_l_eoCheck__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_eoCheck;
return x_1;
}
}
static uint8_t _init_l_k2Check__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_k2Check;
return x_1;
}
}
static uint8_t _init_l_g1KeepsEO__true___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = l_g1KeepsEO;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Phase12(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube_Phase12Thm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Phase12(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_eoCheck__true___nativeDecide__1__1 = _init_l_eoCheck__true___nativeDecide__1__1();
l_k2Check__true___nativeDecide__1__1 = _init_l_k2Check__true___nativeDecide__1__1();
l_g1KeepsEO__true___nativeDecide__1__1 = _init_l_g1KeepsEO__true___nativeDecide__1__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
