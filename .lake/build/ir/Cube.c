// Lean compiler output
// Module: Cube
// Imports: Init Cube.Model Cube.Square Cube.Phase12 Cube.Phase34 Cube.Phase4 Cube.Parity Cube.SwapLemmas Cube.ParityLaw Cube.Select Cube.Kph1 Cube.BenchDefs
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Model(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Square(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Phase12(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Phase34(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Phase4(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Parity(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_SwapLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_ParityLaw(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Select(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_Kph1(uint8_t builtin, lean_object*);
lean_object* initialize_Cube_BenchDefs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cube(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Model(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Square(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Phase12(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Phase34(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Phase4(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Parity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_SwapLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_ParityLaw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Select(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_Kph1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cube_BenchDefs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
