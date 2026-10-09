import Lake
open Lake DSL
package cubelean where
  moreLeanArgs := #["-DmaxRecDepth=100000"]
@[default_target]
lean_lib Cube where
  precompileModules := true

/-- proofs and `native_decide` certificates: deliberately NOT precompiled, so that importing them does not
re-run the certificate computations at load time. -/
lean_lib CubeP where
  globs := #[.submodules `CubeP]
