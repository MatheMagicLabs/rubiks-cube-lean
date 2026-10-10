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

/-- generic God's-number tables (2×2×2), precompiled. -/
lean_lib CubeG where
  precompileModules := true

/-- Kociemba phase 2 tables (precompiled). -/
lean_lib CubeH where
  precompileModules := true

/-- 28-move certificates (precompiled). -/
lean_lib CubeK where
  precompileModules := true

/-- slice groups and order-11 search (precompiled). -/
lean_lib CubeO where
  precompileModules := true
