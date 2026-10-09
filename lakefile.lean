import Lake
open Lake DSL
package cubelean where
  moreLeanArgs := #["-DmaxRecDepth=100000"]
@[default_target]
lean_lib Cube where
  precompileModules := true
