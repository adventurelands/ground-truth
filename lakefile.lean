import Lake
open Lake DSL

package "ProofFarm" where
  version := v!"0.1.0"

@[default_target]
lean_lib «ProofFarm» where
