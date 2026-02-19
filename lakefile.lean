import Lake
open Lake DSL

package snsft where
  name := "snsft"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib SNSFT where
  roots := #[`SNSFT_Master]
