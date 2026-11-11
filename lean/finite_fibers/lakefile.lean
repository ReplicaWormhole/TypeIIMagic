import Lake
open Lake DSL

package "finiteFiberFormalization" where
  -- This package deliberately depends only on public mathlib APIs.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib FiniteFiber where
