import Lake
open Lake DSL

package «stabilizerHyperfiniteFormalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib Formalization where

lean_lib AristotleCandidates where
