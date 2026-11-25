import Lake
open Lake DSL

package cmo2026 where

@[default_target]
lean_lib Cmo2026 where
lean_lib Check where

require mathlib from git "https://github.com/leanprover-community/mathlib4"
