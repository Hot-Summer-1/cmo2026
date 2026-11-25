module

public import Cmo2026.Defs
public import Cmo2026.Problem1
public import Cmo2026.Problem2
public import Cmo2026.Problem3

set_option autoImplicit false

@[expose] public section

namespace CMO2026
/-- 所有问题 -/
theorem all_problems:
  prop_problem1∧prop_problem2∧prop_problem3:=⟨problem1,problem2,problem3⟩
end CMO2026
