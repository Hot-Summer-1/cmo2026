module

public import Cmo2026.Defs
public import Cmo2026.Problem1
public import Cmo2026.Problem2
public import Cmo2026.Problem3
public import Cmo2026.Problem4
public import Cmo2026.Problem5
public import Cmo2026.Problem6

set_option autoImplicit false

@[expose] public section

namespace CMO2026
/-- 所有问题 -/
theorem all_problems:
  prop_problem1∧prop_problem2∧prop_problem3∧prop_problem4∧prop_problem5∧prop_problem6:=⟨problem1,problem2,problem3,problem4,problem5,problem6⟩
end CMO2026
