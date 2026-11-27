module

public import Cmo2026.Defs

set_option autoImplicit false

@[expose] public section

namespace CMO2026
noncomputable def your_answer_to_problem6_part1:ℝ:=sorry
def prop_problem6_part1:Prop:= F 20 26=your_answer_to_problem6_part1
def prop_problem6_part2:Prop:=∃N:ℕ,2≤N∧∀(n:ℕ),N≤n→minOverM n<0.85
def prop_problem6:Prop:=prop_problem6_part1∧prop_problem6_part2
theorem problem6:prop_problem6:=by sorry
end CMO2026
