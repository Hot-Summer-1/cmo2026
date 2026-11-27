module

public import Cmo2026.Defs

set_option autoImplicit false

@[expose] public section

namespace CMO2026
def your_answer_to_problem5(d M:ℕ):ℕ:=sorry
def prop_problem5_part1:Prop:=
  ∀(d M:ℕ),2≤d→2≤M→(∃S:Finset (Fin d→ℕ),S.card=your_answer_to_problem5 d M∧IsGoodSet M S)
def prop_problem5_part2:Prop:=
  ∀(d M:ℕ),2≤d→2≤M→∀(S:Finset (Fin d→ℕ)),IsGoodSet M S→S.card≤your_answer_to_problem5 d M
def prop_problem5:Prop:=
  prop_problem5_part1∧prop_problem5_part2
theorem problem5:prop_problem5:=by sorry

end CMO2026
