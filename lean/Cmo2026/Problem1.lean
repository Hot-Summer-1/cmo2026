/-
  第 1 题

  称正整数数列 {a_n} 是好的, 如果
    a_{n+1} = a_n - 1 (a_n > 1),    a_{n+1} = n (a_n = 1).
  给定整数 m, t ≥ 2, 设好数列 {a_n} 满足
    a_1 = m = (1/t)(a_1 + a_2 + ⋯ + a_t).
  (1) 求证: t ≥ (5/2) m;
  (2) 对所有的 m, t, 求最小的实数 C, 使得 t ≤ C m.
-/
module

public import Cmo2026.Defs

set_option autoImplicit false

@[expose] public section

namespace CMO2026

/-- 第 1 题 (1): 对题设条件下的 `m, t`, 有 `t ≥ (5/2) m`, 即 `2 t ≥ 5 m`。 -/
def prop_problem1_part1(m t:ℕ):Prop:=5 * m ≤ 2 * t
/-- 第 1 题 (1) 的证明 -/
theorem problem1_part1 (m t : ℕ) (h : Admissible m t) : prop_problem1_part1 m t := by
  sorry

/-- 第 1 题 (2) 所要求的常数 `C`（此处以 `sorry` 占位；本工程只陈述其性质，不计算数值）。 -/
noncomputable def your_answer_to_problem1_part2 : ℝ := sorry

/-- 第 1 题 (2): `C` 是上界, 且任何比它小的实数都不是上界, 即 `C` 是所有可行
    `t/m` 的最小上界（也就是“最小的实数 C”）。 -/
def prop_problem1_part2:=IsUpperBound your_answer_to_problem1_part2 ∧
      ∀ c : ℝ, c < your_answer_to_problem1_part2 → ¬ IsUpperBound c
/-- 第 1 题 (2) 的证明-/
theorem problem1_part2 :
    prop_problem1_part2 := by
  sorry

/-- 第 1 题两问合并 -/
def prop_problem1:Prop:=(∀ (m t :ℕ),Admissible m t→prop_problem1_part1 m t)∧prop_problem1_part2
/-- 第 1 题的证明 -/
theorem problem1:
     prop_problem1:= by
  constructor
  · intro m t h
    exact problem1_part1 m t h
  · exact problem1_part2

end CMO2026
