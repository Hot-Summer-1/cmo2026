/-
  第 2 题

  求证: 存在正整数 N, 使得对任意整数 n ≥ N, 存在与 n! + 1 互质的整数 a,
  使 a - 1, a^2 - 1, ⋯, a^{n^2} - 1 都不是 n! + 1 的倍数。

  "a 与 n!+1 互质" 用 `Int.gcd a (n!+1) = 1` 表述;
  "不是倍数" 即在 `ℤ` 中的整除关系不成立。
-/
module

public import Cmo2026.Defs
public import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

@[expose] public section

namespace CMO2026

/-- 第 2 题 -/
def prop_problem2:Prop:=∃ N : ℕ,
  ∀ n : ℕ, N ≤ n →
    ∃ a : ℤ,
      Int.gcd a ((n.factorial : ℤ) + 1) = 1 ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ n ^ 2 →
          ¬ (((n.factorial : ℤ) + 1) ∣ a ^ k - 1)
/-- 第 2 题的证明 -/
theorem problem2 :
    prop_problem2 := by
  sorry

end CMO2026
