/-
  2026 年（第 42 届）中国数学奥林匹克 第一天
  题目的形式化陈述（只陈述问题，不给出证明）。

  本工程依赖 Mathlib，并按需只导入用到的模块：
  * `Mathlib.Data.Real.Basic`  — 实数 ℝ；
  * `Mathlib.Algebra.Ring.Parity` — `Odd` / `Even`（用于第 3 题的“一奇一偶”）；
  * 第 2 题额外导入 `Mathlib.Data.Nat.Factorial.Basic` — 阶乘 `n!`；
  * 第 3 题额外导入 `Mathlib.Analysis.Real.Sqrt` — 平方根 `Real.sqrt`。
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false

@[expose] public section

namespace CMO2026

/-! ## 第 1 题的公共定义 -/

/-- 正整数数列（下标从 1 开始，只要求 `n ≥ 1` 处为正）。 -/
def IsPosSeq (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 1 ≤ a n

/-- 好数列 `{a_n}`：
    `a_{n+1} = a_n - 1`（当 `a_n > 1`），否则 `a_{n+1} = n`。 -/
def IsGood (a : ℕ → ℕ) : Prop :=
  IsPosSeq a ∧
    ∀ n : ℕ, 1 ≤ n → a (n + 1) = if 1 < a n then a n - 1 else n

/-- 前 `t` 项之和 `a_1 + a_2 + ⋯ + a_t`。 -/
def prefixSum (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  ((List.range t).map (fun i => a (i + 1))).sum

/-- 题设条件：`m, t ≥ 2`，且存在好数列 `{a_n}` 使 `a_1 = m` 且
    `t * m = a_1 + a_2 + ⋯ + a_t`（即 `m = (1/t)(a_1 + ⋯ + a_t)`）。 -/
def Admissible (m t : ℕ) : Prop :=
  2 ≤ m ∧ 2 ≤ t ∧
    ∃ a : ℕ → ℕ, IsGood a ∧ a 1 = m ∧ t * m = prefixSum a t

/-- 第 1 题 (2) 中“上界”的含义：实数 `c` 使得一切可行 `(m, t)` 都满足 `t ≤ c * m`。 -/
def IsUpperBound (c : ℝ) : Prop :=
  ∀ m t : ℕ, Admissible m t → (t : ℝ) ≤ c * (m : ℝ)


/-! ## 第 3 题的公共定义 -/

/-- 平面整点。跳跃位移都是整向量，非整点不可能被跳到。 -/
abbrev Point : Type := ℤ × ℤ

/-- 一次甲跳跃的四种位移。 -/
def jiaMoves (a b : ℤ) : List Point :=
  [(a, b), (-b, a), (-a, -b), (b, -a)]

/-- 一次乙跳跃的四种位移。 -/
def yiMoves (a b : ℤ) : List Point :=
  [(b, a), (-a, b), (-b, -a), (a, -b)]

/-- 位移 `s` 是某一次甲跳跃。 -/
def IsJiaStep (a b : ℤ) (s : Point) : Prop :=
  s ∈ jiaMoves a b

/-- 位移 `s` 是某一次乙跳跃。 -/
def IsYiStep (a b : ℤ) (s : Point) : Prop :=
  s ∈ yiMoves a b

/-- 一串位移的坐标和（起点为原点）。 -/
def sumPoints : List Point → Point
  | [] => (0, 0)
  | p :: ps => (p.1 + (sumPoints ps).1, p.2 + (sumPoints ps).2)

/-- 用任意次乙跳跃和不超过 `k` 次甲跳跃，可以从原点跳到 `P`。 -/
def ReachableJia (a b : ℤ) (k : ℕ) (P : Point) : Prop :=
  ∃ jia yi : List Point,
    jia.length ≤ k ∧
      (∀ s ∈ jia, IsJiaStep a b s) ∧
      (∀ s ∈ yi, IsYiStep a b s) ∧
      sumPoints (jia ++ yi) = P

/-- 用不超过 `k` 次跳跃（甲、乙任意搭配），可以从原点跳到 `P`。 -/
def ReachableAny (a b : ℤ) (k : ℕ) (P : Point) : Prop :=
  ∃ jia yi : List Point,
    jia.length + yi.length ≤ k ∧
      (∀ s ∈ jia, IsJiaStep a b s) ∧
      (∀ s ∈ yi, IsYiStep a b s) ∧
      sumPoints (jia ++ yi) = P

/-- `a, b` 一奇一偶。 -/
def OneOddOneEven (a b : ℤ) : Prop :=
  (Odd a ∧ Even b) ∨ (Even a ∧ Odd b)

end CMO2026
