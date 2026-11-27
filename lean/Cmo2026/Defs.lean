/-
  2026 年（第 42 届）中国数学奥林匹克 第一天
  题目的形式化陈述（只陈述问题，不给出证明）。

  本工程依赖 Mathlib，并按需只导入用到的模块：
  * `Mathlib.Data.Real.Basic`  — 实数 ℝ；
  * `Mathlib.Algebra.Ring.Parity` — `Odd` / `Even`（用于第 3 题的“一奇一偶”）；
  * 第 2 题额外导入 `Mathlib.Data.Nat.Factorial.Basic` — 阶乘 `n!`。
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic

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
  (Finset.range (t)).sum (fun i => a (i + 1))

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

/-! ## 第 4 题：平面几何 ##-/

open scoped EuclideanGeometry

/-- 平面 `ℝ²`。 -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable section
/-- 平面向量的叉积 `u × v = u₀ v₁ - u₁ v₀`（平行四边形有向面积的 2 倍）。 -/
def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- 三角形 `A B C` 的有向面积（2 倍）。 -/
def orient (A B C : Plane) : ℝ := cross (B - A) (C - A)
end

/-- `A B C D` 是简单四边形：四个顶点互异，两组对边（所在线段）不相交。 -/
def IsSimpleQuadrilateral (A B C D : Plane) : Prop :=
  Function.Injective ![A, B, C, D] ∧ Disjoint (segment ℝ A B) (segment ℝ C D) ∧
    Disjoint (segment ℝ B C) (segment ℝ A D)

/-- `A B C D` 是严格凸四边形：为简单四边形，且四个三角形 `ABC`、`BCD`、`CDA`、`DAB`
的有向面积同号且均非零（即顶点按逆时针或顺时针顺序处于凸位置）。 -/
def IsStrictlyConvexQuadrilateral (A B C D : Plane) : Prop :=
  IsSimpleQuadrilateral A B C D ∧
    0 < orient A B C * orient B C D ∧ 0 < orient B C D * orient C D A ∧
      0 < orient C D A * orient D A B

/-- `P` 是两条线段 `AB` 与 `CD` 的交点（`P` 同时落在两条线段上）。 -/
def IsSegmentIntersection (P : Plane) (A B C D : Plane) : Prop :=
  P ∈ segment ℝ A B ∩ segment ℝ C D

/-! ### 叉积与有向面积的基本性质 -/

@[simp]
lemma cross_self (u : Plane) : cross u u = 0 := by
  simp only [cross]
  ring

lemma cross_smul_smul (a b : ℝ) (u v : Plane) :
    cross (a • u) (b • v) = a * b * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]
  ring

lemma cross_smul_left_self (a : ℝ) (u : Plane) : cross (a • u) u = 0 := by
  simpa using cross_smul_smul a 1 u u

/-- 三点共线时，其有向面积为 `0`。 -/
lemma orient_eq_zero_of_collinear {A B C : Plane}
    (h : Collinear ℝ ({A, B, C} : Set Plane)) : orient A B C = 0 := by
  have hA : A ∈ ({A, B, C} : Set Plane) := by simp
  rw [collinear_iff_of_mem hA] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨a, ha⟩ := hv B (by simp)
  obtain ⟨b, hb⟩ := hv C (by simp)
  have hAB : B - A = a • v := by rw [ha]; simp
  have hAC : C - A = b • v := by rw [hb]; simp
  rw [orient, hAB, hAC, cross_smul_smul, cross_self, mul_zero]

/-- 若 `X` 在线段 `Y Z` 上，则三角形 `Y X Z` 的有向面积为 `0`。 -/
lemma orient_eq_zero_of_mem_segment {X Y Z : Plane} (h : X ∈ segment ℝ Y Z) :
    orient Y X Z = 0 := by
  rw [segment_eq_image_lineMap] at h
  obtain ⟨t, -, ht⟩ := h
  have hXY : X - Y = t • (Z - Y) := by
    rw [← ht]
    have h := AffineMap.lineMap_vsub_left Y Z t
    rw [vsub_eq_sub, vsub_eq_sub] at h
    exact h
  rw [orient, hXY]
  exact cross_smul_left_self t (Z - Y)

/-- 严格凸四边形两条对角线的交点，与任一对相邻顶点构成非退化三角形：
`ABE` 与 `CDE` 都仿射无关（三点不共线）。 -/
lemma AffineIndependentInStrictlyConvexQuadrilateral (A B C D E : Plane)
    (hQuadrilateral : IsStrictlyConvexQuadrilateral A B C D)
    (hE : IsSegmentIntersection E A C B D) :
    AffineIndependent ℝ ![A, B, E] ∧ AffineIndependent ℝ ![C, D, E] := by
  obtain ⟨-, h₁, h₂, h₃⟩ := hQuadrilateral
  obtain ⟨hEAC, hEBD⟩ := hE
  -- 四个三角形的有向面积均非零
  have hABC : orient A B C ≠ 0 := (mul_ne_zero_iff.mp h₁.ne').1
  have hBCD : orient B C D ≠ 0 := (mul_ne_zero_iff.mp h₁.ne').2
  have hCDA : orient C D A ≠ 0 := (mul_ne_zero_iff.mp h₂.ne').2
  have hDAB : orient D A B ≠ 0 := (mul_ne_zero_iff.mp h₃.ne').2
  -- 交点不在任一顶点上
  have hEA : E ≠ A := by
    rintro rfl
    rw [segment_symm ℝ B D] at hEBD
    exact hDAB (orient_eq_zero_of_mem_segment hEBD)
  have hEB : E ≠ B := by
    rintro rfl
    exact hABC (orient_eq_zero_of_mem_segment hEAC)
  have hEC : E ≠ C := by
    rintro rfl
    exact hBCD (orient_eq_zero_of_mem_segment hEBD)
  have hED : E ≠ D := by
    rintro rfl
    rw [segment_symm ℝ A C] at hEAC
    exact hCDA (orient_eq_zero_of_mem_segment hEAC)
  constructor
  · -- `A`、`B`、`E` 不共线
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    have hBE : B ∈ line[ℝ, A, E] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEA.symm
    have hCE : C ∈ line[ℝ, A, E] :=
      (mem_segment_iff_wbtw.mp hEAC).right_mem_affineSpan_of_left_ne hEA.symm
    refine hABC (orient_eq_zero_of_collinear ?_)
    exact collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair ℝ A E) hBE hCE
  · -- `C`、`D`、`E` 不共线
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    have hDE : D ∈ line[ℝ, C, E] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hEC.symm
    have hBED : B ∈ line[ℝ, D, E] :=
      (mem_segment_iff_wbtw.mp hEBD).left_mem_affineSpan_of_right_ne hED.symm
    have hBCE : B ∈ line[ℝ, C, E] :=
      (affineSpan_pair_le_of_left_mem hDE) hBED
    refine hBCD (orient_eq_zero_of_collinear ?_)
    exact collinear_triple_of_mem_affineSpan_pair hBCE (left_mem_affineSpan_pair ℝ C E) hDE

/-! ## 第 5 题的公共定义 -/
def SumOfIndex{d:ℕ}(S:Finset (Fin d→ℕ))(i:Fin d):ℕ:=
  S.sum (fun v=>v i)
def AvgOfIndex{d:ℕ}(S:Finset (Fin d→ℕ))(i:Fin d):ℚ:=
  ((SumOfIndex S i):ℚ)/S.card
/-- 第 5 题的平均值条件：前 `d-1` 个分量（0-based 下标 `i.val ≠ d-1`）的平均值
    不超过 `M`，最后一个分量（`i.val = d-1`）的平均值不超过 `3M+1`。 -/
def IsGoodSet {d : ℕ} (M : ℕ) (S : Finset (Fin d → ℕ)) : Prop :=
  (∀ i : Fin d, i.val ≠ d - 1 → AvgOfIndex S i ≤ (M : ℚ)) ∧
  (∀ i : Fin d, i.val = d - 1 → AvgOfIndex S i ≤ ((3 * M + 1 : ℕ) : ℚ))

/-! ## 第 6 题的公共定义 -/
noncomputable def SumOfFinSeq {n:ℕ}(S : Fin n → ℝ) (f:ℝ→ℝ):ℝ :=
  Finset.univ.sum (fun i:Fin n=>f (S (i)))
def IsGoodFinSeq {n:ℕ}(S: Fin n→ℝ):Prop:=
  Antitone S∧SumOfFinSeq S id =0∧
  SumOfFinSeq S (fun x=>x^2)=1
noncomputable def SetOfGoodFinSeq(n:ℕ):Set (Fin n→ℝ):=
  {f:Fin n→ℝ | IsGoodFinSeq f}
lemma SetOfGoodFinSeqNonEmpty(n:ℕ)(hn:2≤n):(SetOfGoodFinSeq n).Nonempty:= by
  let f:=(fun i:Fin n=>if i = ⟨0,by omega⟩ then Real.sqrt (1/2) else if i=⟨n-1,by omega⟩ then -Real.sqrt (1/2) else 0)
  use f
  simp[SetOfGoodFinSeq,IsGoodFinSeq]
  constructor
  · intro i j hij
    by_cases hi0:i=⟨0,by omega⟩
    · simp[hi0]at hij
      simp[hi0,f]
      split_ifs with hj0 hjn
      · rfl
      · norm_num
      · norm_num
    simp[f,hi0]
    split_ifs with hj hi h1 h2 h3
    · simp[hi,hj] at hij
      omega
    · simp[hj] at hij
      by_contra
      apply hi0
      apply Fin.ext
      exact Nat.le_zero.mp hij
    rfl
    norm_num
    · simp[h3]at hij
      by_contra
      apply h1
      apply Fin.ext
      show j.val=n-1
      have h:j.val≥n-1:=hij
      omega
    rfl

  constructor
  · -- `SumOfFinSeq f id = 0`
    simp only [SumOfFinSeq, id]
    have hn1 : n - 1 ≠ 0 := by omega
    have hzl : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h
      have h0 : (0 : ℕ) = n - 1 := congrArg Fin.val h
      omega
    have hterm : ∀ i : Fin n,
        f i = (if i = ⟨0, by omega⟩ then Real.sqrt (1 / 2) else 0) +
          (if i = ⟨n - 1, by omega⟩ then -Real.sqrt (1 / 2) else 0) := by
      intro i
      by_cases hi : i = ⟨0, by omega⟩
      · rw [hi]; simp [f, hzl]
      · by_cases hj : i = ⟨n - 1, by omega⟩
        · rw [hj]; simp [f, hn1]
        · simp [f, hi, hj]
    calc ∑ i : Fin n, f i
        = ∑ i : Fin n, ((if i = ⟨0, by omega⟩ then Real.sqrt (1 / 2) else 0) +
            (if i = ⟨n - 1, by omega⟩ then -Real.sqrt (1 / 2) else 0)) :=
          Finset.sum_congr rfl (fun i _ ↦ hterm i)
      _ = (∑ i : Fin n, (if i = ⟨0, by omega⟩ then Real.sqrt (1 / 2) else 0)) +
            (∑ i : Fin n, (if i = ⟨n - 1, by omega⟩ then -Real.sqrt (1 / 2) else 0)) := by
          rw [Finset.sum_add_distrib]
      _ = Real.sqrt (1 / 2) + (-Real.sqrt (1 / 2)) := by
          rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
      _ = 0 := by ring
  · -- `SumOfFinSeq f (fun x => x ^ 2) = 1`
    simp only [SumOfFinSeq]
    have hn1 : n - 1 ≠ 0 := by omega
    have hzl : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h
      have h0 : (0 : ℕ) = n - 1 := congrArg Fin.val h
      omega
    have hterm : ∀ i : Fin n,
        f i ^ 2 = (if i = ⟨0, by omega⟩ then (Real.sqrt (1 / 2)) ^ 2 else 0) +
          (if i = ⟨n - 1, by omega⟩ then (Real.sqrt (1 / 2)) ^ 2 else 0) := by
      intro i
      by_cases hi : i = ⟨0, by omega⟩
      · rw [hi]; simp [f, hzl]
      · by_cases hj : i = ⟨n - 1, by omega⟩
        · rw [hj]; simp [f, hn1]
        · simp [f, hi, hj]
    calc ∑ i : Fin n, f i ^ 2
        = ∑ i : Fin n, ((if i = ⟨0, by omega⟩ then (Real.sqrt (1 / 2)) ^ 2 else 0) +
            (if i = ⟨n - 1, by omega⟩ then (Real.sqrt (1 / 2)) ^ 2 else 0)) :=
          Finset.sum_congr rfl (fun i _ ↦ hterm i)
      _ = (∑ i : Fin n, (if i = ⟨0, by omega⟩ then (Real.sqrt (1 / 2)) ^ 2 else 0)) +
            (∑ i : Fin n, (if i = ⟨n - 1, by omega⟩ then (Real.sqrt (1 / 2)) ^ 2 else 0)) := by
          rw [Finset.sum_add_distrib]
      _ = (Real.sqrt (1 / 2)) ^ 2 + (Real.sqrt (1 / 2)) ^ 2 := by
          rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
      _ = 1 := by
          have hc : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
          rw [hc, ← add_div, add_self_div_two]


noncomputable def SumOfSubFinSeq{n:ℕ}(S:Fin n→ℝ)(K:Finset (Fin n)):=
  K.sum (fun i=>S i)

noncomputable def SetOfSumOfSubFinSeq{n:ℕ}(K:Finset (Fin n)):Set ℝ:=
  {SumOfSubFinSeq S K | S∈SetOfGoodFinSeq n}
def AdmissibleSubSet{n:ℕ}(K:Finset (Fin n)):Prop:=
  ∀(f:Fin n→ℝ),IsGoodFinSeq f→SumOfSubFinSeq f K≥0

/-- 前 `m` 个下标 `{0, …, m-1}` 作为 `Fin n` 的子集（要求 `m ≤ n`）。 -/
def firstIndices {m n : ℕ} (h : m ≤ n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin m)).map
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩,
      fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij)⟩

/-- 一个下标属于 `firstIndices h` 当且仅当它的数值小于 `m`。 -/
lemma mem_firstIndices {m n : ℕ} (h : m ≤ n) {i : Fin n} :
    i ∈ firstIndices h ↔ i.val < m := by
  constructor
  · intro hi
    obtain ⟨a, -, ha⟩ := Finset.mem_map.mp hi
    have hv : i.val = a.val := (congrArg Fin.val ha).symm
    rw [hv]
    exact a.isLt
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- 前 `m` 个下标组成恰好 `m` 元集合。 -/
lemma firstIndices_card {m n : ℕ} (h : m ≤ n) : (firstIndices h).card = m := by
  simp [firstIndices]

/-- 前缀下标集是“可容许”的：单调不增且总和为零的序列，其前 `m` 项和非负。

证明思路：设 `P = ∑_{i<m} x_i`、`Q = ∑_{i≥m} x_i`。由于 `x` 单调不增，
前缀中的每个元素都不小于后缀中的每个元素，于是
`m·Q ≤ (n-m)·P`；又 `P + Q = 0`，故 `n·P ≥ 0`，即 `P ≥ 0`。 -/
lemma firstIndices_admissible {m n : ℕ} (h : m < n) :
    AdmissibleSubSet (firstIndices (Nat.le_of_lt h)) := by
  intro f hf
  have hle : m ≤ n := Nat.le_of_lt h
  have hanti : Antitone f := hf.1
  have htot : (∑ i : Fin n, f i) = 0 := by
    simpa [SumOfFinSeq] using hf.2.1
  have hKcard : (firstIndices hle).card = m := firstIndices_card hle
  have hdisj : Disjoint (firstIndices hle) (Finset.univ \ firstIndices hle) :=
    Finset.disjoint_sdiff
  have hunion : firstIndices hle ∪ (Finset.univ \ firstIndices hle) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsplit : (∑ i ∈ firstIndices hle, f i) +
      (∑ i ∈ Finset.univ \ firstIndices hle, f i) = 0 := by
    rw [← Finset.sum_union hdisj, hunion, htot]
  have hstep : (∑ i ∈ firstIndices hle, ∑ j ∈ Finset.univ \ firstIndices hle, f j) ≤
      (∑ i ∈ firstIndices hle, ∑ j ∈ Finset.univ \ firstIndices hle, f i) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
    have hi' : i.val < m := (mem_firstIndices hle).mp hi
    have hj' : m ≤ j.val := by
      refine Nat.le_of_not_lt (fun hlt => ?_)
      exact (Finset.mem_sdiff.mp hj).2 ((mem_firstIndices hle).mpr hlt)
    exact hanti (Fin.le_iff_val_le_val.mpr (by omega))
  have h1 : (∑ i ∈ firstIndices hle, ∑ j ∈ Finset.univ \ firstIndices hle, f j) =
      ((firstIndices hle).card : ℝ) *
        (∑ j ∈ Finset.univ \ firstIndices hle, f j) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ i ∈ firstIndices hle, ∑ j ∈ Finset.univ \ firstIndices hle, f i) =
      ((Finset.univ \ firstIndices hle).card : ℝ) *
        (∑ i ∈ firstIndices hle, f i) := by
    simp only [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hineq : ((firstIndices hle).card : ℝ) *
        (∑ j ∈ Finset.univ \ firstIndices hle, f j) ≤
      ((Finset.univ \ firstIndices hle).card : ℝ) *
        (∑ i ∈ firstIndices hle, f i) := by
    rw [← h1, ← h2]
    exact hstep
  have hLcard : (Finset.univ \ firstIndices hle).card = n - m := by
    rw [Finset.card_sdiff]
    simp [hKcard]
  have hP : 0 ≤ ∑ i ∈ firstIndices hle, f i := by
    have hn : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le m) h)
    have hk : ((firstIndices hle).card : ℝ) = (m : ℝ) := by exact_mod_cast hKcard
    have hl : ((Finset.univ \ firstIndices hle).card : ℝ) = (n : ℝ) - (m : ℝ) := by
      rw [hLcard, Nat.cast_sub hle]
    nlinarith [hineq, hsplit, hk, hl, hn]
  simpa [SumOfSubFinSeq] using hP

/-- 存在可容许的 `m` 元子集：取前 `m` 个下标即可。 -/
lemma exists_admissibleSubSet {m n : ℕ} (hm : m < n) :
    ∃ K : Finset (Fin n), K.card = m ∧ AdmissibleSubSet K :=
  ⟨firstIndices (Nat.le_of_lt hm), firstIndices_card (Nat.le_of_lt hm),
    firstIndices_admissible hm⟩
/-- 好数列的每一项都不超过 `1`：各项平方和为 `1`，故单项平方不超过 `1`。 -/
lemma IsGoodFinSeq_apply_le_one {n : ℕ} {S : Fin n → ℝ} (hS : IsGoodFinSeq S) (i : Fin n) :
    S i ≤ 1 := by
  obtain ⟨-, -, hsq⟩ := hS
  have htot : (∑ j : Fin n, S j ^ 2) = 1 := by
    simpa [SumOfFinSeq] using hsq
  have hle : S i ^ 2 ≤ ∑ j : Fin n, S j ^ 2 := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun j : Fin n ↦ S j ^ 2) (Finset.mem_univ i)
    rw [← hsplit]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ ↦ sq_nonneg (S j)))
  have h2 : S i ^ 2 ≤ 1 := hle.trans_eq htot
  nlinarith [h2, sq_nonneg (S i)]

/-- `SetOfSumOfSubFinSeq K` 非空：任取一个好数列 `S`，`∑_{i∈K} S i` 即是其中元素。 -/
lemma SetOfSumOfSubFinSeqNonempty {n : ℕ} (hn : 2 ≤ n) (K : Finset (Fin n)) :
    (SetOfSumOfSubFinSeq K).Nonempty := by
  obtain ⟨S, hS⟩ := SetOfGoodFinSeqNonEmpty n hn
  exact ⟨SumOfSubFinSeq S K, S, hS, rfl⟩

/-- `SetOfSumOfSubFinSeq K` 有上界 `n`：好数列每项 `≤ 1`，且 `K` 至多 `n` 个元素。 -/
lemma BddAboveSetOfSumOfSubFinSeq {n : ℕ} (K : Finset (Fin n)) :
    BddAbove (SetOfSumOfSubFinSeq K) := by
  refine ⟨(n : ℝ), ?_⟩
  rintro x ⟨S, hS, rfl⟩
  calc SumOfSubFinSeq S K = ∑ i ∈ K, S i := rfl
    _ ≤ ∑ i ∈ K, (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ IsGoodFinSeq_apply_le_one hS i)
    _ = (K.card : ℝ) := by simp
    _ ≤ (n : ℝ) := by
        have hcard : K.card ≤ n := by
          simpa using Finset.card_le_card (Finset.subset_univ K)
        exact_mod_cast hcard

noncomputable def SmallestUpperBoundOfSumOfSubFinSeq{n:ℕ}(K:Finset (Fin n)):ℝ:=
  sSup (SetOfSumOfSubFinSeq K)
/-- 所有**可容许**的 `m` 元子集 `K` 对应的 `sup ∑_{i∈K} x_i` 组成的有限集。 -/
noncomputable def SetOfSmallestUpperBoundOfAdmissibleSubSetWithCard(m:ℕ)(n:ℕ):Finset ℝ:= by
  classical
  exact (((Finset.univ : Finset (Fin n)).powersetCard m).filter AdmissibleSubSet).image
    SmallestUpperBoundOfSumOfSubFinSeq
/-- 题中的 `F(m,n)`：在所有可容许的 `m` 元子集 `K` 上，`∑_{i∈K} x_i` 的上确界的最小值；
    等价于“使题述命题成立的最小正实数 `C`”。 -/
noncomputable def F (m:ℕ)(n:ℕ)(_h1:1≤m)(h2:m<n):ℝ:=
  (SetOfSmallestUpperBoundOfAdmissibleSubSetWithCard m n).min' (by
    classical
    obtain ⟨K, hKcard, hKadm⟩ := exists_admissibleSubSet h2
    unfold SetOfSmallestUpperBoundOfAdmissibleSubSetWithCard
    rw [Finset.image_nonempty]
    exact ⟨K, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, hKcard⟩, hKadm⟩⟩)
/-- `F(m,n)` 恒为正：对 `1 ≤ m < n` 有 `0 < F m n h1 h2`。

证明用尖峰（归一化）序列 `x`：令 `v i0 = n-1`（其中 `i0 = 0`）、其余 `v i = -1`，
`t = √((n-1)n)`，`x = v / t`。则 `x` 是单调不增、和为 `0`、平方和为 `1` 的好序列；
并且任意可容许的 `m` 元子集 `K` 必含 `0`，此时 `∑_{i∈K} x i = (n-m)/t > 0`。
于是每个 `U_K = sSup {∑_{i∈K} x i}` 都为正，从而 `F = min_K U_K > 0`。 -/
lemma F_pos (m n : ℕ) (h1 : 1 ≤ m) (h2 : m < n) : 0 < F m n h1 h2 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  -- 尖峰序列（未归一化）`v` 与归一化因子 `t`
  let i0 : Fin n := ⟨0, by omega⟩
  let v : Fin n → ℝ := fun i => if i = i0 then (n : ℝ) - 1 else -1
  let t : ℝ := Real.sqrt (((n : ℝ) - 1) * (n : ℝ))
  have htpos : 0 < t := by
    have t_def : t = Real.sqrt (((n : ℝ) - 1) * (n : ℝ)) := rfl
    rw [t_def]
    exact Real.sqrt_pos_of_pos (by nlinarith)
  have ht2 : t ^ 2 = ((n : ℝ) - 1) * (n : ℝ) := by
    have t_def : t = Real.sqrt (((n : ℝ) - 1) * (n : ℝ)) := rfl
    rw [t_def]
    exact Real.sq_sqrt (by nlinarith)
  have ht2pos : 0 < ((n : ℝ) - 1) * (n : ℝ) := by nlinarith
  let x : Fin n → ℝ := fun i => v i / t
  have hv0 : v i0 = (n : ℝ) - 1 := by simp [v]
  have hvne : ∀ i : Fin n, i ≠ i0 → v i = -1 := by
    intro i hi
    simp [v, hi]
  -- `v` 单调不增
  have hv_anti : Antitone v := by
    intro i j hij
    by_cases hi : i = i0
    · rw [show v i = (n : ℝ) - 1 from by rw [hi]; exact hv0]
      by_cases hj : j = i0
      · rw [show v j = (n : ℝ) - 1 from by rw [hj]; exact hv0]
      · rw [hvne j hj]
        linarith
    · have hj : j ≠ i0 := by
        intro hj
        have hle : i.val ≤ (i0 : Fin n).val := by
          exact Fin.le_iff_val_le_val.mp (hj ▸ hij)
        have hle0 : i.val ≤ 0 := by simpa [i0] using hle
        have hval : i.val = 0 := by omega
        exact hi (Fin.ext (by simpa [i0] using hval))
      rw [hvne i hi, hvne j hj]
  -- `v` 在全集上的和与平方和
  have hsum_v : ∑ i : Fin n, v i = 0 := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) v
      (Finset.mem_univ i0)
    rw [← hsplit, hv0]
    have hconst : ∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, v i =
        ((n - 1 : ℕ) : ℝ) * (-1) := by
      rw [show ∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, v i =
          ∑ _ ∈ (Finset.univ : Finset (Fin n)).erase i0, (-1 : ℝ) from
        Finset.sum_congr rfl (fun i hi => hvne i (Finset.ne_of_mem_erase hi))]
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ]
      simp
    rw [hconst, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hsum_v2 : ∑ i : Fin n, v i ^ 2 = ((n : ℝ) - 1) * (n : ℝ) := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun i => v i ^ 2) (Finset.mem_univ i0)
    rw [← hsplit, hv0]
    have hconst : ∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, v i ^ 2 =
        ((n - 1 : ℕ) : ℝ) := by
      rw [show ∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, v i ^ 2 =
          ∑ _ ∈ (Finset.univ : Finset (Fin n)).erase i0, (1 : ℝ) from
        Finset.sum_congr rfl (fun i hi => by
          rw [hvne i (Finset.ne_of_mem_erase hi)]
          norm_num)]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ]
      simp
    rw [hconst, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  -- `x` 是好序列
  have hx_good : IsGoodFinSeq x := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      exact div_le_div_of_nonneg_right (hv_anti hij) (le_of_lt htpos)
    · simp only [SumOfFinSeq, id]
      rw [← Finset.sum_div, hsum_v, zero_div]
    · simp only [SumOfFinSeq]
      have hcongr : ∀ i : Fin n, (v i / t) ^ 2 = v i ^ 2 / t ^ 2 := fun i => by
        rw [div_pow]
      rw [Finset.sum_congr rfl (fun i _ => hcongr i), ← Finset.sum_div, hsum_v2, ht2]
      exact div_self (ne_of_gt ht2pos)
  -- 任意子集上 `v`、`x` 的和
  have hsumK_v : ∀ K : Finset (Fin n), i0 ∈ K → ∑ i ∈ K, v i =
      (n : ℝ) - (K.card : ℝ) := by
    intro K hK
    have hsplit := Finset.add_sum_erase K v hK
    rw [← hsplit, hv0]
    have hconst : ∑ i ∈ K.erase i0, v i = ((K.card - 1 : ℕ) : ℝ) * (-1) := by
      rw [show ∑ i ∈ K.erase i0, v i = ∑ _ ∈ K.erase i0, (-1 : ℝ) from
        Finset.sum_congr rfl (fun i hi => hvne i (Finset.ne_of_mem_erase hi))]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hK]
    rw [hconst]
    have hcard1 : 1 ≤ K.card := by
      have := Finset.card_pos.mpr ⟨i0, hK⟩
      omega
    rw [Nat.cast_sub hcard1, Nat.cast_one]
    ring
  have hsumK_v_not : ∀ K : Finset (Fin n), i0 ∉ K → ∑ i ∈ K, v i =
      -((K.card : ℝ)) := by
    intro K hK
    rw [show ∑ i ∈ K, v i = ∑ _ ∈ K, (-1 : ℝ) from
      Finset.sum_congr rfl (fun i hi => hvne i (fun h => hK (h ▸ hi)))]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hsumK_x : ∀ K : Finset (Fin n), i0 ∈ K →
      SumOfSubFinSeq x K = ((n : ℝ) - (K.card : ℝ)) / t := by
    intro K hK
    simp only [SumOfSubFinSeq]
    rw [← Finset.sum_div, hsumK_v K hK]
  have hsumK_x_not : ∀ K : Finset (Fin n), i0 ∉ K →
      SumOfSubFinSeq x K = -((K.card : ℝ)) / t := by
    intro K hK
    simp only [SumOfSubFinSeq]
    rw [← Finset.sum_div, hsumK_v_not K hK]
  -- 对可容许的 `m` 元子集，上确界为正
  have hKpos : ∀ K : Finset (Fin n), K.card = m → AdmissibleSubSet K →
      0 < SmallestUpperBoundOfSumOfSubFinSeq K := by
    intro K hKcard hKadm
    have hbdd := BddAboveSetOfSumOfSubFinSeq K
    have hmem : SumOfSubFinSeq x K ∈ SetOfSumOfSubFinSeq K := ⟨x, hx_good, rfl⟩
    have hle : SumOfSubFinSeq x K ≤ SmallestUpperBoundOfSumOfSubFinSeq K :=
      le_csSup hbdd hmem
    have hpos : 0 < SumOfSubFinSeq x K := by
      by_cases hi0 : i0 ∈ K
      · rw [hsumK_x K hi0, hKcard]
        apply div_pos
        · have hmn : (m : ℝ) < (n : ℝ) := by exact_mod_cast h2
          linarith
        · exact htpos
      · exfalso
        have hnonneg := hKadm x hx_good
        rw [hsumK_x_not K hi0] at hnonneg
        have hneg : -((K.card : ℝ)) / t < 0 := by
          apply div_neg_of_neg_of_pos
          · have : (0 : ℝ) < (K.card : ℝ) := by
              rw [hKcard]
              exact_mod_cast h1
            linarith
          · exact htpos
        linarith
    exact lt_of_lt_of_le hpos hle
  -- 目标：`F` 是这些上确界的最小值
  unfold F
  rw [Finset.lt_min'_iff]
  intro b hb
  unfold SetOfSmallestUpperBoundOfAdmissibleSubSetWithCard at hb
  rw [Finset.mem_image] at hb
  obtain ⟨K, hKmem, rfl⟩ := hb
  rw [Finset.mem_filter] at hKmem
  obtain ⟨hKpw, hKadm⟩ := hKmem
  rw [Finset.mem_powersetCard] at hKpw
  obtain ⟨-, hKcard⟩ := hKpw
  exact hKpos K hKcard hKadm

noncomputable def ImageOfF(n:ℕ):Finset ℝ:=(Finset.Ico 1 n).attach.image (fun ⟨m,hm⟩ => F m n (by
  simp[Finset.mem_Ico] at hm
  obtain⟨h,_⟩:=hm
  exact h)
  (by
  simp[Finset.mem_Ico] at hm
  obtain⟨_,h⟩:=hm
  exact h))
lemma ImageOfFNonEmpty(n:ℕ)(hn:n≥2):(ImageOfF n).Nonempty:=by
  unfold ImageOfF
  rw[Finset.image_nonempty,Finset.attach_nonempty_iff]
  use 1
  rw[Finset.mem_Ico]
  omega
/-- `min_{1 ≤ m ≤ n-1} F(m,n)`；`n < 2` 时 `ImageOfF n` 为空，约定取 `0`。 -/
noncomputable def minOverM(n:ℕ):ℝ:=
  if h : 2 ≤ n then (ImageOfF n).min' (ImageOfFNonEmpty n h) else 0

end CMO2026
