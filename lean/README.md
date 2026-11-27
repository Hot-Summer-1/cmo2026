# 2026 年（第 42 届）中国数学奥林匹克 · Lean 4 形式化陈述

本工程用 Lean 4 + Lake 把两日六道题的形式化**陈述**写出来。只陈述命题，
不证明：题目的主定理（`problem1` … `problem6`）以及“答案常量”都以 `sorry` 收尾，
`lake build` 会编译通过并给出 `declaration uses 'sorry'` 警告，这是预期行为；
公共定义所需的辅助引理（如 `F_pos`）则给出了完整证明。

本工程使用 **Mathlib**（按需只导入用到的模块），主要涉及：

| 模块 | 用途 |
| --- | --- |
| `Mathlib.Basic.Real.Basic` | 实数 `ℝ` |
| `Mathlib.Data.Nat.Factorial.Basic` | 阶乘 `n!`（第 2 题，由 `Problem2.lean` 额外导入） |
| `Mathlib.Algebra.Ring.Parity` | `Odd` / `Even`（第 3 题“一奇一偶”） |
| `Mathlib.Analysis.Convex.Between`、`Mathlib.Analysis.Convex.Segment` | 线段与凸性（第 4 题） |
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace ℝ (Fin 2)`（第 4 题） |
| `Mathlib.Geometry.Euclidean.Basic`、`…Sphere.Basic` | 平面几何、球/外接圆（第 4 题） |
| `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic` | 仿射子空间与平行（第 4 题） |
| `Mathlib.Algebra.BigOperators.…` | 有限和（第 5、6 题） |
| `Mathlib.Data.Finset.Powerset`、`Mathlib.Data.Finset.Card`、`Mathlib.Data.Fin.Basic` | 子集、基数与下标（第 5、6 题） |

第 3 题**不使用实数**：题中的根式与距离条件都等价地化成了整数不等式，见下文。

各文件遵循 Mathlib 的 module system 写法（`module` + `public import` +
`@[expose] public section`），以避免与 Mathlib 模块系统不兼容的警告。

## 目录结构

```
lean/
├── lakefile.lean        # Lake 构建脚本（require mathlib）
├── lean-toolchain       # leanprover/lean4:v4.37.0-rc1（与 Mathlib 对应）
├── lake-manifest.json   # 依赖锁定（mathlib 及各依赖的具体 commit）
├── Cmo2026.lean         # 根模块（import 全部题目，all_problems 汇总）
├── README.md
└── Cmo2026/
    ├── Defs.lean        # 公共定义：第 1–6 题
    ├── Problem1.lean    # 第 1 题 (1)(2)
    ├── Problem2.lean    # 第 2 题
    ├── Problem3.lean    # 第 3 题 (1)(2)
    ├── Problem4.lean    # 第 4 题（求 AD/BC 的所有可能值）
    ├── Problem5.lean    # 第 5 题（求 |S| 的最大值）
    └── Problem6.lean    # 第 6 题（F(20,26) 与 min F 的上界）
```

## 构建

```bash
cd lean
lake exe cache get   # 首次：下载 Mathlib 预编译缓存（约 9100 个文件）
lake build
```

* 预编译缓存已下载到本工程的 `.lake/mathlib-cache/`（通过 `MATHLIB_CACHE_DIR`
  指定），此后 `lake build` 可离线进行。
* 若要重新下载缓存或清空缓存，删除 `.lake/mathlib-cache/` 即可。
* `lake-manifest.json` 已锁定依赖版本，不需要再 `lake update`。

## 形式化约定与说明（第 1–3 题）

| 原题表述 | Lean 中的表述 |
| --- | --- |
| 正整数数列 `{a_n}`（`n ≥ 1`） | `IsPosSeq : (ℕ → ℕ) → Prop` |
| 好数列递推式 | `IsGood`：`a (n+1) = if 1 < a n then a n - 1 else n` |
| `a_1 + ⋯ + a_t` | `prefixSum a t = (Finset.range t).sum (fun i => a (i+1))` |
| `a_1 = m = (1/t)(a_1+⋯+a_t)` | `t * m = prefixSum a t` 且 `a 1 = m`（`Admissible`） |
| (1) `t ≥ (5/2) m` | `5 * m ≤ 2 * t`（`ℕ` 上与原式等价：`2t ≥ 5m`） |
| (2) “最小的实数 C 使 t ≤ C m” | `IsUpperBound C := ∀ m t, Admissible m t → (t:ℝ) ≤ C * m`（定义在 `Defs.lean`）；答案常量 `your_answer_to_problem1_part2 : ℝ`（`sorry` 占位）；定理断言 `IsUpperBound C ∧ ∀ c < C, ¬ IsUpperBound c` |
| `n!` | Mathlib 的 `Nat.factorial`（`n.factorial`） |
| `a` 与 `n!+1` 互质 | `Int.gcd a ((n.factorial : ℤ) + 1) = 1` |
| `n!+1` 不是 `a^k-1` 的倍数 | `¬ (((n.factorial : ℤ) + 1) ∣ a ^ k - 1)` |
| 甲跳跃的四种位移 | `jiaMoves a b = [(a,b), (-b,a), (-a,-b), (b,-a)]` |
| 乙跳跃的四种位移 | `yiMoves a b = [(b,a), (-a,b), (-b,-a), (a,-b)]` |
| “任意次乙跳跃 + 不超过 k 次甲跳跃能跳到” | `ReachableJia a b k P`，其中 `jia.length ≤ k` |
| “不超过 k 次跳跃能跳到” | `ReachableAny a b k P`，其中 `jia.length + yi.length ≤ k` |
| (1) 中的 `k ≤ √((a²+b²)/2) − 100` | `2 * ((k:ℤ) + 100) ^ 2 ≤ a ^ 2 + b ^ 2` |
| (2) 中的 `k ≤ √2·a(a+b)/√(a²+2ab−b²) − 100` | `((k:ℤ) + 100) ^ 2 * (a^2 + 2*a*b - b^2) ≤ 2 * a^2 * (a+b)^2` |
| 点 `Q` 距原点 `≤ √(a²+b²)` | `Q.1 ^ 2 + Q.2 ^ 2 ≤ a ^ 2 + b ^ 2` |
| `a, b` 一奇一偶 | `OneOddOneEven a b`，即 `(Odd a ∧ Even b) ∨ (Even a ∧ Odd b)` |

几点说明：

* 第 1 题(2) 求的是使 `t ≤ C m` **恒成立**的**最小**实数 `C`（即所有可行 `t/m` 的上确界），
  `your_answer_to_problem1_part2` 以 `sorry` 占位，只断言其性质、不给出其数值。
  证明时请填入正确的数值。
* 第 3 题中的整点 `P`、`Q` 用 `Point := ℤ × ℤ` 表达：跳跃位移都是整向量，
  被跳到的点必为整点，故只需在整点上讨论。
* 第 3 题**不使用实数**：`k` 是跳跃次数（`ℕ`），题中三个实数条件在 `a > b > 0`
  下都等价地写成整数不等式（两边非负、平方可逆）：
  `k ≤ √((a²+b²)/2) − 100 ⇔ 2(k+100)² ≤ a²+b²`；
  `k ≤ √2·a(a+b)/√(a²+2ab−b²) − 100 ⇔ (k+100)²(a²+2ab−b²) ≤ 2a²(a+b)²`；
  `dist(Q,0) ≤ √(a²+b²) ⇔ Q₁²+Q₂² ≤ a²+b²`。
  因此第 3 题的陈述里不出现实数；`Problem3.lean` 自身也不导入任何 Mathlib 模块
  （只依赖 `Cmo2026.Defs`）。

## 形式化约定与说明（第 4–6 题）

| 原题表述 | Lean 中的表述 |
| --- | --- |
| 平面 | `Plane := EuclideanSpace ℝ (Fin 2)` |
| 有向面积 / 三点共线 | `cross`、`orient`（`Defs.lean`） |
| 凸四边形 | `IsStrictlyConvexQuadrilateral`（简单四边形 + 四个三角形有向面积同号） |
| 对角线 `AC` 与 `BD` 交于 `E` | `IsSegmentIntersection E A C B D`（两条线段交点） |
| `AD ∥ BC` | `AffineSubspace.Parallel line[ℝ,A,D] line[ℝ,B,C]` |
| 圆 `ABE`、`CDE` | `(Affine.Simplex.mk ![A,B,E] …).circumsphere`（Mathlib 的外接圆） |
| `F` 是两圆除 `E` 外的交点 | `F ∈ 两个 circumsphere ∧ F ≠ E` |
| `G ∈ 直线 EF`、`AG ∥ BD` | `G ∈ line[ℝ,E,F]`、`AffineSubspace.Parallel line[ℝ,A,G] line[ℝ,B,D]` |
| `EF·EG = EA²` | `dist E F * dist E G = dist E A ^ 2` |
| 求 `AD/BC` 的所有可能值 | `prop_problem4_part1`（所有构型的比值 ∈ `your_answer_to_problem4`）∧ `prop_problem4_part2`（集合中每个值都可实现）；答案 `your_answer_to_problem4 : Set ℝ` 以 `sorry` 占位 |
| `d` 元自然数组之集 `S` | `S : Finset (Fin d → ℕ)`（分量从 `0` 到 `d-1`） |
| 第 `i` 个分量的平均值 | `AvgOfIndex S i : ℚ = (∑ v ∈ S, v i) / S.card` |
| 平均值条件 | `IsGoodSet M S`：对 `i.val ≠ d-1` 有 `AvgOfIndex S i ≤ M`，对 `i.val = d-1` 有 `AvgOfIndex S i ≤ 3M+1` |
| 求集合 `S` 的最大元素个数 | `prop_problem5_part1 ∧ prop_problem5_part2`；答案 `your_answer_to_problem5 d M : ℕ` 以 `sorry` 占位 |
| `[n] = {1,…,n}` | `Fin n`（下标 `0` 到 `n-1`） |
| `x_1 ≥ … ≥ x_n` | `Antitone S` |
| `∑x_i = 0`、`∑x_i² = 1` | `SumOfFinSeq S id = 0`、`SumOfFinSeq S (fun x => x^2) = 1`（合称 `IsGoodFinSeq`） |
| `K ⊆ [n]` 为 `m` 元子集 | `K : Finset (Fin n)`，`K.card = m` |
| `∑_{i∈K} x_i` | `SumOfSubFinSeq S K` |
| `F(m,n)` | `F m n h1 h2`（`h1 : 1 ≤ m`，`h2 : m < n`）：在所有**可容许**的 `m` 元子集上取 `sSup {∑_{i∈K} S i}` 的最小值（可容许性由 `AdmissibleSubSet` 表达；用 `firstIndices` 证明可容许子集存在） |
| `min_{1≤m≤n-1} F(m,n)` | `minOverM n`（`n < 2` 时约定为 `0`） |
| `F > 0` | `F_pos`：`1 ≤ m → m < n → 0 < F m n h1 h2`，无 `sorry` 的引理 |

几点说明：

* 第 4 题的答案用 `your_answer_to_problem4 : Set ℝ` 占位；`prop_problem4` 用
  “任意构型的 `AD/BC` 都在集合中”和“集合中每个值都能实现”两条来刻画“所有可能值”。
  另外，`prop_problem4_part2` 中 `∃ (hQuadrilateral : …) (hE : …)` 的证明绑定是
  构造 `Affine.Simplex.circumsphere` 所需要的（Mathlib 的 `Simplex.mk` 要求独立性证明）。
* 第 5 题使用 0-based 分量（`Fin d`），平均值取在 `ℚ` 中；`IsGoodSet` 不再依赖
  `d ≥ 2` 的证明参数，命题中以 `2 ≤ d` 的形式出现。
* 第 6 题 `F` 只对**可容许**的 `m` 元子集取最小值（`AdmissibleSubSet`：所有好序列在
  `K` 上的和都非负）；`F_pos` 证明 `F > 0`。`minOverM` 是 `ImageOfF n` 的最小值，
  `n < 2` 时 `ImageOfF n` 为空，约定取 `0`。
