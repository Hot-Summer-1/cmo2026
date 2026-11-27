# 2026 年（第 42 届）中国数学奥林匹克 · 两日试题

本目录整理 CMO 试题的两种成果：**LaTeX 排版**与
**Lean 4 形式化陈述**。两者互相独立；其中 Lean 形式化覆盖两日全部六题。

## 目录结构

```
cmo2026/
├── cmo2026-day1.tex     # 第一天（第 1–3 题）LaTeX 源码（XeLaTeX 编译）
├── cmo2026-day2.tex     # 第二天（第 4–6 题）LaTeX 源码（XeLaTeX 编译）
├── lean/                # Lean 4 + Mathlib 形式化陈述工程
└── .gitignore           # LaTeX / VSCode / Lean 构建产物（.lake/、*.pdf 等）的忽略规则
```

## LaTeX 排版

- 编译：`xelatex cmo2026-day1.tex`、`xelatex cmo2026-day2.tex`
  （使用 `ctexart` 文档类，需 XeLaTeX）。

## 题目一览

| 题号 | 内容 | LaTeX | Lean |
| --- | --- | --- | --- |
| 1 | 数列：“好数列”的递推与 `t`、`m` 的关系 | `cmo2026-day1.tex` | `problem1_part1`、`problem1_part2` |
| 2 | 数论：模 `n!+1` 的互质整数与幂次 | 同上 | `problem2` |
| 3 | 格点跳跃：甲、乙两种跳跃的可达性估计 | 同上 | `problem3_part1`、`problem3_part2` |
| 4 | 平面几何：梯形中的圆与平行线，求 `AD/BC` | `cmo2026-day2.tex` | `problem4`（答案 `your_answer_to_problem4` 占位） |
| 5 | 组合：`d` 元自然数组之集的分量平均值约束，求集合 `S` 的最大元素个数 | 同上 | `problem5`（答案 `your_answer_to_problem5` 占位） |
| 6 | 组合与不等式：常数 `F(m,n)` 的计算与上界 | 同上 | `problem6`（答案 `your_answer_to_problem6_part1` 占位） |

## Lean 形式化陈述（`lean/` 子目录）

独立的 Lake 工程，依赖 Mathlib，**只陈述不证明**（所有命题以 `sorry` 收尾，
`lake build` 会给出预期的 `declaration uses 'sorry'` 警告）。

- 工具链：`leanprover/lean4:v4.37.0-rc1`；依赖版本由 `lake-manifest.json` 锁定。
- 构建：

  ```bash
  cd lean
  lake exe cache get   # 首次：下载 Mathlib 预编译缓存（约 9100 个文件）
  lake build
  ```

- 文件：`Cmo2026/Defs.lean`（公共定义：第 1–6 题）、`Problem1.lean` … `Problem6.lean`；
  根模块 `Cmo2026.lean`（`all_problems` 汇总六题）。
- 覆盖两日全部六题（第 1–3 题、第 4–6 题），均为陈述。
- 对应关系：

  | 题 | Lean 陈述 | 约定 |
  | --- | --- | --- |
  | 1(1) | `problem1_part1`：`5 * m ≤ 2 * t` | 与原题 `t ≥ (5/2)m` 等价 |
  | 1(2) | `problem1_part2`：`IsUpperBound C ∧ ∀ c < C, ¬ IsUpperBound c` | C 以 `your_answer_to_problem1_part2`（`sorry`）占位 |
  | 2 | `problem2` | `Int.gcd a (n!+1) = 1`，`n!+1 ∤ a^k − 1`（`1 ≤ k ≤ n²`） |
  | 3(1) | `problem3_part1` | `∃ P, ∀ k, 2(k+100)² ≤ a²+b² → ¬ ReachableJia a b k P` |
  | 3(2) | `problem3_part2` | `∃ Q, Q₁²+Q₂² ≤ a²+b² ∧ ∀ k, (k+100)²(a²+2ab−b²) ≤ 2a²(a+b)² → ¬ ReachableAny a b k Q` |
  | 4 | `prop_problem4_part1 ∧ prop_problem4_part2`（`problem4`） | 凸四边形、`AD∥BC`、`IsSegmentIntersection`、`circumsphere` 等见 `Defs.lean`；答案 `your_answer_to_problem4 : Set ℝ` 用两条刻画 |
  | 5 | `prop_problem5_part1 ∧ prop_problem5_part2`（`problem5`） | `S : Finset (Fin d → ℕ)`（0-based 分量），平均值在 `ℚ`；答案 `your_answer_to_problem5 d M : ℕ` |
  | 6 | `prop_problem6_part1 ∧ prop_problem6_part2`（`problem6`） | `F m n`（全函数，参数不合法即 `m = 0` 或 `n ≤ m` 时返回 `0`）= 可容许 `m` 元子集上 `sup ∑_{i∈K} x_i` 的最小值；`minOverM n` 为 `min_{1≤m≤n−1} F(m,n)` |

- `lean/README.md` 有更详细的模块说明与形式化对照表。
