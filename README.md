# 2026 年（第 42 届）中国数学奥林匹克 · 第一天

本目录整理CMO题的两种成果：**LaTeX 排版**与
**Lean 4 形式化陈述**。两者互相独立。

## 目录结构

```
cmod1/
├── cmo2026-day1.tex     # LaTeX 源码（XeLaTeX 编译）
├── lean/                # Lean 4 + Mathlib 形式化陈述工程
└── .gitignore           # LaTeX / VSCode / Lean 构建产物（.lake/）的忽略规则
```

## LaTeX 排版

- 编译：`xelatex cmo2026-day1.tex`（使用 `ctexart` 文档类，需 XeLaTeX）。

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

- 文件：`Cmo2026/Defs.lean`（公共定义）、`Problem1.lean`、`Problem2.lean`、
  `Problem3.lean`；根模块 `Cmo2026.lean`。
- 对应关系：

  | 题 | Lean 陈述 | 约定 |
  | --- | --- | --- |
  | 1(1) | `problem1_part1`：`5 * m ≤ 2 * t` | 与原题 `t ≥ (5/2)m` 等价 |
  | 1(2) | `problem1_part2`：`IsUpperBound C ∧ ∀ c < C, ¬ IsUpperBound c` | C 以 `your_answer_to_problem1_part2`（`sorry`）占位 |
  | 2 | `problem2` | `Int.gcd a (n!+1) = 1`，`n!+1 ∤ a^k − 1`（`1 ≤ k ≤ n²`） |
  | 3(1) | `problem3_part1` | `∃ P, ∀ k, 2(k+100)² ≤ a²+b² → ¬ ReachableJia a b k P` |
  | 3(2) | `problem3_part2` | `∃ Q, Q₁²+Q₂² ≤ a²+b² ∧ ∀ k, (k+100)²(a²+2ab−b²) ≤ 2a²(a+b)² → ¬ ReachableAny a b k Q` |

- 第 3 题不使用实数：根式与距离条件在 `a > b > 0` 下等价地写成整数不等式
  （详见 `lean/Cmo2026/Problem3.lean` 头部注释）；可达性的步数预算用 `ℕ`。
- `lean/README.md` 有更详细的模块说明与形式化对照表。
