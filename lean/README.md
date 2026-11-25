# 2026 年（第 42 届）中国数学奥林匹克 第一天 · Lean 4 形式化陈述

本工程用 Lean 4 + Lake 把第一天三道题的形式化**陈述**写出来。只陈述命题，
不证明：所有 `theorem`（以及“答案常量”）都以 `sorry` 收尾，`lake build` 会编译通过
并给出 `declaration uses 'sorry'` 警告，这是预期行为。

本工程使用 **Mathlib**（`Mathlib.Basic.Real.Basic` 起，按需只导入用到的模块）：

| 模块 | 用途 |
| --- | --- |
| `Mathlib.Basic.Real.Basic` | 实数 `ℝ`（第 1 题 (1)(2) 的常数） |
| `Mathlib.Algebra.Ring.Parity` | `Odd` / `Even`（第 3 题“a, b 一奇一偶”） |
| `Mathlib.Data.Nat.Factorial.Basic` | 阶乘 `n!`（第 2 题） |

第 3 题**不使用实数**：题中的根式与距离条件都等价地化成了整数不等式，见下文。

各文件遵循 Mathlib 的 module system 写法（`module` + `public import` +
`@[expose] public section`），以避免与 Mathlib 模块系统不兼容的警告。

## 目录结构

```
lean/
├── lakefile.lean        # Lake 构建脚本（require mathlib）
├── lean-toolchain       # leanprover/lean4:v4.37.0-rc1（与 Mathlib 对应）
├── lake-manifest.json   # 依赖锁定（mathlib 及各依赖的具体 commit）
├── Cmo2026.lean         # 根模块（import 全部题目）
├── check.lean           # 检查用到的公理和证明定理的类型
├── README.md
└── Cmo2026/
    ├── Defs.lean        # 公共定义：好数列、跳跳马位移与可达性、奇偶性
    ├── Problem1.lean    # 第 1 题 (1)(2)
    ├── Problem2.lean    # 第 2 题
    └── Problem3.lean    # 第 3 题 (1)(2)
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

## 形式化约定与说明

| 原题表述 | Lean 中的表述 |
| --- | --- |
| 正整数数列 `{a_n}`（`n ≥ 1`） | `IsPosSeq : (ℕ → ℕ) → Prop` |
| 好数列递推式 | `IsGood`：`a (n+1) = if 1 < a n then a n - 1 else n` |
| `a_1 + ⋯ + a_t` | `prefixSum a t = ((List.range t).map (fun i => a (i+1))).sum` |
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
* 第 3 题中“存在点 `P`, `Q`”等同于“存在整点 `P`, `Q`”（`Point := ℤ × ℤ`）：
  跳跃位移都是整向量，非整点不可能被跳到。
* 第 3 题**不使用实数**：`k` 是跳跃次数（`ℕ`），题中三个实数条件在 `a > b > 0`
  下都等价地写成整数不等式（两边非负、平方可逆）：
  `k ≤ √((a²+b²)/2) − 100 ⇔ 2(k+100)² ≤ a²+b²`；
  `k ≤ √2·a(a+b)/√(a²+2ab−b²) − 100 ⇔ (k+100)²(a²+2ab−b²) ≤ 2a²(a+b)²`；
  `dist(Q,0) ≤ √(a²+b²) ⇔ Q₁²+Q₂² ≤ a²+b²`。
  因此第 3 题的陈述里不出现实数；`Problem3.lean` 自身也不导入任何 Mathlib 模块
  （只依赖 `Cmo2026.Defs`）。
