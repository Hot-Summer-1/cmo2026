/-
  第 3 题

  给定互质的正整数 a, b, 满足 a > b 且 a, b 一奇一偶。
  平面直角坐标系上有一只 "跳跳马", 初始时在原点 (0,0)。
  一次甲跳跃是指: 将当前格的坐标加 (a,b), (-b,a), (-a,-b), (b,-a) 之一;
  一次乙跳跃是指: 将当前格的坐标加 (b,a), (-a,b), (-b,-a), (a,-b) 之一。

  (1) 求证: 存在点 P, 使得从原点到 P 不能用任意次乙跳跃和不超过
      √((a^2+b^2)/2) - 100 次甲跳跃跳到;
  (2) 求证: 存在距原点不超过 √(a^2+b^2) 的点 Q, 使得从原点到 Q 不能用
      不超过 √2 a(a+b)/√(a^2+2ab-b^2) - 100 次跳跃跳到。

  本文件不用实数: 题中的根式与距离条件在 a > b > 0 下都等价于整数不等式
  (两边非负, 平方保持等价):
  * `k ≤ √((a^2+b^2)/2) - 100`
      ⇔ `k + 100 ≤ √((a^2+b^2)/2)`
      ⇔ `2 (k+100)^2 ≤ a^2 + b^2`;
  * `Q` 到原点的距离 `≤ √(a^2+b^2)`  ⇔ `Q.1^2 + Q.2^2 ≤ a^2 + b^2`;
  * `k ≤ √2 a(a+b)/√(a^2+2ab-b^2) - 100`
      ⇔ `(k+100) √(a^2+2ab-b^2) ≤ √2 a(a+b)`
      ⇔ `(k+100)^2 (a^2+2ab-b^2) ≤ 2 a^2 (a+b)^2`。
  其中 `a^2 + 2ab - b^2 > 0` 由 `a > b > 0` 保证。
-/
module

public import Cmo2026.Defs

set_option autoImplicit false

@[expose] public section

namespace CMO2026

/-- 第 3 题 (1): 存在整点 `P`, 使得对一切满足 `2 (k+100)^2 ≤ a^2 + b^2` 的 `k`,
    都无法用 "任意次乙跳跃 + 不超过 `k` 次甲跳跃" 从原点跳到 `P`。 -/
theorem problem3_part1 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hcop : Int.gcd a b = 1) (hpar : OneOddOneEven a b) :
    ∃ P : Point,
      ∀ k : ℕ, 2 * ((k : ℤ) + 100) ^ 2 ≤ a ^ 2 + b ^ 2 → ¬ ReachableJia a b k P := by
  sorry

/-- 第 3 题 (2): 存在距原点不超过 `√(a^2+b^2)` 的整点 `Q`（即
    `Q.1^2 + Q.2^2 ≤ a^2 + b^2`）, 使得对一切满足
    `(k+100)^2 (a^2+2ab-b^2) ≤ 2 a^2 (a+b)^2` 的 `k`,
    都无法用不超过 `k` 次跳跃（甲、乙任意搭配）从原点跳到 `Q`。 -/
theorem problem3_part2 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hcop : Int.gcd a b = 1) (hpar : OneOddOneEven a b) :
    ∃ Q : Point,
      Q.1 ^ 2 + Q.2 ^ 2 ≤ a ^ 2 + b ^ 2 ∧
        ∀ k : ℕ,
          ((k : ℤ) + 100) ^ 2 * (a ^ 2 + 2 * a * b - b ^ 2) ≤ 2 * a ^ 2 * (a + b) ^ 2 →
            ¬ ReachableAny a b k Q := by
  sorry

end CMO2026
