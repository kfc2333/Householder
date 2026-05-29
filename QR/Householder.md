# Householder.md

```lean
def sign {n : ℕ} (x : Vec n) (hn : n ≠ 0) : ℝ :=
  if x ⟨0, Nat.pos_of_ne_zero hn⟩ < 0 then -1 else 1
```
定义 Householder 变换里用到的符号函数。它只看向量的第一个分量，用来决定后面构造中的符号方向。注意和通常的`sign`函数不同，这里没有考虑零的情况，直接把非负的情况都归为 `1`。

```lean
lemma sign_mul_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) : sign x hn * x ⟨0, Nat.pos_of_ne_zero hn⟩ ≥ 0
```
`sign x hn` 乘上向量首项非负。

```lean
lemma dotProduct_self_nonneg (n : ℕ) (x : Vec n) : x ⬝ᵥ x ≥ 0
```
向量和自身的点积总是非负的。

```lean
structure Householder (n : ℕ) (hn : n ≠ 0) where
  l' : ℝ
  l : ℝ
  s : ℝ
  v0 : ℝ
  v' : Vec n
  p : ℝ
  β : ℝ
  b : ℝ
  v : Vec n
```
定义了一个Householder过程，并且把变换的中间量全部打包成一个结构体。这里包含了从 `l'` 到最终向量 `v` 的每一步中间结果，便于后续统一引用和证明。

```lean
def householder (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  Householder n hn :=
```
定义标准严格的 Householder 构造过程。它按顺序计算 `l'`、`l`、`s`、`v0`、`p`、`β`、`b` 和 `v`，最后返回整个中间状态。

```lean
lemma expand_l' (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.l' = x ⬝ᵥ x
```
```lean
lemma expand_l (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.l = Real.sqrt hv.l'
```
```lean
lemma expand_s (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.s = sign x hn * hv.l
```
```lean
lemma expand_v0 (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v0 = x ⟨0, Nat.pos_of_ne_zero hn⟩ + hv.s
```
```lean
lemma expand_v' (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v' = fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv.v0 else x i
```
```lean
lemma expand_p (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.p = hv.s * hv.v0
```
```lean
lemma expand_β (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.β = 1 / hv.p
```
```lean
lemma expand_b (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.b = Real.sqrt hv.β
```
```lean
lemma expand_v (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v = hv.b • hv.v'
```
一系列用于展开标准Householder过程变量的引理。

```lean
lemma l'_ne_zero (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.l' ≠ 0
```
如果原向量 `x` 非零，那么 `l'` 也非零。这个引理保证后面平方根、倒数等操作不会退化到零。

```lean
lemma l'_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.l' ≥ 0
```
说明 `l'` 非负。因为它就是点积 `x ⬝ᵥ x`，所以本质上是平方和非负。

```lean
lemma l'_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.l' > 0
```
如果 `x` 非零，那么 `l'` 不但非负，而且严格大于零。

```lean
lemma l_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.l > 0
```
说明 `l` 也严格为正。因为 `l` 是 `l'` 的平方根，而 `l'` 已经被证明为正。

```lean
lemma beta_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.β ≥ 0
```
说明 `β` 非负。这个结论来自 `p` 的正性和倒数的非负性，是后面求平方根前的重要准备。

```lean
lemma p_ne_zero (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.p ≠ 0
```
说明 `p` 不为零。这样才能安全地定义 `β = 1 / p`，不会遇到除零问题。

```lean
lemma p_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.p > 0
```
说明 `p` 实际上是正数，不只是非零。这个结论在后面分析 `β` 的正性时更强，也更方便使用。

```lean
def sigma_e₁ (n : ℕ) (x : Vec n) (hn : n ≠ 0) : Vec n := fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then - sign x hn * Real.sqrt (x ⬝ᵥ x) else 0
```
定义标准基向量方向上的目标结果 `sigma_e₁`。它表示 Householder 变换最终要把 `x` 送到的那个只有首项非零的向量。

```lean
theorem sigma_e₁_of_householder
  (n : ℕ)
  (x : Vec n)
  (hn : n ≠ 0)
  (hx : x ≠ 0) :
  let hv := householder n x hn
  let P := 1 - (vecMulVec hv.v hv.v)
  P • x = sigma_e₁ n x hn
```
这是 Householder 构造的核心定理。它说明由 `v` 生成的投影矩阵 `P` 作用在 `x` 上，得到的正是 `sigma_e₁`，也就是把向量压到第一个坐标轴方向上。
