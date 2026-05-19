# Basic.md

```lean
lemma convert_hnu (n : ℕ) (a b c d : ℝ) (h₁ : c ≤ a) (h₂ : d ≤ b) (hnu : (a * n + b : ℝ) * (u : ℝ) < 1) : (c * n + d : ℝ) * (u : ℝ) < 1
```
一个Helper引理。帮助Lean在无法使用linarith识别hnu条件的时候显式地转换成一个更弱的条件。

```lean
abbrev Vec (n : ℕ) := Fin n → ℝ
```
使用Lean中最常用的Vec定义

```lean
def norm {n : ℕ} (x : Vec n) : ℝ := √(∑ i, ‖x i‖ ^ 2)
```
Lean中定义的Lp范数使用时较为不便，本项目并不需要很多范数的性质，因此自行定义了一个函数。

```lean
def γ (n : ℕ) : ℝ := (n : ℝ) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ))
```
定义参考文献中的误差`γ_n`。

```lean
lemma gamma_nonneg (n : ℕ) (hnu : (n : ℝ) * (u : ℝ) < 1) : γ u n ≥ 0
```
`n * u < 1`推出`γ u n`非负。

```lean
lemma gamma_lt_one (n : ℕ) (hnu : 2 * (n : ℝ) * (u : ℝ) < 1) : γ u n < 1
```
`2 * n * u < 1`推出`γ u n < 1`。

```lean
lemma gamma_monotune (n₁ n₂ : ℕ) (hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1) (hnu₂ : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) :
  γ u n₁ ≤ γ u n₂
```
`γ u n`关于`n`单调递增。

```lean
lemma gamma_mul_le (n₁ n₂ : ℕ) (hnu : ((n₁ + n₂) : ℝ) * (u : ℝ) < 1) :
  (γ u n₁ + 1) * (γ u n₂ + 1) ≤ γ u (n₁ + n₂) + 1
```
两个分别为`n_1`与`n_2`阶的误差因子相乘后被`n_1 + n_2`阶的误差因子控制。

```lean
def diff_gamma_bound (n : ℕ) (x x' : ℝ) : Prop :=
  |x - x'| ≤ γ u n * |x|
```
定义浮点误差界限。`x'`与`x`之间的误差被`γ u n`倍的`|x|`控制。

```lean
def diff_gamma_bound_theta (n : ℕ) (x x' : ℝ) : Prop :=
  ∃ θ : ℝ, x' = x * (1 + θ) ∧ |θ| ≤ γ u n
```
与`diff_gamma_bound`等价的定义。在能显式的给出误差`θ`的情况下使证明更简单。

```lean
lemma diff_gamma_bound_theta_iff_diff_gamma_bound (n : ℕ) (hnu : (n : ℝ) * (u : ℝ) < 1) (x x' : ℝ) :
  diff_gamma_bound_theta u n x x' ↔ diff_gamma_bound u n x x'
```
两个误差定义的等价性。

```lean
lemma pos_diff_gamma_bound_pos (n : ℕ) (x x' : ℝ) (hnu : 2 * (n : ℝ) * (u : ℝ) < 1) (hx : x > 0) (hbound : diff_gamma_bound u n x x') :
  x' > 0
```
如果真实值 `x` 为正，并且 `x'` 与 `x` 之间的误差满足 `diff_gamma_bound`，那么在足够小的误差条件下，`x'` 仍然保持正数。它在处理平方根、倒数等依赖正性的运算时非常重要。

```lean
def gamma_bound (n : ℕ) (η : ℝ) : Prop :=
  |η - 1| ≤ γ u n
```
把误差写成相对 `1` 的偏差。这个定义常用于处理 `1 + θ` 这种标准的浮点误差形式。

```lean
def gamma_bound' (n : ℕ) (η : ℝ) : Prop :=
  diff_gamma_bound_theta u n 1 η
```
`gamma_bound` 的等价写法。它直接把 `η` 看成 `1` 经过乘法扰动后的结果。

```lean
lemma gamma_bound_iff_gamma_bound' (n : ℕ) (η : ℝ) :
  gamma_bound u n η ↔ gamma_bound' u n η
```
两个关于 `η` 的误差定义是等价的。后续证明里可以按需要在两种形式之间切换。

```lean
lemma diff_gamma_bound_iff_gamma_bound (n : ℕ) (hnu : (n : ℝ) * (u : ℝ) < 1) (x x' : ℝ) (hx : x ≠ 0) :
  diff_gamma_bound u n x x' ↔ gamma_bound u n (x' / x)
```
把一般的相对误差界，改写成除以真实值之后对 `1` 的误差界。这个引理在处理比例、归一化和倒数时很方便。

```lean
lemma gamma_bound_monotune (n₁ n₂ : ℕ) (η : ℝ) (hnu : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) (hη : gamma_bound u n₁ η) :
  gamma_bound u n₂ η
```
`gamma_bound` 关于阶数 `n` 是单调的。已在较小阶数下成立的界，在更大阶数下仍然成立。

```lean
lemma diff_gamma_bound_monotune (n₁ n₂ : ℕ) (x x' : ℝ) (hnu : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) (hbound : diff_gamma_bound u n₁ x x') :
  diff_gamma_bound u n₂ x x'
```
`diff_gamma_bound` 也有同样的单调性。误差阶数放大以后，原来的估计仍然能保留。

```lean
theorem diff_gamma_bound_trans (n₁ n₂ : ℕ) (x x' x'' : ℝ) (hnu : ((n₁ + n₂) : ℝ) * (u : ℝ) < 1) (hbound₁ : diff_gamma_bound u n₁ x x') (hbound₂ : diff_gamma_bound u n₂ x' x'') :
  diff_gamma_bound u (n₁ + n₂) x x''
```
这是一个误差传递引理。前一步和后一步的误差可以合并成总阶数 `n₁ + n₂` 下的误差界。

```lean
lemma add_bound_nonneg
  (nx ny : ℕ)
  (x y x' y' : ℝ)
  (hx : x ≥ 0) (hy : y ≥ 0)
  (hnu : ((nx ⊔ ny) : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u (nx ⊔ ny) (x + y) (x' + y')
```
当 `x` 和 `y` 都非负时，加法的误差可以用两个分量误差直接控制。这个引理是后面分析向量分量相加的基础。

```lean
lemma add_bound_nonpos
  (nx ny : ℕ)
  (x y x' y' : ℝ)
  (hx : x ≤ 0) (hy : y ≤ 0)
  (hnu : ((nx ⊔ ny) : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u (nx ⊔ ny) (x + y) (x' + y')
```
这是上一个引理的非正版本。把两个非正量先取负，再化归到非负情形处理。

```lean
lemma mul_bound
  (nx ny : ℕ)
  (x y x' y' : ℝ)
  (hnu : ((nx + ny) : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u (nx + ny) (x * y) (x' * y')
```
乘法误差界。两个独立的误差项相乘后，仍能被总阶数 `nx + ny` 的界控制。

```lean
def fl (x x' : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ (u : ℝ) ∧ x * (1 + δ) = x'
```
这是最基础的浮点模型。它表示 `x'` 可以看成 `x` 经过一个大小不超过 `u` 的相对扰动得到。

```lean
lemma fl_to_gammma_bound (x x' : ℝ) (hu : (u : ℝ) < 1) :
  fl u x x' → diff_gamma_bound u 1 x x'
```
把基础浮点模型 `fl` 变成 `diff_gamma_bound` 的一阶误差界。它说明一次浮点运算的误差可以纳入 `γ_1` 控制。

```lean
lemma fl_bound (n : ℕ) (x x' x'' : ℝ) (hnu : ((n : ℝ) + 1) * (u : ℝ) < 1) (hbound : diff_gamma_bound u n x x') (hfl : fl u x' x'') :
  diff_gamma_bound u (n + 1) x x''
```
如果 `x` 到 `x'` 已经有 `n` 阶误差，再经过一次浮点运算得到 `x''`，那么总误差就是 `n + 1` 阶。

```lean
def diff_gamma_bound_vec (n : ℕ) {m : ℕ} (x : Vec m) (x' : Vec m) : Prop := ∀ i, diff_gamma_bound u n (x i) (x' i)
```
把标量误差界推广到向量上。它要求每个分量都满足同样阶数的误差控制。

```lean
def fl_add (x y z : ℝ) : Prop :=
  fl u (x + y) z
```
定义浮点加法模型。也就是把 `x + y` 的浮点结果记成 `z`。

```lean
def fl_mul (x y z : ℝ) : Prop :=
  fl u (x * y) z
```
定义浮点乘法模型。也就是把 `x * y` 的浮点结果记成 `z`。

```lean
lemma fl_add_bound
  (nx ny : ℕ)
  (x y x' y' z : ℝ)
  (hx : x ≥ 0) (hy : y ≥ 0)
  (hfl_add : fl_add u x' y' z)
  (hnu : ((nx ⊔ ny) + 1 : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u ((nx ⊔ ny) + 1) (x + y) z
```
非负情形下的浮点加法误差界。它先控制两个输入误差，再叠加一次浮点加法误差。

```lean
lemma fl_add_bound'
  (nx ny : ℕ)
  (x y x' y' z : ℝ)
  (hx : x ≤ 0) (hy : y ≤ 0)
  (hfl_add : fl_add u x' y' z)
  (hnu : ((nx ⊔ ny) + 1 : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u ((nx ⊔ ny) + 1) (x + y) z
```
非正情形下的浮点加法误差界。它和上一个引理配合，覆盖加法输入的两种符号情况。

```lean
lemma fl_mul_bound
  (nx ny : ℕ)
  (x y x' y' z : ℝ)
  (hfl_mul : fl_mul u x' y' z)
  (hnu : ((nx + ny) + 1 : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u ((nx + ny) + 1) (x * y) z
```
浮点乘法的误差界。先合并两个输入误差，再加上最后一次乘法产生的误差。

```lean
def fl_smul_vec (a : ℝ) (x : Vec n) (y : Vec n) : Prop :=
  ∀ i, fl u (a * x i) (y i)
```
定义向量的浮点数乘法模型。每个分量都由标量乘法的浮点结果组成。

```lean
def fl_vec_dot : {n : ℕ} → Vec n → Vec n → ℝ → Prop
```
定义向量点积的递归浮点模型。它把点积拆成首项乘积和剩余部分的递归相加。

```lean
theorem fl_vec_dot_bound
  (n : ℕ)
  (hnu : ((n : ℝ) + 1) * (u : ℝ) < 1)
  (x : Vec n)
  (z : ℝ)
  (hfl : fl_vec_dot u x x z) :
  diff_gamma_bound u (n + 1) (x ⬝ᵥ x) z
```
点积的整体误差界。它说明递归定义出来的浮点点积，和真实点积之间的误差可以被 `n + 1` 阶控制。

```lean
lemma sqrt_trans_gamma_bound (n : ℕ) (x x' : ℝ) (hx : x ≥ 0) (hnu : 2 * (n : ℝ) * (u : ℝ) < 1) (h_bound : diff_gamma_bound u n x x') :
  diff_gamma_bound u n (Real.sqrt x) (Real.sqrt x')
```
平方根运算的误差传递引理。只要原值非负并且误差足够小，开方后仍然满足同阶误差界。这里可以将界改进至 `n / 2`，但证明会更复杂。

```lean
lemma div_inv_trans_gamma_bound (n : ℕ) (x x' : ℝ) (hx : x > 0) (hnu : 2 * (n : ℝ) * (u : ℝ) < 1) (h_bound : diff_gamma_bound u n x x') :
  diff_gamma_bound u (2 * n) (1 / x) (1 / x')
```
倒数运算的误差传递引理。它说明如果 `x` 和 `x'` 足够接近且 `x` 为正，那么它们的倒数之间也能得到显式误差界。这个阶是紧的，但原论文中使用了 `n + 1` 阶，虽然不影响结果但此处做了修正。
