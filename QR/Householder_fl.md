# Householder_fl.md

```lean
def fl_householder (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hv_fl : Householder n hn)
```
定义了一个Householder变换过程每一步需要满足哪些条件后，可以看作一个在精度u下可能的有浮点计算误差的结果。

```lean
theorem Lemma_19_1 (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) (hv_fl : Householder n hn) (hnu : (8 * n + 26 : ℝ) * (u : ℝ) < 1) (hfl : fl_householder u n x hn hv_fl) :
  diff_gamma_bound_vec u (5 * n + 18) (householder n x hn).v hv_fl.v := by
```
本项目的中心定理。证明了在某线性条件下，Householder变换的结果在精度u下的误差界限。该定理表明误差随向量长度n只是线性的增加，并且给出了一个明确的界。在需要某特定精度的数值计算中，可以保证只需将u提到一个线性增长的精度，就可以得到结果的精度保证。