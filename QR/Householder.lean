import Mathlib
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import QR.Basic
open scoped BigOperators
open Matrix
open QR
set_option linter.style.longLine false
set_option linter.dupNamespace false

namespace Householder
noncomputable section
-- σ = - sign(x₀) * ‖x‖
def sign {n : ℕ} (x : Vec n) (hn : n ≠ 0) : ℝ :=
  if x ⟨0, Nat.pos_of_ne_zero hn⟩ < 0 then -1 else 1
lemma sign_mul_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) : sign x hn * x ⟨0, Nat.pos_of_ne_zero hn⟩ ≥ 0 := by
  unfold sign
  split_ifs with h
  · rw [neg_mul_comm, one_mul]
    linarith
  · simpa only [one_mul, not_lt] using h

lemma dotProduct_self_nonneg (n : ℕ) (x : Vec n) : x ⬝ᵥ x ≥ 0 := by
  rw [dotProduct]
  apply Finset.sum_nonneg
  simp only [Finset.mem_univ, forall_const]
  intro i
  exact mul_self_nonneg (x i)

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

def householder (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  Householder n hn :=
by
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  -- (1) l' = fl(xᵀx)
  let l' := x ⬝ᵥ x
  -- (2) l = fl(sqrt(l'))
  let l := Real.sqrt l'
  let s := sign x hn * l
  -- (4) v₀ = fl(x₀ + s)
  let v0 := x i₀ + s
  -- (3) p = fl(s * v₀)
  let p := s * v0
  -- (4) β = fl(1 / p)
  let β := 1 / p
  -- (5) b = fl(√β)
  let b := Real.sqrt β
  -- (6) v = fl(b • v')
  let v' : Vec n := fun i => if i = i₀ then v0 else x i
  let v := b • v'
  -- constr
  exact {
    l' := l',
    l := l,
    s := s,
    v0 := v0,
    v' := v',
    p := p,
    β := β,
    b := b,
    v := v
  }

lemma expand_l' (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.l' = x ⬝ᵥ x := by
  intro hv
  rfl
lemma expand_l (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.l = Real.sqrt hv.l' := by
  intro hv
  rfl
lemma expand_s (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.s = sign x hn * hv.l := by
  intro hv
  rfl
lemma expand_v0 (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v0 = x ⟨0, Nat.pos_of_ne_zero hn⟩ + hv.s := by
  intro hv
  rfl
lemma expand_v' (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v' = fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv.v0 else x i := by
  intro hv
  rfl
lemma expand_p (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.p = hv.s * hv.v0 := by
  intro hv
  rfl
lemma expand_β (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.β = 1 / hv.p := by
  intro hv
  rfl
lemma expand_b (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.b = Real.sqrt hv.β := by
  intro hv
  rfl
lemma expand_v (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v = hv.b • hv.v' := by
  intro hv
  rfl

lemma l'_ne_zero (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.l' ≠ 0 := by
  intro hv
  rw [expand_l']
  simpa only [ne_eq, dotProduct_self_eq_zero] using hx
lemma l'_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.l' ≥ 0 := by
  intro hv
  rw [expand_l']
  exact dotProduct_self_nonneg n x
lemma l'_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.l' > 0 := lt_of_le_of_ne' (l'_nonneg n x hn) (l'_ne_zero n x hn hx)
lemma l_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.l > 0 := by
  intro hv
  rw [expand_l]
  exact Real.sqrt_pos.2 (l'_pos n x hn hx)
lemma beta_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.β ≥ 0 := by
  intro hv
  rw [expand_β, expand_p, expand_v0]
  apply one_div_nonneg.2
  rw [left_distrib]
  apply add_nonneg
  · rw [expand_s]
    rw [mul_comm, ← mul_assoc, mul_comm]
    apply mul_nonneg
    · simpa only [expand_l] using Real.sqrt_nonneg _
    · simpa only [mul_comm] using sign_mul_nonneg n x hn
  · exact mul_self_nonneg _
lemma p_ne_zero (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.p ≠ 0 := by
  intro hv
  rw [expand_p]
  apply mul_ne_zero
  · rw [expand_s]
    apply mul_ne_zero
    · rw [sign]
      split_ifs <;> simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true]
    · linarith [l_pos n x hn hx]
  · rw [expand_v0, expand_s, sign]
    by_cases h : x ⟨0, Nat.pos_of_ne_zero hn⟩ < 0
    · simp only [h, if_true, neg_mul, one_mul]
      linarith [h, l_pos n x hn hx]
    · simp only [h, if_false, one_mul]
      linarith [h, l_pos n x hn hx]
lemma p_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.p > 0 := by
  intro hv
  have beta_nonneg : hv.β ≥ 0 := beta_nonneg n x hn
  rw [expand_β] at beta_nonneg
  simp only [one_div, inv_nonneg] at beta_nonneg
  rw [← ge_iff_le] at beta_nonneg
  exact lt_of_le_of_ne' beta_nonneg (p_ne_zero n x hn hx)

theorem e1_of_householder
  (n : ℕ)
  (x : Vec n)
  (hn : n ≠ 0)
  (hx : x ≠ 0) :
  let hv := householder n x hn
  let P := 1 - (vecMulVec hv.v hv.v)
  P • x = fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then - sign x hn * Real.sqrt (x ⬝ᵥ x) else 0 := by
  intro hv P
  have : P • x = x - (hv.v ⬝ᵥ x) • hv.v := by
    unfold P
    rw [sub_smul]
    simp only [one_smul, smul_eq_mulVec, sub_right_inj]
    rw [← op_smul_eq_smul]
    exact vecMulVec_mulVec hv.v hv.v x
  rw [this]
  clear this P
  have hv_back : householder n x hn = hv := rfl
  have : hv.v' = (fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv.s else 0) + x := by
    rw [expand_v', expand_v0, expand_s]
    funext i
    by_cases h : i = ⟨0, Nat.pos_of_ne_zero hn⟩
    · simp only [h, if_true, add_comm, Pi.add_apply]
    · simp only [h, if_false, Pi.add_apply, zero_add]
  have : (hv.β * hv.v' ⬝ᵥ x) = 1 := by
    rw [expand_β, this]
    field_simp [p_ne_zero n x hn hx]
    rw [add_dotProduct, expand_p, expand_v0, hv_back, left_distrib]
    have : (fun i ↦ if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv.s else 0) ⬝ᵥ x = hv.s * x ⟨0, Nat.pos_of_ne_zero hn⟩ := by
      simp only [dotProduct, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this, add_right_inj]
    rw [expand_s, expand_l, expand_l']
    calc
    _ = sign x hn * sign x hn * (x ⬝ᵥ x) := by
      rw [sign]
      split_ifs <;> simp only [mul_neg, mul_one, neg_neg, one_mul]
    _ = _ := by
      ring_nf
      rw [Real.sq_sqrt]
      exact dotProduct_self_nonneg n x
  have : (hv.v ⬝ᵥ x) • hv.v = hv.v' := by
    rw [expand_v, hv_back, smul_dotProduct, smul_comm, ←smul_assoc, ←smul_assoc]
    simp only [smul_eq_mul]
    unfold hv
    rw [expand_b n x hn, hv_back]
    rw [(Real.mul_self_sqrt (beta_nonneg n x hn))]
    rw [this]
    simp only [one_smul]
  rw [this]
  ext i
  by_cases h : i = ⟨0, Nat.pos_of_ne_zero hn⟩
  · rw [if_pos h, h, expand_v', expand_v0, expand_s, expand_l, expand_l']
    simp only [Pi.sub_apply, if_true, sub_add_cancel_left, neg_mul]
  · rw [expand_v', expand_v0, expand_s]
    simp only [Pi.sub_apply, if_neg h, sub_self, neg_mul]

end
end Householder
