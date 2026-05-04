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

structure Householder (n : ℕ) (hn : n ≠ 0) where
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
  -- (1) s = sign(x₀) * fl(sqrt(fl(xᵀx)))
  let s := sign x hn * ‖x‖
  -- (2) v₀ = fl(x₀ + s)
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
    s := s,
    v0 := v0,
    v' := v',
    p := p,
    β := β,
    b := b,
    v := v
  }

lemma householder_s (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.s = sign x hn * ‖x‖ := by
  intro hv
  rfl
lemma householder_v0 (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v0 = x ⟨0, Nat.pos_of_ne_zero hn⟩ + hv.s := by
  intro hv
  rfl
lemma householder_v' (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v' = fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv.v0 else x i := by
  intro hv
  rfl
lemma householder_p (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.p = hv.s * hv.v0 := by
  intro hv
  rfl
lemma householder_β (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.β = 1 / hv.p := by
  intro hv
  rfl
lemma householder_b (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.b = Real.sqrt hv.β := by
  intro hv
  rfl
lemma householder_v (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.v = hv.b • hv.v' := by
  intro hv
  rfl

lemma householder_beta_nonneg (n : ℕ) (x : Vec n) (hn : n ≠ 0) :
  let hv := householder n x hn
  hv.β ≥ 0 := by
  intro hv
  rw [householder_β, householder_p, householder_v0]
  apply one_div_nonneg.2
  rw [left_distrib]
  apply add_nonneg
  · rw [householder_s]
    rw [mul_comm, ← mul_assoc, mul_comm]
    apply mul_nonneg
    · exact norm_nonneg x
    · simpa only [mul_comm] using sign_mul_nonneg n x hn
  · exact mul_self_nonneg _
lemma householder_p_pos (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) :
  let hv := householder n x hn
  hv.p > 0 := by
  intro hv
  rw [householder_p]
  sorry

theorem e1_of_householder
  (n : ℕ)
  (hn : n ≠ 0)
  (x : Vec n) :
  let hv := householder n x hn
  let P := 1 - (vecMulVec hv.v hv.v)
  P • x = fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then - sign x hn * ‖x‖ else 0 := by
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
  have : hv.v' = (fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv.s else 0) + x := by sorry
  have : (hv.β * hv.v' ⬝ᵥ x) = 1 := by
    rw [householder_β, householder_p, householder_v0, hv_back, this]
    rw [left_distrib]
    sorry
  have : (hv.v ⬝ᵥ x) • hv.v = hv.v' := by
    rw [householder_v, hv_back, smul_dotProduct, smul_comm, ←smul_assoc, ←smul_assoc]
    simp only [smul_eq_mul]
    unfold hv
    rw [householder_b n x hn, hv_back]
    rw [(Real.mul_self_sqrt (householder_beta_nonneg n x hn))]
    rw [this]
    simp only [one_smul]
  rw [this]
  ext i
  by_cases h : i = ⟨0, Nat.pos_of_ne_zero hn⟩
  · rw [if_pos h, h, householder_v', householder_v0, householder_s]
    simp only [Pi.sub_apply, ↓reduceIte, sub_add_cancel_left, neg_mul]
  · rw [householder_v', householder_v0, householder_s]
    simp only [Pi.sub_apply, if_neg h, sub_self, neg_mul]

end
end Householder
