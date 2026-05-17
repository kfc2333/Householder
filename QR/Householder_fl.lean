import Mathlib
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import QR.Basic
import QR.Householder
open scoped BigOperators
open Matrix
open Basic
open Householder
set_option linter.style.longLine false
set_option linter.dupNamespace false

namespace Householder_fl
noncomputable section

variable (u : NNReal)

def fl_householder (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hv_fl : Householder n hn) :
  Prop :=
  -- (1) l' = fl(xᵀx)
  fl_vec_dot u x x hv_fl.l' ∧
  -- (2) l = fl(sqrt(l'))
  fl u (Real.sqrt hv_fl.l') hv_fl.l ∧
  hv_fl.s = sign x hn * hv_fl.l ∧
  -- (3) v₀ = fl(x₀ + s)
  fl_add u (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv_fl.s hv_fl.v0 ∧
  -- (4) p = fl(s * v₀)
  fl_mul u hv_fl.s hv_fl.v0 hv_fl.p ∧
  -- (5) β = fl(1 / p)
  fl u (1 / hv_fl.p) hv_fl.β ∧
  -- (6) b = fl(√β)
  fl u (Real.sqrt hv_fl.β) hv_fl.b ∧
  -- (7) v = fl(b • v')
  hv_fl.v' = (fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then hv_fl.v0 else (x i)) ∧
  fl_smul_vec u hv_fl.b hv_fl.v' hv_fl.v

theorem Lemma_19_1 (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) (hv_fl : Householder n hn) (hnu : (8 * n + 26 : ℝ) * (u : ℝ) < 1) (hfl : fl_householder u n x hn hv_fl) :
  diff_gamma_bound_vec u (5 * n + 18) (householder n x hn).v hv_fl.v := by
  have hu : 1 * (u : ℝ) < 1 := by
    simpa only [one_mul, zero_mul, zero_add] using convert_hnu u n 8 26 0 1 (by linarith) (by linarith) hnu
  rw [one_mul] at hu
  let hv := householder n x hn
  unfold fl_householder at hfl
  have hv_back : householder n x hn = hv := rfl
  rw [hv_back]
  rcases hfl with ⟨hfl_l', hfl_l, hfl_s, hfl_v0, hfl_p, hfl_β, hfl_b, hfl_v', hfl_v⟩
  have l'_bound : diff_gamma_bound u (n + 1) hv.l' hv_fl.l' := by
    exact fl_vec_dot_bound u n (by linarith [hnu]) x hv_fl.l' hfl_l'
  have l_bound : diff_gamma_bound u (n + 2) hv.l hv_fl.l := by
    have : diff_gamma_bound u (n + 1) √hv.l' √hv_fl.l' := by
      have : 2 * ((n + 1) : ℝ) * (u : ℝ) < 1 := by linarith [hnu]
      exact sqrt_trans_gamma_bound u (n + 1) hv.l' hv_fl.l' (l'_nonneg n x hn) (by simpa only [Nat.cast_add, Nat.cast_one] using this) l'_bound
    rw [expand_l, hv_back]
    have hnu' : (n + 1 + 1 : ℝ) * (u : ℝ) < 1 := by linarith [hnu]
    exact diff_gamma_bound_trans u (n + 1) 1 √hv.l' √hv_fl.l' hv_fl.l (by simpa only [Nat.cast_add, Nat.cast_one] using hnu') this (fl_to_gammma_bound u _ _ hu hfl_l)
  have s_bound : diff_gamma_bound u (n + 2) hv.s hv_fl.s := by
    rw [expand_s, hv_back, hfl_s]
    rw [diff_gamma_bound] at l_bound ⊢
    rw [abs_mul, ← mul_sub, abs_mul, ← mul_assoc, mul_comm (γ u (n + 2)), mul_assoc]
    exact mul_le_mul_of_nonneg_left l_bound (abs_nonneg _)
  have v0_bound : diff_gamma_bound u (n + 3) hv.v0 hv_fl.v0 := by
    rw [expand_v0, hv_back]
    have : diff_gamma_bound u 0 (x ⟨0, Nat.pos_of_ne_zero hn⟩) (x ⟨0, Nat.pos_of_ne_zero hn⟩) := by
      simp only [diff_gamma_bound, sub_self, abs_zero, γ, CharP.cast_eq_zero, zero_mul, sub_zero, div_one, Std.le_refl]
    have hnu' : (n + 2 + 1 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 1 3 (by linarith) (by linarith) hnu
      linarith
    by_cases h : (x ⟨0, Nat.pos_of_ne_zero hn⟩) < 0
    · have hvs_nonpos : hv.s ≤ 0 := by
        rw [expand_s, expand_l, sign]
        apply mul_nonpos_of_nonpos_of_nonneg
        · simp only [h, ↓reduceIte, Left.neg_nonpos_iff, zero_le_one]
        · exact Real.sqrt_nonneg _
      exact fl_add_bound' u 0 (n + 2) (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv.s (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv_fl.s hv_fl.v0 (by linarith [h]) hvs_nonpos hfl_v0 (by simpa only [le_add_iff_nonneg_left, zero_le, sup_of_le_right, Nat.cast_add, Nat.cast_ofNat] using hnu') this s_bound
    · have hvs_nonneg : hv.s ≥ 0 := by
        rw [expand_s, expand_l, sign]
        apply mul_nonneg
        · simp only [h, ↓reduceIte, zero_le_one]
        · exact Real.sqrt_nonneg _
      exact fl_add_bound u 0 (n + 2) (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv.s (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv_fl.s hv_fl.v0 (by simpa only [ge_iff_le, not_lt] using h) hvs_nonneg hfl_v0 (by simpa only [le_add_iff_nonneg_left, zero_le, sup_of_le_right, Nat.cast_add, Nat.cast_ofNat] using hnu') this s_bound
  have p_bound : diff_gamma_bound u (2 * n + 6) hv.p hv_fl.p := by
    rw [expand_p, hv_back]
    have hnu' : ((n + 2 : ℝ) + (n + 3 : ℝ) + 1) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 2 6 (by linarith) (by linarith) hnu
      linarith
    have := fl_mul_bound u (n + 2) (n + 3) hv.s hv.v0 hv_fl.s hv_fl.v0 hv_fl.p hfl_p (by simpa using hnu') s_bound v0_bound
    ring_nf at this
    ring_nf
    exact this
  have p_bound' : diff_gamma_bound u (4 * n + 12) (1 / hv.p) (1 / hv_fl.p) := by
    have : 2 * (2 * n + 6 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 4 12 (by linarith) (by linarith) hnu
      linarith
    have h := div_inv_trans_gamma_bound u (2 * n + 6) hv.p hv_fl.p (p_pos n x hn hx) (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using this) p_bound
    have : (2 * (2 * n + 6)) = 4 * n + 12 := by linarith
    rw [this] at h
    exact h
  have β_bound : diff_gamma_bound u (4 * n + 13) hv.β hv_fl.β := by
    rw [expand_β, hv_back]
    have := fl_to_gammma_bound u (1 / hv_fl.p) hv_fl.β hu hfl_β
    have hnu' : (4 * n + 12 + 1 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 4 13 (by linarith) (by linarith) hnu
      linarith
    exact diff_gamma_bound_trans u (4 * n + 12) 1 (1 / hv.p) (1 / hv_fl.p) hv_fl.β (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hnu') p_bound' this
  have b_bound : diff_gamma_bound u (4 * n + 14) hv.b hv_fl.b := by
    rw [expand_b, hv_back]
    have hnu₁ : 2 * (4 * n + 13 : ℝ) * (u : ℝ) < 1 := by linarith
    have hnu₂ : (4 * n + 13 + 1 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 4 14 (by linarith) (by linarith) hnu
      linarith
    have h1 := sqrt_trans_gamma_bound u (4 * n + 13) hv.β hv_fl.β (beta_nonneg n x hn) (by simpa using hnu₁) β_bound
    have h2 := fl_to_gammma_bound u (√hv_fl.β) hv_fl.b hu hfl_b
    exact diff_gamma_bound_trans u (4 * n + 13) 1 (√hv.β) (√hv_fl.β) hv_fl.b (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hnu₂) h1 h2
  rw [expand_v, expand_v', hv_back]
  rw [diff_gamma_bound_vec]
  rw [fl_smul_vec] at hfl_v
  simp only [Pi.smul_apply, smul_eq_mul]
  intro i
  have v_bound := fl_to_gammma_bound u (hv_fl.b * hv_fl.v' i) (hv_fl.v i) hu (hfl_v i)
  rw [hfl_v'] at v_bound
  by_cases hi : i = ⟨0, Nat.pos_of_ne_zero hn⟩
  · simp only [hi, ↓reduceIte] at v_bound ⊢
    have : (4 * n + 14 + (n + 3) : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 5 17 (by linarith) (by linarith) hnu
      linarith
    have b_bound' : diff_gamma_bound u (5 * n + 17) (hv.b * hv.v0) (hv_fl.b * hv_fl.v0) := by
      have h := mul_bound u (4 * n + 14) (n + 3) hv.b hv.v0 hv_fl.b hv_fl.v0 (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using this) b_bound v0_bound
      have : (4 * n + 14 + (n + 3)) = 5 * n + 17 := by linarith
      rw [this] at h
      exact h
    have : (5 * n + 17 + 1 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 5 18 (by linarith) (by linarith) hnu
      linarith
    have v_bound' : diff_gamma_bound u (5 * n + 18) (hv.b * hv.v0) (hv_fl.v ⟨0, Nat.pos_of_ne_zero hn⟩) := by
      exact diff_gamma_bound_trans u (5 * n + 17) 1 (hv.b * hv.v0) (hv_fl.b * hv_fl.v0) (hv_fl.v ⟨0, Nat.pos_of_ne_zero hn⟩) (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using this) b_bound' v_bound
    exact v_bound'
  · simp only [hi, ↓reduceIte] at v_bound ⊢
    have : (4 * n + 14 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 4 14 (by linarith) (by linarith) hnu
      linarith
    have b_bound' : diff_gamma_bound u (4 * n + 14) (hv.b * x i) (hv_fl.b * x i) := by
      exact mul_bound u (4 * n + 14) 0 hv.b (x i) hv_fl.b (x i) (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharP.cast_eq_zero, add_zero] using this) b_bound (by simp only [diff_gamma_bound, sub_self, abs_zero, γ, CharP.cast_eq_zero, zero_mul, sub_zero, div_one, Std.le_refl])
    have : (4 * n + 14 + 1 : ℝ) * (u : ℝ) < 1 := by
      have := convert_hnu u n 8 26 4 15 (by linarith) (by linarith) hnu
      linarith
    have v_bound' : diff_gamma_bound u (4 * n + 15) (hv.b * x i) (hv_fl.v i) := by
      exact diff_gamma_bound_trans u (4 * n + 14) 1 (hv.b * x i) (hv_fl.b * x i) (hv_fl.v i) (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using this) b_bound' v_bound
    have : (5 * n + 18 : ℝ) * (u : ℝ) < 1 := by
      exact convert_hnu u n 8 26 5 18 (by linarith) (by linarith) hnu
    exact diff_gamma_bound_monotune u (4 * n + 15) (5 * n + 18) (hv.b * x i) (hv_fl.v i) (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using this) (by linarith) v_bound'

end
end Householder_fl
