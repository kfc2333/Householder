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
  fl_smul_vec u hv_fl.b hv_fl.v' hv_fl.v

lemma sqrt_trans_gamma_bound (n : ℕ) (x x' : ℝ) (hx : x ≥ 0) (hnu : 2 * (n : ℝ) * (u : ℝ) < 1) (h_bound : diff_gamma_bound u n x x') :
  diff_gamma_bound u n (Real.sqrt x) (Real.sqrt x') := by
  rw [diff_gamma_bound] at h_bound ⊢
  by_cases h : x = 0
  · simp only [h, zero_sub, abs_neg, abs_zero, mul_zero, abs_nonpos_iff,
    Real.sqrt_zero] at h_bound ⊢
    rw [h_bound]
    simp only [Real.sqrt_zero]
  · rw [← ne_eq] at h
    have hx' : x > 0 := lt_of_le_of_ne hx h.symm
    have hx'' : x' > 0 := pos_diff_gamma_bound_pos u n x x' hnu hx' h_bound
    have : |√x - √x'| * |√x| ≤ γ u n * |√x| * |√x| := by
      calc
        _ ≤ |√x - √x'| * |√x + √x'| := by
          apply mul_le_mul_of_nonneg_left
          · apply abs_le_abs_of_nonneg
            · exact Real.sqrt_nonneg x
            · simp only [le_add_iff_nonneg_right, Real.sqrt_nonneg]
          · exact abs_nonneg _
        _ = |x - x'| := by
          rw [← abs_mul]
          ring_nf
          rw [Real.sq_sqrt (by linarith [hx']), Real.sq_sqrt (by linarith [hx''])]
        _ ≤ γ u n * |x| := h_bound
        _ = _ := by
          rw [mul_assoc, ← abs_mul, Real.mul_self_sqrt]
          linarith
    have hx' := abs_pos.2 ((Real.sqrt_ne_zero hx).2 h)
    simp only [hx', mul_le_mul_iff_left₀] at this
    exact this

theorem Lemma_19_1 (n : ℕ) (x : Vec n) (hn : n ≠ 0) (hx : x ≠ 0) (hv_fl : Householder n hn) (hnu : (4 * n + 8 : ℝ) * (u : ℝ) < 1) (hfl : fl_householder u n x hn hv_fl) :
  diff_gamma_bound_vec u (4 * n + 8) x hv_fl.v := by
  have hu : 1 * (u : ℝ) < 1 := by
    simpa only [one_mul, zero_mul, zero_add] using convert_hnu u n 4 8 0 1 (by linarith) (by linarith) hnu
  rw [one_mul] at hu
  let hv := householder n x hn
  unfold fl_householder at hfl
  have hv_back : householder n x hn = hv := rfl
  rcases hfl with ⟨hfl_l', hfl_l, hfl_s, hfl_v0, hfl_p, hfl_β, hfl_b, hfl_v⟩
  have l'_bound : diff_gamma_bound u (n + 1) hv.l' hv_fl.l' := by
    exact fl_vec_dot_bound u n (by linarith [hnu]) x x hv_fl.l' hfl_l'
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
      have := convert_hnu u n 4 8 1 3 (by linarith) (by linarith) hnu
      linarith
    exact fl_add_bound u 0 (n + 2) (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv.s (x ⟨0, Nat.pos_of_ne_zero hn⟩) hv_fl.s hv_fl.v0 hfl_v0 (by simpa only [le_add_iff_nonneg_left, zero_le, sup_of_le_right, Nat.cast_add, Nat.cast_ofNat] using hnu') this s_bound
  have p_bound : diff_gamma_bound u (2 * n + 6) hv.p hv_fl.p := by
    rw [expand_p, hv_back]
    have hnu' : ((n + 2 : ℝ) + (n + 3 : ℝ) + 1) * (u : ℝ) < 1 := by
      have := convert_hnu u n 4 8 2 6 (by linarith) (by linarith) hnu
      linarith
    have := fl_mul_bound u (n + 2) (n + 3) hv.s hv.v0 hv_fl.s hv_fl.v0 hv_fl.p hfl_p (by simpa using hnu') s_bound v0_bound
    ring_nf at this
    ring_nf
    exact this
  have p_bound' : diff_gamma_bound u (2 * n + 6) (1 / hv.p) (1 / hv_fl.p) := by
    rw [diff_gamma_bound] at p_bound ⊢
    sorry
  have β_bound : diff_gamma_bound u (2 * n + 7) hv.β hv_fl.β := by
    rw [expand_β, hv_back]
    have := fl_to_gammma_bound u (1 / hv_fl.p) hv_fl.β hu hfl_β
    sorry
  sorry

end
end Householder_fl
