import Mathlib
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
open scoped BigOperators
set_option linter.style.longLine false

namespace QR
noncomputable section
variable (u : NNReal)

abbrev Vec (n : Nat) := Fin n → ℝ
def gamma (n : Nat) : ℝ := (n : ℝ) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ))

-- Lemma 3.1 in the book
lemma theta_n_leq_gamma_n_rho_posneg
  (n : Nat)
  (δ : Fin n → ℝ)
  (ρ : Fin n → ℤ)
  (hδ : ∀ i, |δ i| ≤ u)
  (hρ : ∀ i, ρ i = (1 : ℤ) ∨ ρ i = (-1 : ℤ))
  (hnu : (n : ℝ) * (u : ℝ) < 1) :
  ∃ θn : ℝ,
    (∏ i : Fin n, (1 + δ i) ^ (ρ i)) = 1 + θn ∧
    |θn| ≤ gamma u n :=
  by induction n with
  | zero =>
    exists 0
    simp [gamma]
  | succ n ih =>
    let δ_ih : Fin n → ℝ := fun i => δ i.succ
    let ρ_ih : Fin n → ℤ := fun i => ρ i.succ
    have hδ_ih : ∀ (i : Fin n), |δ_ih i| ≤ u := by
      intro i
      simpa [δ_ih] using hδ i.succ
    have hρ_ih : ∀ (i : Fin n), ρ_ih i = (1 : ℤ) ∨ ρ_ih i = (-1 : ℤ) := by
      intro i
      simpa [ρ_ih] using hρ i.succ
    have hnu_ih : (n : ℝ) * (u : ℝ) < 1 := by
      have hle_nat : (n : ℝ) ≤ (n.succ : ℝ) := by
        exact_mod_cast Nat.le_succ n
      have hle_mul : (n : ℝ) * (u : ℝ) ≤ (n.succ : ℝ) * (u : ℝ) := by
        exact mul_le_mul_of_nonneg_right hle_nat (by exact_mod_cast u.2)
      exact lt_of_le_of_lt hle_mul hnu
    have hnu_neq1 : (n : ℝ) * (u : ℝ) ≠ 1 := by
      exact ne_of_lt hnu_ih
    have hnu_neq : 1 - (u : ℝ) * (n : ℝ) ≠ 0 := by
      linarith
    have uge0 : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast u.property
    have hu_le : (u : ℝ) ≤ (n.succ : ℝ) * (u : ℝ) := by
      have : (1 : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa [one_mul] using mul_le_mul_of_nonneg_right this uge0
    have ul1 : (u : ℝ) < 1 :=
      lt_of_le_of_lt hu_le hnu
    obtain ⟨θn, hθn, hθn_bound⟩ := ih δ_ih ρ_ih hδ_ih hρ_ih hnu_ih
    cases (hρ 0) with
    | inl h=>
      exists δ 0 + (1 + δ 0) * θn
      constructor
      · rw [Fin.prod_univ_succ, hθn, h]
        simp
        ring
      · calc
          |(δ 0 : ℝ) + (1 + δ 0) * θn| ≤ |(δ 0 : ℝ)| + |(1 + δ 0) * θn| := by
            exact abs_add_le _ _
          |(δ 0 : ℝ)| + |(1 + δ 0 : ℝ) * θn| = |(δ 0 : ℝ)| + |(1 + δ 0 : ℝ)| * |θn| := by
            simp
          |(δ 0 : ℝ)| + |(1 + δ 0 : ℝ)| * |θn|
          ≤ (u : ℝ) + (1 + (u : ℝ)) * ((n : ℝ) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ))) := by
            gcongr
            · exact (hδ 0)
            · have : |(1 + δ 0 : ℝ)| ≤ 1 + u := by
                calc
                  |(1 + δ 0 : ℝ)| ≤ |1| + |(δ 0 : ℝ)| := by
                    apply abs_add_le 1 (δ 0)
                  _ ≤ 1 + |(δ 0 : ℝ)| := by simp
                  _ ≤ 1 + u := by exact add_le_add_right (hδ 0) 1
              exact this
            · exact hθn_bound
          u + (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u))
          = ((n : ℝ) + 1) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ)) := by
            field_simp [hnu_neq]
            ring
          ((n : ℝ) + 1) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ)) ≤ gamma u n.succ := by
            simp only [gamma, Nat.cast_succ]
            apply mul_le_mul_of_nonneg_left
            · have h1: 0 < 1 - ((n : ℝ) + 1) * (u : ℝ) := by
                simp [Nat.cast_succ] at hnu
                linarith
              have h2: 1 - ((n : ℝ) + 1) * (u : ℝ) ≤ 1 - (n : ℝ) * (u : ℝ) := by
                ring_nf
                simp
              exact inv_anti₀ h1 h2
            · apply mul_nonneg
              · exact_mod_cast Nat.zero_le n.succ
              · exact_mod_cast u.2
    | inr h=>
      exists (θn - δ 0) / (1 + δ 0)
      have : 1 + δ 0 > 0 := by
        have : (δ 0 : ℝ) ≥ -(u : ℝ) := by
          have h := abs_le.mp (hδ 0)
          exact h.1
        linarith
      constructor
      · rw [Fin.prod_univ_succ, hθn, h]
        field_simp
        ring
      · have uunge0 : (u : ℝ) ^ 2 * (n : ℝ) ≥ 0 := by
          apply mul_nonneg
          · exact sq_nonneg (u : ℝ)
          · exact_mod_cast Nat.zero_le n
        calc
          |(θn - δ 0) / (1 + δ 0)| = |(θn - δ 0)| / |(1 + δ 0)| := by
            exact abs_div _ _
          |(θn - δ 0)| / |(1 + δ 0)| ≤ |(θn - δ 0)| / (1 - (u : ℝ)) := by
            have h1: 1 - (u : ℝ) ≤ |(1 + δ 0)| := by
              calc
                1 - (u : ℝ) ≤ 1 + δ 0 := by
                  have h := abs_le.mp (hδ 0)
                  linarith
                _ ≤ |(1 + δ 0)| := by
                  exact le_abs_self (1 + δ 0)
            apply mul_le_mul_of_nonneg_left
            · exact inv_anti₀ (by linarith) h1
            · exact abs_nonneg _
          |(θn - δ 0)| / (1 - (u : ℝ)) ≤ (|θn| + |(δ 0 : ℝ)|) / (1 - (u : ℝ)) := by
            field_simp [ul1]
            have := (abs_add_le θn (-(δ 0)))
            simp only [abs_neg] at this
            exact this
          (|θn| + |(δ 0 : ℝ)|) / (1 - (u : ℝ)) ≤ (|θn| + u) / (1 - (u : ℝ)) := by
            field_simp [ul1]
            simp [(hδ 0)]
          (|θn| + u) / (1 - (u : ℝ)) ≤ (gamma u n + u) / (1 - (u : ℝ)) := by
            field_simp [ul1]
            simp only [gamma, add_le_add_iff_right]
            exact hθn_bound
          (gamma u n + u) / (1 - (u : ℝ)) = (((n : ℝ) + 1) * (u : ℝ) - (n : ℝ) * (u : ℝ) * (u : ℝ)) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) := by
            simp only [gamma]
            have : (1 - (u : ℝ)) ≠ 0 := by linarith
            have : (1 - (n : ℝ) * (u : ℝ)) ≠ 0 := by linarith
            field_simp [ul1]
            ring
          (((n : ℝ) + 1) * (u : ℝ) - (n : ℝ) * (u : ℝ) * (u : ℝ)) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) ≤ ((n : ℝ) + 1) * (u : ℝ) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) := by
            have : (1 - (u : ℝ)) ≠ 0 := by
              linarith
            have : (1 - (n : ℝ) * (u : ℝ)) > 0 := by
              linarith
            field_simp [ul1, this]
            ring_nf
            simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
            exact uunge0
          ((n : ℝ) + 1) * (u : ℝ) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) ≤ gamma u n.succ := by
            simp only [gamma, Nat.cast_succ]
            apply mul_le_mul_of_nonneg_left
            · have h1: 0 < 1 - ((n : ℝ) + 1) * (u : ℝ) := by
                simp [Nat.cast_succ] at hnu
                linarith
              have h2: 1 - ((n : ℝ) + 1) * (u : ℝ) ≤ (1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ)) := by
                ring_nf
                simp only [tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right]
                rw [mul_comm (n : ℝ) ((u : ℝ) ^ 2)]
                exact uunge0
              exact inv_anti₀ h1 h2
            · apply mul_nonneg
              · exact_mod_cast Nat.zero_le n.succ
              · exact_mod_cast u.2

def fl (x y : Real) : Prop :=
  ∃ δ : ℝ, |δ| ≤ (u : ℝ) ∧ x * (1 + δ) = y

def fl_add (x y z : Real) : Prop :=
  fl u (x + y) z
def fl_mul (x y z : Real) : Prop :=
  fl u (x * y) z

def fl_vec_dot : {n : Nat} → Vec n → Vec n → Real → Prop
  | 0, _, _, z => z = 0
  | n + 1, x, y, z =>
    ∃ p s : ℝ,
      fl_mul u (x 0) (y 0) p ∧
      fl_vec_dot (n := n) (fun i => x i.succ) (fun i => y i.succ) s ∧
      fl_add u p s z

end
end QR
