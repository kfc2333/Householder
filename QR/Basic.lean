import Mathlib
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
open scoped BigOperators
set_option linter.style.longLine false

namespace QR
noncomputable section
variable (u : NNReal)

abbrev Vec (n : ℕ) := Fin n → ℝ
def γ (n : ℕ) : ℝ := (n : ℝ) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ))

lemma gamma_nonneg (n : ℕ) (hnu : (n : ℝ) * (u : ℝ) < 1) : 0 ≤ γ u n := by
  have h1: 0 ≤ (n : ℝ) * (u : ℝ) := by
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le n
    · exact_mod_cast u.2
  have h2: 0 ≤ 1 - (n : ℝ) * (u : ℝ) := by
    linarith
  exact div_nonneg h1 h2

lemma gamma_monotune (n₁ n₂ : ℕ) (hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1) (hnu₂ : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) :
  γ u n₁ ≤ γ u n₂ := by
  calc
    γ u n₁ = (n₁ : ℝ) * (u : ℝ) / (1 - (n₁ : ℝ) * (u : ℝ)) := by simp [γ]
    _ ≤ (n₂ : ℝ) * (u : ℝ) / (1 - (n₁ : ℝ) * (u : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hle
        · exact_mod_cast u.2
      · have h1: 0 ≤ 1 - (n₁ : ℝ) * (u : ℝ) := by
          linarith
        exact h1
    _ ≤ (n₂ : ℝ) * (u : ℝ) / (1 - (n₂ : ℝ) * (u : ℝ)) := by
      apply div_le_div_of_nonneg_left
      · apply mul_nonneg
        · exact_mod_cast Nat.zero_le n₂
        · exact_mod_cast u.2
      · simp only [sub_pos]
        exact hnu₂
      · apply sub_le_sub_left
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hle
        · exact_mod_cast u.2
    _ = γ u n₂ := by simp [γ]

def diff_gamma_bound (n : ℕ) (x x' : ℝ) : Prop :=
  |x - x'| ≤ γ u n * |x|
def diff_gamma_bound_theta (n : ℕ) (x x' : ℝ) : Prop :=
  ∃ θ : ℝ, x' = x * (1 + θ) ∧ |θ| ≤ γ u n

lemma diff_gamma_bound_theta_iff_diff_gamma_bound (n : ℕ) (hnu : (n : ℝ) * (u : ℝ) < 1) (x x' : ℝ) :
  diff_gamma_bound_theta u n x x' ↔ diff_gamma_bound u n x x' := by
  constructor
  · rintro ⟨θ, hxx', hθ⟩
    rw [hxx', diff_gamma_bound]
    ring_nf
    simp only [abs_neg, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  · intro h
    by_cases hx : x = 0
    · exists 0
      rw [diff_gamma_bound, hx] at h
      simp only [zero_sub, abs_neg, abs_zero, mul_zero, abs_nonpos_iff] at h
      simp only [add_zero, mul_one, abs_zero, hx]
      exact ⟨h, gamma_nonneg u n hnu⟩
    · exists (x' / x - 1)
      constructor
      · ring_nf
        field_simp [hx]
      · rw [diff_gamma_bound] at h
        have : |x' / x - 1| = |x' - x| / |x| := by
          field_simp [hx]
          rw [abs_div]
          field_simp [hx]
        rw [this]
        field_simp [hx]
        rw [mul_comm, abs_sub_comm]
        exact h

-- we use η represents 1 + θ
def gamma_bound (n : ℕ) (η : ℝ) : Prop :=
  |η - 1| ≤ γ u n
def gamma_bound' (n : ℕ) (η : ℝ) : Prop :=
  diff_gamma_bound_theta u n 1 η

lemma gamma_bound_iff_gamma_bound' (n : ℕ) (η : ℝ) :
  gamma_bound u n η ↔ gamma_bound' u n η := by
  constructor
  · intro h
    exists (η - 1)
    simp only [add_sub_cancel, one_mul, true_and]
    exact h
  · rintro ⟨θ, hη, hθ⟩
    rw [hη, gamma_bound]
    ring_nf
    exact hθ

lemma gamma_bound_monotune (n₁ n₂ : ℕ) (η : ℝ) (hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1) (hnu₂ : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) (hη : gamma_bound u n₁ η) :
  gamma_bound u n₂ η := by
  rw [gamma_bound] at hη ⊢
  exact le_trans hη (gamma_monotune u n₁ n₂ hnu₁ hnu₂ hle)

lemma gamma_bound_mul (n₁ n₂ : ℕ) (η₁ η₂ : ℝ) (hnu : ((n₁ : ℝ) + (n₂ : ℝ)) * (u : ℝ) < 1) (hη₁ : gamma_bound u n₁ η₁) (hη₂ : gamma_bound u n₂ η₂) :
  gamma_bound u (n₁ + n₂) (η₁ * η₂) := by
  rw [gamma_bound] at hη₁ hη₂ ⊢
  have hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1 := by
    sorry
  have hnu₁_neq : (1 - (n₁ : ℝ) * (u : ℝ)) ≠ 0 := by linarith
  have hnu₂_neq : (1 - (n₂ : ℝ) * (u : ℝ)) ≠ 0 := by sorry
  have hnu_neq : (1 - ((n₁ + n₂) : ℝ) * (u : ℝ)) ≠ 0 := by linarith
  have h : (γ u n₁ + 1) * (γ u n₂ + 1) ≤ γ u (n₁ + n₂) + 1 := by
    calc
    _ = (1 / (1 - (n₁ : ℝ) * (u : ℝ))) * (γ u n₂ + 1) := by
      rw [γ]
      apply mul_eq_mul_right_iff.2
      left
      field_simp [hnu₁_neq]
      exact add_sub_cancel _ _
    _ = (1 / (1 - (n₁ : ℝ) * (u : ℝ))) * (1 / (1 - (n₂ : ℝ) * (u : ℝ))) := by
      rw [γ]
      apply mul_eq_mul_left_iff.2
      left
      field_simp [hnu₂_neq]
      exact add_sub_cancel _ _
    _ ≤ 1 / (1 - ((n₁ + n₂) : ℝ) * (u : ℝ)) := by
      field_simp
      sorry
    _ = γ u (n₁ + n₂) + 1 := by
      rw [γ]
      sorry
  calc
    |η₁ * η₂ - 1| = |(η₁ - 1) * (η₂ - 1) + (η₁ - 1) + (η₂ - 1)| := by
      ring_nf
    _ ≤ |(η₁ - 1) * (η₂ - 1) + (η₁ - 1)| + |(η₂ - 1)| := abs_add_le _ _
    _ ≤ |(η₁ - 1) * (η₂ - 1)| + |(η₁ - 1)| + |(η₂ - 1)| := by
      rw [add_le_add_iff_right]
      exact abs_add_le _ _
    _ ≤ γ u n₁ * γ u n₂ + γ u n₁ + γ u n₂ := by
      rw [abs_mul]
      gcongr
      exact gamma_nonneg u n₁ hnu₁
    _ ≤ γ u (n₁ + n₂) := by
      linarith [h]


def fl (x x' : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ (u : ℝ) ∧ x * (1 + δ) = x'
lemma fl_gammma_bound (x x' : ℝ) (hu : (u : ℝ) < 1) :
  fl u x x' → diff_gamma_bound u 1 x x' := by
  rintro ⟨δ, hδ, hfl⟩
  rw [diff_gamma_bound, ← hfl]
  ring_nf
  simp only [abs_neg, abs_mul]
  have : |δ| ≤ γ u 1 := by
    simp only [γ, Nat.cast_one, one_mul]
    have hpos : 0 < (1 - (u : ℝ)) := by
      linarith [hu]
    have hle : (u : ℝ) ≤ (u : ℝ) / (1 - (u : ℝ)) := by
      have : (u : ℝ) * 1 ≤ (u : ℝ) * (1 / (1 - (u : ℝ))) := by
        gcongr
        field_simp [hpos]
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, NNReal.zero_le_coe]
      simpa [div_eq_mul_inv]
    exact le_trans hδ hle
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right this (abs_nonneg x)
-- lemma fl_bound (n : ℝ) (x x' x'' : ℝ) (hnu : (n : ℝ + 1) * (u : ℝ) < 1) (hbound : diff_gamma_bound u n x x') (hfl : fl x' x'') ()

def fl_add (x y z : ℝ) : Prop :=
  fl u (x + y) z
def fl_mul (x y z : ℝ) : Prop :=
  fl u (x * y) z

def fl_add_bound
  (nx ny : ℕ)
  (x y x' y' z : ℝ)
  (hfl_add : fl_add u x' y' z)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u ((nx ⊔ ny) + 1) (x + y) z := by sorry

def fl_vec_dot : {n : ℕ} → Vec n → Vec n → ℝ → Prop
  | 0, _, _, z => z = 0
  | n + 1, x, y, z =>
    ∃ p s : ℝ,
      fl_mul u (x (Fin.last n)) (y (Fin.last n)) p ∧
      fl_vec_dot (n := n) (fun i => x (Fin.castSucc i)) (fun i => y (Fin.castSucc i)) s ∧
      fl_add u p s z

lemma fl_vec_dot_bound_delta
  (n : ℕ)
  (x y : Vec n)
  (z : ℝ)
  (hfl : fl_vec_dot u x y z) :
  ∃ θ : Fin n → ℝ,
    z = ∑ i, x i * y i * (1 + θ i) ∧
    (∀ i, |θ i| ≤ γ u (if (i : ℕ) = 0 then n else (n - i + 1))) :=
  by induction n generalizing z with
  | zero =>
    exists fun _ => 0
    simp only [fl_vec_dot] at hfl
    simp only [Finset.univ_eq_empty, add_zero, mul_one, Finset.sum_empty, abs_zero, γ, Nat.cast_ite,
    CharP.cast_eq_zero, ite_mul, zero_mul, IsEmpty.forall_iff, and_true]
    exact hfl
  | succ n ih =>
    -- p: product, i.e. x0 * y0.
    -- s: sum of the rest, i.e. ∑ i, x i.succ * y i.succ * (1 + θ_ih i)
    obtain ⟨p, s, hp, hfl_vec_dot, hfl_add⟩ := hfl
    obtain ⟨θ_ih, hθ_ih⟩ := ih (fun i => x (Fin.castSucc i)) (fun i => y (Fin.castSucc i)) s hfl_vec_dot
    sorry

theorem fl_vec_dot_bound
  (n : ℕ)
  (x y : Vec n)
  (z : ℝ)
  (hfl : fl_vec_dot u x y z) :
  |(z - (x ⬝ᵥ y))| ≤ γ u n * (x ⬝ᵥ y) := by
    sorry

end
end QR
