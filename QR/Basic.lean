import Mathlib
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
open scoped BigOperators
open scoped Matrix.Norms.Frobenius
set_option linter.style.longLine false

namespace Basic
noncomputable section
variable (u : NNReal)

abbrev Vec (n : ℕ) := Fin n → ℝ
def norm {n : ℕ} (x : Vec n) : ℝ := √(∑ i, ‖x i‖ ^ 2)
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
lemma diff_gamma_bound_iff_gamma_bound (n : ℕ) (hnu : (n : ℝ) * (u : ℝ) < 1) (x x' : ℝ) (hx : x ≠ 0) :
  diff_gamma_bound u n x x' ↔ gamma_bound u n (x' / x) := by
  rw [← diff_gamma_bound_theta_iff_diff_gamma_bound u n hnu x x', gamma_bound_iff_gamma_bound', gamma_bound', diff_gamma_bound_theta, diff_gamma_bound_theta]
  constructor
  · rintro ⟨θ, h₁, h₂⟩
    refine ⟨θ, ?_, h₂⟩
    field_simp [h₁, hx]
    exact h₁
  · rintro ⟨θ, h₁, h₂⟩
    refine ⟨θ, ?_, h₂⟩
    field_simp [hx] at h₁
    exact h₁

lemma gamma_bound_monotune (n₁ n₂ : ℕ) (η : ℝ) (hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1) (hnu₂ : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) (hη : gamma_bound u n₁ η) :
  gamma_bound u n₂ η := by
  rw [gamma_bound] at hη ⊢
  exact le_trans hη (gamma_monotune u n₁ n₂ hnu₁ hnu₂ hle)

theorem diff_gamma_bound_trans (n₁ n₂ : ℕ) (x x' x'' : ℝ) (hnu : ((n₁ : ℝ) + (n₂ : ℝ)) * (u : ℝ) < 1) (hbound₁ : diff_gamma_bound u n₁ x x') (hbound₂ : diff_gamma_bound u n₂ x' x'') :
  diff_gamma_bound u (n₁ + n₂) x x'' := by
  have hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1 := by
    sorry
  have hnu₂ : (n₂ : ℝ) * (u : ℝ) < 1 := by
    sorry
  have hnu₁_neq : (1 - (n₁ : ℝ) * (u : ℝ)) ≠ 0 := by linarith
  have hnu₂_neq : (1 - (n₂ : ℝ) * (u : ℝ)) ≠ 0 := by linarith
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

  rw [← diff_gamma_bound_theta_iff_diff_gamma_bound] at hbound₁ hbound₂ ⊢
  · rcases hbound₁ with ⟨θ₁, hxx', hθ₁⟩
    rcases hbound₂ with ⟨θ₂, hx'x'', hθ₂⟩
    exists (θ₁ + θ₂ + θ₁ * θ₂)
    rw [hx'x'', hxx']
    ring_nf
    simp only [true_and]
    sorry
  · simpa [Nat.cast_add] using hnu
  · exact hnu₂
  · exact hnu₁
lemma gamma_bound_trans (n₁ n₂ : ℕ) (η₁ η₂ : ℝ) (hnu : ((n₁ : ℝ) + (n₂ : ℝ)) * (u : ℝ) < 1) (hη₁ : gamma_bound u n₁ η₁) (hη₂ : gamma_bound u n₂ η₂) :
  gamma_bound u (n₁ + n₂) (η₁ * η₂) := by
  sorry


def fl (x x' : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ (u : ℝ) ∧ x * (1 + δ) = x'
lemma fl_to_gammma_bound (x x' : ℝ) (hu : (u : ℝ) < 1) :
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
lemma fl_bound (n : ℕ) (x x' x'' : ℝ) (hnu : ((n : ℝ) + 1) * (u : ℝ) < 1) (hbound : diff_gamma_bound u n x x') (hfl : fl u x' x'') :
  diff_gamma_bound u (n + 1) x x'' := by
  have hbound' : diff_gamma_bound u 1 x' x'' := by
    apply fl_to_gammma_bound u x' x''
    · sorry
    · exact hfl
  sorry

def diff_gamma_bound_vec (n : ℕ) {m : ℕ} (x : Vec m) (x' : Vec m) : Prop := diff_gamma_bound u n (norm x) (norm x')

def fl_add (x y z : ℝ) : Prop :=
  fl u (x + y) z
def fl_mul (x y z : ℝ) : Prop :=
  fl u (x * y) z

def fl_add_bound
  (nx ny : ℕ)
  (x y x' y' z : ℝ)
  (hfl_add : fl_add u x' y' z)
  (hnu : ((nx ⊔ ny) + 1 : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u ((nx ⊔ ny) + 1) (x + y) z := by sorry
def fl_mul_bound
  (nx ny : ℕ)
  (x y x' y' z : ℝ)
  (hfl_mul : fl_mul u x' y' z)
  (hnu : ((nx + ny) + 1 : ℝ) * (u : ℝ) < 1)
  (hboundx : diff_gamma_bound u nx x x')
  (hboundy : diff_gamma_bound u ny y y') :
  diff_gamma_bound u ((nx + ny) + 1) (x * y) z := by sorry

def fl_smul_vec (a : ℝ) (x : Vec n) (y : Vec n) : Prop :=
  ∀ i, fl u (a * x i) (y i)
lemma fl_smul_vec_bound
  (n : ℕ)
  (a : ℝ)
  (x x' x'' : Vec m)
  (hnu : (n + 1 : ℝ) * (u : ℝ) < 1)
  (hbound : diff_gamma_bound_vec u n x x')
  (hfl : fl_smul_vec u a x' x'') :
  diff_gamma_bound_vec u (n + 1) x x'' := by
  sorry

def fl_vec_dot : {n : ℕ} → Vec n → Vec n → ℝ → Prop
  | 0, _, _, z => z = 0
  | n + 1, x, y, z =>
    ∃ p s : ℝ,
      fl_mul u (x 0) (y 0) p ∧
      fl_vec_dot (fun i => x (Fin.succ i)) (fun i => y (Fin.succ i)) s ∧
      fl_add u p s z

theorem fl_vec_dot_bound
  (n : ℕ)
  (hnu : ((n : ℝ) + 1) * (u : ℝ) < 1)
  (x y : Vec n)
  (z : ℝ)
  (hfl : fl_vec_dot u x y z) :
  diff_gamma_bound u (n + 1) (x ⬝ᵥ y) z := by
  induction n generalizing z with
  | zero =>
    simp only [fl_vec_dot] at hfl
    simp only [diff_gamma_bound, Matrix.dotProduct_of_isEmpty, hfl, sub_self, abs_zero, zero_add, mul_zero, Std.le_refl]
  | succ n ih =>
    have hnu_n : ((n : ℝ) + 1) * (u : ℝ) < 1 := by
      sorry
    -- p: product, i.e. x0 * y0.
    -- s: sum of the rest
    obtain ⟨p, s, hp, hfl_vec_dot, hfl_add⟩ := hfl
    have s_bound : diff_gamma_bound u (n + 1) (∑ i, x (Fin.succ i) * y (Fin.succ i)) s := ih hnu_n (fun i => x (Fin.succ i)) (fun i => y (Fin.succ i)) s hfl_vec_dot
    have p_bound : diff_gamma_bound u 1 (x 0 * y 0) p := by
      apply fl_to_gammma_bound u (x 0 * y 0) p
      · sorry
      · exact hp
    have add_bound := fl_add_bound u 1 (n + 1) (x 0 * y 0) (∑ i, x (Fin.succ i) * y (Fin.succ i)) p s z hfl_add hnu p_bound s_bound
    simp only [le_add_iff_nonneg_left, zero_le, sup_of_le_right] at add_bound
    simpa [dotProduct, Fin.sum_univ_succ, add_comm] using add_bound

end
end Basic
