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

-- different from book, we define gamma_bound θ as |θ - 1| ≤ γ
def gamma_bound (n : ℕ) (θ : ℝ) : Prop :=
  diff_gamma_bound_theta u n 1 θ

lemma gamma_bound_monotune (n₁ n₂ : ℕ) (θ : ℝ) (hnu₁ : (n₁ : ℝ) * (u : ℝ) < 1) (hnu₂ : (n₂ : ℝ) * (u : ℝ) < 1) (hle : n₁ ≤ n₂) (hθ : gamma_bound u n₁ θ) :
  gamma_bound u n₂ θ := by
  rw [gamma_bound] at hθ ⊢
  obtain ⟨θ₁, hθ₁, hθ₁_bound⟩ := hθ
  exists θ₁
  exact ⟨hθ₁, le_trans hθ₁_bound (gamma_monotune u n₁ n₂ hnu₁ hnu₂ hle)⟩

lemma theta_n_succ_bound
  (n : ℕ)
  (θn : ℝ)
  (δ : ℝ)
  (hnu' : ((n : ℝ) + 1) * (u : ℝ) < 1)
  (hθn : |θn| ≤ γ u n)
  (hδ : |δ| ≤ u) :
    gamma_bound u n.succ ((1 + δ) * (1 + θn)) := by
  -- ∃ θn' : ℝ,
  --   (1 + δ) * (1 + θn) = 1 + θn' ∧ |θn'| ≤ γ u (n + 1) := by
  exists δ + (1 + δ) * θn
  have hnu : (n : ℝ) * (u : ℝ) < 1 := by
    linarith
  have hnu_neq : 1 - (u : ℝ) * (n : ℝ) ≠ 0 := by
    linarith
  constructor
  · ring
  · calc
    |(δ : ℝ) + (1 + δ) * θn| ≤ |(δ : ℝ)| + |(1 + δ) * θn| := by
      exact abs_add_le _ _
    |(δ : ℝ)| + |(1 + δ : ℝ) * θn| ≤ (u : ℝ) + (1 + (u : ℝ)) * ((n : ℝ) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ))) := by
      rw [abs_mul]
      gcongr
      · have : |(1 + δ : ℝ)| ≤ 1 + u := by
          calc
            |(1 + δ : ℝ)| ≤ |1| + |(δ : ℝ)| := by
              apply abs_add_le 1 (δ)
            _ ≤ 1 + |(δ : ℝ)| := by simp
            _ ≤ 1 + u := by exact add_le_add_right (hδ) 1
        exact this
      · exact hθn
    u + (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u))
    = ((n : ℝ) + 1) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ)) := by
      field_simp [hnu_neq]
      ring_nf
    ((n : ℝ) + 1) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ)) ≤ γ u n.succ := by
      simp only [γ, Nat.cast_succ]
      apply mul_le_mul_of_nonneg_left
      · have h1: 0 < 1 - ((n : ℝ) + 1) * (u : ℝ) := by
          ring_nf
          linarith
        have h2: 1 - ((n : ℝ) + 1) * (u : ℝ) ≤ 1 - (n : ℝ) * (u : ℝ) := by
          ring_nf
          simp
        exact inv_anti₀ h1 h2
      · apply mul_nonneg
        · exact_mod_cast Nat.zero_le n.succ
        · exact_mod_cast u.2

-- lemma theta_n_succ_bound'
--   (n : ℕ)
--   (θn : ℝ)
--   (δ : ℝ)
--   (hnu' : ((n : ℝ) + 1) * (u : ℝ) < 1)
--   (hθn : |θn| ≤ γ u n)
--   (hδ : |δ| ≤ u) :
--   ∃ θn' : ℝ,
--     (1 + δ) ^ (-1 : ℝ) * (1 + θn) = 1 + θn' ∧ |θn'| ≤ γ u (n + 1) := by
--   exists (θn - δ) / (1 + δ)
--   sorry

-- -- Lemma 3.1 in the book
-- lemma theta_n_leq_gamma_n_rho_posneg
--   (n : ℕ)
--   (δ : Fin n → ℝ)
--   (ρ : Fin n → ℤ)
--   (hδ : ∀ i, |δ i| ≤ u)
--   (hρ : ∀ i, ρ i = (1 : ℤ) ∨ ρ i = (-1 : ℤ))
--   (hnu : (n : ℝ) * (u : ℝ) < 1) :
--   ∃ θn : ℝ,
--     (∏ i : Fin n, (1 + δ i) ^ (ρ i)) = 1 + θn ∧
--     |θn| ≤ γ u n :=
--   by induction n with
--   | zero =>
--     exists 0
--     simp [γ]
--   | succ n ih =>
--     let δ_ih : Fin n → ℝ := fun i => δ i.succ
--     let ρ_ih : Fin n → ℤ := fun i => ρ i.succ
--     have hδ_ih : ∀ (i : Fin n), |δ_ih i| ≤ u := by
--       intro i
--       simpa [δ_ih] using hδ i.succ
--     have hρ_ih : ∀ (i : Fin n), ρ_ih i = (1 : ℤ) ∨ ρ_ih i = (-1 : ℤ) := by
--       intro i
--       simpa [ρ_ih] using hρ i.succ
--     have hnu_ih : (n : ℝ) * (u : ℝ) < 1 := by
--       have hle_nat : (n : ℝ) ≤ (n.succ : ℝ) := by
--         exact_mod_cast Nat.le_succ n
--       have hle_mul : (n : ℝ) * (u : ℝ) ≤ (n.succ : ℝ) * (u : ℝ) := by
--         exact mul_le_mul_of_nonneg_right hle_nat (by exact_mod_cast u.2)
--       exact lt_of_le_of_lt hle_mul hnu
--     have hnu_neq1 : (n : ℝ) * (u : ℝ) ≠ 1 := by
--       exact ne_of_lt hnu_ih
--     have hnu_neq : 1 - (u : ℝ) * (n : ℝ) ≠ 0 := by
--       linarith
--     have uge0 : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast u.property
--     have hu_le : (u : ℝ) ≤ (n.succ : ℝ) * (u : ℝ) := by
--       have : (1 : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
--       simpa [one_mul] using mul_le_mul_of_nonneg_right this uge0
--     have ul1 : (u : ℝ) < 1 :=
--       lt_of_le_of_lt hu_le hnu
--     obtain ⟨θn, hθn, hθn_bound⟩ := ih δ_ih ρ_ih hδ_ih hρ_ih hnu_ih
--     cases (hρ 0) with
--     | inl h=>
--       exists δ 0 + (1 + δ 0) * θn
--       constructor
--       · rw [Fin.prod_univ_succ, hθn, h]
--         simp
--         ring
--       · calc
--           |(δ 0 : ℝ) + (1 + δ 0) * θn| ≤ |(δ 0 : ℝ)| + |(1 + δ 0) * θn| := by
--             exact abs_add_le _ _
--           |(δ 0 : ℝ)| + |(1 + δ 0 : ℝ) * θn| = |(δ 0 : ℝ)| + |(1 + δ 0 : ℝ)| * |θn| := by
--             simp
--           |(δ 0 : ℝ)| + |(1 + δ 0 : ℝ)| * |θn|
--           ≤ (u : ℝ) + (1 + (u : ℝ)) * ((n : ℝ) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ))) := by
--             gcongr
--             · exact (hδ 0)
--             · have : |(1 + δ 0 : ℝ)| ≤ 1 + u := by
--                 calc
--                   |(1 + δ 0 : ℝ)| ≤ |1| + |(δ 0 : ℝ)| := by
--                     apply abs_add_le 1 (δ 0)
--                   _ ≤ 1 + |(δ 0 : ℝ)| := by simp
--                   _ ≤ 1 + u := by exact add_le_add_right (hδ 0) 1
--               exact this
--             · exact hθn_bound
--           u + (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u))
--           = ((n : ℝ) + 1) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ)) := by
--             field_simp [hnu_neq]
--             ring
--           ((n : ℝ) + 1) * (u : ℝ) / (1 - (n : ℝ) * (u : ℝ)) ≤ γ u n.succ := by
--             simp only [γ, Nat.cast_succ]
--             apply mul_le_mul_of_nonneg_left
--             · have h1: 0 < 1 - ((n : ℝ) + 1) * (u : ℝ) := by
--                 simp [Nat.cast_succ] at hnu
--                 linarith
--               have h2: 1 - ((n : ℝ) + 1) * (u : ℝ) ≤ 1 - (n : ℝ) * (u : ℝ) := by
--                 ring_nf
--                 simp
--               exact inv_anti₀ h1 h2
--             · apply mul_nonneg
--               · exact_mod_cast Nat.zero_le n.succ
--               · exact_mod_cast u.2
--     | inr h=>
--       exists (θn - δ 0) / (1 + δ 0)
--       have : 1 + δ 0 > 0 := by
--         have : (δ 0 : ℝ) ≥ -(u : ℝ) := by
--           have h := abs_le.mp (hδ 0)
--           exact h.1
--         linarith
--       constructor
--       · rw [Fin.prod_univ_succ, hθn, h]
--         field_simp
--         ring
--       · have uunge0 : (u : ℝ) ^ 2 * (n : ℝ) ≥ 0 := by
--           apply mul_nonneg
--           · exact sq_nonneg (u : ℝ)
--           · exact_mod_cast Nat.zero_le n
--         calc
--           |(θn - δ 0) / (1 + δ 0)| = |(θn - δ 0)| / |(1 + δ 0)| := by
--             exact abs_div _ _
--           |(θn - δ 0)| / |(1 + δ 0)| ≤ |(θn - δ 0)| / (1 - (u : ℝ)) := by
--             have h1: 1 - (u : ℝ) ≤ |(1 + δ 0)| := by
--               calc
--                 1 - (u : ℝ) ≤ 1 + δ 0 := by
--                   have h := abs_le.mp (hδ 0)
--                   linarith
--                 _ ≤ |(1 + δ 0)| := by
--                   exact le_abs_self (1 + δ 0)
--             apply mul_le_mul_of_nonneg_left
--             · exact inv_anti₀ (by linarith) h1
--             · exact abs_nonneg _
--           |(θn - δ 0)| / (1 - (u : ℝ)) ≤ (|θn| + |(δ 0 : ℝ)|) / (1 - (u : ℝ)) := by
--             field_simp [ul1]
--             have := (abs_add_le θn (-(δ 0)))
--             simp only [abs_neg] at this
--             exact this
--           (|θn| + |(δ 0 : ℝ)|) / (1 - (u : ℝ)) ≤ (|θn| + u) / (1 - (u : ℝ)) := by
--             field_simp [ul1]
--             simp [(hδ 0)]
--           (|θn| + u) / (1 - (u : ℝ)) ≤ (γ u n + u) / (1 - (u : ℝ)) := by
--             field_simp [ul1]
--             simp only [γ, add_le_add_iff_right]
--             exact hθn_bound
--           (γ u n + u) / (1 - (u : ℝ)) = (((n : ℝ) + 1) * (u : ℝ) - (n : ℝ) * (u : ℝ) * (u : ℝ)) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) := by
--             simp only [γ]
--             have : (1 - (u : ℝ)) ≠ 0 := by linarith
--             have : (1 - (n : ℝ) * (u : ℝ)) ≠ 0 := by linarith
--             field_simp [ul1]
--             ring
--           (((n : ℝ) + 1) * (u : ℝ) - (n : ℝ) * (u : ℝ) * (u : ℝ)) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) ≤ ((n : ℝ) + 1) * (u : ℝ) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) := by
--             have : (1 - (u : ℝ)) ≠ 0 := by
--               linarith
--             have : (1 - (n : ℝ) * (u : ℝ)) > 0 := by
--               linarith
--             field_simp [ul1, this]
--             ring_nf
--             simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
--             exact uunge0
--           ((n : ℝ) + 1) * (u : ℝ) / ((1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ))) ≤ γ u n.succ := by
--             simp only [γ, Nat.cast_succ]
--             apply mul_le_mul_of_nonneg_left
--             · have h1: 0 < 1 - ((n : ℝ) + 1) * (u : ℝ) := by
--                 simp [Nat.cast_succ] at hnu
--                 linarith
--               have h2: 1 - ((n : ℝ) + 1) * (u : ℝ) ≤ (1 - (u : ℝ)) * (1 - (n : ℝ) * (u : ℝ)) := by
--                 ring_nf
--                 simp only [tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right]
--                 rw [mul_comm (n : ℝ) ((u : ℝ) ^ 2)]
--                 exact uunge0
--               exact inv_anti₀ h1 h2
--             · apply mul_nonneg
--               · exact_mod_cast Nat.zero_le n.succ
--               · exact_mod_cast u.2

-- a simplified version of Lemma 3.1
lemma theta_n_leq_gamma_n_rho
  (n : ℕ)
  (δ : Fin n → ℝ)
  (hδ : ∀ i, |δ i| ≤ u)
  (hnu : (n : ℝ) * (u : ℝ) < 1) :
    gamma_bound u n (∏ i : Fin n, (1 + δ i)) :=
  by induction n with
  | zero =>
    exists 0
    simp [γ]
  | succ n ih =>
    let δ_ih : Fin n → ℝ := fun i => δ i.succ
    have hδ_ih : ∀ (i : Fin n), |δ_ih i| ≤ u := by
      intro i
      simpa [δ_ih] using hδ i.succ
    have hnu_ih : (n : ℝ) * (u : ℝ) < 1 := by
      have hle_nat : (n : ℝ) ≤ (n.succ : ℝ) := by
        exact_mod_cast Nat.le_succ n
      have hle_mul : (n : ℝ) * (u : ℝ) ≤ (n.succ : ℝ) * (u : ℝ) := by
        exact mul_le_mul_of_nonneg_right hle_nat (by exact_mod_cast u.2)
      exact lt_of_le_of_lt hle_mul hnu
    obtain ⟨θn, hθn, hθn_bound⟩ := ih δ_ih hδ_ih hnu_ih
    have : ((n : ℝ) + 1) * u < 1 := by
      simpa using hnu
    obtain ⟨θn', hθn', hθn'_bound⟩ := theta_n_succ_bound u n θn (δ 0) this hθn_bound (hδ 0)
    exists θn'
    exact ⟨by rw [Fin.prod_univ_succ, hθn, one_mul, hθn'], hθn'_bound⟩

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
lemma fl_bound (n : ℝ) (x x' x'' : ℝ) (hnu : (n : ℝ + 1) * (u : ℝ) < 1) (hbound : diff_gamma_bound u n x x') (hfl : fl x x')

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
  diff_gamma_bound u ((nx ⊔ ny) + 1) (x + y) z := by

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
