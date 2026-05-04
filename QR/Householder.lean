import Mathlib
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import QR.Basic
open scoped BigOperators
open QR
set_option linter.style.longLine false

namespace Householder
noncomputable section
-- σ = - sign(x₀) * ‖x‖
def sign {n : ℕ} (x : Vec n) (hn : n ≠ 0) : ℝ :=
  if x ⟨0, Nat.pos_of_ne_zero hn⟩ < 0 then -1 else 1

def householder (n : ℕ) (x : Vec n) (hn : n ≠ 0) : Vec n :=
  -- if hn : n = 0 then
  --   x
  -- else

  -- (1) s = sign(x₀) * fl(sqrt(fl(xᵀx)))
  let s : ℝ := sign x hn * ‖x‖
  -- (2) v₀ = fl(x₀ + s)
  let v₀ : ℝ := x ⟨0, Nat.pos_of_ne_zero hn⟩ + s
  let v' : Vec n :=
    fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then v₀ else x i
  -- (3) p = fl(s * v₀)
  let p : ℝ := s * v₀
  -- (4) β = fl(1 / p)
  let β : ℝ := 1 / p
  -- (5) b = fl(√β)
  let b : ℝ := Real.sqrt β
  -- (6) w = fl(b • v)
  let v : Vec n := b • v'
  v

theorem e1_of_householder
  (n : ℕ)
  (hn : n ≠ 0)
  (x : Vec n) :
  let v := householder n x hn
  let P : Matrix (Fin n) (Fin n) ℝ := 1 - (Matrix.vecMulVec v v)
  P • x = fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then - sign x hn * ‖x‖ else 0 := by sorry

end
end Householder
