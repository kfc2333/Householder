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

end
end Householder_fl
