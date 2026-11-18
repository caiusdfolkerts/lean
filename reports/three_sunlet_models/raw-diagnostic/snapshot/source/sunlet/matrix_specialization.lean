module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! An injective specialized matrix remains injective in the generic field.
A linear left inverse at the special point gives a square matrix whose
determinant specializes to one. This avoids assuming a generic-rank result. -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Sunlet.MatrixSpecialization

variable {k R E m n : Type*} [Field k] [CommRing R] [Field E] [Algebra k R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem injective_of_specialization
    (M : Matrix m n R) (evaluate : R →ₐ[k] k) (generic : R →+* E)
    (hgeneric : Function.Injective generic)
    (hevaluate : Function.Injective (M.map evaluate).mulVecLin) :
    Function.Injective (M.map generic).mulVecLin := by
  obtain ⟨left, hleft⟩ := (M.map evaluate).mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hevaluate)
  let C : Matrix n m k := LinearMap.toMatrix' left
  have hC : C * M.map evaluate = 1 := by
    have hh := congrArg LinearMap.toMatrix' hleft
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', C] using hh
  let N : Matrix n n R := C.map (algebraMap k R) * M
  have hN : N.map evaluate = 1 := by
    have hc : (C.map (algebraMap k R)).map evaluate = C := by
      ext i j
      exact evaluate.commutes (C i j)
    simpa only [N, Matrix.map_mul, hc] using hC
  have hdet : N.det ≠ 0 := by
    intro hh
    have he : evaluate N.det = 1 := by
      rw [evaluate.map_det]
      change (N.map evaluate).det = 1
      rw [hN, Matrix.det_one]
    rw [hh, map_zero] at he
    exact zero_ne_one he
  have hdetGeneric : (N.map generic).det ≠ 0 := by
    change (generic.mapMatrix N).det ≠ 0
    rw [← generic.map_det]
    exact fun h => hdet (hgeneric (h.trans generic.map_zero.symm))
  intro v w hvw
  apply Matrix.mulVec_injective_of_det_ne_zero hdetGeneric
  change (N.map generic) *ᵥ v = (N.map generic) *ᵥ w
  simp only [N, Matrix.map_mul, ← Matrix.mulVec_mulVec]
  exact congrArg ((C.map (algebraMap k R)).map generic).mulVec hvw

end Sunlet.MatrixSpecialization
