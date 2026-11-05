module

public import PaperVerification.CentralLieCochainCoordinates

/-!
# The original vector-space presentation of the two-step Lie algebra

When the original exterior algebra is `Λ(V*)`, the dual-coordinate
construction uses `V**` as its noncentral vector space. This file defines
the ordinary bracket directly on `V × K²`, by the original exterior
pairing, and proves that the canonical evaluation map is a Lie equivalence.
Both central directions are preserved literally. No independence or
nonvanishing hypothesis on the two original forms is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoStepOriginalLie

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The original alternating form on `V`, obtained from its actual exterior
cochain by the universal exterior pairing. -/
def alternatingForm (f : ⋀[K]^2 (Module.Dual K V)) :
    AlternatingMap K V K (Fin 2) :=
  exteriorPower.alternatingMapLinearEquiv.symm (exteriorPower.pairingDual K V 2 f)

theorem alternatingForm_apply (f : ⋀[K]^2 (Module.Dual K V)) (x y : V) :
    alternatingForm f ![x,y] = exteriorPower.pairingDual K V 2 f
      (exteriorPower.ιMulti K 2 ![x,y]) :=
  exteriorPower.alternatingMapLinearEquiv_symm_apply _ _

/-- The literal bilinear coefficient of the original central bracket. -/
def bilinearForm (f : ⋀[K]^2 (Module.Dual K V)) : V →ₗ[K] V →ₗ[K] K :=
  ExteriorTwoFormEvaluation.bilinearOfAlternating (alternatingForm f)

theorem bilinearForm_apply (f : ⋀[K]^2 (Module.Dual K V)) (x y : V) :
    bilinearForm f x y = exteriorPower.pairingDual K V 2 f
      (exteriorPower.ιMulti K 2 ![x,y]) :=
  alternatingForm_apply f x y

/-- Evaluation in the double dual preserves the original form, including
its determinant normalization and sign. -/
theorem bilinearForm_eval (f : ⋀[K]^2 (Module.Dual K V)) (x y : V) :
    bilinearForm f x y = ExteriorTwoFormEvaluation.bilinear f
      (Module.evalEquiv K V x) (Module.evalEquiv K V y) := by
  rw [bilinearForm_apply, ExteriorTwoFormEvaluation.pairingDual_eq_evaluate]
  rfl

/-- The two-step bracket on the original vector space, before any passage
to its double dual. -/
def bracketData (f g : ⋀[K]^2 (Module.Dual K V)) :
    TwoStepCentralLie.Data (K := K) (V := V) (Z := Fin 2 → K) where
  bilinear := LinearMap.mk₂ K (fun x y ↦ ![bilinearForm f x y, bilinearForm g x y])
    (by intro x x' y; ext i; fin_cases i <;> simp)
    (by intro r x y; ext i; fin_cases i <;> simp)
    (by intro x y y'; ext i; fin_cases i <;> simp)
    (by intro r x y; ext i; fin_cases i <;> simp)
  alternating x := by
    ext i
    fin_cases i
    · change bilinearForm f x x = 0
      exact ExteriorTwoFormEvaluation.bilinearOfAlternating_self (alternatingForm f) x
    · change bilinearForm g x x = 0
      exact ExteriorTwoFormEvaluation.bilinearOfAlternating_self (alternatingForm g) x

/-- The ordinary Lie algebra on `V × K²` with the original form coefficients. -/
abbrev L (f g : ⋀[K]^2 (Module.Dual K V)) :=
  TwoStepCentralLie.LieSpace (bracketData f g)

/-- The bracket is exactly the one printed in the paper, expressed through
the independently defined exterior pairing on the original vectors. -/
theorem bracket_apply (f g : ⋀[K]^2 (Module.Dual K V)) (x y : L f g) :
    ⁅x,y⁆ = ((0 : V),
      ![exteriorPower.pairingDual K V 2 f (exteriorPower.ιMulti K 2 ![x.1,y.1]),
        exteriorPower.pairingDual K V 2 g (exteriorPower.ιMulti K 2 ![x.1,y.1])]) := by
  change ((0 : V), ![bilinearForm f x.1 y.1, bilinearForm g x.1 y.1]) = _
  rw [bilinearForm_apply, bilinearForm_apply]

/-- Canonical evaluation gives an actual Lie equivalence from the original
presentation to the dual-coordinate presentation used in the CE calculation. -/
def evalLieEquiv (f g : ⋀[K]^2 (Module.Dual K V)) :
    L f g ≃ₗ⁅K⁆ CentralLieCochainCoordinates.L f g :=
  { (Module.evalEquiv K V).prodCongr (LinearEquiv.refl K (Fin 2 → K)) with
    map_lie' := by
      intro x y
      apply Prod.ext
      · change Module.evalEquiv K V (0 : V) = 0
        exact map_zero _
      · change ![bilinearForm f x.1 y.1, bilinearForm g x.1 y.1] =
          ![ExteriorTwoFormEvaluation.bilinear f
              (Module.evalEquiv K V x.1) (Module.evalEquiv K V y.1),
            ExteriorTwoFormEvaluation.bilinear g
              (Module.evalEquiv K V x.1) (Module.evalEquiv K V y.1)]
        ext i
        fin_cases i
        · exact bilinearForm_eval f x.1 y.1
        · exact bilinearForm_eval g x.1 y.1 }

/-- The equivalence is the canonical evaluation map on the original
vectors and the literal identity on the central coordinates. -/
theorem evalLieEquiv_apply (f g : ⋀[K]^2 (Module.Dual K V)) (x : L f g) :
    evalLieEquiv f g x = (Module.evalEquiv K V x.1, x.2) := rfl

@[simp] theorem evalLieEquiv_central (f g : ⋀[K]^2 (Module.Dual K V)) (z : Fin 2 → K) :
    evalLieEquiv f g ((0 : V), z) = (0, z) := by
  change (Module.evalEquiv K V (0 : V), z) = (0, z)
  rw [map_zero]

end PaperVerification.TwoStepOriginalLie
