module

public import PaperVerification.ExteriorTwoFormEvaluation
public import PaperVerification.TwoStepCentralLie
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Pi

/-!
# Original forms, the actual central Lie bracket, and cochains

The two original exterior forms define an ordinary two-step Lie algebra
on `M* ⊕ R²`.  Its cochain generators are identified with `M ⊕ R²` using
the evaluation isomorphism on `M` and the negatives of the two central
dual coordinates.  This fixes the conventional equation
`d α (x,y) = -α [x,y]` while retaining `d ε₀ = f`, `d ε₁ = g`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.CentralLieCochainCoordinates

open ExteriorTwoFormEvaluation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The literal bracket coefficients of the original two forms. -/
def bracketData (f g : ⋀[R]^2 M) :
    TwoStepCentralLie.Data (K := R) (V := Module.Dual R M) (Z := Fin 2 → R) where
  bilinear := LinearMap.mk₂ R (fun v w ↦ ![bilinear f v w, bilinear g v w])
    (by intro v v' w; ext i; fin_cases i <;> simp)
    (by intro r v w; ext i; fin_cases i <;> simp)
    (by intro v w w'; ext i; fin_cases i <;> simp)
    (by intro r v w; ext i; fin_cases i <;> simp)
  alternating v := by ext i; fin_cases i <;> simp

/-- Mathlib's ordinary Lie algebra, with the actual constructed bracket. -/
abbrev L (f g : ⋀[R]^2 M) := TwoStepCentralLie.LieSpace (bracketData f g)

@[simp] theorem bracket_apply (f g : ⋀[R]^2 M) (x y : L f g) :
    ⁅x,y⁆ = ((0 : Module.Dual R M), ![bilinear f x.1 y.1, bilinear g x.1 y.1]) := rfl

/-- The canonical dual pairing for the two central coordinates. -/
theorem twoCoordinate_dual (r z : Fin 2 → R) :
    (Pi.basisFun R (Fin 2)).toDual r z = r 0 * z 0 + r 1 * z 1 := by
  let b := Pi.basisFun R (Fin 2)
  have hr : r = r 0 • b 0 + r 1 • b 1 := by
    ext i
    fin_cases i <;> simp [b, Pi.basisFun_apply]
  rw [hr, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply,
    b.toDual_apply_right, b.toDual_apply_right]
  simp [b, Pi.basisFun_repr]

section Reflexive

variable [Module.IsReflexive R M]

/-- Original generators and negative central dual generators give all
actual one-cochains.  Finite-dimensional vector spaces satisfy reflexivity. -/
def oneCochainEquiv (f g : ⋀[R]^2 M) :
    (M × (Fin 2 → R)) ≃ₗ[R] Module.Dual R (L f g) :=
  ((Module.evalEquiv R M).prodCongr
    ((Pi.basisFun R (Fin 2)).toDualEquiv.trans (LinearEquiv.neg R))).trans
      (Module.dualProdDualEquivDual R (Module.Dual R M) (Fin 2 → R))

theorem oneCochainEquiv_apply (f g : ⋀[R]^2 M) (v : M × (Fin 2 → R)) (x : L f g) :
    oneCochainEquiv f g v x = x.1 v.1 - (Pi.basisFun R (Fin 2)).toDual v.2 x.2 := by
  change x.1 v.1 + (-((Pi.basisFun R (Fin 2)).toDualEquiv v.2)) x.2 = _
  rw [LinearMap.neg_apply, Module.Basis.toDualEquiv_apply, sub_eq_add_neg]

@[simp] theorem oneCochainEquiv_original (f g : ⋀[R]^2 M) (m : M) (x : L f g) :
    oneCochainEquiv f g (m,0) x = x.1 m := by
  simp [oneCochainEquiv_apply]

@[simp] theorem oneCochainEquiv_central (f g : ⋀[R]^2 M) (i : Fin 2) (x : L f g) :
    oneCochainEquiv f g ((0 : M),Pi.single i 1) x = -x.2 i := by
  rw [oneCochainEquiv_apply]
  change x.1 (0 : M) - (Pi.basisFun R (Fin 2)).toDual (Pi.single i 1) x.2 = _
  rw [map_zero, ← Pi.basisFun_apply R (Fin 2) i, Module.Basis.toDual_apply_right]
  simp [Pi.basisFun_repr]

/-- The negative bracket dual in the original cochain coordinates. -/
theorem negative_bracket_dual (f g : ⋀[R]^2 M) (v : M × (Fin 2 → R)) (x y : L f g) :
    -(oneCochainEquiv f g v ⁅x,y⁆) =
      v.2 0 * bilinear f x.1 y.1 + v.2 1 * bilinear g x.1 y.1 := by
  rw [oneCochainEquiv_apply, bracket_apply, twoCoordinate_dual]
  simp

/-- The original two-form as an actual exterior two-cochain of the Lie algebra. -/
def originalTwoCochain (f g h : ⋀[R]^2 M) : ⋀[R]^2 (Module.Dual R (L f g)) :=
  exteriorPower.map 2
    ((oneCochainEquiv f g).toLinearMap.comp (LinearMap.inl R M (Fin 2 → R))) h

/-- Evaluation of the actual pulled-back two-cochain is the original
bracket coefficient, with no sign or scalar normalization omitted. -/
theorem originalTwoCochain_pairing (f g h : ⋀[R]^2 M) (x y : L f g) :
    exteriorPower.pairingDual R (L f g) 2 (originalTwoCochain f g h)
      (exteriorPower.ιMulti R 2 ![x,y]) = bilinear h x.1 y.1 := by
  have he :
      (Module.Dual.eval R (⋀[R]^2 (L f g)) (exteriorPower.ιMulti R 2 ![x,y])).comp
          ((exteriorPower.pairingDual R (L f g) 2).comp
            (exteriorPower.map 2
              ((oneCochainEquiv f g).toLinearMap.comp (LinearMap.inl R M (Fin 2 → R))))) =
        exteriorPower.alternatingMapToDual R M 2 ![x.1,y.1] := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Module.Dual.eval_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.pairingDual_ιMulti_ιMulti,
      exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Function.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply,
      oneCochainEquiv_original]
    ring
  exact LinearMap.congr_fun he h

end Reflexive
end PaperVerification.CentralLieCochainCoordinates
