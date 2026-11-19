module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Evaluation of exterior two-forms

These definitions use the determinant pairing in Mathlib.  They identify an
actual exterior two-form with its alternating evaluation on dual vectors;
the separation result proves that this evaluation loses no information in
finite dimension.  The transpose identity fixes the sign convention when
passing between exterior forms and Chevalley--Eilenberg cochains.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorTwoFormEvaluation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Evaluate a genuine exterior two-form on two dual vectors. -/
def evaluate (f : ⋀[R]^2 M) : AlternatingMap R (Module.Dual R M) R (Fin 2) :=
  (Module.Dual.eval R (⋀[R]^2 M) f).compAlternatingMap
    (exteriorPower.alternatingMapToDual R M 2)

@[simp] theorem evaluate_apply (f : ⋀[R]^2 M) (v : Fin 2 → Module.Dual R M) :
    evaluate f v = exteriorPower.alternatingMapToDual R M 2 v f := rfl

/-- The two-by-two determinant formula, including its orientation. -/
theorem evaluate_word (m : Fin 2 → M) (v w : Module.Dual R M) :
    evaluate (exteriorPower.ιMulti R 2 m) ![v,w] =
      v (m 0) * w (m 1) - w (m 0) * v (m 1) := by
  simp only [evaluate_apply, exteriorPower.alternatingMapToDual_apply_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Repackage an alternating two-variable map as the ordinary bilinear map. -/
def bilinearOfAlternating (A : AlternatingMap R M R (Fin 2)) : M →ₗ[R] M →ₗ[R] R :=
  LinearMap.mk₂ R (fun v w ↦ A ![v,w])
    (fun v v' w ↦ A.map_vecCons_add ![w] v v')
    (fun r v w ↦ A.map_vecCons_smul ![w] r v)
    (fun v w w' ↦ (A.curryLeft v).map_vecCons_add ![] w w')
    (fun r v w ↦ (A.curryLeft v).map_vecCons_smul ![] r w)

@[simp] theorem bilinearOfAlternating_apply (A : AlternatingMap R M R (Fin 2)) (v w : M) :
    bilinearOfAlternating A v w = A ![v,w] := rfl

@[simp] theorem bilinearOfAlternating_self (A : AlternatingMap R M R (Fin 2)) (v : M) :
    bilinearOfAlternating A v v = 0 :=
  A.map_eq_zero_of_eq ![v,v] (i := 0) (j := 1) rfl (by decide)

/-- The bracket coefficient determined by the original exterior form. -/
def bilinear (f : ⋀[R]^2 M) : Module.Dual R M →ₗ[R] Module.Dual R M →ₗ[R] R :=
  bilinearOfAlternating (evaluate f)

@[simp] theorem bilinear_self (f : ⋀[R]^2 M) (v : Module.Dual R M) : bilinear f v v = 0 :=
  bilinearOfAlternating_self _ _

/-- Transposing the determinant converts the dual exterior pairing into
ordinary alternating evaluation on the two evaluation functionals. -/
theorem pairingDual_eq_evaluate (f : ⋀[R]^2 (Module.Dual R M)) (v w : M) :
    exteriorPower.pairingDual R M 2 f (exteriorPower.ιMulti R 2 ![v,w]) =
      evaluate f ![Module.Dual.eval R M v, Module.Dual.eval R M w] := by
  have h :
      (Module.Dual.eval R (⋀[R]^2 M) (exteriorPower.ιMulti R 2 ![v,w])).comp
          (exteriorPower.pairingDual R M 2) =
        exteriorPower.alternatingMapToDual R (Module.Dual R M) 2
          ![Module.Dual.eval R M v, Module.Dual.eval R M w] := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Module.Dual.eval_apply, exteriorPower.pairingDual_ιMulti_ιMulti,
      exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  exact LinearMap.congr_fun h f

section Separation

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Every two-form coefficient is detected by alternating evaluation. -/
theorem evaluate_injective : Function.Injective (evaluate (R := K) (M := V)) := by
  classical
  let b := Module.finBasis K V
  intro f g hfg
  apply (b.exteriorPower 2).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  have hd : exteriorPower.ιMultiDual K 2 b s =
      exteriorPower.alternatingMapToDual K V 2 ![b.coord (a 0), b.coord (a 1)] := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro m
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.ιMultiDual_apply_ιMulti,
      exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Module.Basis.coord_apply, a]
  rw [hd]
  exact congrArg (fun A : AlternatingMap K (Module.Dual K V) K (Fin 2) ↦
    A ![b.coord (a 0), b.coord (a 1)]) hfg

/-- In finite dimension, equality on all pairs of vectors is equality of
actual exterior two-cochains. -/
theorem pairingDual_injective_on_pairs (f g : ⋀[K]^2 (Module.Dual K V))
    (h : ∀ v w, exteriorPower.pairingDual K V 2 f (exteriorPower.ιMulti K 2 ![v,w]) =
      exteriorPower.pairingDual K V 2 g (exteriorPower.ιMulti K 2 ![v,w])) : f = g := by
  apply evaluate_injective
  apply AlternatingMap.ext
  intro a
  obtain ⟨v, hv⟩ := (Module.evalEquiv K V).surjective (a 0)
  obtain ⟨w, hw⟩ := (Module.evalEquiv K V).surjective (a 1)
  have ha : a = ![Module.Dual.eval K V v, Module.Dual.eval K V w] := by
    ext i
    fin_cases i <;> simp_all
  rw [ha, ← pairingDual_eq_evaluate, ← pairingDual_eq_evaluate]
  exact h v w

end Separation
end PaperVerification.ExteriorTwoFormEvaluation
