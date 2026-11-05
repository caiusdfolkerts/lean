module

public import PaperVerification.SheafModulePowers

/-!
# Morphisms specified by finite families of actual sheaf sections

The formulas use the genuine structure module, product projections and
the canonical structure-module/sections equivalence.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace PaperVerification.SheafCoordinateMorphisms

universe u

/-- A linear frame carries the coordinate sum to the same linear combination
of the corresponding frame sections. -/
theorem sum_smul_eq_frame {R M I : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype I] (e : R ≃ₗ[R] M)
    (v a : I → R) (s : I → M) (h : ∀ i, e (a i) = s i) :
    (∑ i, v i • s i) = e (∑ i, v i * a i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [smul_eq_mul] using
    (congrArg (fun z : M => v i • z) (h i).symm).trans
      (e.map_smul (v i) (a i)).symm

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

theorem unit_morphism_apply (s : M.sections) (U : X.Opens)
    (a : X.ringCatSheaf.obj.obj (op U)) :
    ((SheafOfModules.unitHomEquiv M).symm s).val.app (op U) a =
      a • s.eval (op U) := by
  let f := (SheafOfModules.unitHomEquiv M).symm s
  have h : f.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)) = s.eval (op U) := by
    have hh := congrArg (fun z : M.sections => z.eval (op U))
      ((SheafOfModules.unitHomEquiv M).apply_symm_apply s)
    exact hh
  have hh := (f.val.app (op U)).hom.map_smul a
    (1 : X.ringCatSheaf.obj.obj (op U))
  simpa only [f, smul_eq_mul, mul_one, h] using hh

/-- The finite structure-module power maps to `M` by the chosen sections. -/
def fromSections {I : Type u} [Fintype I] (s : I → M.sections) :
    SheafModulePowers.structurePower X I ⟶ M :=
  ∑ i, Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
    (SheafOfModules.unitHomEquiv M).symm (s i)

/-- Its map on sections is the literal finite linear combination. -/
theorem fromSections_apply {I : Type u} [Fintype I] (s : I → M.sections)
    (U : X.Opens) (x : (SheafModulePowers.structurePower X I).val.obj (op U)) :
    (fromSections M s).val.app (op U) x =
      ∑ i, (show X.ringCatSheaf.obj.obj (op U) from
        SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit X.ringCatSheaf) I U x i) • (s i).eval (op U) := by
  classical
  have h (T : Finset I) :
      (∑ i ∈ T, Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        (SheafOfModules.unitHomEquiv M).symm (s i)).val.app (op U) x =
      ∑ i ∈ T, (show X.ringCatSheaf.obj.obj (op U) from
        SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit X.ringCatSheaf) I U x i) • (s i).eval (op U) := by
    induction T using Finset.induction_on with
    | empty => rfl
    | @insert i T hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change ((SheafOfModules.unitHomEquiv M).symm (s i)).val.app (op U)
          ((Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).val.app
            (op U) x) + _ = _ + _
      apply congrArg₂ (fun a b : M.val.obj (op U) => a + b)
      · rw [unit_morphism_apply, SheafModulePowers.sectionsEquiv_apply]
      · exact ih
  exact h Finset.univ

end PaperVerification.SheafCoordinateMorphisms
