module

public import ToricPower.SingleAugmentationComponent
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Epimorphy of an actual top-quotient quasi-isomorphism -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : CochainComplex C ℕ} {n : ℕ} {M : C}
  (f : K ⟶ (single C (.up ℕ) n).obj M) [QuasiIso f]
  (outgoing : K.d n (n + 1) = 0)

include outgoing in
/-- The original top component is epi because it is the original
opcycles quotient followed by the actual homology isomorphism. -/
theorem singleAugmentationComponent_epi : Epi (singleAugmentationComponent f) := by
  rw [← topHomologyQuotient_toComponent outgoing f]
  infer_instance

include outgoing in
/-- The entire augmentation is degreewise epi, including the zero
target degrees. -/
theorem singleAugmentation_epi : Epi f := by
  apply HomologicalComplex.epi_of_epi_f
  intro q
  by_cases equal : q = n
  · subst q
    haveI : Epi (f.f n ≫ (singleObjXSelf (.up ℕ) n M).hom) :=
      singleAugmentationComponent_epi f outgoing
    exact (epi_comp_iff_of_isIso (f.f n) (singleObjXSelf (.up ℕ) n M).hom).mp inferInstance
  · exact (isZero_single_obj_X (.up ℕ) n M q equal).epi _

end ToricPower

end
