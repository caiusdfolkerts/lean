module

public import Recovery.Unimodular.GraphicSectionRing.ActualSectionRing
public import Recovery.Unimodular.GraphicSectionRing.GradedScalarChange

/-!
# Independence of genuine section rings from Cartier presentation

Equality of fractional Cartier presentations identifies every actual power
value space. Principal translation gives the explicit degree-d factor q^d.
Both constructions are proved algebra equivalences of the independently
defined ordinary section rings, retaining the complete grading.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.GraphicSectionRing.ActualSections

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BaseSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C D : RationalCartierCocycle X)

/-- Fractional-presentation equality propagates to every actual Cartier power. -/
theorem powerValues_eq_of_equivalent
    (h : C.toCartierData.Equivalent D.toCartierData) (d : ℕ) :
    powerValues k C d = powerValues k D d := by
  have hCD := C.generatorRatios_of_equivalent D h
  have hDC := D.generatorRatios_of_equivalent C
    (C.toCartierData.equivalent_symm D.toCartierData h)
  have hp := (C.pow d).equivalent_of_generatorRatios (D.pow d)
    (RationalCartierCocycle.GeneratorRatioRegular.pow C D hCD d)
    (RationalCartierCocycle.GeneratorRatioRegular.pow D C hDC d)
  have hr := (C.pow d).toCartierData.equivalent_sectionValueRange
    (D.pow d).toCartierData hp ⊤
  apply SetLike.coe_injective
  change Set.range ((C.pow d).toCartierData.sectionValue ⊤) =
    Set.range ((D.pow d).toCartierData.sectionValue ⊤)
  exact congrArg (fun P : Submodule Γ(X, ⊤) X.functionField =>
    (P : Set X.functionField)) hr

 theorem sectionRing_eq_of_equivalent
    (h : C.toCartierData.Equivalent D.toCartierData) : sectionRing k C = sectionRing k D := by
  ext p
  change (∀ d, p.coeff d ∈ powerValues k C d) ↔ ∀ d, p.coeff d ∈ powerValues k D d
  simp only [powerValues_eq_of_equivalent k C D h]

/-- The exact graded algebra equivalence for equal fractional presentations. -/
def equivalenceOfEquivalent (h : C.toCartierData.Equivalent D.toCartierData) :
    sectionRing k C ≃ₐ[k] sectionRing k D :=
  Subalgebra.equivOfEq _ _ (sectionRing_eq_of_equivalent k C D h)

@[simp] theorem equivalenceOfEquivalent_value
    (h : C.toCartierData.Equivalent D.toCartierData) (p : sectionRing k C) :
    (equivalenceOfEquivalent k C D h p).val = p.val := rfl

variable (q : X.functionFieldˣ)

/-- Principal scaling multiplies the genuine degree-d section value by q^d. -/
theorem powerValues_scale_iff (d : ℕ) (r : X.functionField) :
    (q : X.functionField) ^ d * r ∈ powerValues k (C.scale q) d ↔
      r ∈ powerValues k C d := by
  rw [mem_powerValues_iff, mem_powerValues_iff]
  have he (i : C.index) :
      ((q : X.functionField) ^ d * r) /
        ((C.scale q).generator i : X.functionField) ^ d =
        r / (C.generator i : X.functionField) ^ d := by
    change ((q : X.functionField) ^ d * r) /
      ((q : X.functionField) * (C.generator i : X.functionField)) ^ d = _
    rw [mul_pow]
    field_simp [Units.ne_zero]
  constructor
  · intro h i x hx
    have hi := h i x hx
    rwa [he] at hi
  · intro h i x hx
    rw [he]
    exact h i x hx

 theorem gradedScale_mem_iff (p : AddMonoidAlgebra X.functionField ℕ) :
    GradedScalarChange.equivalence (K := k) q p ∈ sectionRing k (C.scale q) ↔
      p ∈ sectionRing k C := by
  change (∀ d, (GradedScalarChange.equivalence (K := k) q p).coeff d ∈
    powerValues k (C.scale q) d) ↔ ∀ d, p.coeff d ∈ powerValues k C d
  simp only [GradedScalarChange.equivalence_coefficient, powerValues_scale_iff]

/-- A principal divisor changes the actual section ring by a proved graded
algebra isomorphism, not an assumed invariance principle. -/
def scaleEquivalence : sectionRing k C ≃ₐ[k] sectionRing k (C.scale q) :=
  AlgEquiv.ofBijective
    (((GradedScalarChange.equivalence (K := k) q).toAlgHom.comp (sectionRing k C).val).codRestrict
      (sectionRing k (C.scale q)) (fun p => (gradedScale_mem_iff k C q p.val).mpr p.property))
    ⟨fun p r h => Subtype.ext ((GradedScalarChange.equivalence (K := k) q).injective
      (congrArg Subtype.val h)), by
      intro p
      let r := (GradedScalarChange.equivalence (K := k) q).symm p.val
      have hr : r ∈ sectionRing k C := (gradedScale_mem_iff k C q r).mp (by
        rw [show GradedScalarChange.equivalence (K := k) q r = p.val from
          (GradedScalarChange.equivalence (K := k) q).apply_symm_apply p.val]
        exact p.property)
      exact ⟨⟨r, hr⟩, Subtype.ext
        ((GradedScalarChange.equivalence (K := k) q).apply_symm_apply p.val)⟩⟩

@[simp] theorem scaleEquivalence_coefficient (p : sectionRing k C) (d : ℕ) :
    (scaleEquivalence k C q p).val.coeff d = (q : X.functionField) ^ d * p.val.coeff d :=
  GradedScalarChange.equivalence_coefficient q p.val d

#print axioms powerValues_eq_of_equivalent
#print axioms equivalenceOfEquivalent
#print axioms scaleEquivalence
#print axioms scaleEquivalence_coefficient

end Unimodular.GraphicSectionRing.ActualSections

#check Unimodular.GraphicSectionRing.ActualSections.scaleEquivalence
