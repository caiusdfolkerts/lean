module

public import Recovery.Unimodular.GraphicSectionRing.ActualSectionRing

/-!
# Genuine degree-one sections and the graphic polynomial map

These exact proof bodies are separated from the ample embedding machinery
so the actual homogeneous coordinate ring can be checked independently.
They recover genuine degree-one sections from their existing graded sum,
and merely lift variable labels to the scalar field's universe.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical BigOperators BaseSections

namespace Unimodular.GraphicSectionRing.ActualSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)
  {ι : Type u} (Φ : MvPolynomial ι k →ₐ[k] sectionRing k C)

/-- Recover a polynomial variable as an actual degree-one section, using
the coefficient space of the independently defined ordinary section ring. -/
def polynomialDegreeOneSection (i : ι) : Γ(C.sheaf, ⊤) := by
  let t := coefficientSection k C 1 (Φ (MvPolynomial.X i))
  refine ⟨t.val, ?_⟩
  intro j x hx
  have h := t.property j x hx
  simpa only [RationalCartierCocycle.pow, pow_one] using h

@[simp] theorem polynomialDegreeOneSection_value (i : ι) :
    C.toCartierData.sectionValue ⊤ (polynomialDegreeOneSection k C Φ i) =
      (Φ (MvPolynomial.X i)).val.coeff 1 := by
  change (C.pow 1).toCartierData.globalSectionValue k
      (coefficientSection k C 1 (Φ (MvPolynomial.X i))) = _
  exact coefficientSection_value k C 1 _

theorem polynomialDegreeOneSection_single
    (hX : ∀ (i : ι) (d : ℕ), d ≠ 1 →
      (Φ (MvPolynomial.X i)).val.coeff d = 0) (i : ι) :
    (Φ (MvPolynomial.X i)).val = AddMonoidAlgebra.single 1
      (C.toCartierData.sectionValue ⊤ (polynomialDegreeOneSection k C Φ i)) := by
  apply AddMonoidAlgebra.coeff_injective
  ext d
  by_cases hd : d = 1
  · subst d
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
      polynomialDegreeOneSection_value]
  · rw [hX i d hd]
    simp only [AddMonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hd)]

end Unimodular.GraphicSectionRing.ActualSections


end
