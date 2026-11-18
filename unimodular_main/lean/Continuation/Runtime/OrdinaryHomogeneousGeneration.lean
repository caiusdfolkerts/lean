module

public import Continuation.Runtime.AmpleDegreeOneFoundations
public import Continuation.Runtime.PolynomialSectionDegree
public import Continuation.Runtime.OrdinaryDegreeOneSections

/-!
# Homogeneous generation by the genuine degree-one sections

Surjectivity of the ordinary section-ring presentation is converted into
homogeneous polynomial expressions in each tensor power. The degree-one
variables are recovered as actual sections, and the coefficient calculation
proves that no auxiliary grading is being substituted.

The final theorem constructs the actual degree-one morphism for every
ordinary ample invertible sheaf on the original graphic fan scheme. Closed
immersion and the pullback of O(1) are proved in the subsequent modules.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical BigOperators BaseSections

namespace Unimodular.GraphicSectionRing.ActualSections



section ActualSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)
  {ι : Type u} (Φ : MvPolynomial ι k →ₐ[k] sectionRing k C)

/-- An actual homogeneous polynomial preimage exists in every degree.
Only surjectivity of the actual ring map and its checked degree-one variable
formula are used; an arbitrary inhomogeneous preimage is projected to N. -/
theorem homogeneous_generation_of_surjective
    (hΦ : Function.Surjective Φ)
    (hX : ∀ (i : ι) (d : ℕ), d ≠ 1 →
      (Φ (MvPolynomial.X i)).val.coeff d = 0)
    (N : ℕ) (t : Γ((C.pow N).sheaf, ⊤)) :
    ∃ p : MvPolynomial ι k, p.IsHomogeneous N ∧
      C.sectionProjectiveFieldMap k (polynomialDegreeOneSection k C Φ) p =
        (C.pow N).toCartierData.sectionValue ⊤ t := by
  obtain ⟨p, hp⟩ := hΦ (homogeneousSection k C N t)
  let v : ι → X.functionField := fun i =>
    C.toCartierData.sectionValue ⊤ (polynomialDegreeOneSection k C Φ i)
  have he : (sectionRing k C).val.toRingHom.comp Φ.toRingHom =
      degreeOnePolynomialEvaluation (algebraMap k X.functionField) v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (Φ (algebraMap k (MvPolynomial ι k) a)).val = _
      rw [Φ.commutes]
      simp only [degreeOnePolynomialEvaluation, MvPolynomial.eval₂Hom_C,
        RingHom.comp_apply]
      rfl
    · intro i
      change (Φ (MvPolynomial.X i)).val = _
      rw [degreeOnePolynomialEvaluation, MvPolynomial.eval₂Hom_X']
      exact polynomialDegreeOneSection_single k C Φ hX i
  refine ⟨MvPolynomial.homogeneousComponent N p,
    MvPolynomial.homogeneousComponent_isHomogeneous N p, ?_⟩
  have hcoeff := congrArg (fun q : sectionRing k C => q.val.coeff N) hp
  rw [homogeneousSection_val, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same] at hcoeff
  have hpval : (Φ p).val =
      degreeOnePolynomialEvaluation (algebraMap k X.functionField) v p :=
    congrArg (fun g : MvPolynomial ι k →+* AddMonoidAlgebra X.functionField ℕ => g p) he
  rw [hpval, degreeOnePolynomialEvaluation_coefficient] at hcoeff
  exact hcoeff

end ActualSections

end Unimodular.GraphicSectionRing.ActualSections


end
