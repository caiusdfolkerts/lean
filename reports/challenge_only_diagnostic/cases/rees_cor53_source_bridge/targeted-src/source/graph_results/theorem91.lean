module
public import graph_results.closed_graph_specialized_integer_grading

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem91 -/
section

/-!
# Theorem 9.1: the displayed integral family of graded free resolutions

The constructors imported here give the integral resolution itself and its
polynomial-linear realization over every commutative ℤ[z]-algebra. Every
specialization uses the same finite index sets and the same shifts; its matrix
entries are the coefficientwise images of the integral matrices. Exactness is
proved by the coefficient-linear contraction, not by a flatness assumption.

The field endpoints are obtained by the algebra structures induced by
`Polynomial.eval₂RingHom (Int.castRingHom K) 0` and the analogous map at `1`.
The literal generator equalities at these two values are
`graphSpecializedParameterIdeal_zero` and `graphSpecializedParameterIdeal_one`.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice

open MvPolynomial

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
  (s : ℕ) (hs : 0 < s)
  (A : Type*) [CommRing A] [Algebra GraphIntegralCoefficientRing A]

/-- The finite free resolution, arbitrary specialization, minimal-entry,
and actual ordinary-grading conclusions of Theorem 9.1. The maps and terms
in this statement are the explicit constructions, with the literal
specialized ideal power as augmentation target. -/
theorem theorem91 :
    (∀ p, Module.Free (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) ∧
      Module.Finite (MvPolynomial (GraphIntegralVariables N) A)
        (IntegralGraphSpecializedFreeTerm hG s hs A p)) ∧
    (∀ p, Fintype.card (GraphIntegralVariables N) < p →
      Subsingleton (IntegralGraphSpecializedFreeTerm hG s hs A p)) ∧
    Function.Surjective (integralGraphSpecializedFreeAugmentation hG s hs A) ∧
    Function.Exact (integralGraphSpecializedFreeDifferential hG s hs A 0)
      (integralGraphSpecializedFreeAugmentation hG s hs A) ∧
    (∀ p, Function.Exact (integralGraphSpecializedFreeDifferential hG s hs A (p+1))
      (integralGraphSpecializedFreeDifferential hG s hs A p)) ∧
    (∀ p i j, (integralGraphSpecializedFreeDifferential hG s hs A p
      (Finsupp.single i 1)) j ∈ MvPolynomial.idealOfVars (GraphIntegralVariables N) A) ∧
    (∀ p q x, x ∈ integralGraphSpecializedFreeOrdinaryPiece hG s hs A (p+1) q →
      integralGraphSpecializedFreeDifferential hG s hs A p x ∈
        integralGraphSpecializedFreeOrdinaryPiece hG s hs A p q) ∧
    (∀ q x, x ∈ integralGraphSpecializedFreeOrdinaryPiece hG s hs A 0 q →
      IsWeightedHomogeneous (fun _ : GraphIntegralVariables N => (1 : ℕ))
        (integralGraphSpecializedFreeAugmentation hG s hs A x).val q) := by
  obtain ⟨hf,hb,hsurj,he0,hep,hm⟩ := integralGraphSpecializedFree_resolution hG s hs A
  exact ⟨hf,hb,hsurj,he0,hep,hm,
    fun p q _ hx => integralGraphSpecializedFree_differential_preserves_ordinary hG s hs A p q hx,
    fun q _ hx => integralGraphSpecializedFree_augmentation_preserves_ordinary hG s hs A q hx⟩

variable (B : Type*) [CommRing B] [Algebra GraphIntegralCoefficientRing B]

/-- Every two nontrivial coefficient specializations have the same rank in
each homological degree, because their displayed bases have exactly the
same index set. The shift of an index is the same original Koszul degree. -/
theorem theorem91_same_ranks [Nontrivial A] [Nontrivial B] (p : ℕ) :
    Module.finrank (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) =
    Module.finrank (MvPolynomial (GraphIntegralVariables N) B)
      (IntegralGraphSpecializedFreeTerm hG s hs B p) := by
  rw [integralGraphSpecializedFree_finrank hG s hs A p,
    integralGraphSpecializedFree_finrank hG s hs B p]

end FourPapers.Sublattice

end
end
end


end
