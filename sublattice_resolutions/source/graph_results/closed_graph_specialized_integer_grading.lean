module
public import graph_results.closed_graph_specialized_resolution
public import shared_results.part003

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphSpecializedIntegerGrading -/
section

/-!
# Integer degrees of the universal graded free resolution

The natural degree of a monomial times a free generator is its polynomial
degree plus the generator shift. Regrading along `ℕ → ℤ` gives the literal
integer degree on this same coefficient basis. Thus the graded resolution
identities also hold in every integer degree; the negative pieces vanish
because no basis vector has negative degree.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg MvPolynomial

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
  (s : ℕ) (hs : 0 < s)
  (A : Type*) [CommRing A] [Algebra GraphIntegralCoefficientRing A]

/-- The integer-graded submodule of the actual specialized free term. -/
def integralGraphSpecializedFreeIntegerPiece (p : ℕ) (q : ℤ) :
    Submodule A (IntegralGraphSpecializedFreeTerm hG s hs A p) :=
  ordinaryIntegerRegrade (integralGraphSpecializedFreeOrdinaryPiece hG s hs A p) q

/-- The regrading is exactly the integer-valued degree of the displayed
monomial-times-generator basis, rather than a separate convention. -/
theorem integralGraphSpecializedFreeIntegerPiece_eq (p : ℕ) (q : ℤ) :
    integralGraphSpecializedFreeIntegerPiece hG s hs A p q =
      Grading.Piece
        (ShiftedPolynomialFree.expandedBasis
          (R := A) (V := GraphIntegralVariables N)
          (I := IntegralGraphDegreeIndex hG s hs p))
        (fun a => ((a.2.degree + integralGraphSpecializedFreeShift hG s hs p a.1 : ℕ) : ℤ)) q :=
  ordinaryIntegerRegrade_basisPiece
    (ShiftedPolynomialFree.expandedBasis (R := A) (V := GraphIntegralVariables N)
      (I := IntegralGraphDegreeIndex hG s hs p))
    (ShiftedPolynomialFree.expandedDegree (integralGraphSpecializedFreeShift hG s hs p)) q

@[simp] theorem integralGraphSpecializedFreeIntegerPiece_nat (p q : ℕ) :
    integralGraphSpecializedFreeIntegerPiece hG s hs A p (q : ℤ) =
      integralGraphSpecializedFreeOrdinaryPiece hG s hs A p q :=
  ordinaryIntegerRegrade_nat _ q

theorem integralGraphSpecializedFreeIntegerPiece_negative (p : ℕ) (q : ℤ)
    (hq : q < 0) : integralGraphSpecializedFreeIntegerPiece hG s hs A p q = ⊥ :=
  ordinaryIntegerRegrade_negative _ q hq

/-- The actual polynomial-linear differential preserves every integer
homogeneous piece, including the vanishing negative pieces. -/
theorem integralGraphSpecializedFree_differential_preserves_integer (p : ℕ) (q : ℤ)
    {x : IntegralGraphSpecializedFreeTerm hG s hs A (p+1)}
    (hx : x ∈ integralGraphSpecializedFreeIntegerPiece hG s hs A (p+1) q) :
    integralGraphSpecializedFreeDifferential hG s hs A p x ∈
      integralGraphSpecializedFreeIntegerPiece hG s hs A p q := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [integralGraphSpecializedFreeIntegerPiece_nat] at hx ⊢
    exact integralGraphSpecializedFree_differential_preserves_ordinary hG s hs A p n hx
  · have hx0 : x = 0 := by
      change x ∈ ordinaryIntegerRegrade
        (integralGraphSpecializedFreeOrdinaryPiece hG s hs A (p+1)) q at hx
      rw [ordinaryIntegerRegrade_eq_bot_of_not_image _ q hq, Submodule.mem_bot] at hx
      exact hx
    rw [hx0, map_zero]
    exact (integralGraphSpecializedFreeIntegerPiece hG s hs A p q).zero_mem

/-- Augmentation preserves the literal integer degree in the target
polynomial ideal; its value is graded in the original polynomial basis. -/
theorem integralGraphSpecializedFree_augmentation_preserves_integer (q : ℤ)
    {x : IntegralGraphSpecializedFreeTerm hG s hs A 0}
    (hx : x ∈ integralGraphSpecializedFreeIntegerPiece hG s hs A 0 q) :
    (integralGraphSpecializedFreeAugmentation hG s hs A x).val ∈
      Grading.Piece (MvPolynomial.basisMonomials (GraphIntegralVariables N) A)
        (fun a => (a.degree : ℤ)) q := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [integralGraphSpecializedFreeIntegerPiece_nat] at hx
    have hε := integralGraphSpecializedFree_augmentation_preserves_ordinary hG s hs A n hx
    rw [Grading.mem_piece]
    intro a ha
    have hc : ((integralGraphSpecializedFreeAugmentation hG s hs A x).val).coeff a ≠ 0 := ha
    have hn : a.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one] using hε hc
    exact congrArg (fun t : ℕ => (t : ℤ)) hn
  · have hx0 : x = 0 := by
      change x ∈ ordinaryIntegerRegrade
        (integralGraphSpecializedFreeOrdinaryPiece hG s hs A 0) q at hx
      rw [ordinaryIntegerRegrade_eq_bot_of_not_image _ q hq, Submodule.mem_bot] at hx
      exact hx
    rw [hx0, map_zero]
    exact (Grading.Piece (MvPolynomial.basisMonomials (GraphIntegralVariables N) A)
      (fun a => (a.degree : ℤ)) q).zero_mem

end FourPapers.Sublattice

end
end
end


end
