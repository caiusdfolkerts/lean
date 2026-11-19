module

public import higher_specht.verified.remaining04_geometry_complete

@[expose] public section
noncomputable section

namespace HigherSpecht

/-- Both conventional multiplicities: actual local length and the leading
coefficient of the eventual Hilbert polynomial of the actual quotient. -/
theorem untruncated_primary_and_graded_multiplicities (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (∀ A : SpringerCoordinateBlocks n lam,
      genericComponentLength K A = (lam.card.factorial / rowFactorialProduct lam : ℕ)) ∧
    let m := n - lam.card
    let M : ℚ := ((n.factorial / (m.factorial * rowFactorialProduct lam) : ℕ) : ℚ)
    (m = 0 → (Module.finrank K (UntruncatedRing K n lam) : ℚ) = M) ∧
    (0 < m → ∃ P : Polynomial ℚ,
      (∃ N : ℕ, ∀ d > N, (untruncatedHilbertFunction K n lam d : ℚ) = P.eval (d : ℚ)) ∧
      P.natDegree = m - 1 ∧ ((m - 1).factorial : ℚ) * P.leadingCoeff = M) := by
  refine ⟨fun A => proposition_7_3_generic_component_length hk A, ?_⟩
  dsimp only
  constructor
  · intro h
    simpa only [standardGradedMultiplicity, if_pos h] using
      proposition_7_3_standard_graded_multiplicity K n lam hk
  · intro h
    refine ⟨untruncatedHilbertPolynomial n lam,
      untruncatedHilbertPolynomial_eventual K n lam hk,
      (untruncatedHilbertPolynomial_degree_and_leadingCoeff n lam hk h).1, ?_⟩
    simpa only [standardGradedMultiplicity, if_neg (Nat.ne_of_gt h)] using
      proposition_7_3_standard_graded_multiplicity K n lam hk

end HigherSpecht
