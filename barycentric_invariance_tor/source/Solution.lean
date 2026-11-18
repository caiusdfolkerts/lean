module
public import theorem12

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators DirectSum
namespace PalomarBarycentricTor
open Classical CategoryTheory FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [Field K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)

/-- The actual ordinary derived Tor is computed by this actual parameter Koszul complex. -/
theorem actualDerivedTorComparison (i : ℕ) :
    Nonempty (originalParameterTor K hs d i ≅ (originalKoszulComplex K hs d).homology i) := by
  exact ⟨originalParameterTorKoszulIso K hs d i⟩

/-- The homogeneous Koszul formulation of the graded-filtration clause of Theorem1.2. -/
theorem associatedGraded (j i : ℕ) :
    Nonempty ((⨁ n, Grade (originalInternalHomologyFiltration K hs d hrank j i) n) ≃ₗ[K]
      (⨁ (S : {S : Finset (Fin d) // rankSubsetDegree S = j}),
        rankSelectedCohomology K hs d hrank S.val i)) := by
  let E : (⨁ n, Grade (originalInternalHomologyFiltration K hs d hrank j i) n) ≃ₗ[K]
      originalTorAssociatedGraded K hs d hrank j i :=
    DirectSum.congrLinearEquiv (fun n =>
      gradeEquiv _ _ (originalInternalTorEquiv K hs d hrank j i)
        (originalInternalTorEquiv_filtered K hs d hrank j i) n)
  exact ⟨E.trans (FourPapers.Universal.theorem_1_2 K hs d hrank j i)⟩
end PalomarBarycentricTor
