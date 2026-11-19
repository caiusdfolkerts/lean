module

public import higher_specht.verified.remaining04_geometry_complete

@[expose] public section
noncomputable section
open TauCeti MvPolynomial
open scoped BigOperators Classical

namespace HigherSpecht

theorem finiteHarmonic_master_eligible {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    CatDominates (prefixTableau i.left (⊥ : YoungDiagram).card
      (fixedMasterIndex_bound (YoungDiagram.ofPartition i.part))) ⊥ := (finiteHarmonicToFixed i).eligible

theorem finiteHarmonic_master_length {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    i.multiplier.colLen 0 ≤ (YoungDiagram.ofPartition i.part).card - (⊥ : YoungDiagram).card := (finiteHarmonicToFixed i).multiplier_length

def adaptedMasterDegreeIndex {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    FixedFiniteDegreeIndex (YoungDiagram.ofPartition i.part) s i.toUnboundedHarmonicIndex.degree :=
  ⟨{ left := i.left
     multiplier := i.multiplier
     eligible := finiteHarmonic_master_eligible i
     descents_lt := i.descents_lt
     multiplier_length := finiteHarmonic_master_length i
     multiplier_width := i.multiplier_width }, rfl⟩

/-- A single triangular coefficient change, independent of the right
tableau and of the quotient, works for every allowed Griffin ideal. -/
theorem adapted_master_triangular_basis_and_vanishing (R : Type*) [CommRing R] [Nontrivial R]
    (n s : ℕ) (hs : 0 < s) (hfac : IsUnit (n.factorial : R)) :
    ∃ P : (i : FiniteHarmonicIndex n s) →
        StandardYoungTableau (YoungDiagram.ofPartition i.part) → PolynomialRing n R,
    ∃ F : ∀ (part : n.Partition) (d : ℕ), Fintype (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d),
    ∃ C : ∀ (part : n.Partition) (d : ℕ),
        Matrix (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d)
          (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d) R,
      (∀ part d, letI := F part d
        IsUnit (C part d) ∧
        ∃ order : LinearOrder (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d),
          letI := order
          (C part d).IsUpperTriangular) ∧
      (∀ i T, let d := i.toUnboundedHarmonicIndex.degree
        letI := F i.part d
        P i T = rename (finCongr (YoungDiagram.card_ofPartition i.part))
          (∑ j, C i.part d j (adaptedMasterDegreeIndex i) • fixedGriffinPolynomial T j.val)) ∧
      (∀ i T, (P i T).IsHomogeneous i.toUnboundedHarmonicIndex.degree) ∧
      ∀ (lam : YoungDiagram) (hk : lam.card ≤ n) (hheight : lam.colLen 0 ≤ s),
        IsSpecifiedBasis (R := R)
          (fun z : EligibleHarmonicTableauIndex n s lam hk =>
            Ideal.Quotient.mk (griffinIdeal R n lam s) (P z.1.val z.2)) ∧
        ∀ i T, P i T ∈ griffinIdeal R n lam s ↔
          ¬ i.toUnboundedHarmonicIndex.eligible lam hk := by
  classical
  let F (part : n.Partition) (d : ℕ) :=
    (inferInstance : Fintype (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d))
  let C (part : n.Partition) (d : ℕ) :=
    (commonPairingMatrix R (YoungDiagram.ofPartition part) s d)⁻¹
  refine ⟨adaptedMasterPolynomial R, F, C, ?_, ?_, adaptedMasterPolynomial_isHomogeneous R, ?_⟩
  · intro part d
    have hfac' : IsUnit ((YoungDiagram.ofPartition part).card.factorial : R) := by
      rw [YoungDiagram.card_ofPartition]
      exact hfac
    have hdet := commonPairingMatrix_det_isUnit R (YoungDiagram.ofPartition part) s d hfac'
    refine ⟨Matrix.isUnit_iff_isUnit_det _ |>.mpr
      (Matrix.isUnit_det_of_right_inverse (Matrix.nonsing_inv_mul _ hdet)), ?_⟩
    exact ⟨pairingKeyOrder commonPairingKey,
      commonPairingMatrix_inverse_triangular R (YoungDiagram.ofPartition part) s d hfac'⟩
  · intro i T
    rfl
  · intro lam hk hheight
    exact corollary_5_7_of_factorial_isUnit R hfac lam hk hs hheight

end HigherSpecht
