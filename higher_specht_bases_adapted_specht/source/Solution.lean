module

public import higher_specht.verified.remaining04_geometry_complete

@[expose] public section
noncomputable section

universe palomarRepU
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

/-- The localized adapted family gives the actual shape copies after every
coefficient map, using the same triangular coefficients for every right tableau. -/
theorem adapted_specht_lattices_and_specialization (n s : ℕ) (hs : 0 < s) :
    ∃ P : (i : FiniteHarmonicIndex n s) →
        StandardYoungTableau (YoungDiagram.ofPartition i.part) → PolynomialRing n (FactorialLocalization n),
    ∃ F : ∀ (part : n.Partition) (d : ℕ), Fintype (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d),
    ∃ C : ∀ (part : n.Partition) (d : ℕ),
        Matrix (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d)
          (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d) (FactorialLocalization n),
      (∀ part d, letI := F part d
        IsUnit (C part d) ∧
        ∃ order : LinearOrder (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d),
          letI := order
          (C part d).IsUpperTriangular) ∧
      (∀ i T, let d := i.toUnboundedHarmonicIndex.degree
        letI := F i.part d
        P i T = rename (finCongr (YoungDiagram.card_ofPartition i.part))
          (∑ j, C i.part d j (adaptedMasterDegreeIndex i) • fixedGriffinPolynomial T j.val)) ∧
      (∀ (R : Type palomarRepU) [CommRing R] [Nontrivial R] (f : FactorialLocalization n →+* R)
          (lam : YoungDiagram) (hk : lam.card ≤ n) (hheight : lam.colLen 0 ≤ s)
          (i : EligibleFiniteHarmonicIndex n s lam hk),
        ∃ W : Subrepresentation (griffinRepresentation R n lam s),
          W.toSubmodule = Submodule.span R (Set.range
            (fun T => Ideal.Quotient.mk (griffinIdeal R n lam s) (MvPolynomial.map f (P i.val T)))) ∧
          Nonempty (Representation.Equiv (partitionSpechtRepresentationOver R i.val.part)
            W.toRepresentation)) ∧
      ∀ (K : Type palomarRepU) [Field K], ringChar K = 0 ∨ n < ringChar K →
        ∃ f : FactorialLocalization n →+* K,
        ∀ (lam : YoungDiagram) (hk : lam.card ≤ n) (hheight : lam.colLen 0 ≤ s)
          (i : EligibleFiniteHarmonicIndex n s lam hk),
        ∃ W : Subrepresentation (griffinRepresentation K n lam s),
          W.toSubmodule = Submodule.span K (Set.range
            (fun T => Ideal.Quotient.mk (griffinIdeal K n lam s) (MvPolynomial.map f (P i.val T)))) ∧
          W.toRepresentation.IsIrreducible ∧
          Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K i.val.part)
            W.toRepresentation) := by
  classical
  let A := FactorialLocalization n
  have hA : IsUnit (n.factorial : A) := factorial_isUnit_localization n
  let F (part : n.Partition) (d : ℕ) :=
    (inferInstance : Fintype (FixedFiniteDegreeIndex (YoungDiagram.ofPartition part) s d))
  let C (part : n.Partition) (d : ℕ) :=
    (commonPairingMatrix A (YoungDiagram.ofPartition part) s d)⁻¹
  refine ⟨adaptedMasterPolynomial A, F, C, ?_, ?_, ?_, ?_⟩
  · intro part d
    have hfac' : IsUnit ((YoungDiagram.ofPartition part).card.factorial : A) := by
      rw [YoungDiagram.card_ofPartition]
      exact hA
    have hdet := commonPairingMatrix_det_isUnit A (YoungDiagram.ofPartition part) s d hfac'
    refine ⟨Matrix.isUnit_iff_isUnit_det _ |>.mpr
      (Matrix.isUnit_det_of_right_inverse (Matrix.nonsing_inv_mul _ hdet)), ?_⟩
    exact ⟨pairingKeyOrder commonPairingKey,
      commonPairingMatrix_inverse_triangular A (YoungDiagram.ofPartition part) s d hfac'⟩
  · intro i T
    rfl
  · intro R _ _ f lam hk hheight i
    have hfac : IsUnit (n.factorial : R) := by
      simpa only [map_natCast] using hA.map f
    refine ⟨adaptedGriffinCopy (R := R) lam i.val, ?_,
      ⟨adaptedGriffinSpechtEquiv hfac lam hk hs hheight i⟩⟩
    simpa only [map_adaptedMasterPolynomial f hA] using
      adaptedGriffinCopy_eq_span (R := R) lam i.val
  · intro K _ hchar
    have hfac : IsUnit (n.factorial : K) :=
      isUnit_iff_ne_zero.mpr ((factorial_ne_zero_iff_characteristic_range K n).mpr hchar)
    let f : A →+* K := factorialLocalizationMap K n hfac
    refine ⟨f, ?_⟩
    intro lam hk hheight i
    have h := corollary_5_7_field_copy K hchar lam hk hs hheight i
    refine ⟨adaptedGriffinCopy (R := K) lam i.val, ?_, h⟩
    simpa only [map_adaptedMasterPolynomial f hA] using
      adaptedGriffinCopy_eq_span (R := K) lam i.val

end HigherSpecht
