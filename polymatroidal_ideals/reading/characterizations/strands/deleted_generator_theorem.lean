import Characterizations.Strands.DeletedBetti
import Characterizations.Isolators.Pure

/-! # The complete deleted-generator proposition, including its localized ideals -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem deletedVeronese_proper_localization (a : Exponent V) (ha : 2 ≤ a.support.card)
    (U : Finset V) (hU : U ⊂ Finset.univ) :
    monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_of_ssubset hU
  rw [monomialLocalization_eq]
  have he : localFamily (deletedVeronese a) U = {0} :=
    Isolators.localFamily_eq_zero_of_purePower ∅ U a ha j (Finset.notMem_empty _) hj
  rw [he, Ideal.eq_top_iff_one]
  have h : MvPolynomial.monomial (0 : Exponent U) (1 : k) ∈
      monomialIdeal k ({0} : Family U) := (monomial_mem_iff _ _).mpr
        ⟨0, Finset.mem_singleton_self _, le_rfl⟩
  simpa using h

/-- Proposition 4.3: every proper localization is the unit ideal, every
nonlinear fine Betti entry is exactly zero or one as stated, and the total
nonlinear strand has the exact binomial coefficient (including out-of-range zero). -/
theorem deleted_generator_nonlinear_strand (a : Exponent V) (ha : 2 ≤ a.support.card) :
    (∀ U : Finset V, U ⊂ Finset.univ →
      monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤) ∧
    (∀ i b, b.degree ≠ a.degree+i →
      bettiNumber (k := k) (deletedVeronese a) b i =
        if ∃ T : Finset V, a.support ⊆ T ∧ T.card=i+1 ∧ b=a+faceExponent T
          then 1 else 0) ∧
    (∀ i, totalBettiNumber (k := k) (deletedVeronese a) i (a.degree+i+1) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V-a.support.card) (i+1-a.support.card) else 0) ∧
    (∀ i j, j ≠ a.degree+i → j ≠ a.degree+i+1 →
      totalBettiNumber (k := k) (deletedVeronese a) i j = 0) := by
  refine ⟨deletedVeronese_proper_localization a ha, ?_,
    deletedVeronese_total_nonlinear a ha, deletedVeronese_total_other a ha⟩
  intro i b hb
  simpa only [mem_exceptionalDegrees] using deletedVeronese_betti_off_linear a b ha i hb

theorem deletedVeronese_full_support (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (hfull : a.support = Finset.univ) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    bettiNumber (k := k) (deletedVeronese a) b i =
      if i+1=Fintype.card V ∧ b=a+faceExponent Finset.univ then 1 else 0 := by
  rw [deletedVeronese_betti_off_linear a b ha i hoff]
  have he : b ∈ exceptionalDegrees a i ↔
      i+1=Fintype.card V ∧ b=a+faceExponent Finset.univ := by
    rw [mem_exceptionalDegrees]
    constructor
    · rintro ⟨T, hT, hc, he⟩
      have hTu : T = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) (hfull ▸ hT)
      subst T
      exact ⟨by simpa using hc.symm, he⟩
    · rintro ⟨hc, he⟩
      exact ⟨Finset.univ, Finset.subset_univ _, by simpa using hc.symm, he⟩
  simp only [he]

end Characterizations.Strands
