module

public import higher_specht.verified.remaining04_geometry_complete

@[expose] public section
noncomputable section

open TauCeti MvPolynomial
open scoped BigOperators

namespace HigherSpecht

/-- The ordinary apolar pairing written in monomial coefficients. -/
def apolarCoefficientPairing {n : ℕ} (f p : PolynomialRing n ℂ) : ℂ :=
  ∑ a ∈ f.support, f.coeff a * (p.coeff a * ((∏ j, (a j).factorial : ℕ) : ℂ))

private theorem apolarCoefficientPairing_eq {n : ℕ} (f p : PolynomialRing n ℂ) :
    apolarCoefficientPairing f p = ordinaryApolarFunctional p f := by
  unfold apolarCoefficientPairing
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hm : MvPolynomial.monomial a (f.coeff a) =
      f.coeff a • MvPolynomial.monomial a (1 : ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, ordinaryApolar_monomial] <;> rfl

theorem finite_harmonics_simultaneous
    (n s : ℕ) (hn : 0 < n) (hs : 0 < s) :
    ∃ W : FiniteHarmonicIndex n s → Subrepresentation (polynomialRepresentation ℂ n),
      (∀ i, (W i).toRepresentation.IsIrreducible ∧
        (W i).toSubmodule ≤
          homogeneousSubmodule (Fin n) ℂ i.toUnboundedHarmonicIndex.degree) ∧
      iSupIndep (fun i => (W i).toSubmodule) ∧
      ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
        ∀ p : PolynomialRing n ℂ,
          (∀ f ∈ griffinIdeal ℂ n lam s, apolarCoefficientPairing f p = 0) ↔
          p ∈ ⨆ i : {i : FiniteHarmonicIndex n s //
            i.toUnboundedHarmonicIndex.eligible lam hk}, (W i.val).toSubmodule := by
  classical
  let T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part) :=
    fun part => (StandardYoungTableau.rowSuperstandard _).toTableau
  obtain ⟨hcopy, hind, hdecomp⟩ := theorem_5_2_actual_specht n s hn hs T
  let W : FiniteHarmonicIndex n s → Subrepresentation (polynomialRepresentation ℂ n) :=
    fun i => Classical.choose (hcopy i).1
  have hW (i) : (W i).toSubmodule = finiteCommonHarmonicCopyWithTableau i (T i.part) :=
    (Classical.choose_spec (hcopy i).1).1
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(Classical.choose_spec (hcopy i).1).2.1, by simpa only [hW] using (hcopy i).2⟩
  · simpa only [hW] using hind
  · intro lam hk hheight p
    simpa only [apolarCoefficientPairing_eq, ← mem_ordinaryHarmonics_iff_apolar, hW] using
      (show p ∈ ordinaryHarmonics (griffinIdeal ℂ n lam s) ↔
        p ∈ ⨆ i : {i : FiniteHarmonicIndex n s // i.toUnboundedHarmonicIndex.eligible lam hk},
          finiteCommonHarmonicCopyWithTableau i.val (T i.val.part) from by rw [hdecomp lam hk hheight])

theorem untruncated_harmonics_simultaneous
    (n : ℕ) :
    ∃ W : UnboundedHarmonicIndex n → Subrepresentation (polynomialRepresentation ℂ n),
      (∀ i, (W i).toRepresentation.IsIrreducible ∧
        (W i).toSubmodule ≤ homogeneousSubmodule (Fin n) ℂ i.degree) ∧
      iSupIndep (fun i => (W i).toSubmodule) ∧
      (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n | i.degree = d}) ∧
      ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), ∀ p : PolynomialRing n ℂ,
        (∀ f ∈ untruncatedIdeal ℂ n lam, apolarCoefficientPairing f p = 0) ↔
        p ∈ ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk}, (W i.val).toSubmodule := by
  classical
  let T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part) :=
    fun part => (StandardYoungTableau.rowSuperstandard _).toTableau
  obtain ⟨hcopy, hind, hfinite, hdecomp⟩ := theorem_6_6_actual_specht n T
  let W : UnboundedHarmonicIndex n → Subrepresentation (polynomialRepresentation ℂ n) :=
    fun i => Classical.choose (hcopy i).1
  have hW (i) : (W i).toSubmodule = untruncatedCommonHarmonicCopyWithTableau i (T i.part) :=
    (Classical.choose_spec (hcopy i).1).1
  refine ⟨W, ?_, ?_, hfinite, ?_⟩
  · intro i
    exact ⟨(Classical.choose_spec (hcopy i).1).2.1, by simpa only [hW] using (hcopy i).2⟩
  · simpa only [hW] using hind
  · intro lam hk p
    simpa only [apolarCoefficientPairing_eq, ← mem_ordinaryHarmonics_iff_apolar, hW] using
      (show p ∈ ordinaryHarmonics (untruncatedIdeal ℂ n lam) ↔
        p ∈ ⨆ i : {i : UnboundedHarmonicIndex n // i.eligible lam hk},
          untruncatedCommonHarmonicCopyWithTableau i.val (T i.val.part) from by rw [hdecomp lam hk])

end HigherSpecht
