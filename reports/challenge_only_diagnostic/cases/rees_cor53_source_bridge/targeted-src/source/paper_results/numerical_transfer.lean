module
public import paper_results.numerical_invariants
public import paper_results.homogeneous_ideal_quotient_tor_shift
public import paper_results.transfer_formulas
public import paper_results.ideal_projective_dimension
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiPolynomialInvariants -/
section

/-! # Projective dimension and depth along the powers

The homological maximum is obtained from actual Betti groups. Its existence
uses a constructed resolution, its attainment uses the least vanishing bound,
and its equality with projective dimension uses both a free-resolution upper
bound and the nonzero-Tor lower bound. Depth is the literal Ext-defined depth.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [Field k]

lemma monomial_projectiveDimension_le_of_betti_vanishing {V : Type u}
    [Fintype V] [LinearOrder V] (B : Family V) (N : ℕ)
    (hvan : ∀ p, N < p → ∀ q, ordinaryMonomialBettiNumber (k := k) B q p = 0) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) ≤ (N : WithBot ℕ∞) := by
  let o : MonomialOrder V := MonomialOrder.degLex
  apply ideal_projectiveDimension_le_of_betti_vanishing
    (canonicalQuotientGroebnerData o (monomialIdeal k B))
    (monomialIdeal_isOrdinaryHomogeneous B) N
  intro p hp q
  exact (monomialTorBettiNumber_eq o B p q).trans (hvan p hp q)

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

theorem powerBettiBound_exists (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ) :
    ∃ N : ℕ, ∀ p, N < p → ∀ q, ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) q p = 0 := by
  refine ⟨finiteLatticeHeight hE hne, ?_⟩
  intro p hp q
  by_contra hq
  have he := ordinaryBetti_nonzero_le_projectiveDimension
    (exponentPowerFamily (finiteRowFamily n E) m) q p hq
  rw [finitePowerFamily_ideal] at he
  have hle := he.trans (theorem81_projectiveDimension_upper (k := k) hE hne m)
  have hpn : p ≤ finiteLatticeHeight hE hne := by exact_mod_cast hle
  omega

/-- The least genuine homological vanishing bound; no Betti number is redefined. -/
def powerBettiBound (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ) : ℕ :=
  Nat.find (powerBettiBound_exists (k := k) hE hne m)

lemma powerBettiBound_spec (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ)
    (p : ℕ) (hp : powerBettiBound (k := k) hE hne m < p) (q : ℕ) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) q p = 0 :=
  Nat.find_spec (powerBettiBound_exists (k := k) hE hne m) p hp q

lemma powerBettiBound_attained (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (m : ℕ) (hm : 0 < m) : ∃ q,
    ordinaryMonomialBettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) m)
      q (powerBettiBound (k := k) hE hne m) ≠ 0 := by
  by_cases h0 : powerBettiBound (k := k) hE hne m = 0
  · exact ⟨m*d, by simpa only [h0] using power_betti_generator_nonzero (k := k) hE hne m hm⟩
  · obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero h0
    by_contra hn
    push_neg at hn
    have hgood : ∀ p, N < p → ∀ q,
        ordinaryMonomialBettiNumber (k := k)
          (exponentPowerFamily (finiteRowFamily n E) m) q p = 0 := by
      intro p hp q
      by_cases he : p = N+1
      · simpa only [he, hN] using hn q
      · exact powerBettiBound_spec hE hne m p (by omega) q
    have hle := Nat.find_min' (powerBettiBound_exists (k := k) hE hne m) hgood
    change powerBettiBound (k := k) hE hne m ≤ N at hle
    omega

lemma power_projectiveDimension_eq_bettiBound (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (m : ℕ) (hm : 0 < m) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k := k) E)^m)) =
      (powerBettiBound (k := k) hE hne m : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [← finitePowerFamily_ideal]
    exact monomial_projectiveDimension_le_of_betti_vanishing _ _
      (powerBettiBound_spec hE hne m)
  · obtain ⟨q, hq⟩ := powerBettiBound_attained (k := k) hE hne m hm
    have he := ordinaryBetti_nonzero_le_projectiveDimension _ q _ hq
    rwa [finitePowerFamily_ideal] at he

lemma powerBettiBound_mono (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    powerBettiBound (k := k) hE hne m ≤ powerBettiBound (k := k) hE hne N := by
  obtain ⟨Q, hQ⟩ := powerBettiBound_attained (k := k) hE hne m hm
  have hQlo : m*d ≤ Q := by
    by_contra h
    exact hQ (ordinaryPowerBetti_eq_zero_below hE m hm Q _ (lt_of_not_ge h))
  let q := Q - m*d
  have he : m*d+q = Q := Nat.add_sub_of_le hQlo
  have hnonzero : normalizedBettiSequence (k := k) (E := E) q
      (powerBettiBound (k := k) hE hne m) (m-1) ≠ 0 := by
    simpa only [normalizedBettiSequence, Nat.sub_add_cancel (by omega : 1 ≤ m), he] using hQ
  have hle := normalizedBettiSequence_monotone (k := k) hE q
    (powerBettiBound (k := k) hE hne m) (Nat.sub_le_sub_right hmN 1)
  have hN : 0 < N := hm.trans_le hmN
  have hβ : ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) N) (N*d+q)
      (powerBettiBound (k := k) hE hne m) ≠ 0 := by
    have hp := (Nat.pos_of_ne_zero hnonzero).trans_le hle
    simpa only [normalizedBettiSequence, Nat.sub_add_cancel (by omega : 1 ≤ N)] using ne_of_gt hp
  by_contra h
  exact hβ (powerBettiBound_spec hE hne N _ (lt_of_not_ge h) _)

/-- Corollary 5.2 for the actual projective dimensions. -/
theorem corollary52_projectiveDimension_monotone_nonempty (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k := k) E)^m)) ≤
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k := k) E)^N)) := by
  rw [power_projectiveDimension_eq_bettiBound hE hne m hm,
    power_projectiveDimension_eq_bettiBound hE hne N (hm.trans_le hmN)]
  exact_mod_cast powerBettiBound_mono (k := k) hE hne hm hmN

lemma power_quotient_bettiBound_tor_nonzero (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (hd : 0 < d) (m : ℕ) (hm : 0 < m) :
    ¬IsZero (finitePolynomialTor (powerBettiBound (k := k) hE hne m+1)
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m))) := by
  obtain ⟨Q, hQ⟩ := powerBettiBound_attained (k := k) hE hne m hm
  have hQlo : m*d ≤ Q := by
    by_contra h
    exact hQ (ordinaryPowerBetti_eq_zero_below hE m hm Q _ (lt_of_not_ge h))
  rw [ordinaryMonomialBettiNumber_eq_sum] at hQ
  obtain ⟨α, _, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hα0 : α.val ≠ 0 := by
    intro he
    have hpos : 0 < Q := (Nat.mul_pos hm hd).trans_le hQlo
    have hz := α.property
    rw [he, map_zero] at hz
    omega
  have ht := quotientTor_nonzero_of_idealBetti
    (exponentPowerFamily (finiteRowFamily n E) m) α.val hα0 _ hα
  change ¬IsZero (finitePolynomialTor _
    (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      (MvPolynomial (FiniteVariable.{u} n) k ⧸ FourPapers.Universal.forbiddenIdeal
        (QuotientAllowed (exponentPowerFamily (finiteRowFamily n E) m))))) at ht
  rwa [forbiddenIdeal_eq_monomialIdeal, finitePowerFamily_ideal] at ht

/-- The Ext-defined depth is computed from the attained genuine top Tor degree. -/
lemma power_depth_eq_bettiBound (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hd : 0 < d) (m : ℕ) (hm : 0 < m) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m)) =
      ((Fintype.card (FiniteVariable.{u} n) - powerBettiBound (k := k) hE hne m - 1 : ℕ) : ℕ∞) := by
  let M := ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
    (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m)
  let h := powerBettiBound (k := k) hE hne m
  have ht : ¬IsZero (finitePolynomialTor (h+1) M) :=
    power_quotient_bettiBound_tor_nonzero hE hne hd m hm
  have hbound : projectiveDimension M ≤ (h+1 : ℕ) :=
    idealQuotient_projectiveDimension_le _ h
      (power_projectiveDimension_eq_bettiBound (k := k) hE hne m hm).le
  have hN : h+1 ≤ Fintype.card (FiniteVariable.{u} n) := by
    by_contra hh
    exact ht (polynomialTor_isZero_of_card_lt M _ (lt_of_not_ge hh))
  have he := FourPapers.KoszulExtTorDuality.depth_eq_of_topTor M (h+1) (by omega) hN ht
    (fun p hp => polynomialTor_isZero_of_projectiveDimension_le M _ hbound p hp)
  simpa only [Nat.sub_sub, M, h] using he

/-- Corollary 5.2 for the actual depth of every proper positive-row quotient. -/
theorem corollary52_depth_antitone_proper (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hd : 0 < d) {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^N)) ≤
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m)) := by
  rw [power_depth_eq_bettiBound hE hne hd N (hm.trans_le hmN),
    power_depth_eq_bettiBound hE hne hd m hm]
  have he := powerBettiBound_mono (k := k) hE hne hm hmN
  exact_mod_cast Nat.sub_le_sub_right (Nat.sub_le_sub_left he _) 1

/-- The empty generating family is the literal zero ideal. -/
lemma finiteSublatticeIdeal_empty_family :
    finiteSublatticeIdeal n (k := k) (∅ : Finset (FiniteTuple n)) = ⊥ := by
  simp only [finiteSublatticeIdeal, Finset.coe_empty, Set.image_empty, Ideal.span_empty]

lemma finiteSublatticeIdeal_zero_rows (h0 : d = 0) (hne : E.Nonempty) :
    finiteSublatticeIdeal n (k := k) E = ⊤ := by
  subst d
  obtain ⟨a, ha⟩ := hne
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  have hu : finiteRowMonomial n (k := k) a ∈ finiteSublatticeIdeal n (k := k) E := by
    apply Ideal.subset_span
    exact ⟨a, ha, rfl⟩
  simpa only [finiteRowMonomial, Finset.univ_eq_empty, Finset.prod_empty] using hu

/-- Projective-dimension monotonicity includes the empty family. -/
theorem corollary52_projectiveDimension_monotone (hE : finiteLatticeClosed n E)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k := k) E)^m)) ≤
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k := k) E)^N)) := by
  by_cases hne : E.Nonempty
  · exact corollary52_projectiveDimension_monotone_nonempty hE hne hm hmN
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, finiteSublatticeIdeal_empty_family,
      Ideal.bot_pow hm.ne', Ideal.bot_pow (hm.trans_le hmN).ne']

/-- Depth monotonicity includes both the empty family and zero-row unit ideal. -/
theorem corollary52_depth_antitone (hE : finiteLatticeClosed n E)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^N)) ≤
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m)) := by
  by_cases hne : E.Nonempty
  · by_cases hd : 0 < d
    · exact corollary52_depth_antitone_proper hE hne hd hm hmN
    · rw [finiteSublatticeIdeal_zero_rows (by omega) hne, Ideal.top_pow, Ideal.top_pow]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, finiteSublatticeIdeal_empty_family,
      Ideal.bot_pow hm.ne', Ideal.bot_pow (hm.trans_le hmN).ne']

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary52_projectiveDimension_monotone
#print axioms FourPapers.Sublattice.corollary52_depth_antitone

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiPolynomialInvariantTransfer -/
section

/-! # Actual projective dimension and depth under the first-power criterion

The all-power Betti comparison is a proved input. Projective dimension is
bounded by the constructed free resolution and detected by an attained Tor
entry. The quotient depth is then computed by the explicit connecting class
and Koszul Ext/Tor duality. Empty families and zero-row unit ideals are
included in the monotonicity statements.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul
open CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (o : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
  (hβ : ∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
    sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)

include hβ in
lemma comparison_power_projectiveDimension (hne : E.Nonempty) (m : ℕ) (hm : 0 < m) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K) ↥(J^m)) =
      (powerBettiBound (k := K) hE hne m : WithBot ℕ∞) := by
  apply le_antisymm
  · apply ideal_projectiveDimension_le_of_betti_vanishing
      (sublatticePowerQuotientData n o J E hE hinit m)
      (homogeneousIdealPower n J hJ m) (powerBettiBound (k := K) hE hne m)
    intro p hp q
    change sublatticePowerBettiNumber n o J E hE hinit hJ m p q = 0
    rw [theorem43_ordinary_betti n o J E hE hinit hJ hβ m p q]
    exact powerBettiBound_spec hE hne m p hp q
  · obtain ⟨q, hq⟩ := powerBettiBound_attained (k := K) hE hne m hm
    apply ordinaryIdealBetti_nonzero_le_projectiveDimension
      (sublatticePowerQuotientData n o J E hE hinit m)
      (homogeneousIdealPower n J hJ m) _ q
    change sublatticePowerBettiNumber n o J E hE hinit hJ m _ q ≠ 0
    rwa [theorem43_ordinary_betti n o J E hE hinit hJ hβ m _ q]

include hβ in
lemma comparison_power_depth (hne : E.Nonempty) (hd : 0 < d) (m : ℕ) (hm : 0 < m) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) K).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K)
        (MvPolynomial (FiniteVariable.{u} n) K ⧸ J^m)) =
      ((Fintype.card (FiniteVariable.{u} n) - powerBettiBound (k := K) hE hne m - 1 : ℕ) : ℕ∞) := by
  let M := ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K)
    (MvPolynomial (FiniteVariable.{u} n) K ⧸ J^m)
  let b := powerBettiBound (k := K) hE hne m
  obtain ⟨q, hq⟩ := powerBettiBound_attained (k := K) hE hne m hm
  have hqlo : m*d ≤ q := by
    by_contra hh
    exact hq (ordinaryPowerBetti_eq_zero_below hE m hm q _ (lt_of_not_ge hh))
  have ht : ¬ IsZero (finitePolynomialTor (b+1) M) := by
    apply quotientTor_nonzero_of_ordinaryIdealBetti
      (sublatticePowerQuotientData n o J E hE hinit m)
      (homogeneousIdealPower n J hJ m) b q ((Nat.mul_pos hm hd).trans_le hqlo)
    change sublatticePowerBettiNumber n o J E hE hinit hJ m b q ≠ 0
    rwa [theorem43_ordinary_betti n o J E hE hinit hJ hβ m b q]
  have hbound : projectiveDimension M ≤ (b+1 : ℕ) :=
    idealQuotient_projectiveDimension_le (J^m) b
      (comparison_power_projectiveDimension n o J E hE hinit hJ hβ hne m hm).le
  have hbN : b+1 ≤ Fintype.card (FiniteVariable.{u} n) := by
    by_contra hh
    exact ht (polynomialTor_isZero_of_card_lt M _ (lt_of_not_ge hh))
  have hh := FourPapers.KoszulExtTorDuality.depth_eq_of_topTor M (b+1) (by omega) hbN ht
    (fun p hp => polynomialTor_isZero_of_projectiveDimension_le M _ hbound p hp)
  simpa only [Nat.sub_sub, M, b] using hh

lemma ideal_eq_bot_of_initialIdeal_eq_bot {V : Type u} [Fintype V] [LinearOrder V]
    (o : MonomialOrder V) (J : Ideal (MvPolynomial V K))
    (h : FourPapers.initialIdeal o J = ⊥) : J = ⊥ := by
  apply bot_unique
  intro f hf
  have he := FourPapers.leadingTerm_mem_initial o hf
  rw [h, Ideal.mem_bot] at he
  exact (o.leadingTerm_eq_zero_iff f).mp he

lemma initialIdeal_eq_self_of_no_variables {V : Type u} [IsEmpty V]
    (o : MonomialOrder V) (J : Ideal (MvPolynomial V K)) :
    FourPapers.initialIdeal o J = J := by
  have he (f : MvPolynomial V K) : o.leadingTerm f = f := by
    have hd : o.degree f = 0 := Subsingleton.elim _ _
    rw [o.eq_C_of_degree_eq_zero hd]
    exact o.leadingTerm_C _
  have hf : o.leadingTerm = id := funext he
  rw [FourPapers.initialIdeal, hf, Set.image_id, Ideal.span_eq]

include hβ in
/-- Corollary 5.2 for the genuine projective dimensions of the original J powers. -/
theorem corollary52_projectiveDimension_monotone_transfer {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K) ↥(J^m)) ≤
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K) ↥(J^N)) := by
  by_cases hne : E.Nonempty
  · rw [comparison_power_projectiveDimension n o J E hE hinit hJ hβ hne m hm,
      comparison_power_projectiveDimension n o J E hE hinit hJ hβ hne N (hm.trans_le hmN)]
    exact_mod_cast powerBettiBound_mono (k := K) hE hne hm hmN
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hi : FourPapers.initialIdeal o J = ⊥ := by
      rw [hinit, he, finiteSublatticeIdeal_empty_family]
    rw [ideal_eq_bot_of_initialIdeal_eq_bot o J hi, Ideal.bot_pow hm.ne',
      Ideal.bot_pow (hm.trans_le hmN).ne']

include hβ in
/-- Corollary 5.2 for the Ext-defined depths of the original quotient powers. -/
theorem corollary52_depth_antitone_transfer {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) K).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K)
        (MvPolynomial (FiniteVariable.{u} n) K ⧸ J^N)) ≤
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) K).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) K)
        (MvPolynomial (FiniteVariable.{u} n) K ⧸ J^m)) := by
  by_cases hne : E.Nonempty
  · by_cases hd : 0 < d
    · rw [comparison_power_depth n o J E hE hinit hJ hβ hne hd N (hm.trans_le hmN),
        comparison_power_depth n o J E hE hinit hJ hβ hne hd m hm]
      have he := powerBettiBound_mono (k := K) hE hne hm hmN
      exact_mod_cast Nat.sub_le_sub_right (Nat.sub_le_sub_left he _) 1
    · have hd0 : d = 0 := by omega
      have hi : J = ⊤ := by
        have hI := finiteSublatticeIdeal_zero_rows (k := K) hd0 hne
        subst d
        rw [initialIdeal_eq_self_of_no_variables] at hinit
        exact hinit.trans hI
      rw [hi, Ideal.top_pow, Ideal.top_pow]
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hi : FourPapers.initialIdeal o J = ⊥ := by
      rw [hinit, he, finiteSublatticeIdeal_empty_family]
    rw [ideal_eq_bot_of_initialIdeal_eq_bot o J hi, Ideal.bot_pow hm.ne',
      Ideal.bot_pow (hm.trans_le hmN).ne']

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary52_projectiveDimension_monotone_transfer
#print axioms FourPapers.Sublattice.corollary52_depth_antitone_transfer

end
end
end


end
