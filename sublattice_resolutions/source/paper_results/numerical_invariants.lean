module
public import shared_results.part023
public import paper_results.part005
public import paper_results.dimension_core
public import shared_results.part003
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import paper_results.part002
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import paper_results.ordinary_ideal_tor_bounds
public import graph_foundation.part010
public import paper_results.transfer_formulas
public import paper_results.theorem81_analytic_spread
public import paper_results.torsion_core
public import paper_results.graded_homology_core
public import Mathlib.Algebra.CharP.Basic
public import graph_foundation.part009
public import paper_results.part003
public import paper_results.part004
public import graph_foundation.part008
public import paper_results.part001
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialRegularity -/
section

/-!
# Regularity from genuine Tor and its eventual linear formula

The regularity support is defined using the actual ordinary homogeneous
submodules of Mathlib's derived Tor. The usual maximum is taken only after
nonemptiness and an upper bound have been proved. For a positive power of
a nonempty sublattice ideal, a displayed degree-zero Koszul class proves
nonemptiness, and an actual exterior-creation contraction supplies the
upper bound. Thus no convention for the regularity of the zero module is
used in the theorem.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The support whose maximum is Castelnuovo--Mumford regularity, with
the homological subtraction performed in the integers. -/
def monomialTorRegularitySupport (o : MonomialOrder V) (B : Family V) : Set ℤ :=
  {r | ∃ p q : ℕ, monomialTorBettiNumber (k := k) o B p q ≠ 0 ∧ r = (q : ℤ) - p}

/-- This maximum is used only with a proved nonempty, bounded support.
The following theorem proves it is attained, so no empty-set convention
enters either its meaning or the later eventual formula. -/
def monomialTorRegularity (o : MonomialOrder V) (B : Family V)
    (_hne : (monomialTorRegularitySupport (k := k) o B).Nonempty)
    (_hb : BddAbove (monomialTorRegularitySupport (k := k) o B)) : ℤ :=
  sSup (monomialTorRegularitySupport (k := k) o B)

theorem monomialTorRegularity_isGreatest (o : MonomialOrder V) (B : Family V)
    (hne : (monomialTorRegularitySupport (k := k) o B).Nonempty)
    (hb : BddAbove (monomialTorRegularitySupport (k := k) o B)) :
    IsGreatest (monomialTorRegularitySupport (k := k) o B)
      (monomialTorRegularity o B hne hb) :=
  ⟨Int.csSup_mem hne hb, (isLUB_csSup hne hb).1⟩

/-- The empty exterior face represents a genuine nonzero degree-zero
class whenever the quotient ideal contains no unit monomial. -/
theorem quotient_zero_degree_homology_nontrivial (B : Family V) (hB : ¬Contains B 0) :
    Nontrivial (ClosedGraphDegreeHomology (k := k) B 0 0) := by
  let Q := quotientKoszulFaces B 0
  let b := totalFaceBasis (k := k) Q
  let e : {F : Finset V // Q F} :=
    ⟨∅, (quotientKoszulFaces_zero_iff B hB ∅).mpr rfl⟩
  letI : IsEmpty (QuotientFaceIndex B 0 1) := ⟨fun F => by
    have he := (quotientKoszulFaces_zero_iff B hB F.val).mp F.property.1
    have hc := F.property.2
    simp only [he, Finset.card_empty] at hc
    omega⟩
  letI : Subsingleton (totalFacePiece (k := k) Q 1) :=
    (quotientTotalPieceBasis (k := k) B 0 1).repr.injective.subsingleton
  have hd : closedGraphDegreeBoundary (k := k) B 0 0 = 0 := by
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have he : b e ∈ totalFacePiece (k := k) Q 0 := by
    change (totalFaceBasis (k := k) Q e).val ∈ Simplicial.Chains Q 0
    rw [totalFaceBasis_val]
    exact Simplicial.basis_mem e.property rfl
  let z : ClosedGraphDegreeCycles (k := k) B 0 0 :=
    ⟨b e, ⟨quotientTotalDifferential_zero_degree B 0 (b e) he, he⟩⟩
  have hz : (Submodule.Quotient.mk z : ClosedGraphDegreeHomology (k := k) B 0 0) ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [hd, LinearMap.zero_apply] at hy
    exact b.ne_zero e (congrArg Subtype.val hy.symm)
  exact ⟨⟨Submodule.Quotient.mk z, 0, hz⟩⟩

theorem quotientBetti_zero_degree_nonzero (B : Family V) (hB : ¬Contains B 0) :
    quotientBettiNumber (k := k) B 0 0 ≠ 0 := by
  letI := quotient_zero_degree_homology_nontrivial (k := k) B hB
  letI : Module.Finite k (ClosedGraphDegreeHomology (k := k) B 0 0) :=
    Module.Finite.equiv (quotientCategoricalDegreeHomologyEquiv B 0 0)
  rw [quotientBettiNumber_eq_homology,
    (quotientCategoricalDegreeHomologyEquiv B 0 0).finrank_eq]
  exact ne_of_gt Module.finrank_pos

section Rows
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def constantBottomChain (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ) :
    FiniteMultichain n E m :=
  ⟨fun _ => finiteLatticeBottom hE hne, fun _ _ _ => le_rfl⟩

theorem constantBottomChain_coefficient (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (m : ℕ) :
    finiteChainCoefficientFamily.{u} n (constantBottomChain hE hne m) = ∅ := by
  ext a
  simp only [finiteChainCoefficientFamily, Finset.mem_biUnion, Finset.mem_univ,
    true_and, constantBottomChain, finitePredecessorFamily_bottom, Finset.notMem_empty,
    exists_false]

/-- The actual ideal power has a generator in degree dm. This explicit
class also covers height zero and zero-dimensional row products. -/
theorem power_betti_generator_nonzero (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (m : ℕ) (hm : 0 < m) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) (m*d) 0 ≠ 0 := by
  apply (ordinary_power_betti_nonzero_iff hE m hm _ _).mpr
  refine ⟨constantBottomChain hE hne m, 0, by simp, ?_⟩
  rw [constantBottomChain_coefficient]
  apply quotientBetti_zero_degree_nonzero
  rintro ⟨a, ha, _⟩
  exact Finset.notMem_empty a ha

theorem power_ordinaryBetti_eq_zero_of_degree_gt (m Q p : ℕ)
    (hQ : Fintype.card (FiniteVariable.{u} n) * m < Q) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) Q p = 0 := by
  rw [ordinaryMonomialBettiNumber_eq_sum]
  apply Finset.sum_eq_zero
  intro α _
  let B := exponentPowerFamily (finiteRowFamily n E) m
  letI : Subsingleton ((homogeneousComplex (k := k) B α.val).homology p) :=
    finitePowerFamily_homology_subsingleton_of_degree_gt E m α.val
      (by simpa only [α.property] using hQ) p
  rw [bettiNumber, ← (gradedTorIso (k := k) B α.val p).toLinearEquiv.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

theorem power_regularitySupport_nonempty (o : MonomialOrder (FiniteVariable.{u} n))
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ) (hm : 0 < m) :
    (monomialTorRegularitySupport (k := k) o
      (exponentPowerFamily (finiteRowFamily n E) m)).Nonempty := by
  refine ⟨(m*d : ℕ), 0, m*d, ?_, by simp⟩
  rw [monomialTorBettiNumber_eq]
  exact power_betti_generator_nonzero hE hne m hm

theorem power_regularitySupport_bddAbove (o : MonomialOrder (FiniteVariable.{u} n)) (m : ℕ) :
    BddAbove (monomialTorRegularitySupport (k := k) o
      (exponentPowerFamily (finiteRowFamily n E) m)) := by
  refine ⟨Fintype.card (FiniteVariable.{u} n) * m, ?_⟩
  rintro r ⟨p, q, h, rfl⟩
  rw [monomialTorBettiNumber_eq] at h
  have hq : q ≤ Fintype.card (FiniteVariable.{u} n) * m := by
    by_contra hh
    exact h (power_ordinaryBetti_eq_zero_of_degree_gt m q p (lt_of_not_ge hh))
  exact (sub_le_self _ (Nat.cast_nonneg p)).trans (by exact_mod_cast hq)

/-- Regularity of the literal ideal I_E^m, as the attained maximum of its
genuine ordinary Tor support. Every order gives the same integer. -/
def finiteSublatticePowerRegularity (o : MonomialOrder (FiniteVariable.{u} n))
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ) (hm : 0 < m) : ℤ :=
  monomialTorRegularity (k := k) o (exponentPowerFamily (finiteRowFamily n E) m)
    (power_regularitySupport_nonempty o hE hne m hm) (power_regularitySupport_bddAbove o m)

theorem finiteSublatticePowerRegularity_isGreatest
    (o : MonomialOrder (FiniteVariable.{u} n))
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ) (hm : 0 < m) :
    IsGreatest (monomialTorRegularitySupport (k := k) o
      (exponentPowerFamily (finiteRowFamily n E) m))
        (finiteSublatticePowerRegularity (k := k) o hE hne m hm) :=
  monomialTorRegularity_isGreatest (k := k) o _ _ _

theorem power_regularitySupport_normalized
    (o : MonomialOrder (FiniteVariable.{u} n)) (m : ℕ) (r : ℤ) :
    r ∈ monomialTorRegularitySupport (k := k) o
      (exponentPowerFamily (finiteRowFamily n E) m) ↔
      ∃ b ∈ normalizedBettiSupport (k := k) (n := n) (E := E) m,
        r = (d : ℤ)*m + (b.2 - b.1) := by
  constructor
  · rintro ⟨p, q, h, rfl⟩
    rw [monomialTorBettiNumber_eq] at h
    exact ⟨(p, (q : ℤ)-(d : ℤ)*m), ⟨q, h, rfl⟩, by ring⟩
  · rintro ⟨⟨p, s⟩, ⟨q, h, hs⟩, hr⟩
    refine ⟨p, q, ?_, ?_⟩
    · rwa [monomialTorBettiNumber_eq]
    · dsimp at hr
      omega

theorem power_regularitySupport_translate
    (o : MonomialOrder (FiniteVariable.{u} n))
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ)
    (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    monomialTorRegularitySupport (k := k) o (exponentPowerFamily (finiteRowFamily n E) m) =
      (fun r : ℤ => (d : ℤ)*m - (d : ℤ)*(max 1 (finiteLatticeHeight hE hne)) + r) ''
        monomialTorRegularitySupport (k := k) o
          (exponentPowerFamily (finiteRowFamily n E) (max 1 (finiteLatticeHeight hE hne))) := by
  ext r
  constructor
  · intro hr
    obtain ⟨b, hb, he⟩ := (power_regularitySupport_normalized o m r).mp hr
    rw [theorem81_support_stabilization hE hne m hm] at hb
    refine ⟨(d : ℤ)*(max 1 (finiteLatticeHeight hE hne)) + (b.2-b.1),
      (power_regularitySupport_normalized o _ _).mpr ⟨b, hb, rfl⟩, ?_⟩
    rw [he]
    ring
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨b, hb, he⟩ := (power_regularitySupport_normalized o _ s).mp hs
    rw [← theorem81_support_stabilization hE hne m hm] at hb
    apply (power_regularitySupport_normalized o m _).mpr
    refine ⟨b, hb, ?_⟩
    rw [he]
    ring

/-- The regularity clause of Theorem 8.1, with its constant defined by the
actual regularity at the stated stabilization power M=max(1,h). -/
theorem theorem81_regularity (o : MonomialOrder (FiniteVariable.{u} n))
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (m : ℕ)
    (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    finiteSublatticePowerRegularity (k := k) o hE hne m
        (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) hm) =
      (d : ℤ)*m +
        (finiteSublatticePowerRegularity (k := k) o hE hne
          (max 1 (finiteLatticeHeight hE hne))
            (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) -
          (d : ℤ)*(max 1 (finiteLatticeHeight hE hne))) := by
  let M := max 1 (finiteLatticeHeight hE hne)
  have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hm' : 0 < m := hM.trans_le hm
  let c : ℤ := (d : ℤ)*m - (d : ℤ)*M
  have hmmax := finiteSublatticePowerRegularity_isGreatest (k := k) o hE hne m hm'
  have hMmax := finiteSublatticePowerRegularity_isGreatest (k := k) o hE hne M hM
  have htranslate := power_regularitySupport_translate (k := k) o hE hne m hm
  have hshift : IsGreatest
      (monomialTorRegularitySupport (k := k) o (exponentPowerFamily (finiteRowFamily n E) m))
      (c + finiteSublatticePowerRegularity (k := k) o hE hne M hM) := by
    rw [htranslate]
    refine ⟨⟨_, hMmax.1, rfl⟩, ?_⟩
    rintro r ⟨s, hs, rfl⟩
    change c + s ≤ c + finiteSublatticePowerRegularity (k := k) o hE hne M hM
    exact add_le_add_right (hMmax.2 hs) c
  have he := hmmax.unique hshift
  change finiteSublatticePowerRegularity (k := k) o hE hne m hm' = _
  rw [he]
  dsimp [c, M]
  ring

end Rows
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem81Depth -/
section

/-! # The genuine depth conclusion of Theorem 8.1

The proof uses the actual Ext definition of depth. The displayed ideal
class gives nonzero quotient Tor one degree higher; the cellular
projective resolution and the short exact sequence I → S → S/I give
vanishing above that degree. Complementary Koszul Ext/Tor duality then
determines depth. Positive row count is explicit because the zero-row
unit-ideal exception is real and is recorded separately.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u

section QuotientBound
variable {R : Type u} [CommRing R]

def idealInclusionShortComplex (I : Ideal R) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero

theorem idealInclusionShortComplex_shortExact (I : Ideal R) :
    (idealInclusionShortComplex I).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ I)
    I.subtype_injective I.mkQ_surjective

/-- The quotient bound is proved from the actual short exact sequence. -/
theorem idealQuotient_projectiveDimension_le (I : Ideal R) (h : ℕ)
    (hI : projectiveDimension (ModuleCat.of R I) ≤ (h : WithBot ℕ∞)) :
    projectiveDimension (ModuleCat.of R (R ⧸ I)) ≤ (h+1 : ℕ) := by
  have hI' : HasProjectiveDimensionLT (ModuleCat.of R I) (h+1) :=
    (projectiveDimension_le_iff _ h).mp hI
  have hR : HasProjectiveDimensionLT (ModuleCat.of R R) (h+2) :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of R R) 1 (h+2) (by omega)
  exact (projectiveDimension_le_iff _ (h+1)).mpr
    ((idealInclusionShortComplex_shortExact I).hasProjectiveDimensionLT_X₃ (h+1) hI' hR)

end QuotientBound

section Polynomial
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]

theorem polynomialTor_isZero_of_card_lt
    (M : ModuleCat.{u} (MvPolynomial V k)) (p : ℕ) (hp : Fintype.card V < p) :
    IsZero (finitePolynomialTor p M) := by
  letI : Module.Free (MvPolynomial V k) (V → MvPolynomial V k) :=
    Module.Free.of_basis (Pi.basisFun (MvPolynomial V k) V)
  letI : Module.Finite (MvPolynomial V k) (V → MvPolynomial V k) :=
    Module.Finite.of_basis (Pi.basisFun (MvPolynomial V k) V)
  have hlarge : Module.finrank (MvPolynomial V k) (V → MvPolynomial V k) < p := by
    simpa only [Module.finrank_eq_card_basis (Pi.basisFun (MvPolynomial V k) V)] using hp
  letI : Subsingleton (⋀[MvPolynomial V k]^p (V → MvPolynomial V k)) :=
    subsingleton_of_forall_eq 0 (exteriorPower.eq_zero_of_finrank_lt
      (R := MvPolynomial V k) (M := V → MvPolynomial V k) p hlarge)
  let C := familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M
  have hz : IsZero (C.X p) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton ((⋀[MvPolynomial V k]^p (V → MvPolynomial V k)) ⊗[MvPolynomial V k] M)
    infer_instance
  exact (finitePolynomialTorIso p M).isZero_iff.mpr
    (HomologicalComplex.ExactAt.isZero_homology (HomologicalComplex.ExactAt.of_isZero hz))

theorem polynomialTor_isZero_of_projectiveDimension_le
    (M : ModuleCat.{u} (MvPolynomial V k)) (h : ℕ)
    (hM : projectiveDimension M ≤ (h : WithBot ℕ∞)) (p : ℕ) (hp : h < p) :
    IsZero (finitePolynomialTor p M) := by
  by_contra hz
  have he := (finitePolynomialTor_nonzero_le_projectiveDimension M p hz).trans hM
  have hph : p ≤ h := by exact_mod_cast he
  omega

end Polynomial

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type u} [Field k]

/-- The exact homological height is detected by a nonzero ordinary
component in total degree at least dm, including the height-zero case. -/
theorem power_height_betti_exists (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    ∃ Q : ℕ, m*d ≤ Q ∧ ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) Q (finiteLatticeHeight hE hne) ≠ 0 := by
  have hm' : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  by_cases hh : finiteLatticeHeight hE hne = 0
  · refine ⟨m*d, le_rfl, ?_⟩
    rw [hh]
    exact power_betti_generator_nonzero hE hne m hm'
  · refine ⟨m*d+(maximalCrossingDegree hE hne).degree, Nat.le_add_right _ _, ?_⟩
    exact power_top_betti_nonzero hE hne (Nat.pos_of_ne_zero hh) m
      ((le_max_right _ _).trans hm)

theorem power_quotient_topTor_nonzero (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hd : 0 < d) (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    ¬IsZero (finitePolynomialTor (finiteLatticeHeight hE hne+1)
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m))) := by
  obtain ⟨Q, hQ, hβ⟩ := power_height_betti_exists (k := k) hE hne m hm
  rw [ordinaryMonomialBettiNumber_eq_sum] at hβ
  obtain ⟨α, _, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  have hα0 : α.val ≠ 0 := by
    intro he
    have hm' : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
    have hpos : 0 < Q := (Nat.mul_pos hm' hd).trans_le hQ
    have he' := α.property
    rw [he, map_zero] at he'
    omega
  have ht := quotientTor_nonzero_of_idealBetti
    (exponentPowerFamily (finiteRowFamily n E) m) α.val hα0 (finiteLatticeHeight hE hne) hα
  change ¬IsZero (finitePolynomialTor (finiteLatticeHeight hE hne+1)
    (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      (MvPolynomial (FiniteVariable.{u} n) k ⧸
        FourPapers.Universal.forbiddenIdeal
          (QuotientAllowed (exponentPowerFamily (finiteRowFamily n E) m))))) at ht
  rwa [forbiddenIdeal_eq_monomialIdeal, finitePowerFamily_ideal] at ht

include k in
/-- The finite depth expression in the paper is nonnegative. This bound
comes from an actual nonzero quotient Tor group, including height zero. -/
theorem theorem81_height_add_one_le_variables (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (hd : 0 < d) (m : ℕ)
    (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    finiteLatticeHeight hE hne + 1 ≤ Fintype.card (FiniteVariable.{u} n) := by
  by_contra hh
  exact power_quotient_topTor_nonzero (k := k) hE hne hd m hm
    (polynomialTor_isZero_of_card_lt _ _ (lt_of_not_ge hh))

/-- The depth clause of Theorem 8.1 for the intended positive-row case,
with the polynomial maximal ideal and quotient module both literal. -/
theorem theorem81_depth (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hd : 0 < d) (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m)) =
      ((Fintype.card (FiniteVariable.{u} n) - finiteLatticeHeight hE hne - 1 : ℕ) : ℕ∞) := by
  let M := ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
    (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k := k) E)^m)
  have ht : ¬IsZero (finitePolynomialTor (finiteLatticeHeight hE hne+1) M) :=
    power_quotient_topTor_nonzero hE hne hd m hm
  have hbound : projectiveDimension M ≤ (finiteLatticeHeight hE hne+1 : ℕ) :=
    idealQuotient_projectiveDimension_le _ (finiteLatticeHeight hE hne)
      (theorem81_projectiveDimension_upper hE hne m)
  have hN : finiteLatticeHeight hE hne+1 ≤ Fintype.card (FiniteVariable.{u} n) := by
    exact theorem81_height_add_one_le_variables (k := k) hE hne hd m hm
  have he := FourPapers.KoszulExtTorDuality.depth_eq_of_topTor M
    (finiteLatticeHeight hE hne+1) (by omega) hN ht
    (fun p hp => polynomialTor_isZero_of_projectiveDimension_le M _ hbound p hp)
  simpa only [Nat.sub_sub, M] using he

/-- The same depth conclusion with the paper's literal integer subtraction.
The preceding bound justifies the equality with Mathlib's natural-valued
finite depth, so no truncation is hidden in the displayed formula. -/
theorem theorem81_depth_integer (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hd : 0 < d) (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    WithTop.map (fun N : ℕ => (N : ℤ))
      ((MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
        (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
          (MvPolynomial (FiniteVariable.{u} n) k ⧸
            (finiteSublatticeIdeal n (k := k) E)^m))) =
      (((Fintype.card (FiniteVariable.{u} n) : ℤ) -
        (finiteLatticeHeight hE hne : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  rw [theorem81_depth hE hne hd m hm]
  change (((Fintype.card (FiniteVariable.{u} n) - finiteLatticeHeight hE hne - 1 : ℕ) : ℤ) :
    WithTop ℤ) = _
  congr 1
  have hN := theorem81_height_add_one_le_variables (k := k) hE hne hd m hm
  omega

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem81 -/
section

/-!
# Theorem 8.1: public statements and genuine invariants

`theorem81_cellularResolution` and `theorem81_cellularBasis` give the
explicit resolution and shifts over every commutative coefficient ring.
The theorem below groups the field-valued clauses using the actual special
fiber, Mathlib projective dimension, and actual ordinary derived Tor.
The depth clause is supplied separately, since the empty-row convention
needs an explicit proper-ideal hypothesis for that clause alone.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  {k : Type u} [Field k]

/-- Normalized support written directly in terms of ordinary derived Tor. -/
def normalizedOrdinaryTorSupport (o : MonomialOrder (FiniteVariable.{u} n))
    (m : ℕ) : Set (ℕ × ℤ) :=
  {b | ∃ q : ℕ,monomialTorBettiNumber (k:=k) o
    (exponentPowerFamily (finiteRowFamily n E) m) b.1 q≠0 ∧
      (q : ℤ)-(d : ℤ)*m=b.2}

theorem normalizedOrdinaryTorSupport_eq (o : MonomialOrder (FiniteVariable.{u} n))
    (m : ℕ) : normalizedOrdinaryTorSupport (k:=k) (E:=E) o m=
      normalizedBettiSupport (k:=k) (n:=n) (E:=E) m := by
  ext b
  simp only [normalizedOrdinaryTorSupport,normalizedBettiSupport,Set.mem_setOf_eq,
    monomialTorBettiNumber_eq]

def stabilizationPower (hE : finiteLatticeClosed n E) (hne : E.Nonempty) : ℕ :=
  max 1 (finiteLatticeHeight hE hne)

theorem stabilizationPower_pos (hE : finiteLatticeClosed n E) (hne : E.Nonempty) :
    0<stabilizationPower hE hne :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

def eventualRegularityConstant (o : MonomialOrder (FiniteVariable.{u} n))
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty) : ℤ :=
  finiteSublatticePowerRegularity (k:=k) o hE hne (stabilizationPower hE hne)
    (stabilizationPower_pos hE hne)-(d : ℤ)*stabilizationPower hE hne

/-- All the field clauses except depth, with their original quantifiers.
The cellular construction is the explicit `theorem81_cellularResolution`;
it has the finite free bases and height bound recorded beside it. -/
theorem theorem81 (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (o : MonomialOrder (FiniteVariable.{u} n)) :
    finiteSublatticeAnalyticSpread (k:=k) (E:=E)=
        ((finiteLatticeHeight hE hne+1 : ℕ) : WithBot ℕ∞) ∧
    (∀ m : ℕ,0< m →
      projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        ↥((finiteSublatticeIdeal n (k:=k) E)^m))≤(finiteLatticeHeight hE hne : WithBot ℕ∞)) ∧
    (∀ m N : ℕ,0< m →m≤N →
      normalizedOrdinaryTorSupport (k:=k) (E:=E) o m⊆
        normalizedOrdinaryTorSupport (k:=k) (E:=E) o N) ∧
    (∀ m : ℕ,∀ hm : stabilizationPower hE hne≤m,
      projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        ↥((finiteSublatticeIdeal n (k:=k) E)^m))=(finiteLatticeHeight hE hne : WithBot ℕ∞) ∧
      normalizedOrdinaryTorSupport (k:=k) (E:=E) o m=
        normalizedOrdinaryTorSupport (k:=k) (E:=E) o (stabilizationPower hE hne) ∧
      finiteSublatticePowerRegularity (k:=k) o hE hne m
        ((stabilizationPower_pos hE hne).trans_le hm)=
          (d : ℤ)*m+eventualRegularityConstant (k:=k) o hE hne) := by
  refine ⟨theorem81_analyticSpread hE hne,
    fun m _ => theorem81_projectiveDimension_upper hE hne m,?_,?_⟩
  · intro m N hm hmN
    rw [normalizedOrdinaryTorSupport_eq,normalizedOrdinaryTorSupport_eq]
    exact normalizedBettiSupport_mono hE hne hm hmN
  · intro m hm
    refine ⟨theorem81_projectiveDimension hE hne m hm,?_,?_⟩
    · rw [normalizedOrdinaryTorSupport_eq,normalizedOrdinaryTorSupport_eq]
      exact theorem81_support_stabilization hE hne m hm
    · exact theorem81_regularity o hE hne m hm

/-- The eventual depth assertion uses the actual homogeneous maximal
ideal and its Ext-defined depth. The positive-row condition is explicit:
with no rows the ideal is the unit ideal, whose zero quotient has infinite
depth. Every other clause above also includes that degenerate convention. -/
theorem theorem81_depthClause (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hd : 0<d) (m : ℕ) (hm : stabilizationPower hE hne≤m) :
    (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
      (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        (MvPolynomial (FiniteVariable.{u} n) k ⧸ (finiteSublatticeIdeal n (k:=k) E)^m))=
      ((Fintype.card (FiniteVariable.{u} n)-finiteLatticeHeight hE hne-1 : ℕ) : ℕ∞) :=
  theorem81_depth hE hne hd m hm

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem81IntegerSupport -/
section

/-!
# Theorem 8.1 with every integer internal degree

The natural-degree support used in the cellular proof is exactly the full
integer-degree support of the actual derived Tor module. This is proved
from its genuine integer regrading and the absence of negative-degree
polynomial Koszul basis vectors. The regularity support is treated in the
same way, so the maximum in the final formula retains all integer degrees.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u

section General
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

/-- The full integer-degree support defining the regularity of a literal
monomial ideal, using its actual derived Tor submodules. -/
def monomialIntegerTorRegularitySupport (o : MonomialOrder V) (B : Family V) : Set ℤ :=
  {r | ∃ p : ℕ, ∃ q : ℤ,
    integerMonomialTorBettiNumber (K := K) o B p q ≠ 0 ∧ r = q - p}

/-- Restricting to natural internal degrees loses no nonzero Tor component. -/
theorem monomialIntegerTorRegularitySupport_eq (o : MonomialOrder V) (B : Family V) :
    monomialIntegerTorRegularitySupport (K := K) o B =
      monomialTorRegularitySupport (k := K) o B := by
  ext r
  constructor
  · rintro ⟨p, q, hβ, hr⟩
    have hq : 0 ≤ q := by
      by_contra hq
      exact hβ (integerMonomialTorBettiNumber_negative o B p q (lt_of_not_ge hq))
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    refine ⟨p, q, ?_, hr⟩
    simpa only [integerMonomialTorBettiNumber_nat, monomialTorBettiNumber_eq] using hβ
  · rintro ⟨p, q, hβ, hr⟩
    refine ⟨p, (q : ℤ), ?_, hr⟩
    simpa only [integerMonomialTorBettiNumber_nat, monomialTorBettiNumber_eq] using hβ

end General

section Rows
variable {K : Type u} [Field K] {d : ℕ} {n : Fin d → ℕ}
  {E : Finset (FiniteTuple n)}

/-- The paper's literal normalized support, with `q` ranging over all
integers and with ordinary integer subtraction. -/
def normalizedIntegerOrdinaryTorSupport
    (o : MonomialOrder (FiniteVariable.{u} n)) (m : ℕ) : Set (ℕ × ℤ) :=
  {b | ∃ q : ℤ,
    integerMonomialTorBettiNumber (K := K) o
      (exponentPowerFamily (finiteRowFamily n E) m) b.1 q ≠ 0 ∧
    q - (d : ℤ) * m = b.2}

/-- Equality with the support used in the main proof; negative internal
degrees are proved to vanish in the actual Tor module. -/
theorem normalizedIntegerOrdinaryTorSupport_eq
    (o : MonomialOrder (FiniteVariable.{u} n)) (m : ℕ) :
    normalizedIntegerOrdinaryTorSupport (K := K) (E := E) o m =
      normalizedOrdinaryTorSupport (k := K) (E := E) o m := by
  ext b
  constructor
  · rintro ⟨q, hβ, hb⟩
    have hq : 0 ≤ q := by
      by_contra hq
      exact hβ (integerMonomialTorBettiNumber_negative o _ b.1 q (lt_of_not_ge hq))
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    refine ⟨q, ?_, hb⟩
    simpa only [integerMonomialTorBettiNumber_nat, monomialTorBettiNumber_eq] using hβ
  · rintro ⟨q, hβ, hb⟩
    refine ⟨(q : ℤ), ?_, hb⟩
    simpa only [integerMonomialTorBettiNumber_nat, monomialTorBettiNumber_eq] using hβ

/-- The complete integer-degree support is nondecreasing at every
positive power and is constant from `max 1 h` onward. -/
theorem theorem81_integer_support
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (o : MonomialOrder (FiniteVariable.{u} n)) :
    (∀ m N : ℕ, 0 < m → m ≤ N →
      normalizedIntegerOrdinaryTorSupport (K := K) (E := E) o m ⊆
        normalizedIntegerOrdinaryTorSupport (K := K) (E := E) o N) ∧
    (∀ m : ℕ, stabilizationPower hE hne ≤ m →
      normalizedIntegerOrdinaryTorSupport (K := K) (E := E) o m =
        normalizedIntegerOrdinaryTorSupport (K := K) (E := E) o
          (stabilizationPower hE hne)) := by
  constructor
  · intro m N hm hmN
    rw [normalizedIntegerOrdinaryTorSupport_eq, normalizedIntegerOrdinaryTorSupport_eq,
      normalizedOrdinaryTorSupport_eq, normalizedOrdinaryTorSupport_eq]
    exact normalizedBettiSupport_mono hE hne hm hmN
  · intro m hm
    rw [normalizedIntegerOrdinaryTorSupport_eq, normalizedIntegerOrdinaryTorSupport_eq,
      normalizedOrdinaryTorSupport_eq, normalizedOrdinaryTorSupport_eq]
    exact theorem81_support_stabilization hE hne m hm

/-- The regularity formula is the attained maximum of `q-p` over the
entire integer-graded Tor support, at the paper's exact threshold. -/
theorem theorem81_integer_regularity
    (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (o : MonomialOrder (FiniteVariable.{u} n)) (m : ℕ)
    (hm : stabilizationPower hE hne ≤ m) :
    IsGreatest (monomialIntegerTorRegularitySupport (K := K) o
      (exponentPowerFamily (finiteRowFamily n E) m))
      ((d : ℤ) * m + eventualRegularityConstant (k := K) o hE hne) := by
  rw [monomialIntegerTorRegularitySupport_eq]
  have hm' : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm)
  have hmax := finiteSublatticePowerRegularity_isGreatest (k := K) o hE hne m hm'
  rw [theorem81_regularity o hE hne m hm] at hmax
  simpa only [eventualRegularityConstant, stabilizationPower] using hmax

end Rows
end FourPapers.Sublattice
end

end
end


end
