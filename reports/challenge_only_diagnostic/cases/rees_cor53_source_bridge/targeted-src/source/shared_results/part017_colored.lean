module
public import graph_foundation.part012
public import shared_results.part016

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredInitialPowers -/
section

/-! # The finite initial-ideal criterion for all mixed products

A single actual initial identity for Σ z_c J_c implies every mixed initial
identity. The restricted monomial order is constructed, and coefficient
extraction is proved compatible with leading exponents. No mixed-power
initial hypothesis is added to the final theorem.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open scoped MonomialOrder
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {K : Type u} [Field K]
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Fin r → Finset (FiniteTuple n))
  (M : MonomialOrder (FiniteVariable.{u} (coloredRows (r := r) n)))

def coloredDeformedIdeal : Ideal (MvPolynomial (FiniteVariable.{u} (coloredRows (r := r) n)) K) :=
  Ideal.map (coloredPolynomialEquiv (k := K) n).toRingHom (coloredIdeal J)

lemma coloredDeformedPower_mem (s : ℕ)
    (f : MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) K)) :
    coloredPolynomialEquiv (k := K) n f∈coloredDeformedIdeal J^s ↔ f∈coloredIdeal J^s := by
  rw [coloredDeformedIdeal, ← Ideal.map_pow, RingEquiv.toRingHom_eq_coe,
    Ideal.map_coe (coloredPolynomialEquiv (k := K) n).toRingEquiv]
  simpa only [AlgEquiv.coe_toRingEquiv] using
    (Ideal.apply_mem_of_equiv_iff
      (I := coloredIdeal J ^ s) (f := (coloredPolynomialEquiv (k := K) n).toRingEquiv)
      (x := f))

lemma coloredInitialPower_le (m : ULift.{u} (Fin r)→₀ℕ)
    (hpow : FourPapers.initialIdeal M (coloredDeformedIdeal J^m.degree)=
      finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E)^m.degree) :
    FourPapers.initialIdeal (coloredRestrictedOrder M) (powerProduct J m)≤
      powerProduct (coloredIdeals (k := K) n E) m := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,rfl⟩
  have hmono := monomial_powerProduct_mem_coloredPower J m f hf
  have himage := (coloredDeformedPower_mem J m.degree _).mpr hmono
  have hlead := FourPapers.leadingTerm_mem_initial M himage
  rw [hpow,coloredLeadingTerm_monomial] at hlead
  rw [← coloredIdeal_map_eq_sublattice (k := K) n E, ← Ideal.map_pow,
    RingEquiv.toRingHom_eq_coe,
    Ideal.map_coe (coloredPolynomialEquiv (k := K) n).toRingEquiv] at hlead
  have hmono' := (Ideal.apply_mem_of_equiv_iff
    (I := coloredIdeal (coloredIdeals (k := K) n E) ^ m.degree)
    (f := (coloredPolynomialEquiv (k := K) n).toRingEquiv)
    (x := monomial m ((coloredRestrictedOrder M).leadingTerm f))).mp (by
      simpa only [AlgEquiv.coe_toRingEquiv] using hlead)
  exact (coloredIdeal_power_minimal_monomial_iff (coloredIdeals (k := K) n E)
    m ((coloredRestrictedOrder M).leadingTerm f)).mp hmono'

lemma initial_monomial_witness {V : Type*} (m : MonomialOrder V)
    (L : Ideal (MvPolynomial V K)) (a : V→₀ℕ)
    (ha : monomial a (1:K)∈FourPapers.initialIdeal m L) :
    ∃ f∈L,f≠0 ∧ m.degree f≤a := by
  have h := (monomial_mem_initial_iff_not_standard m L (L : Set _)
    (m.isGroebnerBasis_self L) (fun f _ hf => m.isUnit_leadingCoeff.mpr hf) a).mp ha
  rw [MonomialOrder.mem_standardMonomials_iff] at h
  push_neg at h
  exact h

lemma coloredInitialPower_ge (m : ULift.{u} (Fin r)→₀ℕ)
    (hpow : FourPapers.initialIdeal M (coloredDeformedIdeal J^m.degree)=
      finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E)^m.degree) :
    powerProduct (coloredIdeals (k := K) n E) m≤
      FourPapers.initialIdeal (coloredRestrictedOrder M) (powerProduct J m) := by
  rw [← mixedRowPowerFamily_ideal n E K m]
  apply Ideal.span_le.mpr
  rintro _ ⟨a,ha,rfl⟩
  have hmixed : monomial a (1:K)∈powerProduct (coloredIdeals (k := K) n E) m := by
    rw [← mixedRowPowerFamily_ideal n E K m]
    exact Ideal.subset_span ⟨a,ha,rfl⟩
  have hmono := monomial_powerProduct_mem_coloredPower
    (coloredIdeals (k := K) n E) m (monomial a 1) hmixed
  have hlarge : monomial (coloredExponent m a) (1:K)∈
      FourPapers.initialIdeal M (coloredDeformedIdeal J^m.degree) := by
    rw [hpow,← coloredIdeal_map_eq_sublattice (k := K) n E,← Ideal.map_pow,
      ← coloredPolynomialEquiv_monomial (k := K) n m a]
    exact Ideal.mem_map_of_mem (coloredPolynomialEquiv (k := K) n).toRingHom hmono
  obtain ⟨g,hg,hg0,hga⟩ := initial_monomial_witness M (coloredDeformedIdeal J^m.degree)
    (coloredExponent m a) hlarge
  let f := (coloredPolynomialEquiv (k := K) n).symm g
  let c := colorExponent (M.degree g)
  let b := baseExponent (M.degree g)
  have hf : f∈coloredIdeal J^m.degree := by
    apply (coloredDeformedPower_mem J m.degree f).mp
    simpa only [f,AlgEquiv.apply_symm_apply] using hg
  have hf0 : f≠0 := (coloredPolynomialEquiv (k := K) n).symm.map_ne_zero_iff.mpr hg0
  have hcoeff : (f.coeff c).coeff b≠0 := by
    rw [← coloredPolynomialEquiv_coeff]
    change ((coloredPolynomialEquiv (k := K) n) f).coeff
      (coloredExponent (colorExponent (M.degree g)) (baseExponent (M.degree g)))≠0
    rw [coloredExponent_reconstruct]
    simpa only [f,AlgEquiv.apply_symm_apply,MonomialOrder.leadingCoeff] using
      M.leadingCoeff_ne_zero_iff.mpr hg0
  have hc_le : c≤m := fun z => hga ⟨0,z⟩
  have hc_lower : m.degree≤c.degree := by
    by_contra h
    have hz := coloredIdeal_power_coeff_below J m.degree f hf c (by omega)
    rw [hz,MvPolynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  have hc : c=m := eq_of_le_of_degree_eq hc_le
    (le_antisymm (CommAlg.Polymatroid.degree_mono hc_le) hc_lower)
  have hfm : f.coeff m∈powerProduct J m :=
    coloredIdeal_power_minimal_coeff J m.degree f hf m rfl
  have hfm0 : f.coeff m≠0 := by
    intro hz
    rw [hc,hz,MvPolynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  have hdeg : (coloredRestrictedOrder M).degree (f.coeff m)=b := by
    have he := coloredLeadingCoefficient_degree M f hf0
    simpa only [f,AlgEquiv.apply_symm_apply,← hc,b,c] using he
  have hba : b≤a := fun v => hga ⟨v.1.succ,v.2⟩
  have hlead := FourPapers.leadingTerm_mem_initial (coloredRestrictedOrder M) hfm
  have hleadmono := ((coloredRestrictedOrder M).leadingTerm_mem_iff
    ((FourPapers.initialIdeal (coloredRestrictedOrder M) (powerProduct J m)).restrictScalars K)
      ((coloredRestrictedOrder M).isUnit_leadingCoeff.mpr hfm0)).mp hlead
  rw [hdeg] at hleadmono
  exact Ideal.mem_of_dvd _ (monomial_one_dvd_monomial_one.mpr hba) hleadmono

/-- Taking the exact minimum-color coefficient commutes with this initial
identity, with the original term order restricted to the old variables. -/
theorem coloredInitialPower_eq (m : ULift.{u} (Fin r)→₀ℕ)
    (hpow : FourPapers.initialIdeal M (coloredDeformedIdeal J^m.degree)=
      finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E)^m.degree) :
    FourPapers.initialIdeal (coloredRestrictedOrder M) (powerProduct J m)=
      powerProduct (coloredIdeals (k := K) n E) m :=
  le_antisymm (coloredInitialPower_le J E M m hpow) (coloredInitialPower_ge J E M m hpow)

/-- **Corollary 5.6, ideal identities.** One initial identity forces every
mixed initial identity; no Betti assumption is required for this clause. -/
theorem corollary56_initial (hE : ColoredLatticeClosed n E)
    (hinit : FourPapers.initialIdeal M (coloredDeformedIdeal J)=
      finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E))
    (m : ULift.{u} (Fin r)→₀ℕ) :
    FourPapers.initialIdeal (coloredRestrictedOrder M) (powerProduct J m)=
      powerProduct (coloredIdeals (k := K) n E) m :=
  coloredInitialPower_eq J E M m
    (finite_initialIdeal_power_eq (coloredRows (r := r) n) M (coloredDeformedIdeal J)
      (coloredFamily n E) ((coloredLatticeClosed_iff n E).mp hE) hinit m.degree)

end FourPapers.Sublattice

end
end
end


end
