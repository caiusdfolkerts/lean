module
public import shared_results.part017_colored

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.NestedColoredInitial -/
section

/-! # Nested families: the actual colored initial identity

In a nonzero color degree the coefficient ideal of a colored nested
family is its largest participating ideal. This proves the single
colored initial identity from the individual initial identities. The
power/intersection clause of Corollary 5.7 is a separate theorem.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option synthInstance.maxHeartbeats 1000
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open scoped MonomialOrder
universe u

section Coefficients
variable {C R : Type*} [Fintype C] [LinearOrder C] [CommRing R]
  (J : C → Ideal R) (hJ : Monotone J)

def largestParticipatingColor (a : C →₀ ℕ) (ha : a≠0) : C :=
  a.support.max' (Finsupp.support_nonempty_iff.mpr ha)

lemma largestParticipatingColor_mem (a : C →₀ ℕ) (ha : a≠0) :
    largestParticipatingColor a ha∈a.support :=
  Finset.max'_mem _ _

include hJ in
lemma mixedCoefficientBound_one_nested (a : C →₀ ℕ) (ha : a≠0) :
    mixedCoefficientBound J 1 a=J (largestParticipatingColor a ha) := by
  apply le_antisymm
  · apply iSup_le
    intro b
    obtain ⟨c,hc⟩ := color_degree_one_eq_unit b.val b.property.2
    have hpos : 0<a c := by
      have hh := b.property.1 c
      rw [hc,Finsupp.single_eq_same] at hh
      omega
    rw [hc,powerProduct_single,pow_one]
    exact hJ (Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hpos)))
  · let c := largestParticipatingColor a ha
    have hpos : 0<a c := Nat.pos_of_ne_zero
      (Finsupp.mem_support_iff.mp (largestParticipatingColor_mem a ha))
    have hs : Finsupp.single c 1≤a := by
      intro j
      by_cases hj : c=j
      · subst j; simpa only [Finsupp.single_eq_same] using (Nat.succ_le_of_lt hpos)
      · simp [Finsupp.single_apply,hj]
    have hh : powerProduct J (Finsupp.single c 1)≤mixedCoefficientBound J 1 a :=
      le_iSup_of_le ⟨Finsupp.single c 1,hs,by simp⟩ le_rfl
    simpa only [powerProduct_single,pow_one] using hh

include hJ in
lemma colored_nested_coeff (f : MvPolynomial C R) (hf : f∈coloredIdeal J)
    (a : C →₀ ℕ) (ha : a≠0) : f.coeff a∈J (largestParticipatingColor a ha) := by
  have hh : f.coeff a ∈ mixedCoefficientBound J 1 a :=
    coloredIdeal_le_bound J hf a
  exact Eq.mp
    (congrArg (fun Q : Ideal R => f.coeff a ∈ Q)
      (mixedCoefficientBound_one_nested J hJ a ha)) hh

lemma colored_nested_monomial_mem (a : C →₀ ℕ) (ha : a≠0) (f : R)
    (hf : f∈J (largestParticipatingColor a ha)) : monomial a f∈coloredIdeal J := by
  let c := largestParticipatingColor a ha
  have hpos : 0<a c := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp (largestParticipatingColor_mem a ha))
  have hs : Finsupp.single c 1≤a := by
    intro j
    by_cases hj : c=j
    · subst j; simpa only [Finsupp.single_eq_same] using (Nat.succ_le_of_lt hpos)
    · simp [Finsupp.single_apply,hj]
  have hh := Ideal.mul_mem_left (coloredIdeal J)
    (monomial (a-Finsupp.single c 1) 1) (coloredIdeal_generator J c f hf)
  simpa only [monomial_mul,one_mul,tsub_add_cancel_of_le hs] using hh

include hJ in
theorem colored_nested_coefficient_iff (a : C →₀ ℕ) (ha : a≠0) (f : R) :
    monomial a f∈coloredIdeal J ↔ f∈J (largestParticipatingColor a ha) := by
  constructor
  · intro h
    simpa only [coeff_monomial,if_true] using colored_nested_coeff J hJ _ h a ha
  · exact colored_nested_monomial_mem J a ha f
end Coefficients

variable {d r : ℕ} {n : Fin d → ℕ} {K : Type u} [Field K]
  (J I : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (M : MonomialOrder (FiniteVariable.{u} (coloredRows (r := r) n)))

lemma coloredLeadingTerm_coefficient
    (f : MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) K))
    (hf : f≠0) :
    let a := colorExponent (M.degree (coloredPolynomialEquiv (k := K) n f))
    M.leadingTerm (coloredPolynomialEquiv (k := K) n f)=
      coloredPolynomialEquiv (k := K) n
        (monomial a ((coloredRestrictedOrder M).leadingTerm (f.coeff a))) := by
  dsimp only
  let q := coloredPolynomialEquiv (k := K) n f
  let a := colorExponent (M.degree q)
  let b := baseExponent (M.degree q)
  have hdeg : (coloredRestrictedOrder M).degree (f.coeff a)=b :=
    coloredLeadingCoefficient_degree M f hf
  have hcoeff : (f.coeff a).coeff b=q.coeff (M.degree q) := by
    rw [← coloredPolynomialEquiv_coeff,coloredExponent_reconstruct]
  have hscalar (c : K) : coloredPolynomialEquiv (k := K) n
      (monomial a (monomial b c))=monomial (coloredExponent a b) c := by
    have hh : monomial a (monomial b c)=c •
        (monomial a (monomial b 1) :
          MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) K)) := by
      simp [smul_monomial]
    rw [hh,map_smul,coloredPolynomialEquiv_monomial,smul_monomial]
    simp
  change monomial (M.degree q) (q.coeff (M.degree q))=
    coloredPolynomialEquiv (k := K) n
      (monomial a (monomial ((coloredRestrictedOrder M).degree (f.coeff a))
        ((f.coeff a).coeff ((coloredRestrictedOrder M).degree (f.coeff a)))))
  rw [hdeg,hcoeff,hscalar,coloredExponent_reconstruct]

set_option maxHeartbeats 100000 in
theorem colored_initial_of_nested
    (hJ : Monotone J)
    (hinit : ∀ c,FourPapers.initialIdeal (coloredRestrictedOrder M) (J c)=I c) :
    FourPapers.initialIdeal M (coloredDeformedIdeal J)=coloredDeformedIdeal I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨g,hg,rfl⟩
    by_cases hg0 : g=0
    · subst g; simp
    let f := (coloredPolynomialEquiv (k := K) n).symm g
    let a := colorExponent (M.degree g)
    have hf : f∈coloredIdeal J := by
      have hmem := coloredDeformedPower_mem J 1 f
      simp only [pow_one] at hmem
      apply hmem.mp
      simpa only [SetLike.mem_coe,f,AlgEquiv.apply_symm_apply] using hg
    have hf0 : f≠0 := (coloredPolynomialEquiv (k := K) n).symm.map_ne_zero_iff.mpr hg0
    have hfa : f.coeff a≠0 := by
      intro hh
      have hlc := M.leadingCoeff_ne_zero_iff.mpr hg0
      apply hlc
      have he : (f.coeff a).coeff (baseExponent (M.degree g))=g.coeff (M.degree g) := by
        rw [← coloredPolynomialEquiv_coeff]
        change ((coloredPolynomialEquiv (k := K) n)
          ((coloredPolynomialEquiv (k := K) n).symm g)).coeff
            (coloredExponent (colorExponent (M.degree g)) (baseExponent (M.degree g)))=_
        rw [AlgEquiv.apply_symm_apply,coloredExponent_reconstruct]
      rw [hh, MvPolynomial.coeff_zero] at he
      exact he.symm
    have ha : a≠0 := by
      intro ha
      have hz := coloredIdeal_power_coeff_below J 1 f (by simpa using hf) a
        (by rw [ha]; simp)
      exact hfa hz
    have hc := colored_nested_coeff J hJ f hf a ha
    have hl := FourPapers.leadingTerm_mem_initial (coloredRestrictedOrder M) hc
    rw [hinit] at hl
    have hm := colored_nested_monomial_mem I a ha
      ((coloredRestrictedOrder M).leadingTerm (f.coeff a)) hl
    have himage : coloredPolynomialEquiv (k := K) n
        (monomial a ((coloredRestrictedOrder M).leadingTerm (f.coeff a))) ∈
          coloredDeformedIdeal I :=
      Ideal.mem_map_of_mem (coloredPolynomialEquiv (k := K) n).toRingHom hm
    have he : M.leadingTerm g = coloredPolynomialEquiv (k := K) n
        (monomial a ((coloredRestrictedOrder M).leadingTerm (f.coeff a))) := by
      simpa only [f,a,AlgEquiv.apply_symm_apply] using
        coloredLeadingTerm_coefficient M f hf0
    change M.leadingTerm g ∈ coloredDeformedIdeal I
    rw [he]
    exact himage
  · rw [coloredDeformedIdeal,Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨c,f,hf,rfl⟩
    rw [← hinit c] at hf
    unfold FourPapers.initialIdeal at hf
    change coloredPolynomialEquiv (k := K) n
      (monomial (Finsupp.single c 1) f)∈FourPapers.initialIdeal M (coloredDeformedIdeal J)
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨g,hg,rfl⟩ := hf
        rw [← coloredLeadingTerm_monomial]
        apply FourPapers.leadingTerm_mem_initial M
        exact Ideal.mem_map_of_mem _ (coloredIdeal_generator J c g hg)
    | zero => simp
    | add f g hf hg ihf ihg =>
        simpa only [map_add] using Ideal.add_mem _ ihf ihg
    | smul q f hf ih =>
        have hh := Ideal.mul_mem_left _ (coloredPolynomialEquiv (k := K) n (MvPolynomial.C q)) ih
        simpa only [← map_mul,C_mul_monomial,smul_eq_mul] using hh

/-- The nested-family initial clause of Corollary 5.7, for the restriction
of the specified extended order. The individual initial identities imply
the colored one used by Corollary 5.6. -/
theorem corollary57_initial (E : Fin r → Finset (FiniteTuple n))
    (hE : ColoredLatticeClosed n E) (hJ : Monotone J)
    (hinit : ∀ c,FourPapers.initialIdeal (coloredRestrictedOrder M) (J c)=
      coloredIdeals (k := K) n E c)
    (m : ULift.{u} (Fin r)→₀ℕ) :
    FourPapers.initialIdeal (coloredRestrictedOrder M) (powerProduct J m)=
      powerProduct (coloredIdeals (k := K) n E) m := by
  apply corollary56_initial J E M hE
  rw [colored_initial_of_nested J (coloredIdeals (k := K) n E) M hJ hinit]
  exact coloredIdeal_map_eq_sublattice (k := K) n E

end FourPapers.Sublattice

end
end
end


end
