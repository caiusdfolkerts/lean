module
public import graph_foundation.part012

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesWeightLeading -/
section

/-! # Leading Rees coefficients for a supplied nonnegative weight

The weight need not represent the monomial order on all monomials. It is
enough that every actual monic generator tail has smaller weight. The normal
form theorem then proves the same strictness for every triangular ideal lift.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial

variable {K V : Type*} [CommRing K]

theorem polynomial_mul_coeff_zero_of_weight_bounds (ω : V → ℕ)
    (f g : MvPolynomial V K) (a b : ℕ)
    (hf : ∀ α ∈ f.support, Finsupp.weight ω α < a)
    (hg : ∀ β ∈ g.support, Finsupp.weight ω β ≤ b)
    (γ : V →₀ ℕ) (hγ : a + b ≤ Finsupp.weight ω γ) : (f * g).coeff γ = 0 := by
  by_contra hn
  obtain ⟨α, hα, β, hβ, he⟩ := Finset.mem_add.mp (support_mul f g (mem_support_iff.mpr hn))
  have hlt := add_lt_add_of_lt_of_le (hf α hα) (hg β hβ)
  rw [← map_add, he] at hlt
  exact (not_lt_of_ge hγ) hlt

theorem monomial_weight_bound (ω : V → ℕ) (a : V →₀ ℕ) :
    ∀ α ∈ (monomial a (1 : K)).support, Finsupp.weight ω α ≤ Finsupp.weight ω a := by
  intro α hα
  exact (congrArg (Finsupp.weight ω) (Finset.mem_singleton.mp (support_monomial_subset hα))).le

variable [Nontrivial K]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))
  (ω : V → ℕ)
  (htail : ∀ s g, g ∈ G s → g ≠ 0 → ∀ a ∈ (monomial (m.degree g) 1 - g).support,
    Finsupp.weight ω a < Finsupp.weight ω (m.degree g))

include htail in
theorem idealLift_weight_tail (s : ℕ) (a : NonstandardIndex m (J ^ s))
    (c : V →₀ ℕ) (hc : c ∈ ((hG s).normalForm (hu s) (monomial a.val 1)).support) :
    Finsupp.weight ω c < Finsupp.weight ω a.val :=
  (mem_restrictSupport_iff K).mp
    (groebner_normalForm_strictly_lowers_of_tails m (J ^ s) (G s) (hG s) (hu s)
      ω (htail s) a.val a.property) hc

include htail in
theorem idealLift_product_weight_upper_coeff
    (s t : ℕ) (a : NonstandardIndex m (J ^ s)) (b : NonstandardIndex m (J ^ t))
    (c : V →₀ ℕ) (hc : Finsupp.weight ω (a.val + b.val) ≤ Finsupp.weight ω c) :
    ((idealLift m (J ^ s) (G s) (hG s) (hu s) a).val *
      (idealLift m (J ^ t) (G t) (hG t) (hu t) b).val).coeff c =
      (monomial (a.val + b.val) (1 : K)).coeff c := by
  let r := (hG s).normalForm (hu s) (monomial a.val 1)
  let z := (hG t).normalForm (hu t) (monomial b.val 1)
  have hr : ∀ α ∈ r.support, Finsupp.weight ω α < Finsupp.weight ω a.val :=
    idealLift_weight_tail m J G hG hu ω htail s a
  have hz : ∀ β ∈ z.support, Finsupp.weight ω β < Finsupp.weight ω b.val :=
    idealLift_weight_tail m J G hG hu ω htail t b
  have hrc : (r * monomial b.val 1).coeff c = 0 :=
    polynomial_mul_coeff_zero_of_weight_bounds ω r _ _ _ hr (monomial_weight_bound ω b.val) c
      (by simpa only [map_add] using hc)
  have hzc : (monomial a.val 1 * z).coeff c = 0 := by
    rw [mul_comm]
    apply polynomial_mul_coeff_zero_of_weight_bounds ω z _ _ _ hz (monomial_weight_bound ω a.val) c
    simpa only [map_add, Nat.add_comm] using hc
  have hrz : (r * z).coeff c = 0 :=
    polynomial_mul_coeff_zero_of_weight_bounds ω r z _ _ hr (fun β hβ => (hz β hβ).le) c
      (by simpa only [map_add] using hc)
  change ((monomial a.val 1 - r) * (monomial b.val 1 - z)).coeff c = _
  simp only [sub_mul, mul_sub, coeff_sub, hrc, hzc, hrz, sub_zero,
    monomial_mul_monomial, one_mul]

include htail in
theorem groebnerReesBasis_product_weight_leading
    (a b c : GroebnerReesIndex J m)
    (hc : Finsupp.weight ω (a.2.val + b.2.val) ≤ Finsupp.weight ω c.2.val) :
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
    (initialReesBasis m J I hinit G hG hu).repr
      (initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b) c := by
  rw [groebnerReesBasis_repr, initialReesBasis_repr,
    groebnerReesBasis_apply, groebnerReesBasis_apply]
  change ((AddMonoidAlgebra.single a.1
      (idealLift m (J ^ a.1) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m (J ^ b.1) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val = _
  rw [Subalgebra.coe_mul, initialReesBasis_val, initialReesBasis_val,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with hs
  · rw [monomial_mul_monomial, one_mul]
    exact idealLift_product_weight_upper_coeff m J G hG hu ω htail a.1 b.1 a.2 b.2 c.2.val hc
  · rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesKoszulWeight -/
section

/-! # The actual weighted Rees Koszul filtration

This numerical-weight variant uses proved strict tails. It does not replace
the monomial order by an allegedly equivalent weight order. The weight and
the order have distinct roles, with their required compatibility proved by
the normal-form tail theorem.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice.WeightedRees

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))
  (ω : V → ℕ)
  (htail : ∀ s g, g ∈ G s → g ≠ 0 → ∀ a ∈ (monomial (m.degree g) 1 - g).support,
    Finsupp.weight ω a < Finsupp.weight ω (m.degree g))

def weight (a : IdealReesKoszulIndex m J) : ℕ :=
  Finsupp.weight ω (reesKoszulFineDegree m J a)

theorem product_homogeneous (a b c : IdealReesKoszulIndex m J)
    (hc : (initialReesKoszulBasis m J I hinit G hG hu).repr
      (initialReesKoszulBasis m J I hinit G hG hu a *
        initialReesKoszulBasis m J I hinit G hG hu b) c ≠ 0) :
    weight m J ω c = weight m J ω a + weight m J ω b := by
  have hm := initialReesKoszul_product_homogeneous m J I hinit G hG hu a b c hc
  have he : reesKoszulFineDegree m J c = reesKoszulFineDegree m J a + reesKoszulFineDegree m J b := by
    apply m.toSyn.injective
    simpa only [reesKoszulWeight, map_add] using hm
  simp only [weight, he, map_add]

include htail in
theorem product_leading (a b c : IdealReesKoszulIndex m J)
    (hc : weight m J ω a + weight m J ω b ≤ weight m J ω c) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      (groebnerReesKoszulBasis m J G hG hu a * groebnerReesKoszulBasis m J G hG hu b) c =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      (initialReesKoszulBasis m J I hinit G hG hu a *
        initialReesKoszulBasis m J I hinit G hG hu b) c := by
  simp only [groebnerReesKoszulBasis, initialReesKoszulBasis,
    Module.Basis.tensorProduct_apply', Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hab : Disjoint a.2 b.2
  · rw [faceBasis_mul_of_disjoint _ _ hab, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, map_zsmul_unit, map_zsmul_unit,
      Finsupp.smul_apply, Finsupp.smul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hF : a.2 ∪ b.2 = c.2
    · rw [if_pos hF, one_smul, one_smul]
      congr 1
      apply groebnerReesBasis_product_weight_leading m J I hinit G hG hu ω htail
      have he : weight m J ω a + weight m J ω b =
          Finsupp.weight ω (a.1.2.val + b.1.2.val) + Finsupp.weight ω (faceExponent c.2) := by
        simp only [weight, reesKoszulFineDegree, ← hF,
          faceExponent_union_of_disjoint _ _ hab, map_add]
        omega
      rw [he] at hc
      apply (add_le_add_iff_right (Finsupp.weight ω (faceExponent c.2))).mp
      simpa only [weight, reesKoszulFineDegree, map_add] using hc
    · rw [if_neg hF, zero_smul, zero_smul]
  · rw [faceBasis_mul_of_not_disjoint _ _ hab]
    simp

theorem one_weight (a : IdealReesKoszulIndex m J)
    (ha : (groebnerReesKoszulBasis m J G hG hu).repr 1 a ≠ 0) : weight m J ω a = 0 := by
  have hm := groebnerReesKoszul_one_weight m J G hG hu a ha
  have he : reesKoszulFineDegree m J a = 0 := by
    apply m.toSyn.injective
    simpa only [reesKoszulWeight, map_zero] using hm
  simp only [weight, he, map_zero]

theorem leading_one :
    OrderedBasis.leadingProjection (groebnerReesKoszulBasis m J G hG hu)
      (initialReesKoszulBasis m J I hinit G hG hu) (weight m J ω) 0 1 = 1 := by
  apply (initialReesKoszulBasis m J I hinit G hG hu).repr.injective
  ext a
  rw [OrderedBasis.leadingProjection_repr]
  by_cases ha : weight m J ω a = 0
  · rw [if_pos ha]
    exact reesKoszul_one_coeff_equal m J I hinit G hG hu a
  · rw [if_neg ha]
    symm
    by_contra hne
    apply ha
    apply one_weight m J G hG hu ω a
    rwa [reesKoszul_one_coeff_equal m J I hinit G hG hu a]

def filtration : WellOrderedFiltered.MultiplicativeFiltration K (IdealReesKoszul J) ℕ :=
  OrderedBasis.comparisonFiltration (groebnerReesKoszulBasis m J G hG hu)
    (initialReesKoszulBasis m J I hinit G hG hu) (weight m J ω)
    (product_homogeneous m J I hinit G hG hu ω)
    (product_leading m J I hinit G hG hu ω htail)
    (fun a ha => (one_weight m J G hG hu ω a ha).le)

def associatedAlgebraEquiv :
    (filtration m J I hinit G hG hu ω htail).AssociatedGraded ≃ₐ[K] IdealReesKoszul I :=
  OrderedBasis.associatedAlgebraEquiv (groebnerReesKoszulBasis m J G hG hu)
    (initialReesKoszulBasis m J I hinit G hG hu) (weight m J ω)
    (product_homogeneous m J I hinit G hG hu ω)
    (product_leading m J I hinit G hG hu ω htail)
    (fun a ha => (one_weight m J G hG hu ω a ha).le)
    (leading_one m J I hinit G hG hu ω)

end FourPapers.Sublattice.WeightedRees

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesKoszulDifferential -/
section

/-! # The literal Koszul differential in the original and initial bases -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

def idealReesZeroIndex (a : V →₀ ℕ) : GroebnerReesIndex J m :=
  ⟨0, ⟨a, by
    intro ha
    apply ha (monomial a (1 : K)) (by simp) (by simp)
    simp only [m.degree_monomial, one_ne_zero, ite_false, le_refl]⟩⟩

theorem groebnerReesBasis_zeroIndex (a : V →₀ ℕ) :
    (groebnerReesBasis J m G hG hu (idealReesZeroIndex m J a)).val =
      AddMonoidAlgebra.single 0 (monomial a (1 : K)) := by
  have hn : (hG 0).normalForm (hu 0) (monomial a 1) = 0 :=
    ((hG 0).normalForm_eq_zero_iff (hu 0)).mpr (by simp)
  rw [groebnerReesBasis_apply]
  change AddMonoidAlgebra.single 0 (monomial a 1 - (hG 0).normalForm (hu 0) (monomial a 1)) = _
  rw [hn, sub_zero]

def idealReesBaseVariable (v : V) : coefficientRees J :=
  idealReesSingle J 0 ⟨X v, by simp [idealPowerPiece]⟩

theorem idealReesBaseVariable_basis (v : V) :
    idealReesBaseVariable J v = groebnerReesBasis J m G hG hu
      (idealReesZeroIndex m J (Finsupp.single v 1)) := by
  apply Subtype.ext
  rw [groebnerReesBasis_zeroIndex]
  rfl

theorem idealReesBaseVariable_initialBasis (v : V) :
    idealReesBaseVariable I v = initialReesBasis m J I hinit G hG hu
      (idealReesZeroIndex m J (Finsupp.single v 1)) := by
  apply Subtype.ext
  rw [initialReesBasis_val]
  rfl

/-- The variables are the actual auxiliary-degree-zero polynomial variables
inside the actual Rees algebra. -/
def idealReesKoszulDGA : ParityDifferential K (IdealReesKoszul J) :=
  TensorExteriorKoszul.parityDifferential (idealReesBaseVariable J)

theorem groebnerReesKoszul_d_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) =
      ∑ v : V, (idealReesBaseVariable J v * groebnerReesBasis J m G hG hu a.1) ⊗ₜ[K]
        Simplicial.contraction v (Simplicial.basis a.2) := by
  rw [groebnerReesKoszulBasis, Module.Basis.tensorProduct_apply']
  exact TensorExteriorKoszul.differential_tmul _ _ _

theorem initialReesKoszul_d_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a) =
      ∑ v : V, (idealReesBaseVariable I v * initialReesBasis m J I hinit G hG hu a.1) ⊗ₜ[K]
        Simplicial.contraction v (Simplicial.basis a.2) := by
  rw [initialReesKoszulBasis, Module.Basis.tensorProduct_apply']
  exact TensorExteriorKoszul.differential_tmul _ _ _

theorem initialReesKoszul_d_fine (a b : IdealReesKoszulIndex m J)
    (hb : (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a)) b ≠ 0) :
    reesKoszulFineDegree m J b = reesKoszulFineDegree m J a := by
  rw [initialReesKoszul_d_basis, map_sum, Finsupp.finsetSum_apply] at hb
  obtain ⟨v, hv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [Simplicial.contraction_basis] at hterm
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, map_zsmul_unit, Finsupp.smul_apply,
      idealReesBaseVariable_initialBasis m J I hinit G hG hu v,
      initialReesBasis_mul m J I hinit G hG hu] at hterm
    change _ • ((initialReesBasis m J I hinit G hG hu).tensorProduct Simplicial.basis).repr
      (_ ⊗ₜ[K] Simplicial.basis (a.2.erase v)) b ≠ 0 at hterm
    rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self,
      Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply] at hterm
    have hF : a.2.erase v = b.2 := by
      by_contra h
      simp [h] at hterm
    have hA : initialReesIndexAdd m J I hinit G hG hu
        (idealReesZeroIndex m J (Finsupp.single v 1)) a.1 = b.1 := by
      by_contra h
      simp [h] at hterm
    have hE : b.1.2.val = Finsupp.single v 1 + a.1.2.val := by
      simpa only [initialReesIndexAdd, idealReesZeroIndex] using
        (congrArg (fun z : GroebnerReesIndex J m => z.2.val) hA).symm
    simp only [reesKoszulFineDegree, hE, ← hF]
    rw [← faceExponent_erase_add hvF]
    abel
  · rw [if_neg hvF, TensorProduct.tmul_zero, map_zero, Finsupp.zero_apply] at hterm
    exact (hterm rfl).elim

section OrderedWeight

variable {Γ : Type*} [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (ρ : (V →₀ ℕ) →+ Γ)
  (hcoef : ∀ a b c : GroebnerReesIndex J m, ρ (a.2.val + b.2.val) ≤ ρ c.2.val →
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
    (initialReesBasis m J I hinit G hG hu).repr
      (initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b) c)

include hcoef in
theorem groebnerReesKoszul_d_leading (a b : IdealReesKoszulIndex m J)
    (hb : ρ (reesKoszulFineDegree m J a) ≤ ρ (reesKoszulFineDegree m J b)) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a)) b =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a)) b := by
  rw [groebnerReesKoszul_d_basis, initialReesKoszul_d_basis, map_sum, map_sum,
    Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Simplicial.contraction_basis]
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      map_zsmul_unit, map_zsmul_unit, Finsupp.smul_apply, Finsupp.smul_apply]
    change _ • ((groebnerReesBasis J m G hG hu).tensorProduct Simplicial.basis).repr
        (_ ⊗ₜ[K] Simplicial.basis (a.2.erase v)) b =
      _ • ((initialReesBasis m J I hinit G hG hu).tensorProduct Simplicial.basis).repr
        (_ ⊗ₜ[K] Simplicial.basis (a.2.erase v)) b
    rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hF : a.2.erase v = b.2
    · rw [if_pos hF, one_smul, one_smul,
        idealReesBaseVariable_basis m J G hG hu v,
        idealReesBaseVariable_initialBasis m J I hinit G hG hu v]
      congr 1
      apply hcoef
      have he : ρ (reesKoszulFineDegree m J a) =
          ρ (Finsupp.single v 1 + a.1.2.val) + ρ (faceExponent b.2) := by
        rw [reesKoszulFineDegree, ← hF, ← faceExponent_erase_add hvF]
        simp only [map_add]
        abel
      rw [he] at hb
      apply (add_le_add_iff_right (ρ (faceExponent b.2))).mp
      simpa only [reesKoszulFineDegree, idealReesZeroIndex, map_add] using hb
    · rw [if_neg hF, zero_smul, zero_smul]
  · rw [if_neg hvF]
    simp

end OrderedWeight

theorem groebnerReesKoszul_parity_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).parity (groebnerReesKoszulBasis m J G hG hu a) =
      (-1 : K) ^ a.2.card • groebnerReesKoszulBasis m J G hG hu a := by
  rw [groebnerReesKoszulBasis, Module.Basis.tensorProduct_apply']
  change TensorExteriorKoszul.involute (_ ⊗ₜ[K] Simplicial.basis a.2) = _
  rw [TensorExteriorKoszul.involute_tmul]
  have he : CliffordAlgebra.involute (Simplicial.basis (k := K) a.2) =
      (-1 : K) ^ a.2.card • Simplicial.basis a.2 :=
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun K V) a.2
  rw [he, TensorProduct.tmul_smul]

theorem initialReesKoszul_parity_basis (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA I).parity (initialReesKoszulBasis m J I hinit G hG hu a) =
      (-1 : K) ^ a.2.card • initialReesKoszulBasis m J I hinit G hG hu a := by
  rw [initialReesKoszulBasis, Module.Basis.tensorProduct_apply']
  change TensorExteriorKoszul.involute (_ ⊗ₜ[K] Simplicial.basis a.2) = _
  rw [TensorExteriorKoszul.involute_tmul]
  have he : CliffordAlgebra.involute (Simplicial.basis (k := K) a.2) =
      (-1 : K) ^ a.2.card • Simplicial.basis a.2 :=
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun K V) a.2
  rw [he, TensorProduct.tmul_smul]

theorem reesKoszul_parity_coeff_equal (a b : IdealReesKoszulIndex m J) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).parity (groebnerReesKoszulBasis m J G hG hu a)) b =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).parity (initialReesKoszulBasis m J I hinit G hG hu a)) b := by
  rw [groebnerReesKoszul_parity_basis, initialReesKoszul_parity_basis,
    map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]

theorem initialReesKoszul_parity_support (a b : IdealReesKoszulIndex m J)
    (hb : (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).parity (initialReesKoszulBasis m J I hinit G hG hu a)) b ≠ 0) : b = a := by
  rw [initialReesKoszul_parity_basis, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply] at hb
  by_contra h
  simp [Ne.symm h] at hb

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.WellOrderedFilteredGenerators -/
section

/-! # Lifting the generators from one homogeneous component

The subset of special homology classes used here is defined by actual Rees
representatives whose coefficients lie in the specified submodule. In the Rees
application that submodule is the auxiliary-degree-one Koszul complex.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.WellOrderedFiltered.MultiplicativeFiltration

open Classical
open scoped BigOperators

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (F : MultiplicativeFiltration K A Γ) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def RelativeLiftsCycles (W : Submodule K A) : Prop :=
  ∀ n (x : A), x ∈ W → x ∈ F.level n → D.d x ∈ F.lower n →
    ∃ z, z ∈ W ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.lower n

def specialClasses (W : Submodule K A) : Set (F.associatedDGA D hd hp).Homology :=
  {u | ∃ (p : F.rees) (hcycle : (F.associatedDGA D hd hp).d (F.leadingMap p) = 0),
    (∀ n, p.val.coeff n ∈ W) ∧
      u = (F.associatedDGA D hd hp).classMap ⟨F.leadingMap p, hcycle⟩}

theorem exists_relative_rees_cycle_lift (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W) (p : F.rees)
    (hcycle : (F.associatedDGA D hd hp).d (F.leadingMap p) = 0)
    (hW : ∀ n, p.val.coeff n ∈ W) :
    ∃ q : F.rees, (F.reesDGA D hd hp).d q = 0 ∧ F.leadingMap q = F.leadingMap p ∧
      ∀ n, q.val.coeff n ∈ W := by
  have hdp : ∀ n, D.d (p.val.coeff n) ∈ F.lower n := by
    rw [F.leadingMap_intertwines, F.leadingMap_eq_zero] at hcycle
    exact hcycle
  choose z hzW hzF hzD hzerr using fun n =>
    hlift n (p.val.coeff n) (hW n) (p.property n) (hdp n)
  let r (n : Γ) : F.rees := F.monomial n ⟨z n, hzF n⟩
  have hrd (n : Γ) : (F.reesDGA D hd hp).d (r n) = 0 := by
    dsimp only [r]
    rw [F.reesDGA_d_monomial]
    have hz : (⟨D.d (z n), hd n (z n) (hzF n)⟩ : F.level n) = 0 :=
      Subtype.ext (hzD n)
    rw [hz, map_zero]
  have hrmap (n : Γ) :
      F.leadingMap (r n) = F.leadingMap (F.monomial n ⟨p.val.coeff n, p.property n⟩) := by
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [← map_sub, F.leadingMap_eq_zero]
    intro i
    change (F.monomial n ⟨p.val.coeff n, p.property n⟩).val.coeff i -
      (r n).val.coeff i ∈ F.lower i
    dsimp only [r]
    rw [F.monomial_coeff, F.monomial_coeff]
    split_ifs with hi
    · subst i
      exact hzerr n
    · rw [sub_self]
      exact (F.lower i).zero_mem
  let q : F.rees := ∑ n ∈ p.val.coeff.support, r n
  have hqd : (F.reesDGA D hd hp).d q = 0 := by
    simp only [q, map_sum, hrd, Finset.sum_const_zero]
  have hqmap : F.leadingMap q = F.leadingMap p := by
    dsimp only [q]
    rw [map_sum]
    calc
      (∑ n ∈ p.val.coeff.support, F.leadingMap (r n)) =
          ∑ n ∈ p.val.coeff.support,
            F.leadingMap (F.monomial n ⟨p.val.coeff n, p.property n⟩) :=
        Finset.sum_congr rfl (fun n _ => hrmap n)
      _ = F.leadingMap (∑ n ∈ p.val.coeff.support,
          F.monomial n ⟨p.val.coeff n, p.property n⟩) := (map_sum _ _ _).symm
      _ = F.leadingMap p := congrArg F.leadingMap
        (coefficient_decomposition F.level F.one_mem F.mul_mem p)
  refine ⟨q, hqd, hqmap, ?_⟩
  intro i
  let c : F.rees →ₗ[K] A := (F.level i).subtype.comp
    (coefficientAt F.level F.one_mem F.mul_mem i)
  change c q ∈ W
  dsimp only [q]
  rw [map_sum]
  apply W.sum_mem
  intro n _
  change (r n).val.coeff i ∈ W
  dsimp only [r]
  rw [F.monomial_coeff]
  split_ifs
  · exact hzW n
  · exact W.zero_mem

theorem specialClasses_lift_of_relativeLifts (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W) :
    F.specialClasses D hd hp W ⊆ Set.range (F.homologySpecialization D hd hp) := by
  rintro u ⟨p, hcycle, hW, rfl⟩
  obtain ⟨q, hqd, hqmap, _⟩ := F.exists_relative_rees_cycle_lift D hd hp W hlift p hcycle hW
  refine ⟨(F.reesDGA D hd hp).classMap ⟨q, hqd⟩, ?_⟩
  rw [homologySpecialization, ParityDifferential.homologyMap_classMap]
  apply congrArg (F.associatedDGA D hd hp).classMap
  exact Subtype.ext hqmap

/-- Generation by a specified homogeneous component propagates its actual
leading-cycle lifting property to the entire filtered differential algebra. -/
theorem liftsCycles_of_relative_generators (W : Submodule K A)
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤)
    (hlift : F.RelativeLiftsCycles D W) :
    F.LiftsCycles D :=
  F.liftsCycles_of_generators D hd hp (F.specialClasses D hd hp W) hgen
    (F.specialClasses_lift_of_relativeLifts D hd hp W hlift)

end FourPapers.WellOrderedFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.WellOrderedFilteredSubalgebraLifting -/
section

/-! # Lifting special classes with coefficients in a prescribed cycle algebra

This construction remembers where the lifted coefficients lie. It is needed
for the generation conclusion of the degeneration principle, beyond equality
of dimensions.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.WellOrderedFiltered.MultiplicativeFiltration

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (F : MultiplicativeFiltration K A Γ) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def reesIn (T : Subalgebra K A) : Subalgebra K F.rees :=
  (gradedCoefficientAlgebra (fun _ : Γ => T.toSubmodule) T.one_mem
    (fun _ _ _ hx _ hy => T.mul_mem hx hy)).comap F.rees.val

@[simp] theorem mem_reesIn (T : Subalgebra K A) (p : F.rees) :
    p ∈ F.reesIn T ↔ ∀ n, p.val.coeff n ∈ T := Iff.rfl

theorem reesIn_cycle (T : Subalgebra K A) (hT : T ≤ D.cycles) (p : F.reesIn T) :
    (F.reesDGA D hd hp).d p.val = 0 := by
  apply Subtype.ext
  ext n
  exact hT (p.property n)

def goodCyclesMap (T : Subalgebra K A) (hT : T ≤ D.cycles) :
    F.reesIn T →ₐ[K] (F.reesDGA D hd hp).cycles :=
  (F.reesIn T).val.codRestrict (F.reesDGA D hd hp).cycles
    (F.reesIn_cycle D hd hp T hT)

def goodSpecialMap (T : Subalgebra K A) (hT : T ≤ D.cycles) :
    F.reesIn T →ₐ[K] (F.associatedDGA D hd hp).Homology :=
  (F.homologySpecialization D hd hp).comp
    ((F.reesDGA D hd hp).classMap.comp (F.goodCyclesMap D hd hp T hT))

theorem specialClasses_lift_to_reesIn (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W)
    (T : Subalgebra K A) (hT : T ≤ D.cycles)
    (hselected : ∀ x ∈ W, D.d x = 0 → x ∈ T) :
    F.specialClasses D hd hp W ⊆ Set.range (F.goodSpecialMap D hd hp T hT) := by
  rintro u ⟨p, hcycle, hW, rfl⟩
  obtain ⟨q, hqd, hqmap, hqW⟩ :=
    F.exists_relative_rees_cycle_lift D hd hp W hlift p hcycle hW
  have hqT : q ∈ F.reesIn T := by
    intro n
    apply hselected _ (hqW n)
    exact congrArg (fun p : F.rees => p.val.coeff n) hqd
  refine ⟨⟨q, hqT⟩, ?_⟩
  change (F.associatedDGA D hd hp).classMap _ = (F.associatedDGA D hd hp).classMap _
  apply congrArg (F.associatedDGA D hd hp).classMap
  exact Subtype.ext hqmap

theorem goodSpecialMap_surjective_of_generators (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W)
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤)
    (T : Subalgebra K A) (hT : T ≤ D.cycles)
    (hselected : ∀ x ∈ W, D.d x = 0 → x ∈ T) :
    Function.Surjective (F.goodSpecialMap D hd hp T hT) := by
  have hr : (⊤ : Subalgebra K (F.associatedDGA D hd hp).Homology) ≤
      (F.goodSpecialMap D hd hp T hT).range := by
    rw [← hgen]
    exact Algebra.adjoin_le (F.specialClasses_lift_to_reesIn D hd hp W hlift T hT hselected)
  intro u
  exact hr (show u ∈ (⊤ : Subalgebra K (F.associatedDGA D hd hp).Homology) from trivial)

/-- A surjective special homology map from coefficientwise `T`-valued Rees
cycles approximates every original cycle by a cycle in `T` of the same leading
weight. Boundary correction stays in `T` because every boundary lies in `T`. -/
theorem cycle_approximation_in_subalgebra
    (T : Subalgebra K A) (hT : T ≤ D.cycles)
    (hbound : ∀ a : A, D.d a ∈ T)
    (hsurj : Function.Surjective (F.goodSpecialMap D hd hp T hT))
    (n : Γ) (x : A) (hx : x ∈ F.level n) (hdx : D.d x = 0) :
    ∃ z, z ∈ T ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.lower n := by
  let r : F.rees := F.monomial n ⟨x, hx⟩
  have hr : (F.associatedDGA D hd hp).d (F.leadingMap r) = 0 := by
    rw [F.leadingMap_intertwines, F.leadingMap_eq_zero]
    intro i
    change D.d (r.val.coeff i) ∈ F.lower i
    dsimp only [r]
    rw [F.monomial_coeff]
    split_ifs
    · rw [hdx]
      exact (F.lower i).zero_mem
    · rw [map_zero]
      exact (F.lower i).zero_mem
  obtain ⟨q, hq⟩ := hsurj ((F.associatedDGA D hd hp).classMap ⟨F.leadingMap r, hr⟩)
  change (F.associatedDGA D hd hp).classMap _ =
    (F.associatedDGA D hd hp).classMap ⟨F.leadingMap r, hr⟩ at hq
  obtain ⟨v, hv⟩ := ((F.associatedDGA D hd hp).classMap_eq_iff _ _).mp hq
  obtain ⟨v, rfl⟩ := F.leadingMap_surjective v
  change (F.associatedDGA D hd hp).d (F.leadingMap v) =
    F.leadingMap q.val - F.leadingMap r at hv
  let q' : F.rees := q.val - (F.reesDGA D hd hp).d v
  have hq'd : (F.reesDGA D hd hp).d q' = 0 := by
    dsimp only [q']
    rw [map_sub, F.reesIn_cycle D hd hp T hT q,
      (F.reesDGA D hd hp).square_zero, sub_self]
  have hq'map : F.leadingMap q' = F.leadingMap r := by
    dsimp only [q']
    rw [map_sub, ← F.leadingMap_intertwines, hv]
    abel
  refine ⟨q'.val.coeff n, ?_, q'.property n, ?_, ?_⟩
  · change q.val.val.coeff n - D.d (v.val.coeff n) ∈ T
    exact T.sub_mem (q.property n) (hbound (v.val.coeff n))
  · exact congrArg (fun p : F.rees => p.val.coeff n) hq'd
  · have hz : F.leadingMap (r - q') = 0 := by rw [map_sub, hq'map, sub_self]
    have hh := (F.leadingMap_eq_zero (r - q')).mp hz n
    change r.val.coeff n - q'.val.coeff n ∈ F.lower n at hh
    simpa [r, F.monomial_coeff] using hh

end FourPapers.WellOrderedFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredRees -/
section

/-! # Integer weight filtrations and their actual Rees differential algebras

Integer exponents are allowed. The ambient Laurent coefficient algebra is used
only to hold finitely supported sums; membership in the Rees subalgebra imposes
the original filtration condition coefficient by coefficient.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered

open Classical

variable (K A : Type*) [CommRing K] [Ring A] [Algebra K A]

structure MultiplicativeFiltration where
  level : ℤ → Submodule K A
  mono : Monotone level
  exhaustive : ∀ x : A, ∃ n, x ∈ level n
  separated : ∀ x : A, (∀ n, x ∈ level n) → x = 0
  one_mem : (1 : A) ∈ level 0
  mul_mem : ∀ a b, ∀ x ∈ level a, ∀ y ∈ level b, x * y ∈ level (a + b)

namespace MultiplicativeFiltration

variable {K A} (F : MultiplicativeFiltration K A)

abbrev rees : Subalgebra K (AddMonoidAlgebra A ℤ) :=
  gradedCoefficientAlgebra F.level F.one_mem F.mul_mem

instance (priority := 1200) reesRing : Ring F.rees :=
  Subalgebra.toRing F.rees

instance (priority := 1200) reesAlgebra : Algebra K F.rees :=
  Subalgebra.algebra F.rees

instance (priority := 1200) reesModule : Module K F.rees := Algebra.toModule

def monomial (n : ℤ) : F.level n →ₗ[K] F.rees :=
  coefficientSingle F.level F.one_mem F.mul_mem n

@[simp] theorem monomial_coeff (n i : ℤ) (a : F.level n) :
    (F.monomial n a).val.coeff i = if n = i then a.val else 0 := by
  have hh := coefficientSingle_coeff F.level F.one_mem F.mul_mem n i a
  split_ifs at hh ⊢ <;> exact hh

def strictIdeal : TwoSidedIdeal F.rees :=
  TwoSidedIdeal.mk' {p : F.rees | ∀ n, p.val.coeff n ∈ F.level (n - 1)}
    (by intro n; simp)
    (by
      intro p q hp hq n
      exact (F.level (n - 1)).add_mem (hp n) (hq n))
    (by
      intro p hp n
      exact (F.level (n - 1)).neg_mem (hp n))
    (by
      intro p q hq n
      change (p.val * q.val).coeff n ∈ F.level (n - 1)
      rw [AddMonoidAlgebra.coeff_mul]
      apply Submodule.sum_mem
      intro a _
      apply Submodule.sum_mem
      intro b _
      dsimp only
      split_ifs with hab
      · subst n
        have h := F.mul_mem a (b - 1) _ (p.property a) _ (hq b)
        simpa only [add_sub_assoc] using h
      · exact (F.level (n - 1)).zero_mem)
    (by
      intro p q hp n
      change (p.val * q.val).coeff n ∈ F.level (n - 1)
      rw [AddMonoidAlgebra.coeff_mul]
      apply Submodule.sum_mem
      intro a _
      apply Submodule.sum_mem
      intro b _
      dsimp only
      split_ifs with hab
      · subst n
        have h := F.mul_mem (a - 1) b _ (hp a) _ (q.property b)
        have he : a - 1 + b = a + b - 1 := by omega
        simpa only [he] using h
      · exact (F.level (n - 1)).zero_mem)

@[simp] theorem mem_strictIdeal (p : F.rees) :
    p ∈ F.strictIdeal ↔ ∀ n, p.val.coeff n ∈ F.level (n - 1) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

abbrev AssociatedGraded := F.rees ⧸ F.strictIdeal.asIdeal

instance (priority := 1200) associatedGradedRing : Ring F.AssociatedGraded :=
  Ideal.Quotient.ring F.strictIdeal.asIdeal

instance (priority := 1200) associatedGradedAlgebra : Algebra K F.AssociatedGraded :=
  Ideal.Quotient.algebra K (A := F.rees) (I := F.strictIdeal.asIdeal)

instance (priority := 1200) associatedGradedModule : Module K F.AssociatedGraded :=
  Algebra.toModule

def leadingMap : F.rees →ₐ[K] F.AssociatedGraded :=
  Ideal.Quotient.mkₐ K F.strictIdeal.asIdeal

theorem leadingMap_surjective : Function.Surjective F.leadingMap :=
  Ideal.Quotient.mk_surjective

@[simp] theorem leadingMap_eq_zero (p : F.rees) :
    F.leadingMap p = 0 ↔ ∀ n, p.val.coeff n ∈ F.level (n - 1) := by
  change Ideal.Quotient.mk F.strictIdeal.asIdeal p = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal, F.mem_strictIdeal]

variable (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def reesDGA : ParityDifferential K F.rees :=
  (D.onMonoidAlgebra (Γ := ℤ)).restrict F.rees
    (by
      intro p h n
      exact hd n (p.coeff n) (h n))
    (by
      intro p h n
      exact hp n (p.coeff n) (h n))

@[simp] theorem reesDGA_d_coeff (p : F.rees) (n : ℤ) :
    ((F.reesDGA D hd hp).d p).val.coeff n = D.d (p.val.coeff n) := rfl

@[simp] theorem reesDGA_parity_coeff (p : F.rees) (n : ℤ) :
    ((F.reesDGA D hd hp).parity p).val.coeff n = D.parity (p.val.coeff n) := rfl

theorem reesDGA_d_monomial (n : ℤ) (a : F.level n) :
    (F.reesDGA D hd hp).d (F.monomial n a) =
      F.monomial n ⟨D.d a.val, hd n a.val a.property⟩ := by
  apply Subtype.ext
  ext i
  rw [F.reesDGA_d_coeff, F.monomial_coeff, F.monomial_coeff]
  split_ifs
  · rfl
  · exact map_zero D.d

theorem reesDGA_d_strict (p : F.rees) (h : p ∈ F.strictIdeal) :
    (F.reesDGA D hd hp).d p ∈ F.strictIdeal := by
  rw [F.mem_strictIdeal] at h ⊢
  intro n
  exact hd (n - 1) (p.val.coeff n) (h n)

theorem reesDGA_parity_strict (p : F.rees) (h : p ∈ F.strictIdeal) :
    (F.reesDGA D hd hp).parity p ∈ F.strictIdeal := by
  rw [F.mem_strictIdeal] at h ⊢
  intro n
  exact hp (n - 1) (p.val.coeff n) (h n)

def associatedDGA : ParityDifferential K F.AssociatedGraded :=
  (F.reesDGA D hd hp).quotient F.strictIdeal
    (F.reesDGA_d_strict D hd hp) (F.reesDGA_parity_strict D hd hp)

@[simp] theorem leadingMap_intertwines (p : F.rees) :
    (F.associatedDGA D hd hp).d (F.leadingMap p) =
      F.leadingMap ((F.reesDGA D hd hp).d p) := rfl

def homologySpecialization :
    (F.reesDGA D hd hp).Homology →ₐ[K] (F.associatedDGA D hd hp).Homology :=
  ParityDifferential.homologyMap (K := K) (F.reesDGA D hd hp) (F.associatedDGA D hd hp)
    F.leadingMap (F.leadingMap_intertwines D hd hp)

def LiftsCycles : Prop :=
  ∀ n (x : A), x ∈ F.level n → D.d x ∈ F.level (n - 1) →
    ∃ z, z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.level (n - 1)

/-- Surjectivity on the homology of the actual associated graded algebra
forces actual leading-cycle lifts in the original filtered algebra. -/
theorem liftsCycles_of_homologySpecialization_surjective
    (hH : Function.Surjective (F.homologySpecialization D hd hp)) :
    F.LiftsCycles D := by
  have hlift := ParityDifferential.strictCyclesLift_of_homologyMap_surjective (K := K)
    (F.reesDGA D hd hp) (F.associatedDGA D hd hp) F.leadingMap
    (F.leadingMap_intertwines D hd hp) F.leadingMap_surjective hH
  intro n x hx hdx
  let r := F.monomial n ⟨x, hx⟩
  have hr : (F.associatedDGA D hd hp).d (F.leadingMap r) = 0 := by
    rw [F.leadingMap_intertwines, F.leadingMap_eq_zero]
    intro i
    rw [F.reesDGA_d_coeff, F.monomial_coeff]
    split_ifs with hi
    · subst i
      exact hdx
    · rw [map_zero]
      exact (F.level (i - 1)).zero_mem
  obtain ⟨q, hq, he⟩ := hlift (F.leadingMap r) hr
  refine ⟨q.val.coeff n, q.property n, ?_, ?_⟩
  · have heq := congrArg (fun p : F.rees => p.val.coeff n) hq
    exact heq
  · have hz : F.leadingMap (r - q) = 0 := by rw [map_sub, he, sub_self]
    have hh := (F.leadingMap_eq_zero (r - q)).mp hz n
    change r.val.coeff n - q.val.coeff n ∈ F.level (n - 1) at hh
    simpa [r, F.monomial_coeff] using hh

/-- Algebra generation propagates cycle lifting from any chosen collection of
special homology generators to all filtration degrees. -/
theorem liftsCycles_of_generators
    (G : Set (F.associatedDGA D hd hp).Homology)
    (hgen : Algebra.adjoin K G = ⊤)
    (hlift : G ⊆ Set.range (F.homologySpecialization D hd hp)) :
    F.LiftsCycles D :=
  F.liftsCycles_of_homologySpecialization_surjective D hd hp
    (ParityDifferential.homologyMap_surjective_of_generators (K := K)
      (F.reesDGA D hd hp) (F.associatedDGA D hd hp) F.leadingMap
      (F.leadingMap_intertwines D hd hp) G hgen hlift)

end MultiplicativeFiltration
end FourPapers.IntegerFiltered

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredGenerators -/
section

/-! # Lifting the generators from one homogeneous component

The subset of special homology classes used here is defined by actual Rees
representatives whose coefficients lie in the specified submodule. In the Rees
application that submodule is the auxiliary-degree-one Koszul complex.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical
open scoped BigOperators

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def RelativeLiftsCycles (W : Submodule K A) : Prop :=
  ∀ n (x : A), x ∈ W → x ∈ F.level n → D.d x ∈ F.level (n - 1) →
    ∃ z, z ∈ W ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.level (n - 1)

def specialClasses (W : Submodule K A) : Set (F.associatedDGA D hd hp).Homology :=
  {u | ∃ (p : F.rees) (hcycle : (F.associatedDGA D hd hp).d (F.leadingMap p) = 0),
    (∀ n, p.val.coeff n ∈ W) ∧
      u = (F.associatedDGA D hd hp).classMap ⟨F.leadingMap p, hcycle⟩}

theorem exists_relative_rees_cycle_lift (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W) (p : F.rees)
    (hcycle : (F.associatedDGA D hd hp).d (F.leadingMap p) = 0)
    (hW : ∀ n, p.val.coeff n ∈ W) :
    ∃ q : F.rees, (F.reesDGA D hd hp).d q = 0 ∧ F.leadingMap q = F.leadingMap p ∧
      ∀ n, q.val.coeff n ∈ W := by
  have hdp : ∀ n, D.d (p.val.coeff n) ∈ F.level (n - 1) := by
    rw [F.leadingMap_intertwines, F.leadingMap_eq_zero] at hcycle
    exact hcycle
  choose z hzW hzF hzD hzerr using fun n =>
    hlift n (p.val.coeff n) (hW n) (p.property n) (hdp n)
  let r (n : ℤ) : F.rees := F.monomial n ⟨z n, hzF n⟩
  have hrd (n : ℤ) : (F.reesDGA D hd hp).d (r n) = 0 := by
    dsimp only [r]
    rw [F.reesDGA_d_monomial]
    have hz : (⟨D.d (z n), hd n (z n) (hzF n)⟩ : F.level n) = 0 :=
      Subtype.ext (hzD n)
    rw [hz, map_zero]
  have hrmap (n : ℤ) :
      F.leadingMap (r n) = F.leadingMap (F.monomial n ⟨p.val.coeff n, p.property n⟩) := by
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [← map_sub, F.leadingMap_eq_zero]
    intro i
    change (F.monomial n ⟨p.val.coeff n, p.property n⟩).val.coeff i -
      (r n).val.coeff i ∈ F.level (i - 1)
    dsimp only [r]
    rw [F.monomial_coeff, F.monomial_coeff]
    split_ifs with hi
    · subst i
      exact hzerr n
    · rw [sub_self]
      exact (F.level (i - 1)).zero_mem
  let q : F.rees := ∑ n ∈ p.val.coeff.support, r n
  have hqd : (F.reesDGA D hd hp).d q = 0 := by
    simp only [q, map_sum, hrd, Finset.sum_const_zero]
  have hqmap : F.leadingMap q = F.leadingMap p := by
    dsimp only [q]
    rw [map_sum]
    calc
      (∑ n ∈ p.val.coeff.support, F.leadingMap (r n)) =
          ∑ n ∈ p.val.coeff.support,
            F.leadingMap (F.monomial n ⟨p.val.coeff n, p.property n⟩) :=
        Finset.sum_congr rfl (fun n _ => hrmap n)
      _ = F.leadingMap (∑ n ∈ p.val.coeff.support,
          F.monomial n ⟨p.val.coeff n, p.property n⟩) := (map_sum _ _ _).symm
      _ = F.leadingMap p := congrArg F.leadingMap
        (coefficient_decomposition F.level F.one_mem F.mul_mem p)
  refine ⟨q, hqd, hqmap, ?_⟩
  intro i
  let c : F.rees →ₗ[K] A := (F.level i).subtype.comp
    (coefficientAt F.level F.one_mem F.mul_mem i)
  change c q ∈ W
  dsimp only [q]
  rw [map_sum]
  apply W.sum_mem
  intro n _
  change (r n).val.coeff i ∈ W
  dsimp only [r]
  rw [F.monomial_coeff]
  split_ifs
  · exact hzW n
  · exact W.zero_mem

theorem specialClasses_lift_of_relativeLifts (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W) :
    F.specialClasses D hd hp W ⊆ Set.range (F.homologySpecialization D hd hp) := by
  rintro u ⟨p, hcycle, hW, rfl⟩
  obtain ⟨q, hqd, hqmap, _⟩ := F.exists_relative_rees_cycle_lift D hd hp W hlift p hcycle hW
  refine ⟨(F.reesDGA D hd hp).classMap ⟨q, hqd⟩, ?_⟩
  rw [homologySpecialization, ParityDifferential.homologyMap_classMap]
  apply congrArg (F.associatedDGA D hd hp).classMap
  exact Subtype.ext hqmap

/-- Generation by a specified homogeneous component propagates its actual
leading-cycle lifting property to the entire filtered differential algebra. -/
theorem liftsCycles_of_relative_generators (W : Submodule K A)
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤)
    (hlift : F.RelativeLiftsCycles D W) :
    F.LiftsCycles D :=
  F.liftsCycles_of_generators D hd hp (F.specialClasses D hd hp W) hgen
    (F.specialClasses_lift_of_relativeLifts D hd hp W hlift)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredDecomposition -/
section

/-! # Passing from finite homogeneous components to one auxiliary degree

The direct-sum decomposition is the actual internal grading. A homogeneous
differential commutes with its projections. Lifts in its finite components can
therefore be added to lift an arbitrary element of a homogeneous submodule.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical DirectSum
open scoped BigOperators DirectSum

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A] [DecidableEq Γ]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (P : Γ → Submodule K A) [DirectSum.Decomposition P]

theorem differential_decompose_commutes
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i) (g : Γ) (x : A) :
    D.d (DirectSum.decompose P x g).val = (DirectSum.decompose P (D.d x) g).val := by
  classical
  refine DirectSum.Decomposition.inductionOn P (by simp) ?_ ?_ x
  · intro i x
    by_cases hi : i = g
    · subst g
      rw [DirectSum.decompose_of_mem_same P x.property,
        DirectSum.decompose_of_mem_same P (hD i x.val x.property)]
    · rw [DirectSum.decompose_of_mem_ne P x.property hi,
        DirectSum.decompose_of_mem_ne P (hD i x.val x.property) hi, map_zero]
  · intro x y hx hy
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      hx, hy]

theorem relativeLiftsCycles_of_homogeneous_projection
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i)
    (hlift : F.LiftsCycles D) (i : Γ) :
    F.RelativeLiftsCycles D (P i) := by
  intro n x hxP hxF hdx
  obtain ⟨z, hzF, hzd, hxz⟩ := hlift n x hxF hdx
  refine ⟨(DirectSum.decompose P z i).val,
    (DirectSum.decompose P z i).property, hF n i hzF, ?_, ?_⟩
  · rw [differential_decompose_commutes D P hD, hzd]
    simp
  · have hh := hF (n - 1) i hxz
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      DirectSum.decompose_of_mem_same P hxP] at hh
    exact hh

theorem relativeLiftsCycles_of_components (W : Submodule K A)
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hW : SetLike.IsHomogeneous P W)
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i)
    (hlift : ∀ i, F.RelativeLiftsCycles D (P i ⊓ W)) :
    F.RelativeLiftsCycles D W := by
  classical
  intro n x hxW hxF hdx
  have hcomp (i : Γ) := hlift i n (DirectSum.decompose P x i).val
    ⟨(DirectSum.decompose P x i).property, hW i hxW⟩
    (hF n i hxF) (by
      rw [differential_decompose_commutes D P hD i x]
      exact hF (n - 1) i hdx)
  choose z hzPW hzF hzD hzerr using hcomp
  let s := (DirectSum.decompose P x).support
  refine ⟨∑ i ∈ s, z i, ?_, ?_, ?_, ?_⟩
  · exact W.sum_mem (fun i _ => (hzPW i).2)
  · exact (F.level n).sum_mem (fun i _ => hzF i)
  · simp only [map_sum, hzD, Finset.sum_const_zero]
  · have hxsum : (∑ i ∈ s, (DirectSum.decompose P x i).val) = x :=
      DirectSum.sum_support_decompose P x
    have he : x - ∑ i ∈ s, z i =
        ∑ i ∈ s, ((DirectSum.decompose P x i).val - z i) := by
      rw [Finset.sum_sub_distrib, hxsum]
    rw [he]
    exact (F.level (n - 1)).sum_mem (fun i _ => hzerr i)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredCycleGeneration -/
section

/-! # The algebra generated by selected cycles and all boundaries

Adjoining the actual boundaries does not enlarge the generated homology algebra.
Keeping this auxiliary algebra inside the original differential algebra makes
homogeneous projections and finite filtration induction literal constructions.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical DirectSum

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A]

theorem adjoin_homogeneous [AddMonoid Γ] [DecidableEq Γ]
    (P : Γ → Submodule K A) [GradedAlgebra P] (S : Set A)
    (hS : ∀ i x, x ∈ S → (DirectSum.decompose P x i).val ∈ S) :
    SetLike.IsHomogeneous P (Algebra.adjoin K S) := by
  change SetLike.IsHomogeneous P
    (Subsemiring.closure (Set.range (algebraMap K A) ∪ S))
  apply _root_.IsHomogeneous.subsemiringClosure
  intro i x hx
  rcases hx with ⟨r, rfl⟩ | hx
  · by_cases hi : i = 0
    · subst i
      rw [DirectSum.decompose_of_mem_same P (SetLike.algebraMap_mem_graded P r)]
      exact Or.inl ⟨r, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne P (SetLike.algebraMap_mem_graded P r) (Ne.symm hi)]
      exact Or.inl ⟨0, map_zero _⟩
  · exact Or.inr (hS i x hx)

variable (D : ParityDifferential K A) (W : Submodule K A)

def cycleGeneratingSet : Set A := {x | x ∈ W ∧ D.d x = 0} ∪ Set.range D.d

def cycleGeneratedAlgebra : Subalgebra K A := Algebra.adjoin K (cycleGeneratingSet D W)

theorem cycleGeneratedAlgebra_le_cycles : cycleGeneratedAlgebra D W ≤ D.cycles := by
  apply Algebra.adjoin_le
  rintro x (⟨_, hx⟩ | ⟨y, rfl⟩)
  · exact hx
  · exact D.square_zero y

theorem boundary_mem_cycleGeneratedAlgebra (x : A) :
    D.d x ∈ cycleGeneratedAlgebra D W :=
  Algebra.subset_adjoin (Or.inr ⟨x, rfl⟩)

theorem selected_cycle_mem_cycleGeneratedAlgebra {x : A} (hx : x ∈ W) (hdx : D.d x = 0) :
    x ∈ cycleGeneratedAlgebra D W :=
  Algebra.subset_adjoin (Or.inl ⟨hx, hdx⟩)

theorem cycleGeneratedAlgebra_homogeneous [AddMonoid Γ] [DecidableEq Γ]
    (P : Γ → Submodule K A) [GradedAlgebra P]
    (hW : SetLike.IsHomogeneous P W)
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i) :
    SetLike.IsHomogeneous P (cycleGeneratedAlgebra D W) := by
  apply adjoin_homogeneous P
  intro i x hx
  rcases hx with ⟨hxW, hdx⟩ | ⟨y, rfl⟩
  · refine Or.inl ⟨hW i hxW, ?_⟩
    rw [differential_decompose_commutes D P hD, hdx]
    simp
  · exact Or.inr ⟨(DirectSum.decompose P y i).val,
      differential_decompose_commutes D P hD i y⟩

def selectedHomologyClasses : Set D.Homology :=
  {u | ∃ x : D.cycles, x.val ∈ W ∧ D.classMap x = u}

theorem classMap_mem_adjoin_of_mem_cycleGeneratedAlgebra (x : D.cycles)
    (hx : x.val ∈ cycleGeneratedAlgebra D W) :
    D.classMap x ∈ Algebra.adjoin K (selectedHomologyClasses D W) := by
  let L := Algebra.adjoin K (selectedHomologyClasses D W)
  have h : ∀ (a : A) (ha : a ∈ cycleGeneratedAlgebra D W),
      ∀ hc : D.d a = 0, D.classMap ⟨a, hc⟩ ∈ L := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
        intro hc
        rcases ha with ⟨haW, _⟩ | ⟨b, rfl⟩
        · exact Algebra.subset_adjoin ⟨⟨a, hc⟩, haW, rfl⟩
        · have hz : D.classMap ⟨D.d b, hc⟩ = 0 :=
            (D.classMap_eq_zero _).mpr ⟨b, rfl⟩
          rw [hz]
          exact L.zero_mem
    | algebraMap r =>
        intro hc
        change D.classMap (algebraMap K D.cycles r) ∈ L
        rw [AlgHom.commutes]
        exact L.algebraMap_mem r
    | add a b ha hb iha ihb =>
        intro hc
        have hca := cycleGeneratedAlgebra_le_cycles D W ha
        have hcb := cycleGeneratedAlgebra_le_cycles D W hb
        change D.classMap ((⟨a, hca⟩ : D.cycles) + ⟨b, hcb⟩) ∈ L
        rw [map_add]
        exact L.add_mem (iha hca) (ihb hcb)
    | mul a b ha hb iha ihb =>
        intro hc
        have hca := cycleGeneratedAlgebra_le_cycles D W ha
        have hcb := cycleGeneratedAlgebra_le_cycles D W hb
        change D.classMap ((⟨a, hca⟩ : D.cycles) * ⟨b, hcb⟩) ∈ L
        rw [map_mul]
        exact L.mul_mem (iha hca) (ihb hcb)
  exact h x.val hx x.property

theorem homology_generated_of_cycles_le_cycleGeneratedAlgebra
    (h : D.cycles ≤ cycleGeneratedAlgebra D W) :
    Algebra.adjoin K (selectedHomologyClasses D W) = ⊤ := by
  apply top_unique
  intro u _
  obtain ⟨x, rfl⟩ := D.classMap_surjective u
  exact classMap_mem_adjoin_of_mem_cycleGeneratedAlgebra D W x (h x.property)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.WellOrderedFilteredGeneration -/
section

/-! # Multiplicative generation for a well-ordered filtration

Leading-term correction terminates by well-founded induction in the original
monomial order. No global representation of that order by an integer weight
is needed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.WellOrderedFiltered.MultiplicativeFiltration

open Classical
open FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [WellFoundedLT Γ]
  (F : MultiplicativeFiltration K A Γ) (D : ParityDifferential K A)

theorem cycles_le_of_approximation (T : Subalgebra K A)
    (happrox : ∀ n x, x ∈ F.level n → D.d x = 0 →
      ∃ z, z ∈ T ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.lower n) :
    D.cycles ≤ T := by
  have hstep : ∀ (n : Γ) (x : A), x ∈ F.level n → D.d x = 0 → x ∈ T := by
    intro n
    induction n using WellFoundedLT.induction with
    | ind n ih =>
      intro x hx hdx
      obtain ⟨z, hzT, _, hdz, herr⟩ := happrox n x hx hdx
      have heT : x - z ∈ T := by
        rcases herr with he | ⟨m, hmn, hem⟩
        · rw [he]; exact T.zero_mem
        · exact ih m hmn (x - z) hem (by rw [map_sub, hdx, hdz, sub_self])
      simpa only [sub_add_cancel] using T.add_mem heT hzT
  intro x hx
  obtain ⟨n, hn⟩ := F.exhaustive x
  exact hstep n x hn hx

variable
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

theorem homology_generated_of_relative_generators
    (W : Submodule K A) (hlift : F.RelativeLiftsCycles D W)
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤) :
    Algebra.adjoin K (selectedHomologyClasses D W) = ⊤ := by
  let T := cycleGeneratedAlgebra D W
  have hTc : T ≤ D.cycles := cycleGeneratedAlgebra_le_cycles D W
  have hsurj := F.goodSpecialMap_surjective_of_generators D hd hp W hlift hgen T hTc
    (fun x hx hdx => selected_cycle_mem_cycleGeneratedAlgebra D W hx hdx)
  have happrox := F.cycle_approximation_in_subalgebra D hd hp T hTc
    (boundary_mem_cycleGeneratedAlgebra D W) hsurj
  apply homology_generated_of_cycles_le_cycleGeneratedAlgebra D W
  exact F.cycles_le_of_approximation D T happrox

end FourPapers.WellOrderedFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedBasisGeneration -/
section

/-! # Propagation from an actual selected basis component

The initial homology generation hypothesis concerns the actual initial
algebra. The comparison of selected homology classes with classes in the
associated algebra is proved here by an explicit coefficientwise Rees lift.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.OrderedBasis

open Classical
open FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A B I Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [Ring B] [Algebra K B]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (b : Module.Basis I K A) (c : Module.Basis I K B) (w : I → Γ)
  (hcprod : ∀ i j k, c.repr (c i * c j) k ≠ 0 → w k = w i + w j)
  (hlead : ∀ i j k, w i + w j ≤ w k → b.repr (b i * b j) k = c.repr (c i * c j) k)
  (h1 : ∀ i, b.repr (1 : A) i ≠ 0 → w i ≤ 0)
  (hone : leadingProjection b c w 0 1 = 1)

local notation "F" => comparisonFiltration b c w hcprod hlead h1

def componentLift : B →ₗ[K] (F).rees :=
  c.constr K (fun i => (F).monomial (w i) ⟨b i, basis_mem_level b w i⟩)

@[simp] theorem componentLift_basis (i : I) :
    componentLift b c w hcprod hlead h1 (c i) =
      (F).monomial (w i) ⟨b i, basis_mem_level b w i⟩ :=
  c.constr_basis K _ i

theorem specialization_componentLift (y : B) :
    specialization b c w hcprod hlead h1 hone
      (componentLift b c w hcprod hlead h1 y) = y := by
  have he : (specialization b c w hcprod hlead h1 hone).toLinearMap.comp
      (componentLift b c w hcprod hlead h1) = LinearMap.id := by
    apply c.ext
    intro i
    change specialization b c w hcprod hlead h1 hone
      (componentLift b c w hcprod hlead h1 (c i)) = c i
    rw [componentLift_basis]
    exact (specialization_monomial b c w hcprod hlead h1 hone (w i)
      ⟨b i, basis_mem_level b w i⟩).trans (by
        rw [leadingProjection_basis, if_pos rfl])
  exact LinearMap.congr_fun he y

theorem componentLift_component (S : Set I) (y : B)
    (hy : y ∈ Submodule.span K (c '' S)) (n : Γ) :
    (componentLift b c w hcprod hlead h1 y).val.coeff n ∈ Submodule.span K (b '' S) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [componentLift_basis, (F).monomial_coeff]
      split_ifs
      · exact Submodule.subset_span ⟨i, hi, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero, ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      (Submodule.span K (b '' S)).zero_mem
  | add y z hy hz ihy ihz =>
      simpa only [map_add, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
        (Submodule.span K (b '' S)).add_mem ihy ihz
  | smul r y hy ih =>
      simpa only [map_smul, Subalgebra.coe_smul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply] using
        (Submodule.span K (b '' S)).smul_mem r ih

variable (D : ParityDifferential K A) (E : ParityDifferential K B)
  (hdhom : ∀ i j, c.repr (E.d (c i)) j ≠ 0 → w j = w i)
  (hdlead : ∀ i j, w i ≤ w j → b.repr (D.d (b i)) j = c.repr (E.d (c i)) j)
  (hphom : ∀ i j, c.repr (E.parity (c i)) j ≠ 0 → w j = w i)
  (hplead : ∀ i j, w i ≤ w j → b.repr (D.parity (b i)) j = c.repr (E.parity (c i)) j)

local notation "hd" => differential_preserves b c w hcprod hlead h1 D E hdhom hdlead
local notation "hp" => parity_preserves b c w hcprod hlead h1 D E hphom hplead
local notation "eA" => associatedAlgebraEquiv b c w hcprod hlead h1 hone
local notation "eH" => associatedHomologyEquiv b c w hcprod hlead h1 hone D E hdhom hdlead hphom hplead

include hone hdhom hdlead hphom hplead

theorem selectedClass_preimage (S : Set I) (u : E.Homology)
    (hu : u ∈ selectedHomologyClasses E (Submodule.span K (c '' S))) :
    ∃ v ∈ (F).specialClasses D hd hp (Submodule.span K (b '' S)), eH v = u := by
  obtain ⟨y, hyS, rfl⟩ := hu
  let p := componentLift b c w hcprod hlead h1 y.val
  have he : eA ((F).leadingMap p) = y.val := by
    rw [associatedAlgebraEquiv_leading]
    exact specialization_componentLift b c w hcprod hlead h1 hone y.val
  have hcycle : ((F).associatedDGA D hd hp).d ((F).leadingMap p) = 0 := by
    apply (eA).injective
    rw [associatedAlgebraEquiv_d b c w hcprod hlead h1 hone D E
      hdhom hdlead hphom hplead ((F).leadingMap p), he, map_zero]
    exact y.property
  let v := ((F).associatedDGA D hd hp).classMap ⟨(F).leadingMap p, hcycle⟩
  refine ⟨v, ⟨p, hcycle, ?_, rfl⟩, ?_⟩
  · exact fun n => componentLift_component b c w hcprod hlead h1 S y.val hyS n
  · change ParityDifferential.homologyEquiv ((F).associatedDGA D hd hp) E eA
      (associatedAlgebraEquiv_d b c w hcprod hlead h1 hone D E
        hdhom hdlead hphom hplead)
      (((F).associatedDGA D hd hp).classMap ⟨(F).leadingMap p, hcycle⟩) = E.classMap y
    rw [ParityDifferential.homologyEquiv_classMap]
    apply congrArg E.classMap
    exact Subtype.ext he

theorem specialClasses_generated (S : Set I)
    (hgen : Algebra.adjoin K (selectedHomologyClasses E (Submodule.span K (c '' S))) = ⊤) :
    Algebra.adjoin K ((F).specialClasses D hd hp (Submodule.span K (b '' S))) = ⊤ := by
  let L := Algebra.adjoin K ((F).specialClasses D hd hp (Submodule.span K (b '' S)))
  have hmap : (⊤ : Subalgebra K E.Homology) ≤ L.map (eH).toAlgHom := by
    rw [← hgen]
    apply Algebra.adjoin_le
    intro u hu
    obtain ⟨v, hv, he⟩ := selectedClass_preimage b c w hcprod hlead h1 hone D E
      hdhom hdlead hphom hplead S u hu
    exact ⟨v, Algebra.subset_adjoin hv, he⟩
  apply top_unique
  intro x hx
  obtain ⟨y, hy, he⟩ := hmap (show eH x ∈ (⊤ : Subalgebra K E.Homology) from trivial)
  exact ((eH).injective he : y = x) ▸ hy

/-- Ring-valued propagation: actual first-component cycle lifting and
actual initial homology generation imply cycle lifting in every component. -/
theorem liftsCycles_of_selected_generators (S : Set I)
    (hgen : Algebra.adjoin K (selectedHomologyClasses E (Submodule.span K (c '' S))) = ⊤)
    (hlift : (F).RelativeLiftsCycles D (Submodule.span K (b '' S))) : (F).LiftsCycles D :=
  (F).liftsCycles_of_relative_generators D hd hp (Submodule.span K (b '' S))
    (specialClasses_generated b c w hcprod hlead h1 hone D E hdhom hdlead hphom hplead S hgen) hlift

theorem homology_generated_of_selected_generators [WellFoundedLT Γ] (S : Set I)
    (hgen : Algebra.adjoin K (selectedHomologyClasses E (Submodule.span K (c '' S))) = ⊤)
    (hlift : (F).RelativeLiftsCycles D (Submodule.span K (b '' S))) :
    Algebra.adjoin K (selectedHomologyClasses D (Submodule.span K (b '' S))) = ⊤ :=
  (F).homology_generated_of_relative_generators D hd hp (Submodule.span K (b '' S)) hlift
    (specialClasses_generated b c w hcprod hlead h1 hone D E hdhom hdlead hphom hplead S hgen)

end FourPapers.OrderedBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesKoszulComparison -/
section

/-! # The constructed Rees Koszul comparison over a coefficient ring

This assembles the actual weighted algebras, their actual Koszul
differentials, and the explicit associated homology equivalence. Generation
and cycle lifting refer to the literal auxiliary-degree-one submodule.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice.WeightedRees

open Classical MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))
  (ω : V → ℕ)
  (htail : ∀ s g, g ∈ G s → g ≠ 0 → ∀ a ∈ (monomial (m.degree g) 1 - g).support,
    Finsupp.weight ω a < Finsupp.weight ω (m.degree g))

local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "c" => initialReesKoszulBasis m J I hinit G hG hu
local notation "w" => weight m J ω
local notation "F" => filtration m J I hinit G hG hu ω htail
local notation "hprod" => product_homogeneous m J I hinit G hG hu ω
local notation "hlead" => product_leading m J I hinit G hG hu ω htail
local notation "h1" => (fun a ha => le_of_eq (one_weight m J G hG hu ω a ha))
local notation "hone" => leading_one m J I hinit G hG hu ω

theorem differential_homogeneous (a z : IdealReesKoszulIndex m J)
    (hz : (c).repr ((idealReesKoszulDGA I).d (c a)) z ≠ 0) : w z = w a :=
  congrArg (Finsupp.weight ω) (initialReesKoszul_d_fine m J I hinit G hG hu a z hz)

include htail in
theorem differential_leading (a z : IdealReesKoszulIndex m J) (hz : w a ≤ w z) :
    (b).repr ((idealReesKoszulDGA J).d (b a)) z = (c).repr ((idealReesKoszulDGA I).d (c a)) z :=
  groebnerReesKoszul_d_leading m J I hinit G hG hu (Finsupp.weight ω)
    (groebnerReesBasis_product_weight_leading m J I hinit G hG hu ω htail) a z hz

theorem parity_homogeneous (a z : IdealReesKoszulIndex m J)
    (hz : (c).repr ((idealReesKoszulDGA I).parity (c a)) z ≠ 0) : w z = w a :=
  congrArg w (initialReesKoszul_parity_support m J I hinit G hG hu a z hz)

theorem parity_leading (a z : IdealReesKoszulIndex m J) (_ : w a ≤ w z) :
    (b).repr ((idealReesKoszulDGA J).parity (b a)) z = (c).repr ((idealReesKoszulDGA I).parity (c a)) z :=
  reesKoszul_parity_coeff_equal m J I hinit G hG hu a z

def differential_preserves : ∀ n x, x ∈ (F).level n → (idealReesKoszulDGA J).d x ∈ (F).level n :=
  OrderedBasis.differential_preserves b c w hprod hlead h1 (idealReesKoszulDGA J)
    (idealReesKoszulDGA I) (differential_homogeneous m J I hinit G hG hu ω)
    (differential_leading m J I hinit G hG hu ω htail)

def parity_preserves : ∀ n x, x ∈ (F).level n → (idealReesKoszulDGA J).parity x ∈ (F).level n :=
  OrderedBasis.parity_preserves b c w hprod hlead h1 (idealReesKoszulDGA J)
    (idealReesKoszulDGA I) (parity_homogeneous m J I hinit G hG hu ω)
    (parity_leading m J I hinit G hG hu ω)

local notation "hd" => differential_preserves m J I hinit G hG hu ω htail
local notation "hp" => parity_preserves m J I hinit G hG hu ω htail

-- The comparison is already proved abstractly.  Keep the concrete basis and
-- differential constructors opaque while instantiating that theorem.
attribute [local irreducible] groebnerReesKoszulBasis initialReesKoszulBasis
  idealReesKoszulDGA

def auxiliaryPiece (s : ℕ) : Submodule K (IdealReesKoszul J) :=
  Submodule.span K (b '' {a : IdealReesKoszulIndex m J | a.1.1 = s})

def initialAuxiliaryPiece (s : ℕ) : Submodule K (IdealReesKoszul I) :=
  Submodule.span K (c '' {a : IdealReesKoszulIndex m J | a.1.1 = s})

set_option backward.isDefEq.respectTransparency true in
/-- All leading cycles lift over the original coefficient ring. The
hypotheses are actual initial Koszul homology generation and actual
first-auxiliary-degree cycle lifting; no freeness or dimension is assumed. -/
theorem all_cycle_lifts
    (hgen : Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (initialAuxiliaryPiece m J I hinit G hG hu 1)) = ⊤)
    (hlift : (F).RelativeLiftsCycles (idealReesKoszulDGA J) (auxiliaryPiece m J G hG hu 1)) :
    (F).LiftsCycles (idealReesKoszulDGA J) :=
  OrderedBasis.liftsCycles_of_selected_generators (K := K) (A := IdealReesKoszul J)
    (B := IdealReesKoszul I) (I := IdealReesKoszulIndex m J) (Γ := ℕ)
    b c w hprod hlead h1 hone
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (differential_homogeneous m J I hinit G hG hu ω)
    (differential_leading m J I hinit G hG hu ω htail)
    (parity_homogeneous m J I hinit G hG hu ω)
    (parity_leading m J I hinit G hG hu ω) {a | a.1.1 = 1} hgen hlift

set_option backward.isDefEq.respectTransparency true in
theorem homology_generated_in_degree_one
    (hgen : Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (initialAuxiliaryPiece m J I hinit G hG hu 1)) = ⊤)
    (hlift : (F).RelativeLiftsCycles (idealReesKoszulDGA J) (auxiliaryPiece m J G hG hu 1)) :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA J)
      (auxiliaryPiece m J G hG hu 1)) = ⊤ :=
  OrderedBasis.homology_generated_of_selected_generators (K := K) (A := IdealReesKoszul J)
    (B := IdealReesKoszul I) (I := IdealReesKoszulIndex m J) (Γ := ℕ)
    b c w hprod hlead h1 hone
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (differential_homogeneous m J I hinit G hG hu ω)
    (differential_leading m J I hinit G hG hu ω htail)
    (parity_homogeneous m J I hinit G hG hu ω)
    (parity_leading m J I hinit G hG hu ω) {a | a.1.1 = 1} hgen hlift

end FourPapers.Sublattice.WeightedRees

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesAuxiliaryPieces -/
section

/-! # Literal powers inside the actual Rees Koszul algebra -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg MvPolynomial
open scoped TensorProduct

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev IdealPowerKoszul (s : ℕ) := idealPowerPiece J s ⊗[K] Simplicial.Ambient V K

def idealPowerKoszulBasis (s : ℕ) :
    Module.Basis (NonstandardIndex m (J ^ s) × Finset V) K (IdealPowerKoszul J s) :=
  (groebnerPowerBasis J m G hG hu s).tensorProduct Simplicial.basis

def powerKoszulInclusion (s : ℕ) : IdealPowerKoszul J s →ₗ[K] IdealReesKoszul J :=
  TensorProduct.map (idealReesSingle J s) (LinearMap.id : Simplicial.Ambient V K →ₗ[K] _)

def powerKoszulProjection (s : ℕ) : IdealReesKoszul J →ₗ[K] IdealPowerKoszul J s :=
  TensorProduct.map
    (coefficientAt (idealPowerPiece J) (idealPowerPiece_one J) (idealPowerPiece_mul J) s)
    (LinearMap.id : Simplicial.Ambient V K →ₗ[K] _)

theorem powerKoszulProjection_inclusion (s : ℕ) (x : IdealPowerKoszul J s) :
    powerKoszulProjection J s (powerKoszulInclusion J s x) = x := by
  have he : (powerKoszulProjection J s).comp (powerKoszulInclusion J s) = LinearMap.id := by
    apply TensorProduct.ext'
    intro a z
    change powerKoszulProjection J s (powerKoszulInclusion J s (a ⊗ₜ[K] z)) = a ⊗ₜ[K] z
    simp only [powerKoszulProjection, powerKoszulInclusion, TensorProduct.map_tmul,
      LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    change (AddMonoidAlgebra.single s a.val).coeff s = a.val
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  exact LinearMap.congr_fun he x

theorem powerKoszulInclusion_injective (s : ℕ) : Function.Injective (powerKoszulInclusion J s) := by
  intro x y h
  have he := congrArg (powerKoszulProjection J s) h
  simpa only [powerKoszulProjection_inclusion] using he

theorem powerKoszulInclusion_basis (s : ℕ)
    (a : NonstandardIndex m (J ^ s) × Finset V) :
    powerKoszulInclusion J s (idealPowerKoszulBasis m J G hG hu s a) =
      groebnerReesKoszulBasis m J G hG hu (⟨s, a.1⟩, a.2) := by
  simp only [idealPowerKoszulBasis, groebnerReesKoszulBasis,
    Module.Basis.tensorProduct_apply', powerKoszulInclusion,
    TensorProduct.map_tmul, LinearMap.id_apply, groebnerPowerBasis_apply,
    groebnerReesBasis_apply]
  rfl

/-- The selected auxiliary component is exactly the image of the tensor
Koszul module of the literal ideal power. -/
theorem auxiliaryPiece_eq_range (s : ℕ) :
    WeightedRees.auxiliaryPiece m J G hG hu s = LinearMap.range (powerKoszulInclusion J s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨⟨t, a⟩, F⟩, ht, rfl⟩
    change t = s at ht
    subst t
    exact ⟨idealPowerKoszulBasis m J G hG hu s (a, F), powerKoszulInclusion_basis m J G hG hu s (a, F)⟩
  · rintro x ⟨y, rfl⟩
    have hy := (idealPowerKoszulBasis m J G hG hu s).mem_span y
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [powerKoszulInclusion_basis]
        exact Submodule.subset_span ⟨(⟨s, a.1⟩, a.2), rfl, rfl⟩
    | zero => simpa only [map_zero] using (WeightedRees.auxiliaryPiece m J G hG hu s).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using
        (WeightedRees.auxiliaryPiece m J G hG hu s).add_mem ihx ihy
    | smul r x hx ih => simpa only [map_smul] using
        (WeightedRees.auxiliaryPiece m J G hG hu s).smul_mem r ih

def idealPowerKoszulDifferential (s : ℕ) : Module.End K (IdealPowerKoszul J s) :=
  TensorExteriorKoszul.differential (K := K) (R := MvPolynomial V K)
    (M := idealPowerPiece J s) (MvPolynomial.X : V → MvPolynomial V K)

theorem baseVariable_mul_single (s : ℕ) (v : V) (a : idealPowerPiece J s) :
    idealReesBaseVariable J v * idealReesSingle J s a =
      idealReesSingle J s ((MvPolynomial.X v : MvPolynomial V K) • a) := by
  apply Subtype.ext
  change (AddMonoidAlgebra.single 0 (MvPolynomial.X v : MvPolynomial V K) :
      AddMonoidAlgebra (MvPolynomial V K) ℕ) * AddMonoidAlgebra.single s a.val =
    AddMonoidAlgebra.single s (MvPolynomial.X v * a.val)
  rw [AddMonoidAlgebra.single_mul_single, zero_add]

theorem powerKoszulInclusion_d (s : ℕ) (x : IdealPowerKoszul J s) :
    (idealReesKoszulDGA J).d (powerKoszulInclusion J s x) =
      powerKoszulInclusion J s (idealPowerKoszulDifferential J s x) := by
  have he : (idealReesKoszulDGA J).d.comp (powerKoszulInclusion J s) =
      (powerKoszulInclusion J s).comp (idealPowerKoszulDifferential J s) := by
    apply TensorProduct.ext'
    intro a z
    change (idealReesKoszulDGA J).d (powerKoszulInclusion J s (a ⊗ₜ[K] z)) =
      powerKoszulInclusion J s (idealPowerKoszulDifferential J s (a ⊗ₜ[K] z))
    rw [powerKoszulInclusion, TensorProduct.map_tmul, LinearMap.id_apply]
    change TensorExteriorKoszul.differential (idealReesBaseVariable J)
        (idealReesSingle J s a ⊗ₜ[K] z) = _
    rw [TensorExteriorKoszul.differential_tmul]
    change _ = powerKoszulInclusion J s
      (TensorExteriorKoszul.differential (MvPolynomial.X : V → MvPolynomial V K) (a ⊗ₜ[K] z))
    rw [TensorExteriorKoszul.differential_tmul, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    change (idealReesBaseVariable J v * idealReesSingle J s a) ⊗ₜ[K] _ =
      powerKoszulInclusion J s ((MvPolynomial.X v • a) ⊗ₜ[K] _)
    rw [powerKoszulInclusion, TensorProduct.map_tmul, LinearMap.id_apply, baseVariable_mul_single]
  exact LinearMap.congr_fun he x

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedCycleLifting -/
section

/-! # Reassembling genuine homogeneous cycle lifts

The decomposition used here is the finite basis-coordinate decomposition of
an actual vector.  Neither its cycles nor its boundaries are replaced by
abstract copies.  A separate weight filtration is retained by every
homogeneous projection.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BasisCycleLifting

open Classical CommAlg

variable {K M I A Γ : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  [LinearOrder Γ] (b : Module.Basis I K M) (w : I → Γ)

def level (n : Γ) : Submodule K M := Submodule.span K (b '' {i | w i ≤ n})
def lower (n : Γ) : Submodule K M := Submodule.span K (b '' {i | w i < n})

def LiftsOn (D : Module.End K M) (W : Submodule K M) : Prop :=
  ∀ n x, x ∈ W → x ∈ level b w n → D x ∈ lower b w n →
    ∃ z, z ∈ W ∧ z ∈ level b w n ∧ D z = 0 ∧ x - z ∈ lower b w n

/-- Lift each nonzero homogeneous component and add the finitely many
resulting cycles. The output lies in exactly the original selected submodule. -/
theorem liftsOn_of_homogeneous_lifts
    (D : Module.End K M) (S : Set I) (deg : I → A)
    (shift : A → A) (hshift : Function.Injective shift)
    (hD : ∀ i, D (b i) ∈ Grading.Piece b deg (shift (deg i)))
    (hlift : ∀ a, LiftsOn b w D
      (Submodule.span K (b '' S) ⊓ Grading.Piece b deg a)) :
    LiftsOn b w D (Submodule.span K (b '' S)) := by
  intro n x hxW hxF hdx
  let π := Grading.projection b deg
  have hπW (a : A) : π a x ∈ Submodule.span K (b '' S) :=
    projection_preserves_basisSpan b deg a S x hxW
  have hπF (a : A) : π a x ∈ level b w n :=
    projection_preserves_basisSpan b deg a {i | w i ≤ n} x hxF
  have hπD (a : A) : D (π a x) ∈ lower b w n := by
    have he := LinearMap.congr_fun
      (shiftedProjection_commutes b b deg deg shift hshift D hD a) x
    change D (π a x) = π (shift a) (D x) at he
    rw [he]
    exact projection_preserves_basisSpan b deg (shift a) {i | w i < n} (D x) hdx
  choose z hzW hzF hzD hzerr using fun a =>
    hlift a n (π a x) ⟨hπW a, Grading.projection_mem b deg a x⟩ (hπF a) (hπD a)
  let T := (b.repr x).support.image deg
  refine ⟨∑ a ∈ T, z a, ?_, ?_, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun a _ => (hzW a).1)
  · exact Submodule.sum_mem _ (fun a _ => hzF a)
  · simp only [map_sum, hzD, Finset.sum_const_zero]
  · have hsum : x - ∑ a ∈ T, z a = ∑ a ∈ T, (π a x - z a) := by
      rw [Finset.sum_sub_distrib]
      change x - _ = (∑ a ∈ (b.repr x).support.image deg,
        Grading.projection b deg a x) - _
      rw [Grading.sum_projections]
    rw [hsum]
    exact Submodule.sum_mem _ (fun a _ => hzerr a)

/-- Conversely an arbitrary genuine lift can be projected back to a fixed
homogeneous component without changing its required leading term. -/
theorem homogeneous_lifts_of_liftsOn
    (D : Module.End K M) (S : Set I) (deg : I → A)
    (shift : A → A) (hshift : Function.Injective shift)
    (hD : ∀ i, D (b i) ∈ Grading.Piece b deg (shift (deg i)))
    (hlift : LiftsOn b w D (Submodule.span K (b '' S))) (a : A) :
    LiftsOn b w D (Submodule.span K (b '' S) ⊓ Grading.Piece b deg a) := by
  intro n x hx hxF hdx
  obtain ⟨y, hyW, hyF, hyD, hxy⟩ := hlift n x hx.1 hxF hdx
  let z := Grading.projection b deg a y
  refine ⟨z, ⟨projection_preserves_basisSpan b deg a S y hyW,
    Grading.projection_mem b deg a y⟩,
    projection_preserves_basisSpan b deg a {i | w i ≤ n} y hyF, ?_, ?_⟩
  · have he := LinearMap.congr_fun
      (shiftedProjection_commutes b b deg deg shift hshift D hD a) y
    simpa only [LinearMap.comp_apply, hyD, map_zero] using he
  · have he := projection_preserves_basisSpan b deg a {i | w i < n} (x-y) hxy
    simpa only [lower, z, map_sub, Grading.projection_eq_self hx.2] using he

end FourPapers.BasisCycleLifting

namespace FourPapers.BasisCycleLifting

open Classical CommAlg

variable {K X Y I J A Γ : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [LinearOrder Γ]
  (b : Module.Basis I K X) (c : Module.Basis J K Y) (w : I → Γ) (v : J → Γ)

def LinearLifts (f : X →ₗ[K] Y) : Prop :=
  ∀ n x,x∈level b w n → f x∈lower c v n →
    ∃ z,z∈level b w n ∧ f z=0 ∧ x-z∈lower b w n

/-- Finite ordinary-degree decomposition also applies to a differential
between different exterior degrees. -/
theorem linearLifts_of_homogeneous_lifts (f : X →ₗ[K] Y)
    (deg : I → A) (degree : J → A)
    (hf : ∀ i,f (b i)∈Grading.Piece c degree (deg i))
    (hlift : ∀ a n x,x∈Grading.Piece b deg a → x∈level b w n → f x∈lower c v n →
      ∃ z,z∈Grading.Piece b deg a ∧ z∈level b w n ∧ f z=0 ∧ x-z∈lower b w n) :
    LinearLifts b c w v f := by
  intro n x hx hfx
  let π := Grading.projection b deg
  have hπF (a : A) : π a x∈level b w n :=
    projection_preserves_basisSpan b deg a {i | w i≤n} x hx
  have hπD (a : A) : f (π a x)∈lower c v n := by
    have he := LinearMap.congr_fun
      (shiftedProjection_commutes b c deg degree id Function.injective_id f hf a) x
    change f (π a x)=Grading.projection c degree a (f x) at he
    rw [he]
    exact projection_preserves_basisSpan c degree a {j | v j<n} (f x) hfx
  choose z hzP hzF hzf hzerr using fun a => hlift a n (π a x)
    (Grading.projection_mem b deg a x) (hπF a) (hπD a)
  let T := (b.repr x).support.image deg
  refine ⟨∑ a∈T,z a,Submodule.sum_mem _ (fun a _ => hzF a),?_,?_⟩
  · simp only [map_sum,hzf,Finset.sum_const_zero]
  · have he : x-∑ a∈T,z a=∑ a∈T,(π a x-z a) := by
      rw [Finset.sum_sub_distrib]
      change x-_=(∑ a∈(b.repr x).support.image deg,Grading.projection b deg a x)-_
      rw [Grading.sum_projections]
    rw [he]
    exact Submodule.sum_mem _ (fun a _ => hzerr a)

end FourPapers.BasisCycleLifting

namespace FourPapers.OrderedBasis

variable {K A I Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (b : Module.Basis I K A) (w : I → Γ)
  (h1 : ∀ i, b.repr (1 : A) i ≠ 0 → w i ≤ 0)
  (hmul : ∀ i j k, b.repr (b i * b j) k ≠ 0 → w k ≤ w i + w j)
  (D : ParityDifferential K A) (W : Submodule K A)

/-- The elementary coordinate statement is the relative leading-cycle
lifting property for the constructed multiplicative filtration. -/
theorem relativeLiftsCycles_iff_basisLifts :
    (filtration b w h1 hmul).RelativeLiftsCycles D W ↔
      BasisCycleLifting.LiftsOn b w D.d W := by
  simp only [WellOrderedFiltered.MultiplicativeFiltration.RelativeLiftsCycles,
    BasisCycleLifting.LiftsOn, filtration_lower]
  rfl

end FourPapers.OrderedBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesOrderComparison -/
section

/-! # Rees Koszul degeneration for the original monomial order

No integer weight representing the term order is assumed. The associated
algebra and its differential are the literal initial Rees Koszul algebra.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice.OrderedRees

open Classical MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "c" => initialReesKoszulBasis m J I hinit G hG hu
local notation "w" => reesKoszulWeight m J
local notation "F" => idealReesKoszulFiltration m J I hinit G hG hu
local notation "hprod" => initialReesKoszul_product_homogeneous m J I hinit G hG hu
local notation "hlead" => groebnerReesKoszul_product_leading m J I hinit G hG hu
local notation "h1" => (fun a ha => le_of_eq (groebnerReesKoszul_one_weight m J G hG hu a ha))
local notation "hone" => groebnerReesKoszul_leading_one m J I hinit G hG hu

theorem differential_homogeneous (a z : IdealReesKoszulIndex m J)
    (hz : (c).repr ((idealReesKoszulDGA I).d (c a)) z ≠ 0) : w z = w a :=
  congrArg m.toSyn (initialReesKoszul_d_fine m J I hinit G hG hu a z hz)

theorem differential_leading (a z : IdealReesKoszulIndex m J) (hz : w a ≤ w z) :
    (b).repr ((idealReesKoszulDGA J).d (b a)) z = (c).repr ((idealReesKoszulDGA I).d (c a)) z :=
  groebnerReesKoszul_d_leading m J I hinit G hG hu m.toSyn.toAddMonoidHom
    (groebnerReesBasis_product_leading_coeff m J I hinit G hG hu) a z hz

theorem parity_homogeneous (a z : IdealReesKoszulIndex m J)
    (hz : (c).repr ((idealReesKoszulDGA I).parity (c a)) z ≠ 0) : w z = w a :=
  congrArg w (initialReesKoszul_parity_support m J I hinit G hG hu a z hz)

theorem parity_leading (a z : IdealReesKoszulIndex m J) (_ : w a ≤ w z) :
    (b).repr ((idealReesKoszulDGA J).parity (b a)) z = (c).repr ((idealReesKoszulDGA I).parity (c a)) z :=
  reesKoszul_parity_coeff_equal m J I hinit G hG hu a z

def differential_preserves : ∀ n x, x ∈ (F).level n → (idealReesKoszulDGA J).d x ∈ (F).level n :=
  OrderedBasis.differential_preserves b c w hprod hlead h1 (idealReesKoszulDGA J)
    (idealReesKoszulDGA I) (differential_homogeneous m J I hinit G hG hu)
    (differential_leading m J I hinit G hG hu)

def parity_preserves : ∀ n x, x ∈ (F).level n → (idealReesKoszulDGA J).parity x ∈ (F).level n :=
  OrderedBasis.parity_preserves b c w hprod hlead h1 (idealReesKoszulDGA J)
    (idealReesKoszulDGA I) (parity_homogeneous m J I hinit G hG hu)
    (parity_leading m J I hinit G hG hu)

local notation "hd" => differential_preserves m J I hinit G hG hu
local notation "hp" => parity_preserves m J I hinit G hG hu

-- These concrete constructors implement the already-proved abstract comparison.
attribute [local irreducible] groebnerReesKoszulBasis initialReesKoszulBasis
  idealReesKoszulDGA

set_option backward.isDefEq.respectTransparency true in
theorem all_cycle_lifts
    (hgen : Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (WeightedRees.initialAuxiliaryPiece m J I hinit G hG hu 1)) = ⊤)
    (hlift : (F).RelativeLiftsCycles (idealReesKoszulDGA J)
      (WeightedRees.auxiliaryPiece m J G hG hu 1)) :
    (F).LiftsCycles (idealReesKoszulDGA J) :=
  OrderedBasis.liftsCycles_of_selected_generators (K := K) (A := IdealReesKoszul J)
    (B := IdealReesKoszul I) (I := IdealReesKoszulIndex m J) (Γ := m.syn)
    b c w hprod hlead h1 hone
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (differential_homogeneous m J I hinit G hG hu)
    (differential_leading m J I hinit G hG hu)
    (parity_homogeneous m J I hinit G hG hu)
    (parity_leading m J I hinit G hG hu) {a | a.1.1 = 1} hgen hlift

set_option backward.isDefEq.respectTransparency true in
theorem homology_generated_in_degree_one
    (hgen : Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (WeightedRees.initialAuxiliaryPiece m J I hinit G hG hu 1)) = ⊤)
    (hlift : (F).RelativeLiftsCycles (idealReesKoszulDGA J)
      (WeightedRees.auxiliaryPiece m J G hG hu 1)) :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA J)
      (WeightedRees.auxiliaryPiece m J G hG hu 1)) = ⊤ :=
  OrderedBasis.homology_generated_of_selected_generators (K := K) (A := IdealReesKoszul J)
    (B := IdealReesKoszul I) (I := IdealReesKoszulIndex m J) (Γ := m.syn)
    b c w hprod hlead h1 hone
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (differential_homogeneous m J I hinit G hG hu)
    (differential_leading m J I hinit G hG hu)
    (parity_homogeneous m J I hinit G hG hu)
    (parity_leading m J I hinit G hG hu) {a | a.1.1 = 1} hgen hlift

end FourPapers.Sublattice.OrderedRees

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredDimensionLifting -/
section

/-! # Equality of homology dimensions forces filtered cycle lifting

For a finite-dimensional square-zero operator preserving a finite exhaustive
filtration, equality of the total homology dimension with that of the associated
graded complex forces every associated graded cycle to lift. The argument uses
only finite-dimensional linear algebra. In particular, it does not assume a
spectral-sequence degeneration or a universal-coefficient statement.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.FilteredHomology

open scoped BigOperators

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

/-- The lower step, viewed inside the next step, is the original lower step. -/
def lowerInLevelEquiv (F : Filtration (K := K) X) (n : ℕ) :
    lowerInLevel F n ≃ₗ[K] F.level n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.mono (Nat.le_succ n) x.property⟩, x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' a x := by rfl

theorem finrank_grade_add_lower (F : Filtration (K := K) X) (n : ℕ) :
    Module.finrank K (Grade F n) + Module.finrank K (F.level n) =
      Module.finrank K (F.level (n + 1)) := by
  have h := (lowerInLevel F n).finrank_quotient_add_finrank
  rw [(lowerInLevelEquiv F n).finrank_eq] at h
  exact h

/-- Dimensions of the literal successive quotients telescope. -/
theorem sum_finrank_grade (F : Filtration (K := K) X) (N : ℕ) :
    ∑ n ∈ Finset.range N, Module.finrank K (Grade F n) =
      Module.finrank K (F.level N) := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [F.zero, finrank_bot]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact (add_comm _ _).trans (finrank_grade_add_lower F N)

/-- The induced filtration of the actual kernel of the differential. -/
def cyclesFiltration (F : Filtration (K := K) X) (f : X →ₗ[K] Y) :
    Filtration (K := K) (LinearMap.ker f) where
  level := cycleLevel F f
  zero := by simp [cycleLevel, F.zero]
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive x := F.exhaustive x.val

theorem cyclesFiltration_top (F : Filtration (K := K) X) (f : X →ₗ[K] Y)
    (N : ℕ) (hN : F.level N = ⊤) :
    (cyclesFiltration F f).level N = ⊤ := by
  simp [cyclesFiltration, cycleLevel, hN]

section KernelComparison

variable (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (f : X →ₗ[K] Y) (hf : Preserves F G f)

/-- The leading class of an actual cycle, as a cycle of the associated graded
differential. This map is always defined; surjectivity is a conclusion below. -/
def gradeCyclesMap (n : ℕ) :
    Grade (cyclesFiltration F f) n →ₗ[K] LinearMap.ker (gradeMap F G f hf n) :=
  (lowerInLevel (cyclesFiltration F f) n).liftQ (cycleToGradeCycle F G f hf n)
    (by
      intro z hz
      apply Subtype.ext
      change (Submodule.Quotient.mk (cycleToLevel F f n z) : Grade F n) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact hz)

@[simp] theorem gradeCyclesMap_mk (n : ℕ) (z : cycleLevel F f (n + 1)) :
    gradeCyclesMap F G f hf n (Submodule.Quotient.mk z) =
      cycleToGradeCycle F G f hf n z := rfl

theorem gradeCyclesMap_injective (n : ℕ) :
    Function.Injective (gradeCyclesMap F G f hf n) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨z, rfl⟩ := (lowerInLevel (cyclesFiltration F f) n).mkQ_surjective z
  have hz' := congrArg Subtype.val hz
  change (Submodule.Quotient.mk (cycleToLevel F f n z) : Grade F n) = 0 at hz'
  rw [Submodule.mem_bot]
  change (Submodule.Quotient.mk z : Grade (cyclesFiltration F f) n) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (Submodule.Quotient.mk_eq_zero (lowerInLevel F n)).mp hz'

theorem finrank_grade_cycles_le (n : ℕ) :
    Module.finrank K (Grade (cyclesFiltration F f) n) ≤
      Module.finrank K (LinearMap.ker (gradeMap F G f hf n)) :=
  LinearMap.finrank_le_finrank_of_injective (gradeCyclesMap_injective F G f hf n)

theorem cycle_lift_of_gradeCyclesMap_surjective (n : ℕ)
    (hsurj : Function.Surjective (gradeCyclesMap F G f hf n))
    (x : X) (hx : x ∈ F.level (n + 1)) (hfx : f x ∈ G.level n) :
    ∃ z, z ∈ F.level (n + 1) ∧ f z = 0 ∧ x - z ∈ F.level n := by
  let x' : Grade F n := Submodule.Quotient.mk (⟨x, hx⟩ : F.level (n + 1))
  have hx' : gradeMap F G f hf n x' = 0 := by
    change (Submodule.Quotient.mk
      (levelMap F G f hf (n + 1) ⟨x, hx⟩) : Grade G n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hfx
  obtain ⟨z, hz⟩ := hsurj ⟨x', hx'⟩
  obtain ⟨z, rfl⟩ := (lowerInLevel (cyclesFiltration F f) n).mkQ_surjective z
  refine ⟨z.val.val, z.property, z.val.property, ?_⟩
  have heq := congrArg Subtype.val hz
  change (Submodule.Quotient.mk (cycleToLevel F f n z) : Grade F n) = x' at heq
  have hd := (Submodule.Quotient.eq _).mp heq.symm
  exact hd

/-- Equality in the usual kernel-dimension inequality forces every individual
graded kernel comparison to be onto, hence every leading cycle to lift. -/
theorem liftsCycles_of_kernel_dimension_eq (N : ℕ) (hN : F.level N = ⊤)
    (hdim : Module.finrank K (LinearMap.ker f) =
      ∑ n ∈ Finset.range N, Module.finrank K (LinearMap.ker (gradeMap F G f hf n))) :
    LiftsCycles F G f := by
  have hsum :
      (∑ n ∈ Finset.range N, Module.finrank K (Grade (cyclesFiltration F f) n)) =
      ∑ n ∈ Finset.range N, Module.finrank K (LinearMap.ker (gradeMap F G f hf n)) := by
    rw [sum_finrank_grade, cyclesFiltration_top F f N hN, finrank_top]
    exact hdim
  intro n x hx hfx
  by_cases hn : n < N
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
    have hrest :
        (∑ i ∈ (Finset.range N).erase n, Module.finrank K (Grade (cyclesFiltration F f) i)) ≤
        ∑ i ∈ (Finset.range N).erase n,
          Module.finrank K (LinearMap.ker (gradeMap F G f hf i)) :=
      Finset.sum_le_sum (fun i _ => finrank_grade_cycles_le F G f hf i)
    have hleft := Finset.sum_erase_add (Finset.range N)
      (fun i => Module.finrank K (Grade (cyclesFiltration F f) i)) hmem
    have hright := Finset.sum_erase_add (Finset.range N)
      (fun i => Module.finrank K (LinearMap.ker (gradeMap F G f hf i))) hmem
    have hpoint := finrank_grade_cycles_le F G f hf n
    have heq : Module.finrank K (Grade (cyclesFiltration F f) n) =
        Module.finrank K (LinearMap.ker (gradeMap F G f hf n)) := by omega
    have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp
      (gradeCyclesMap_injective F G f hf n)
    exact cycle_lift_of_gradeCyclesMap_surjective F G f hf n hs x hx hfx
  · refine ⟨0, (F.level (n + 1)).zero_mem, map_zero f, ?_⟩
    rw [sub_zero]
    exact F.mono (Nat.le_of_not_gt hn) (by rw [hN]; trivial)

end KernelComparison

/-- The codomain restriction in the boundary map does not change its range
dimension. -/
theorem finrank_boundaryMap_range (d : X →ₗ[K] X) (hdd : d.comp d = 0) :
    Module.finrank K (LinearMap.range (boundaryMap d d hdd)) =
      Module.finrank K (LinearMap.range d) := by
  have h := Submodule.finrank_map_subtype_eq (LinearMap.ker d)
    (LinearMap.range (boundaryMap d d hdd))
  rw [← LinearMap.range_comp] at h
  exact h.symm

/-- Rank-nullity for a square-zero operator, written without subtraction. -/
theorem finrank_homology_add_finrank (d : X →ₗ[K] X) (hdd : d.comp d = 0) :
    Module.finrank K (Homology d d hdd) + Module.finrank K X =
      2 * Module.finrank K (LinearMap.ker d) := by
  have hq := (LinearMap.range (boundaryMap d d hdd)).finrank_quotient_add_finrank
  change Module.finrank K (Homology d d hdd) +
    Module.finrank K (LinearMap.range (boundaryMap d d hdd)) =
    Module.finrank K (LinearMap.ker d) at hq
  rw [finrank_boundaryMap_range d hdd] at hq
  have hr := d.finrank_range_add_finrank_ker
  omega

/-- Equality of the total homology dimension with the sum of the associated
graded homology dimensions forces genuine leading-cycle lifts. -/
theorem liftsCycles_of_homology_dimension_eq
    (F : Filtration (K := K) X) (d : X →ₗ[K] X)
    (hd : Preserves F F d) (hdd : d.comp d = 0)
    (N : ℕ) (hN : F.level N = ⊤)
    (hdim : Module.finrank K (Homology d d hdd) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (GradedHomology F F F d d hd hd hdd n)) :
    LiftsCycles F F d := by
  apply liftsCycles_of_kernel_dimension_eq F F d hd N hN
  have hq := finrank_homology_add_finrank d hdd
  have hgrades := sum_finrank_grade F N
  rw [hN, finrank_top] at hgrades
  have hsum := Finset.sum_congr (rfl : Finset.range N = Finset.range N)
    (fun n _ => finrank_homology_add_finrank (gradeMap F F d hd n)
      (gradeMap_comp F F F d d hd hd hdd n))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change (∑ n ∈ Finset.range N, Module.finrank K (GradedHomology F F F d d hd hd hdd n)) +
      (∑ n ∈ Finset.range N, Module.finrank K (Grade F n)) =
      2 * ∑ n ∈ Finset.range N, Module.finrank K (LinearMap.ker (gradeMap F F d hd n)) at hsum
  omega

theorem homologyFiltration_top (F : Filtration (K := K) X)
    (d : X →ₗ[K] X) (hdd : d.comp d = 0) (N : ℕ) (hN : F.level N = ⊤) :
    (homologyFiltration F d d hdd).level N = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap d d hdd)).mkQ_surjective x
  refine ⟨z, ?_, rfl⟩
  change z.val ∈ F.level N
  rw [hN]
  trivial

/-- Actual leading-cycle lifts preserve the total homology dimension. The
associated graded homology is compared one weight at a time by the canonical
quotient equivalences already constructed in `FilteredHomology`. -/
theorem homology_dimension_eq_of_liftsCycles
    (F : Filtration (K := K) X) (d : X →ₗ[K] X)
    (hd : Preserves F F d) (hdd : d.comp d = 0)
    (N : ℕ) (hN : F.level N = ⊤) (hlift : LiftsCycles F F d) :
    Module.finrank K (Homology d d hdd) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (GradedHomology F F F d d hd hd hdd n) := by
  have hs := sum_finrank_grade (homologyFiltration F d d hdd) N
  rw [homologyFiltration_top F d hdd N hN, finrank_top] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro n _
  exact (associatedHomologyEquiv F F F d d hd hd hdd n hlift hlift).finrank_eq

theorem homology_dimension_eq_iff_liftsCycles
    (F : Filtration (K := K) X) (d : X →ₗ[K] X)
    (hd : Preserves F F d) (hdd : d.comp d = 0)
    (N : ℕ) (hN : F.level N = ⊤) :
    (Module.finrank K (Homology d d hdd) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (GradedHomology F F F d d hd hd hdd n)) ↔
      LiftsCycles F F d :=
  ⟨liftsCycles_of_homology_dimension_eq F d hd hdd N hN,
    homology_dimension_eq_of_liftsCycles F d hd hdd N hN⟩

/-- The same conclusion for one homological degree of a chain complex. Only
the middle space needs a finite exhaustive filtration bound. -/
theorem finrank_homology_eq_sum_graded
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (H : Filtration (K := K) Z) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0)
    (N : ℕ) (hN : G.level N = ⊤)
    (liftf : LiftsCycles F G f) (liftg : LiftsCycles G H g) :
    Module.finrank K (Homology f g hfg) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (GradedHomology F G H f g hf hg hfg n) := by
  have htop : (homologyFiltration G f g hfg).level N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    refine ⟨z, ?_, rfl⟩
    change z.val ∈ G.level N
    rw [hN]
    trivial
  have hs := sum_finrank_grade (homologyFiltration G f g hfg) N
  rw [htop, finrank_top] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro n _
  exact (associatedHomologyEquiv F G H f g hf hg hfg n liftf liftg).finrank_eq

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredPerturbation -/
section

/-! # Equal Betti dimensions and a strict filtered perturbation

Two genuine differentials on the same finite vector space are compared. Their
difference is proved to lower the filtration, so the induced maps on the
successive quotients agree. Equality of their actual homology dimensions then
forces all leading cycles of the perturbed differential to lift.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredHomology

open Classical
open scoped BigOperators

variable {K X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

theorem gradeMap_eq_of_strict_difference
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (f g : X →ₗ[K] Y) (hf : Preserves F G f) (hg : Preserves F G g)
    (hstrict : ∀ n x, x ∈ F.level (n + 1) → f x - g x ∈ G.level n) (n : ℕ) :
    gradeMap F G f hf n = gradeMap F G g hg n := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (lowerInLevel F n).mkQ_surjective x
  simp only [Submodule.mkQ_apply]
  rw [gradeMap_mk, gradeMap_mk]
  apply (Submodule.Quotient.eq (lowerInLevel G n)).mpr
  exact hstrict n x.val x.property

end FourPapers.FilteredHomology

namespace FourPapers.FilteredHomology

open Classical
open scoped BigOperators

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
  [FiniteDimensional K X]

theorem liftsCycles_of_equal_homology_strict_perturbation
    (F : Filtration (K := K) X) (d d₀ : X →ₗ[K] X)
    (hd : Preserves F F d) (hd₀ : Preserves F F d₀)
    (hdd : d.comp d = 0) (hdd₀ : d₀.comp d₀ = 0)
    (hstrict : ∀ n x, x ∈ F.level (n + 1) → d x - d₀ x ∈ F.level n)
    (hlift₀ : LiftsCycles F F d₀) (N : ℕ) (hN : F.level N = ⊤)
    (hdim : Module.finrank K (Homology d d hdd) =
      Module.finrank K (Homology d₀ d₀ hdd₀)) :
    LiftsCycles F F d := by
  apply liftsCycles_of_homology_dimension_eq F d hd hdd N hN
  rw [hdim, homology_dimension_eq_of_liftsCycles F d₀ hd₀ hdd₀ N hN hlift₀]
  apply Finset.sum_congr rfl
  intro n _
  have he := gradeMap_eq_of_strict_difference F F d d₀ hd hd₀ hstrict n
  have h₁ := finrank_homology_add_finrank (gradeMap F F d hd n)
    (gradeMap_comp F F F d d hd hd hdd n)
  have h₀ := finrank_homology_add_finrank (gradeMap F F d₀ hd₀ n)
    (gradeMap_comp F F F d₀ d₀ hd₀ hd₀ hdd₀ n)
  change Module.finrank K (GradedHomology F F F d d hd hd hdd n) +
      Module.finrank K (Grade F n) = 2 * Module.finrank K (LinearMap.ker
        (gradeMap F F d hd n)) at h₁
  change Module.finrank K (GradedHomology F F F d₀ d₀ hd₀ hd₀ hdd₀ n) +
      Module.finrank K (Grade F n) = 2 * Module.finrank K (LinearMap.ker
        (gradeMap F F d₀ hd₀ n)) at h₀
  have hk := congrArg
    (fun f : Grade F n →ₗ[K] Grade F n => Module.finrank K (LinearMap.ker f)) he
  omega

end FourPapers.FilteredHomology

end
end
end


end
