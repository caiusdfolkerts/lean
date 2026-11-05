module

public import Recovery.Unimodular.GraphicSectionRing.NormalBasis
public import Recovery.Unimodular.GraphicSectionRing.BarComparison
public import Recovery.Unimodular.FlagKoszul.FlagBasis

/-!
# The actual commutative flag model of the graphic section algebra

The common basis index consists of nonconstant compatible exponent vectors.
It is proved equivalent to the actual nonzero lattice semigroup. The genuine
section-algebra product has the flag-algebra product as its leading part for
the independent height filtration. Internal degrees retain their original
meaning throughout.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.GraphicSectionRing.FlagModel

open PaperVerification.AugmentedAlgebraBasis
open PaperVerification.Fermion.BasisFiltered

attribute [local instance] Classical.propDecidable

variable {n : ℕ} (C : Set (Constraint n))

abbrev Relation : Point C → Point C → Prop := fun a b => Compatible a.val b.val

 theorem relation_refl (a : Point C) : Relation C a a := compatible_refl a.val
 theorem relation_symm {a b : Point C} (h : Relation C a b) : Relation C b a :=
  compatible_symm h

theorem valid_iff_standard (u : Point C →₀ ℕ) :
    FlagKoszul.Valid (Relation C) u ↔ StandardExponent Subtype.val u := by
  constructor
  · intro h x hx y hy
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hy
    exact h a (Finsupp.mem_support_iff.mp ((Finsupp.mem_toMultiset u a).mp ha))
      b (Finsupp.mem_support_iff.mp ((Finsupp.mem_toMultiset u b).mp hb))
  · intro h a ha b hb
    exact h a.val (Multiset.mem_map.mpr ⟨a,
      (Finsupp.mem_toMultiset u a).mpr (Finsupp.mem_support_iff.mpr ha), rfl⟩)
      b.val (Multiset.mem_map.mpr ⟨b,
      (Finsupp.mem_toMultiset u b).mpr (Finsupp.mem_support_iff.mpr hb), rfl⟩)

/-- The common flag index is proved to be the literal positive section semigroup. -/
def positiveEquiv : FlagKoszul.Positive (Relation C) ≃ PositiveSection C where
  toFun u := ⟨sectionDegree C u.val, by
    intro h
    have hz := congrArg (internalDegree C) h
    rw [internalDegree_sectionDegree, map_zero] at hz
    exact u.2.2 ((Finsupp.degree_eq_zero_iff u.val).mp hz)⟩
  invFun z := ⟨normalExponent C z.val,
    (valid_iff_standard C _).mpr (normalExponent_standard C z.val), by
      intro h
      have hz := sectionDegree_normalExponent C z.val
      rw [h, map_zero] at hz
      exact z.2 hz.symm⟩
  left_inv u := Subtype.ext
    (normalExponent_eq_of_standard ((valid_iff_standard C u.val).mp u.2.1))
  right_inv z := Subtype.ext (sectionDegree_normalExponent C z.val)

@[simp] theorem positiveEquiv_val (u : FlagKoszul.Positive (Relation C)) :
    (positiveEquiv C u).val = sectionDegree C u.val := rfl

@[simp] theorem positiveEquiv_symm_val (z : PositiveSection C) :
    ((positiveEquiv C).symm z).val = normalExponent C z.val := rfl

@[simp] theorem positiveEquiv_degree (u : FlagKoszul.Positive (Relation C)) :
    internalDegree C (positiveEquiv C u).val = FlagKoszul.positiveDegree (Relation C) u :=
  internalDegree_sectionDegree C u.val

variable (K : Type*) [Field K]

/-- This is a reindexing of the actual section algebra's monomial basis. -/
def basis : Module.Basis (Option (FlagKoszul.Positive (Relation C))) K (SectionAlgebra C K) :=
  (augmentedSectionBasis C K).reindex (Equiv.optionCongr (positiveEquiv C)).symm

@[simp] theorem basis_none : basis C K none = 1 := by
  simpa only [basis, Module.Basis.reindex_apply, Equiv.symm_symm,
    Equiv.optionCongr_apply, Option.map_none] using augmentedSectionBasis_none C K

@[simp] theorem basis_some (u : FlagKoszul.Positive (Relation C)) :
    basis C K (some u) = AddMonoidAlgebra.single (sectionDegree C u.val) 1 := by
  simp only [basis, Module.Basis.reindex_apply, Equiv.symm_symm,
    Equiv.optionCongr_apply, Option.map_some, augmentedSectionBasis_some, positiveEquiv_val]

@[simp] theorem augmentation_basis (u : FlagKoszul.Positive (Relation C)) :
    sectionAugmentation C K (basis C K (some u)) = 0 := by
  rw [basis_some, sectionAugmentation_single, internalDegree_sectionDegree]
  exact if_neg (fun h => u.2.2 ((Finsupp.degree_eq_zero_iff u.val).mp h))

/-- The actual product basis index is the canonical normal exponent of the
sum of the two original lattice-semigroup elements. -/
def productIndex (u v : FlagKoszul.Positive (Relation C)) : FlagKoszul.Positive (Relation C) :=
  (positiveEquiv C).symm (positiveAdd (positiveEquiv C u) (positiveEquiv C v))

@[simp] theorem productIndex_val (u v : FlagKoszul.Positive (Relation C)) :
    (productIndex C u v).val =
      normalExponent C (sectionDegree C u.val + sectionDegree C v.val) := rfl

theorem basis_product (u v : FlagKoszul.Positive (Relation C)) :
    basis C K (some u) * basis C K (some v) = basis C K (some (productIndex C u v)) := by
  simp only [basis_some, AddMonoidAlgebra.single_mul_single, one_mul, productIndex_val,
    sectionDegree_normalExponent]

@[simp] theorem productCoefficients_basis (u v : FlagKoszul.Positive (Relation C)) :
    productCoefficients (basis C K) u v = Finsupp.single (productIndex C u v) 1 := by
  classical
  ext w
  change (basis C K).repr (basis C K (some u) * basis C K (some v)) (some w) = _
  rw [basis_product, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- Multiplication preserves the original total/internal degree. -/
theorem product_degree (u v w : FlagKoszul.Positive (Relation C))
    (h : productCoefficients (basis C K) u v w ≠ 0) :
    FlagKoszul.positiveDegree (Relation C) w =
      FlagKoszul.positiveDegree (Relation C) u + FlagKoszul.positiveDegree (Relation C) v := by
  classical
  rw [productCoefficients_basis] at h
  have hw : productIndex C u v = w := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at h
  rw [← hw]
  change (normalExponent C (sectionDegree C u.val + sectionDegree C v.val)).degree = _
  rw [normalExponent_degree, map_add, internalDegree_sectionDegree, internalDegree_sectionDegree]
  rfl

/-- The auxiliary filtration weight; it is independent of internal degree. -/
def weight (u : FlagKoszul.Positive (Relation C)) : ℕ := monomialWeight Subtype.val u.val

 theorem weight_productIndex_le (u v : FlagKoszul.Positive (Relation C)) :
    weight C (productIndex C u v) ≤ weight C u + weight C v := by
  have h := sectionHeight_add_le C (sectionDegree C u.val) (sectionDegree C v.val)
  simpa only [sectionHeight,
    normalExponent_eq_of_standard ((valid_iff_standard C u.val).mp u.2.1),
    normalExponent_eq_of_standard ((valid_iff_standard C v.val).mp v.2.1),
    weight, productIndex_val] using h

 theorem weight_productIndex_lt (u v : FlagKoszul.Positive (Relation C))
    (h : ¬ FlagKoszul.Valid (Relation C) (u.val + v.val)) :
    weight C (productIndex C u v) < weight C u + weight C v := by
  have hs : ¬ StandardExponent Subtype.val
      (normalExponent C (sectionDegree C u.val) + normalExponent C (sectionDegree C v.val)) := by
    rw [normalExponent_eq_of_standard ((valid_iff_standard C u.val).mp u.2.1),
      normalExponent_eq_of_standard ((valid_iff_standard C v.val).mp v.2.1)]
    exact fun hs => h ((valid_iff_standard C _).mpr hs)
  have hh := sectionHeight_add_lt hs
  simpa only [sectionHeight,
    normalExponent_eq_of_standard ((valid_iff_standard C u.val).mp u.2.1),
    normalExponent_eq_of_standard ((valid_iff_standard C v.val).mp v.2.1),
    weight, productIndex_val] using hh

 theorem productIndex_eq_sum (u v : FlagKoszul.Positive (Relation C))
    (h : FlagKoszul.Valid (Relation C) (u.val + v.val)) :
    (productIndex C u v).val = u.val + v.val := by
  rw [productIndex_val, ← map_add]
  exact normalExponent_eq_of_standard ((valid_iff_standard C _).mp h)

/-- The actual product in the flag algebra agrees with the section product
exactly when the exponent union is compatible, and vanishes otherwise. -/
theorem flag_productCoefficients (u v : FlagKoszul.Positive (Relation C)) :
    productCoefficients (FlagKoszul.augmentedBasis (Relation C) (K := K)) u v =
      if FlagKoszul.Valid (Relation C) (u.val + v.val) then
        Finsupp.single (productIndex C u v) 1 else 0 := by
  classical
  by_cases h : FlagKoszul.Valid (Relation C) (u.val + v.val)
  · rw [if_pos h]
    have hp : FlagKoszul.augmentedBasis (Relation C) (K := K) (some u) *
        FlagKoszul.augmentedBasis (Relation C) (some v) =
        FlagKoszul.augmentedBasis (Relation C) (some (productIndex C u v)) := by
      rw [FlagKoszul.augmentedBasis_product, FlagKoszul.augmentedBasis_some,
        productIndex_eq_sum C u v h]
    ext w
    change (FlagKoszul.augmentedBasis (Relation C)).repr
      (FlagKoszul.augmentedBasis (Relation C) (some u) *
        FlagKoszul.augmentedBasis (Relation C) (some v)) (some w) = _
    rw [hp, Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    have hp : FlagKoszul.augmentedBasis (Relation C) (K := K) (some u) *
        FlagKoszul.augmentedBasis (Relation C) (some v) = 0 := by
      rw [FlagKoszul.augmentedBasis_product]
      exact FlagKoszul.MonomialQuotient.monomial_eq_zero_of_bad
        (FlagKoszul.bad (Relation C) ∅) (FlagKoszul.bad_upper (Relation C) ∅)
        (fun hv => h hv.1) 1
    ext w
    change (FlagKoszul.augmentedBasis (Relation C)).repr
      (FlagKoszul.augmentedBasis (Relation C) (some u) *
        FlagKoszul.augmentedBasis (Relation C) (some v)) (some w) = _
    rw [hp, map_zero]
    rfl

/-- The genuine coefficient-level leading-map formula. -/
theorem product_hasTop (u v : FlagKoszul.Positive (Relation C)) :
    HasTop (BarComparison.coefficientBasis (K := K)) (weight C) (weight C u + weight C v)
      (productCoefficients (basis C K) u v)
      (productCoefficients (FlagKoszul.augmentedBasis (Relation C) (K := K)) u v) := by
  classical
  rw [productCoefficients_basis, flag_productCoefficients]
  have hh : Homogeneous (BarComparison.coefficientBasis (K := K)) (weight C)
      (weight C (productIndex C u v)) (Finsupp.single (productIndex C u v) (1 : K)) := by
    simpa only [BarComparison.coefficientBasis, Finsupp.coe_basisSingleOne] using
      homogeneous_basis (BarComparison.coefficientBasis (K := K)) (weight C) (productIndex C u v)
  refine ⟨bound_mono _ _ (weight_productIndex_le C u v) (homogeneous_bound _ _ hh), ?_⟩
  rw [component_of_homogeneous _ _ hh]
  by_cases h : FlagKoszul.Valid (Relation C) (u.val + v.val)
  · have he : weight C (productIndex C u v) = weight C u + weight C v := by
      change monomialWeight Subtype.val (productIndex C u v).val = _
      rw [productIndex_eq_sum C u v h, map_add]
      rfl
    rw [if_pos he.symm, if_pos h]
  · rw [if_neg (Ne.symm (ne_of_lt (weight_productIndex_lt C u v h))), if_neg h]

#print axioms positiveEquiv
#print axioms product_degree
#print axioms weight_productIndex_lt
#print axioms product_hasTop

end Unimodular.GraphicSectionRing.FlagModel

#check Unimodular.GraphicSectionRing.FlagModel.product_hasTop
