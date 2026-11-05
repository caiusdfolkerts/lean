import CommAlg.Polymatroid.Localization
import CommAlg.Polymatroid.SocleReconstruction
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Literal monomial localization in the retained-variable polynomial ring -/

noncomputable section

namespace Characterizations

open CommAlg.Polymatroid
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def restrictExponent (U : Finset V) (a : Exponent V) : Exponent U :=
  a.subtypeDomain (· ∈ U)

@[simp] theorem restrictExponent_apply (U : Finset V) (a : Exponent V) (i : U) :
    restrictExponent U a i = a i := rfl

def extendExponent (U : Finset V) (a : Exponent U) : Exponent V := a.extendDomain

@[simp] theorem extendExponent_apply (U : Finset V) (a : Exponent U) (i : V) :
    extendExponent U a i = if hi : i ∈ U then a ⟨i, hi⟩ else 0 := by
  simp [extendExponent, Finsupp.extendDomain_apply]

@[simp] theorem restrict_extend (U : Finset V) (a : Exponent U) :
    restrictExponent U (extendExponent U a) = a := by
  ext i
  simp

@[simp] theorem extend_restrict (U : Finset V) (a : Exponent V) :
    extendExponent U (restrictExponent U a) = project U a := by
  ext i
  by_cases hi : i ∈ U <;> simp [hi]

theorem extendExponent_le_iff (U : Finset V) (a b : Exponent U) :
    extendExponent U a ≤ extendExponent U b ↔ a ≤ b := by
  constructor
  · intro h i
    simpa using h i
  · intro h i
    by_cases hi : i ∈ U
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi]

def extendExponentEmbedding (U : Finset V) : Exponent U ↪o Exponent V :=
  OrderEmbedding.ofMapLEIff (extendExponent U) (extendExponent_le_iff U)

theorem restrictExponent_degree (U : Finset V) (a : Exponent V) :
    (restrictExponent U a).degree = subsetSum a U := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.sum_coe_sort U (fun i => a i)

theorem extendExponent_degree (U : Finset V) (a : Exponent U) :
    (extendExponent U a).degree = a.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp only [extendExponent_apply]
  rw [← Finset.sum_attach_eq_sum_dite U (fun i => a i)]
  rfl

def localFamily (B : Family V) (U : Finset V) : Family U :=
  minimalFamily (B.image (restrictExponent U))

theorem localFamily_antichain (B : Family V) (U : Finset V) : Antichain (localFamily B U) :=
  minimalFamily_antichain _

theorem localFamily_nonempty {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    (localFamily B U).Nonempty := minimalFamily_nonempty (hB.image _)

theorem contains_localFamily (B : Family V) (U : Finset V) (a : Exponent U) :
    Contains (localFamily B U) a ↔ ∃ b ∈ B, restrictExponent U b ≤ a := by
  rw [localFamily, contains_minimalFamily]
  simp [Contains]

theorem contains_localize_iff (B : Family V) (U : Finset V) (a : Exponent V) :
    Contains (localize B U) a ↔ Contains (localFamily B U) (restrictExponent U a) := by
  rw [contains_localize, contains_localFamily]
  constructor
  · rintro ⟨b, hb, hba⟩
    refine ⟨b, hb, ?_⟩
    intro i
    simpa using hba i
  · rintro ⟨b, hb, hba⟩
    refine ⟨b, hb, ?_⟩
    intro i
    by_cases hi : i ∈ U
    · simpa [hi] using hba ⟨i, hi⟩
    · simp [hi]

theorem minimalFamily_image_orderEmbedding {W : Type*} [Fintype W] [DecidableEq W]
    (f : Exponent V ↪o Exponent W) (B : Family V) :
    minimalFamily (B.image f) = (minimalFamily B).image f := by
  ext a
  simp only [mem_minimalFamily, Finset.mem_image]
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hmin⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    intro c hc hcb
    exact f.injective (hmin (f c) ⟨c, hc, rfl⟩ (f.monotone hcb))
  · rintro ⟨b, ⟨hb, hmin⟩, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    rintro _ ⟨c, hc, rfl⟩ hcb
    exact congrArg f (hmin c hc (f.le_iff_le.mp hcb))

theorem localize_eq_extend_localFamily (B : Family V) (U : Finset V) :
    localize B U = (localFamily B U).image (extendExponent U) := by
  have h := minimalFamily_image_orderEmbedding (extendExponentEmbedding U)
    (B.image (restrictExponent U))
  simpa only [Finset.image_image, Function.comp_def, extendExponentEmbedding,
    OrderEmbedding.coe_ofMapLEIff, extend_restrict, localize, localFamily] using h

theorem locallyEquigenerated_iff (B : Family V) :
    LocallyEquigenerated B ↔ ∀ U, ∃ d, Equigenerated (localFamily B U) d := by
  constructor
  · intro h U
    obtain ⟨d, hd⟩ := h U
    refine ⟨d, ?_⟩
    intro a ha
    have he : extendExponent U a ∈ localize B U := by
      rw [localize_eq_extend_localFamily]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    simpa [extendExponent_degree] using hd _ he
  · intro h U
    obtain ⟨d, hd⟩ := h U
    refine ⟨d, ?_⟩
    intro a ha
    rw [localize_eq_extend_localFamily] at ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simpa [extendExponent_degree] using hd _ hb

variable (k : Type*) [CommSemiring k]

def localizationMap (U : Finset V) : MvPolynomial V k →ₐ[k] MvPolynomial U k :=
  MvPolynomial.aeval (fun i => if hi : i ∈ U then MvPolynomial.X ⟨i, hi⟩ else 1)

@[simp] theorem localizationMap_X (U : Finset V) (i : V) :
    localizationMap k U (MvPolynomial.X i) =
      if hi : i ∈ U then MvPolynomial.X ⟨i, hi⟩ else 1 := by simp [localizationMap]

theorem localizationMap_monomial (U : Finset V) (a : Exponent V) (c : k) :
    localizationMap k U (MvPolynomial.monomial a c) =
      MvPolynomial.monomial (restrictExponent U a) c := by
  classical
  rw [localizationMap, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [restrictExponent_apply]
  have he : (fun i : V => (if hi : i ∈ U then (MvPolynomial.X ⟨i, hi⟩ : MvPolynomial U k)
      else 1) ^ a i) = (fun i => if hi : i ∈ U then MvPolynomial.X ⟨i, hi⟩ ^ a i else 1) := by
    funext i
    by_cases hi : i ∈ U <;> simp [hi]
  rw [he, ← Finset.prod_attach_eq_prod_dite U (fun i => MvPolynomial.X i ^ a i)]
  rfl

def monomialLocalization (I : Ideal (MvPolynomial V k)) (U : Finset V) :
    Ideal (MvPolynomial U k) := Ideal.map (localizationMap k U).toRingHom I

theorem monomialLocalization_eq (B : Family V) (U : Finset V) :
    monomialLocalization k (monomialIdeal k B) U = monomialIdeal k (localFamily B U) := by
  rw [monomialLocalization, localFamily, monomialIdeal_minimalFamily]
  simp only [monomialIdeal, Ideal.map_span, Set.image_image, Finset.coe_image]
  congr 1
  ext p
  simp only [Set.mem_image, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, localizationMap_monomial]

end Characterizations
