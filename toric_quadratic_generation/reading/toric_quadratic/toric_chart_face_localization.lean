module

public import PaperVerification.ToricChartLocalization
public import PaperVerification.ToricFanConstruction

@[expose] public section

/-!
# The denominator of a smooth cone face

Removing coordinate inequalities is exactly localization by the product
of the removed coordinate characters. The exponent is their sum in the
actual dual integral basis. This applies to every actual smooth fan cone
and every face ray subset.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]

theorem coordinateConeMonoid_antitone (b : Module.Basis ι ℤ E)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    coordinateConeMonoid b J ≤ coordinateConeMonoid b I :=
  fun x hx i hi => hx i (hIJ hi)

def faceDenominatorExponent (b : Module.Basis ι ℤ E) (I J : Finset ι) : E :=
  ∑ j ∈ J \ I, b j

theorem faceDenominatorExponent_repr (b : Module.Basis ι ℤ E)
    (I J : Finset ι) (i : ι) :
    b.repr (faceDenominatorExponent b I J) i = if i ∈ J \ I then 1 else 0 := by
  simp [faceDenominatorExponent, map_sum, Finsupp.finsetSum_apply,
    Module.Basis.repr_self_apply, Finsupp.single_apply, eq_comm]

theorem faceDenominatorExponent_mem (b : Module.Basis ι ℤ E) (I J : Finset ι) :
    faceDenominatorExponent b I J ∈ coordinateConeMonoid b J := by
  intro i hi
  rw [faceDenominatorExponent_repr]
  split_ifs <;> norm_num

theorem neg_faceDenominatorExponent_mem (b : Module.Basis ι ℤ E) (I J : Finset ι) :
    -faceDenominatorExponent b I J ∈ coordinateConeMonoid b I := by
  intro i hi
  rw [map_neg, Finsupp.neg_apply, faceDenominatorExponent_repr,
    if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hi), neg_zero]

theorem faceDenominatorExponent_clears (b : Module.Basis ι ℤ E)
    {I J : Finset ι} (hIJ : I ⊆ J) (x : E)
    (hx : x ∈ coordinateConeMonoid b I) :
    ∃ N : ℕ, x + N • faceDenominatorExponent b I J ∈ coordinateConeMonoid b J := by
  let N := (J \ I).sup (fun i => (-b.repr x i).toNat)
  refine ⟨N, ?_⟩
  intro i hiJ
  have hrepr : b.repr (x + N • faceDenominatorExponent b I J) i =
      b.repr x i + (N : ℤ) * (if i ∈ J \ I then 1 else 0) := by
    simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul, faceDenominatorExponent_repr]
  rw [hrepr]
  by_cases hiI : i ∈ I
  · rw [if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hiI), mul_zero, add_zero]
    exact hx i hiI
  · have hi : i ∈ J \ I := Finset.mem_sdiff.mpr ⟨hiJ, hiI⟩
    rw [if_pos hi, mul_one]
    have hle : (-b.repr x i).toNat ≤ N :=
      Finset.le_sup (f := fun j => (-b.repr x j).toNat) hi
    have hleZ : (((-b.repr x i).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-b.repr x i)
    omega

/-- After restricting to another face, the original denominator removes
exactly the inequalities not shared by the two faces. Coordinates already
invertible on the restricted chart cause no additional condition. -/
theorem faceDenominatorExponent_clears_intersection (b : Module.Basis ι ℤ E)
    {I K J : Finset ι} (hIJ : I ⊆ J) (x : E)
    (hx : x ∈ coordinateConeMonoid b (I ∩ K)) :
    ∃ N : ℕ, x + N • faceDenominatorExponent b K J ∈ coordinateConeMonoid b I := by
  let N := (I \ K).sup (fun i => (-b.repr x i).toNat)
  refine ⟨N, ?_⟩
  intro i hiI
  have hrepr : b.repr (x + N • faceDenominatorExponent b K J) i =
      b.repr x i + (N : ℤ) * (if i ∈ J \ K then 1 else 0) := by
    simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul, faceDenominatorExponent_repr]
  rw [hrepr]
  by_cases hiK : i ∈ K
  · rw [if_neg (fun hh => (Finset.mem_sdiff.mp hh).2 hiK), mul_zero, add_zero]
    exact hx i (Finset.mem_inter.mpr ⟨hiI, hiK⟩)
  · have hi : i ∈ J \ K := Finset.mem_sdiff.mpr ⟨hIJ hiI, hiK⟩
    rw [if_pos hi, mul_one]
    have hle : (-b.repr x i).toNat ≤ N :=
      Finset.le_sup (f := fun j => (-b.repr x j).toNat)
        (Finset.mem_sdiff.mpr ⟨hiI, hiK⟩)
    have hleZ : (((-b.repr x i).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-b.repr x i)
    omega

variable (k : Type*) [CommSemiring k]

theorem coordinateChartInclusion_isLocalizationMap
    (b : Module.Basis ι ℤ E) {I J : Finset ι} (hIJ : I ⊆ J) :
    (Submonoid.powers (chartCharacter k (coordinateConeMonoid b J)
      (faceDenominatorExponent b I J) (faceDenominatorExponent_mem b I J))).IsLocalizationMap
        (monoidChartInclusion k (coordinateConeMonoid_antitone b hIJ)) :=
  monoidChartInclusion_isLocalizationMap k (coordinateConeMonoid_antitone b hIJ)
    _ (faceDenominatorExponent_mem b I J) (neg_faceDenominatorExponent_mem b I J)
    (faceDenominatorExponent_clears b hIJ)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

theorem dualConeMonoid_antitone {n : ℕ} {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    dualConeMonoid s ≤ dualConeMonoid t := fun m hm u hu => hm u (hts hu)

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Every actual smooth cone face has a single integral character whose
inversion removes precisely the discarded inequalities. -/
theorem exists_face_character_denominator
    (s t : Finset (Lattice n)) (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ v : Lattice n, v ∈ dualConeMonoid s ∧ -v ∈ dualConeMonoid t ∧
      ∀ m ∈ dualConeMonoid t, ∃ N : ℕ, m + N • v ∈ dualConeMonoid s := by
  obtain ⟨b, J, rfl⟩ := «Σ».smooth s hs
  let I := basisRayIndices b t
  have hI : I.image b = t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I ⊆ J := by
    intro i hi
    have hbi : b i ∈ t := hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (hts hbi)
    exact b.injective hji ▸ hj
  refine ⟨faceDenominatorExponent (integralDualBasis b) I J, ?_, ?_, ?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) I J
  · rw [← hI, dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) I J
  · intro m hm
    rw [← hI, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hIJ m hm
    exact ⟨N, (dualConeMonoid_basis_eq b J).symm ▸ hN⟩

theorem chart_face_isLocalizationMap (k : Type*) [CommSemiring k]
    (s t : Finset (Lattice n)) (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ (v : Lattice n) (hv : v ∈ dualConeMonoid s),
      (Submonoid.powers (chartCharacter k (dualConeMonoid s) v hv)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hts)) := by
  obtain ⟨v, hv, hneg, hclear⟩ := «Σ».exists_face_character_denominator s t hs hts
  exact ⟨v, hv, monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hneg hclear⟩

/-- The same character localizes both a cone chart to one face and another
face chart to their actual intersection. -/
theorem exists_intersection_character_denominator
    (q s t : Finset (Lattice n)) (hq : q ∈ «Σ».cones)
    (hs : s ⊆ q) (ht : t ⊆ q) :
    ∃ v : Lattice n, v ∈ dualConeMonoid q ∧ -v ∈ dualConeMonoid t ∧
      (∀ m ∈ dualConeMonoid t, ∃ N : ℕ, m + N • v ∈ dualConeMonoid q) ∧
      (∀ m ∈ dualConeMonoid (s ∩ t), ∃ N : ℕ, m + N • v ∈ dualConeMonoid s) := by
  obtain ⟨b, J, rfl⟩ := «Σ».smooth q hq
  let I := basisRayIndices b s
  let K := basisRayIndices b t
  have hI : I.image b = s := image_basisRayIndices b s
    (hs.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hK : K.image b = t := image_basisRayIndices b t
    (ht.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I ⊆ J := (Finset.image_subset_image_iff b.injective).mp (hI.symm ▸ hs)
  have hKJ : K ⊆ J := (Finset.image_subset_image_iff b.injective).mp (hK.symm ▸ ht)
  have hIK : (I ∩ K).image b = s ∩ t := by
    rw [Finset.image_inter I K b.injective, hI, hK]
  let v := faceDenominatorExponent (integralDualBasis b) K J
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) K J
  · rw [← hK, dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) K J
  · intro m hm
    rw [← hK, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hKJ m hm
    exact ⟨N, (dualConeMonoid_basis_eq b J).symm ▸ hN⟩
  · intro m hm
    rw [← hIK, dualConeMonoid_basis_eq] at hm
    obtain ⟨N, hN⟩ := faceDenominatorExponent_clears_intersection
      (integralDualBasis b) hIJ m hm
    refine ⟨N, ?_⟩
    rw [← hI, dualConeMonoid_basis_eq]
    exact hN

end SmoothCompleteFan

end PaperVerification.ToricGeometry
