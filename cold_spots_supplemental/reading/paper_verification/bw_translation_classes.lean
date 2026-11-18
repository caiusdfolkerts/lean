module

public import PaperVerification.BWEligibleClasses
public import PaperVerification.BWConstruction
public import PaperVerification.BWNormalized
public import PaperVerification.BWNorm
public import PaperVerification.LatticeTranslationClasses
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite


@[expose] public section
/-! # The exact 120 Barnes–Wall translation classes

This file constructs the quotient of actual deep holes by actual lattice
translations and proves its equivalence with 120 explicit character/phase
indices.  Both completeness and distinctness are proved in real coordinates.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem bwGamma_mem_iff (z : Fin 16 → ℝ) :
    z ∈ bwGammaSet ↔ bwLeft z ∈ bwMSet ∧ bwRight z ∈ bwMSet ∧
      bwLeft z - bwRight z ∈ dPlusSet 8 := by
  simpa only [append_bw_blocks] using bwGamma_append_iff (bwLeft z) (bwRight z)

def bwGammaAddSubgroup : AddSubgroup (Fin 16 → ℝ) where
  carrier := bwGammaSet
  zero_mem' := by
    apply (bwGamma_mem_iff 0).mpr
    have hleft : bwLeft (0 : Fin 16 → ℝ) = 0 := by
      funext i
      rfl
    have hright : bwRight (0 : Fin 16 → ℝ) = 0 := by
      funext i
      rfl
    rw [hleft, hright, sub_self]
    exact
      (show (0 : Fin 8 → ℝ) ∈ bwMSet ∧ (0 : Fin 8 → ℝ) ∈ bwMSet ∧
        (0 : Fin 8 → ℝ) ∈ dPlusSet 8 from ⟨bwMSet_zero, bwMSet_zero, zero_mem_dPlusSet 8⟩)
  add_mem' := by
    intro z w hz hw
    obtain ⟨hz₁, hz₂, hz₃⟩ := (bwGamma_mem_iff z).mp hz
    obtain ⟨hw₁, hw₂, hw₃⟩ := (bwGamma_mem_iff w).mp hw
    apply (bwGamma_mem_iff (z + w)).mpr
    refine ⟨bwMSet_add hz₁ hw₁, bwMSet_add hz₂ hw₂, ?_⟩
    have he : bwLeft (z + w) - bwRight (z + w) =
        (bwLeft z - bwRight z) + (bwLeft w - bwRight w) := by
      funext i
      simp only [bwLeft, bwRight, Pi.add_apply, Pi.sub_apply]
      ring
    rw [he]
    exact dPlusSet_add (by decide : Even 8) hz₃ hw₃
  neg_mem' := by
    intro z hz
    obtain ⟨hz₁, hz₂, hz₃⟩ := (bwGamma_mem_iff z).mp hz
    apply (bwGamma_mem_iff (-z)).mpr
    refine ⟨bwMSet_neg hz₁, bwMSet_neg hz₂, ?_⟩
    have he : bwLeft (-z) - bwRight (-z) = -(bwLeft z - bwRight z) := by
      funext i
      simp only [bwLeft, bwRight, Pi.neg_apply, Pi.sub_apply]
      ring
    rw [he]
    exact dPlusSet_neg (by decide : Even 8) hz₃

theorem bwCanonical_pair_gluing_iff (χ ψ : BWCharacter) (q : BWQuotient) :
    BWGluingCondition (bwCanonicalHole χ) (bwCanonicalHole ψ + bwRepresentative q) ↔
      χ = ψ ∧ bwCharacterEval χ q = 1 := by
  have hχ := (bwCanonicalHole_eligible χ).1
  have hψ : squaredDepth bwMSet (bwCanonicalHole ψ + bwRepresentative q) = 1 / 2 := by
    change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
      (bwCanonicalHole ψ + bwRepresentative q) = 1 / 2
    rw [squaredDepth_add_of_subgroup bwMAddSubgroup _ _ (bwRepresentative_mem q)]
    exact (bwCanonicalHole_eligible ψ).1
  have hlocal (r : BWQuotient) :
      (bwDepthProfile (bwCanonicalHole χ) r = 1 ∨
        bwDepthProfile (bwCanonicalHole ψ + bwRepresentative q) r = 1) ↔
      (bwCharacterEval χ r ≠ 0 ∨ bwCharacterEval ψ r ≠ bwCharacterEval ψ q) := by
    rw [bwCanonicalHole_profile, bwDepthProfile_translate_representative,
      bwCanonicalHole_profile, bwNearFar_eq_one_iff, bwNearFar_eq_one_iff,
      bwCharacterEval_sub]
    exact (show ∀ a b c : Binary, (a = 1 ∨ b - c = 1) ↔ (a ≠ 0 ∨ b ≠ c) by decide) _ _ _
  unfold BWGluingCondition
  rw [hχ, hψ]
  simp only [true_and]
  simp_rw [hlocal]
  rw [bwCharacter_complement_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (binary_eq_zero_or_one _).resolve_left (Ne.symm h)⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by simpa [h]⟩

theorem bwCanonical_pair_depth_iff (χ ψ : BWCharacter) (q : BWQuotient) :
    squaredDepth bwGammaSet (Fin.append (bwCanonicalHole χ)
      (bwCanonicalHole ψ + bwRepresentative q)) = 3 / 2 ↔
        χ = ψ ∧ bwCharacterEval χ q = 1 := by
  rw [squaredDepth_bwGamma_eq_iff, bwCanonical_pair_gluing_iff]

def bwCanonicalDeepHole (p : BWHoleIndex) : Fin 16 → ℝ :=
  Fin.append (bwCanonicalHole p.val.1) (bwCanonicalHole p.val.1 + bwRepresentative p.val.2)

theorem bwCanonicalDeepHole_deep (p : BWHoleIndex) : IsDeepHole bwGammaSet (bwCanonicalDeepHole p) := by
  apply (isDeepHole_bwGamma_iff_depth _).mpr
  exact (bwCanonical_pair_depth_iff _ _ _).mpr ⟨rfl, p.property⟩

/-- Every real deep hole belongs to one of the displayed 120 actual cosets. -/
theorem bwDeepHole_coset_coverage {z : Fin 16 → ℝ} (hz : IsDeepHole bwGammaSet z) :
    ∃ p : BWHoleIndex, z - bwCanonicalDeepHole p ∈ bwGammaSet := by
  let x := bwLeft z
  let y := bwRight z
  have hd : squaredDepth bwGammaSet (Fin.append x y) = 3 / 2 := by
    simpa only [x, y, append_bw_blocks] using (isDeepHole_bwGamma_iff_depth z).mp hz
  obtain ⟨hx, hy⟩ := bwGamma_deep_eligible hd
  obtain ⟨χ, hχ⟩ := bwEligible_has_canonical_class hx
  obtain ⟨ψ, hψ⟩ := bwEligible_has_canonical_class hy
  let s := x - bwCanonicalHole χ
  let t := y - bwCanonicalHole ψ
  obtain ⟨q, l, hl, hq⟩ := bw_coset_coverage (bwMAddSubgroup.sub_mem hψ hχ)
  let z₀ := Fin.append (bwCanonicalHole χ) (bwCanonicalHole ψ + bwRepresentative q)
  have htranslate : z - z₀ ∈ bwGammaSet := by
    apply (bwGamma_mem_iff _).mpr
    have hleft : bwLeft (z - z₀) = s := by
      funext i
      simp only [bwLeft, z₀, s, x, Pi.sub_apply, Fin.append_left]
    have hright : bwRight (z - z₀) = t - bwRepresentative q := by
      funext i
      simp only [bwRight, z₀, t, y, Pi.sub_apply, Pi.add_apply, Fin.append_right]
      ring
    rw [hleft, hright]
    refine ⟨hχ, bwMAddSubgroup.sub_mem hψ (bwRepresentative_mem q), ?_⟩
    have he : s - (t - bwRepresentative q) = -l := by
      change t - s = l + bwRepresentative q at hq
      rw [show s - (t - bwRepresentative q) = -(t - s) + bwRepresentative q by abel, hq]
      abel
    rw [he]
    exact dPlusSet_neg (by decide : Even 8) hl
  have hd₀ : squaredDepth bwGammaSet z₀ = 3 / 2 := by
    have h := squaredDepth_sub_of_subgroup bwGammaAddSubgroup z (z - z₀) htranslate
    rw [sub_sub_cancel] at h
    exact h.trans ((isDeepHole_bwGamma_iff_depth z).mp hz)
  obtain ⟨heq, hphase⟩ := (bwCanonical_pair_depth_iff χ ψ q).mp hd₀
  subst ψ
  exact ⟨⟨(χ, q), hphase⟩, htranslate⟩

/-- No two of the 120 representatives differ by a lattice vector. -/
theorem bwCanonicalDeepHole_distinct (p r : BWHoleIndex) :
    bwCanonicalDeepHole p - bwCanonicalDeepHole r ∈ bwGammaSet ↔ p = r := by
  constructor
  · intro h
    obtain ⟨hleft, _, hdiff⟩ := (bwGamma_mem_iff _).mp h
    have hc : p.val.1 = r.val.1 := by
      apply (bwCanonicalHole_sub_mem_iff _ _).mp
      have he : bwLeft (bwCanonicalDeepHole p - bwCanonicalDeepHole r) =
          bwCanonicalHole p.val.1 - bwCanonicalHole r.val.1 := by
        funext i
        simp only [bwLeft, bwCanonicalDeepHole, Pi.sub_apply, Fin.append_left]
      simpa only [he] using hleft
    have hq : bwRepresentative r.val.2 - bwRepresentative p.val.2 ∈ dPlusSet 8 := by
      have he : bwLeft (bwCanonicalDeepHole p - bwCanonicalDeepHole r) -
          bwRight (bwCanonicalDeepHole p - bwCanonicalDeepHole r) =
          bwRepresentative r.val.2 - bwRepresentative p.val.2 := by
        funext i
        simp only [bwLeft, bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply,
          Fin.append_left, Fin.append_right, hc]
        ring
      rwa [he] at hdiff
    have hqr := bwRepresentative_mod_e8_injective hq
    exact Subtype.ext (Prod.ext hc hqr.symm)
  · rintro rfl
    rw [sub_self]
    change (0 : Fin 16 → ℝ) ∈ bwGammaAddSubgroup
    exact bwGammaAddSubgroup.zero_mem

theorem bwDeepHole_coset_iff (z : Fin 16 → ℝ) :
    IsDeepHole bwGammaSet z ↔ ∃ p : BWHoleIndex, z - bwCanonicalDeepHole p ∈ bwGammaSet := by
  constructor
  · exact bwDeepHole_coset_coverage
  · rintro ⟨p, hp⟩
    apply (isDeepHole_bwGamma_iff_depth z).mpr
    have h := squaredDepth_add_of_subgroup bwGammaAddSubgroup
      (bwCanonicalDeepHole p) (z - bwCanonicalDeepHole p) hp
    rw [add_sub_cancel] at h
    exact h.trans ((isDeepHole_bwGamma_iff_depth _).mp (bwCanonicalDeepHole_deep p))

def bwDeepClassMap (p : BWHoleIndex) : DeepTranslationClasses bwGammaAddSubgroup :=
  ⟨(bwCanonicalDeepHole p : (Fin 16 → ℝ) ⧸ bwGammaAddSubgroup),
    bwCanonicalDeepHole p, bwCanonicalDeepHole_deep p, rfl⟩

theorem bwDeepClassMap_bijective : Function.Bijective bwDeepClassMap := by
  constructor
  · intro p r h
    apply (bwCanonicalDeepHole_distinct p r).mp
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, z, hz, hC⟩
    obtain ⟨p, hp⟩ := bwDeepHole_coset_coverage hz
    refine ⟨p, Subtype.ext ?_⟩
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hp).symm.trans hC

def bwDeepClassEquiv : BWHoleIndex ≃ DeepTranslationClasses bwGammaAddSubgroup :=
  Equiv.ofBijective bwDeepClassMap bwDeepClassMap_bijective

/-- Exactly 120 translation classes, in the actual unscaled lattice quotient. -/
theorem bwGamma_deep_translation_class_count :
    Nat.card (DeepTranslationClasses bwGammaAddSubgroup) = 120 := by
  rw [← Nat.card_congr bwDeepClassEquiv, Nat.card_eq_fintype_card, card_bwHoleIndex]

def scaleVecAddHom {n : ℕ} (c : ℝ) : (Fin n → ℝ) →+ (Fin n → ℝ) where
  toFun := scaleVec c
  map_zero' := by funext i; simp [scaleVec]
  map_add' := by intro x y; funext i; simp [scaleVec, mul_add]

def bw16AddSubgroup : AddSubgroup (Fin 16 → ℝ) :=
  bwGammaAddSubgroup.map (scaleVecAddHom (Real.sqrt 2))

theorem bw16AddSubgroup_coe : (bw16AddSubgroup : Set (Fin 16 → ℝ)) = bw16Set := by
  rw [bw16Set_eq_scaledGamma]
  rfl

theorem scaled_difference_mem_bw16 (x y : Fin 16 → ℝ) :
    scaleVec (Real.sqrt 2) x - scaleVec (Real.sqrt 2) y ∈ bw16Set ↔ x - y ∈ bwGammaSet := by
  rw [bw16Set_eq_scaledGamma]
  have he : scaleVec (Real.sqrt 2) x - scaleVec (Real.sqrt 2) y =
      scaleVec (Real.sqrt 2) (x - y) := by
    funext i
    simp only [scaleVec, Pi.sub_apply, mul_sub]
  rw [he]
  constructor
  · rintro ⟨z, hz, h⟩
    exact scaleVec_injective (Real.sqrt 2) sqrt_two_ne_zero h ▸ hz
  · intro h
    exact ⟨x - y, h, rfl⟩

def bw16CanonicalDeepHole (p : BWHoleIndex) : Fin 16 → ℝ :=
  scaleVec (Real.sqrt 2) (bwCanonicalDeepHole p)

theorem bw16CanonicalDeepHole_deep (p : BWHoleIndex) :
    IsDeepHole bw16Set (bw16CanonicalDeepHole p) := by
  rw [bw16Set_eq_scaledGamma]
  exact (isDeepHole_scaled_iff (Real.sqrt 2) sqrt_two_ne_zero bwGammaSet bwGamma_nonempty _).mpr
    (bwCanonicalDeepHole_deep p)

theorem bw16DeepHole_coset_coverage {z : Fin 16 → ℝ} (hz : IsDeepHole bw16Set z) :
    ∃ p : BWHoleIndex, z - bw16CanonicalDeepHole p ∈ bw16Set := by
  let y := scaleVec (Real.sqrt 2)⁻¹ z
  have he : scaleVec (Real.sqrt 2) y = z := scaleVec_inv (Real.sqrt 2) sqrt_two_ne_zero z
  have hy : IsDeepHole bwGammaSet y := by
    apply (isDeepHole_scaled_iff (Real.sqrt 2) sqrt_two_ne_zero bwGammaSet bwGamma_nonempty y).mp
    rw [he, ← bw16Set_eq_scaledGamma]
    exact hz
  obtain ⟨p, hp⟩ := bwDeepHole_coset_coverage hy
  refine ⟨p, ?_⟩
  rw [← he]
  exact (scaled_difference_mem_bw16 y (bwCanonicalDeepHole p)).mpr hp

theorem bw16CanonicalDeepHole_distinct (p r : BWHoleIndex) :
    bw16CanonicalDeepHole p - bw16CanonicalDeepHole r ∈ bw16Set ↔ p = r := by
  rw [bw16CanonicalDeepHole, bw16CanonicalDeepHole, scaled_difference_mem_bw16,
    bwCanonicalDeepHole_distinct]

def bw16DeepClassMap (p : BWHoleIndex) : DeepTranslationClasses bw16AddSubgroup :=
  ⟨(bw16CanonicalDeepHole p : (Fin 16 → ℝ) ⧸ bw16AddSubgroup), bw16CanonicalDeepHole p,
    by rw [bw16AddSubgroup_coe]; exact bw16CanonicalDeepHole_deep p, rfl⟩

theorem bw16DeepClassMap_bijective : Function.Bijective bw16DeepClassMap := by
  constructor
  · intro p r h
    apply (bw16CanonicalDeepHole_distinct p r).mp
    rw [← bw16AddSubgroup_coe]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, z, hz, hC⟩
    rw [bw16AddSubgroup_coe] at hz
    obtain ⟨p, hp⟩ := bw16DeepHole_coset_coverage hz
    refine ⟨p, Subtype.ext ?_⟩
    rw [← bw16AddSubgroup_coe] at hp
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hp).symm.trans hC

def bw16DeepClassEquiv : BWHoleIndex ≃ DeepTranslationClasses bw16AddSubgroup :=
  Equiv.ofBijective bw16DeepClassMap bw16DeepClassMap_bijective

/-- The literal Barnes–Wall normalization has exactly 120 classes as well. -/
theorem bw16_deep_translation_class_count :
    Nat.card (DeepTranslationClasses bw16AddSubgroup) = 120 := by
  rw [← Nat.card_congr bw16DeepClassEquiv, Nat.card_eq_fintype_card, card_bwHoleIndex]

/-! ## The literal union over all E8 roots in §7.5 -/

/-- A root of the actual E8 lattice, with its ordinary Euclidean squared norm. -/
def IsE8Root (r : Fin 8 → ℝ) : Prop := r ∈ dPlusSet 8 ∧ sqDist r 0 = 2

/-- The integer exponent of the paper's character.  Its integrality is proved
below, so taking the floor does not alter `2 * ⟨r,g⟩` on its stated domain. -/
def bwRootExponent (r g : Fin 8 → ℝ) : ℤ := ⌊2 * ∑ i, r i * g i⌋

def bwRootCharacter (r g : Fin 8 → ℝ) : ℝ := (-1 : ℝ) ^ bwRootExponent r g

theorem bwRootCharacter_eq_of_exponent (r g : Fin 8 → ℝ) (k : ℤ)
    (hk : (k : ℝ) = 2 * ∑ i, r i * g i) :
    bwRootCharacter r g = (-1 : ℝ) ^ k := by
  simp only [bwRootCharacter, bwRootExponent, ← hk, Int.floor_intCast]

def bwRootNumerator (χ : BWCharacter) (i : Fin 8) : ℤ :=
  if χ.val.2 = 0 then 2 * ((pairWord χ.val.1 i).val : ℤ)
  else 1 - 2 * ((pairWord χ.val.1 i).val : ℤ)

private def bwRootIntegerPart (χ : BWCharacter) (i : Fin 8) : ℤ :=
  if χ.val.2 = 0 then (pairWord χ.val.1 i).val else -((pairWord χ.val.1 i).val : ℤ)

private def bwRepresentativeNumerator (q : BWQuotient) (i : Fin 8) : ℤ :=
  ((linearWord3 q.1 i).val : ℤ) + 2 * bitUnit q.2 i

private def bwCanonicalPairExponent (χ : BWCharacter) (q : BWQuotient) : ℤ :=
  (∑ i, bwRootNumerator χ i * bwRepresentativeNumerator q i) / 2

set_option maxRecDepth 65536 in
/-- Exact finite integer arithmetic, subsequently related to all real lattice
points.  These finite calculations do not replace the geometric classification. -/
private theorem bwRoot_integer_arithmetic : ∀ χ : BWCharacter,
    Even (∑ i, bwRootIntegerPart χ i) ∧ (∑ i, bwRootNumerator χ i ^ 2) = 8 ∧
    ∀ q : BWQuotient,
      (∑ i, bwRootNumerator χ i * bwRepresentativeNumerator q i) =
        2 * bwCanonicalPairExponent χ q ∧
      (bwCanonicalPairExponent χ q : Binary) = bwCharacterEval χ q := by decide

def bwCanonicalRoot (χ : BWCharacter) : Fin 8 → ℝ :=
  fun i => (bwRootNumerator χ i : ℝ) / 2

theorem bwCanonicalRoot_half (χ : BWCharacter) :
    (fun i => bwCanonicalRoot χ i / 2) = bwCanonicalHole χ := by
  funext i
  by_cases h : χ.val.2 = 0 <;>
    simp only [bwCanonicalRoot, bwRootNumerator, bwCanonicalHole, h, if_true,
      if_false, halfWord, Pi.sub_apply, bwQuarterPoint, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, Int.cast_sub, Int.cast_one] <;> ring

theorem bwCanonicalRoot_isRoot (χ : BWCharacter) : IsE8Root (bwCanonicalRoot χ) := by
  refine ⟨⟨bwRootIntegerPart χ, (bwRoot_integer_arithmetic χ).1, ?_⟩, ?_⟩
  · by_cases h : χ.val.2 = 0
    · left
      funext i
      simp [bwCanonicalRoot, bwRootNumerator, bwRootIntegerPart, intVec, h]
    · right
      funext i
      simp only [bwCanonicalRoot, bwRootNumerator, bwRootIntegerPart, h, if_false,
        Int.cast_sub, Int.cast_one, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_neg]
      ring
  · calc
      sqDist (bwCanonicalRoot χ) 0 = ((∑ i, bwRootNumerator χ i ^ 2 : ℤ) : ℝ) / 4 := by
        simp only [sqDist, Pi.zero_apply, sub_zero, bwCanonicalRoot, Int.cast_sum,
          Int.cast_pow, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 := by rw [(bwRoot_integer_arithmetic χ).2.1]; norm_num

private theorem e8_sqNorm_even {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) :
    ∃ k : ℤ, Even k ∧ sqDist x 0 = (k : ℝ) := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · exact ⟨∑ i, z i ^ 2, even_integer_sqSum z hz, by simp [sqDist, intVec]⟩
  · refine ⟨(∑ i, z i ^ 2) + (∑ i, z i) + 2,
      ((even_integer_sqSum z hz).add hz).add (by decide), ?_⟩
    have hi (i : Fin 8) : ((z i : ℝ) + 1 / 2) ^ 2 = (z i : ℝ) ^ 2 + z i + 1 / 4 := by ring
    simp only [sqDist, Pi.zero_apply, sub_zero, hi, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_pow,
      Int.cast_ofNat]
    ring

private theorem e8_pairing_even {x y : Fin 8 → ℝ}
    (hx : x ∈ dPlusSet 8) (hy : y ∈ dPlusSet 8) :
    ∃ k : ℤ, Even k ∧ 2 * ∑ i, x i * y i = (k : ℝ) := by
  obtain ⟨a, ha, hxa⟩ := e8_sqNorm_even hx
  obtain ⟨b, hb, hyb⟩ := e8_sqNorm_even hy
  obtain ⟨c, hc, hzc⟩ := e8_sqNorm_even (dPlusSet_sub (by decide : Even 8) hx hy)
  refine ⟨a + b - c, (ha.add hb).sub hc, ?_⟩
  have he : sqDist (x - y) 0 = sqDist x 0 + sqDist y 0 - 2 * ∑ i, x i * y i := by
    simp only [sqDist, Pi.sub_apply, Pi.zero_apply, sub_zero, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  push_cast
  linarith

set_option maxRecDepth 65536 in
private theorem bwM_pairing_even {x y : Fin 8 → ℝ}
    (hx : x ∈ bwMSet) (hy : y ∈ bwMSet) :
    ∃ k : ℤ, Even k ∧ 4 * ∑ i, x i * y i = (k : ℝ) := by
  rcases hx with ⟨u, ⟨a, ha⟩, rfl⟩
  rcases hy with ⟨v, ⟨b, hb⟩, rfl⟩
  refine ⟨∑ i, u i * v i, ?_, ?_⟩
  · apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sum, Int.cast_mul]
    have hu (i) : (u i : Binary) = affineWord3 a i := congrFun ha i
    have hv (i) : (v i : Binary) = affineWord3 b i := congrFun hb i
    simp_rw [hu, hv]
    exact (show ∀ a b : AffineCoefficients3,
      (∑ i, affineWord3 a i * affineWord3 b i) = 0 by decide) a b
  · simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Every actual E8 root half belongs to one of the fifteen classes; no
restriction to selected root representatives is made. -/
theorem e8Root_half_has_canonical_class {r : Fin 8 → ℝ} (hr : IsE8Root r) :
    ∃ χ : BWCharacter, (fun i => r i / 2) - bwCanonicalHole χ ∈ bwMSet := by
  let x : Fin 8 → ℝ := fun i => r i / 2
  change ∃ χ : BWCharacter, x - bwCanonicalHole χ ∈ bwMSet
  have hnorm : sqDist x 0 = 1 / 2 := by
    have h : sqDist x 0 = sqDist r 0 / 4 := by
      simp only [sqDist, Pi.zero_apply, sub_zero, Finset.sum_div, x]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h, hr.2]
    norm_num
  have hnot : x ∉ bwMSet := by
    intro hx
    have hmem : Fin.append x x ∈ bwGammaSet := (bwGamma_append_iff x x).mpr
      ⟨hx, hx, by simpa only [sub_self] using zero_mem_dPlusSet 8⟩
    have hd : sqDist (Fin.append x x) 0 = 1 := by
      rw [show (0 : Fin 16 → ℝ) = Fin.append (0 : Fin 8 → ℝ) (0 : Fin 8 → ℝ) by
        funext i
        refine Fin.addCases
          (motive := fun k : Fin (8 + 8) =>
            (0 : ℝ) = Fin.append (0 : Fin 8 → ℝ) (0 : Fin 8 → ℝ) k)
          (fun j : Fin 8 => ?_) (fun j : Fin 8 => ?_) i <;>
          simp only [Fin.append_left, Fin.append_right, Pi.zero_apply],
        sqDist_append, hnorm]
      norm_num
    have hne : Fin.append x x ≠ 0 := by
      intro h
      rw [h] at hd
      norm_num [sqDist] at hd
    have := bwGamma_sqNorm_lower hmem hne
    linarith
  have hsum : IntegerSum8 x := by
    obtain ⟨k, ⟨a, ha⟩, hk⟩ := e8_even_integerSum hr.1
    refine ⟨a, ?_⟩
    change (∑ i, r i / 2) = (a : ℝ)
    rw [← Finset.sum_div, hk, ha]
    push_cast
    ring
  rcases hr.1 with ⟨z, hz, he | he⟩
  · have hg : HalfIntegerGrid x := fun i => ⟨z i, by simp [x, he, intVec]⟩
    obtain ⟨m, c, hc⟩ := halfGrid_integer_halfWord hg
    obtain ⟨k, hk⟩ := hsum
    have hw : (binaryWeight c : ℤ) = 2 * (k - ∑ i, m i) := by
      have hs : (k : ℝ) = ((∑ i, m i : ℤ) : ℝ) + (binaryWeight c : ℝ) / 2 := by
        rw [← hk, hc]
        simp only [Pi.add_apply, Finset.sum_add_distrib, intVec, ← Int.cast_sum,
          sum_halfWord]
      exact_mod_cast (show (binaryWeight c : ℝ) =
        2 * ((k : ℝ) - ((∑ i, m i : ℤ) : ℝ)) by linarith)
    have heven : Even (binaryWeight c) := by
      apply (Int.even_coe_nat _).mp
      rw [hw]
      exact even_two.mul_right _
    obtain ⟨j, hj, _⟩ := even_word_coset_representatives c heven
    have hj0 : j ≠ 0 := by
      intro hj0
      apply hnot
      rw [hc]
      exact bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM (by
        simpa only [hj0, pairWord_zero, Pi.zero_apply, sub_zero] using hj))
    let χ : BWCharacter := ⟨(j, 0), fun h => hj0 (congrArg Prod.fst h)⟩
    refine ⟨χ, ?_⟩
    rw [hc]
    simpa only [bwCanonicalHole, χ, if_pos rfl, ite_true, add_sub_assoc] using
      bwMSet_add (intVec_mem_bwM m) ((halfWord_sub_mem_bwM_iff c (pairWord j)).mpr hj)
  · have hg : QuarterGrid8 x := by
      intro i
      refine ⟨z i, ?_⟩
      simp only [x, he]
      ring
    obtain ⟨m, c, hce, hc⟩ := quarterGrid_integer_normalForm hg hsum
    obtain ⟨j, hj, _⟩ := even_word_coset_representatives c hce
    let χ : BWCharacter := ⟨(j, 1), by intro h; have := congrArg Prod.snd h; simpa using this⟩
    refine ⟨χ, ?_⟩
    have h := bwMAddSubgroup.sub_mem (intVec_mem_bwM m)
      ((halfWord_sub_mem_bwM_iff c (pairWord j)).mpr hj)
    change intVec m - (halfWord c - halfWord (pairWord j)) ∈ bwMSet at h
    convert h using 1
    rw [hc]
    simp only [bwCanonicalHole, χ, one_ne_zero, if_false]
    abel

private theorem bwCanonicalRoot_pairing (χ : BWCharacter) (q : BWQuotient) :
    2 * ∑ i, bwCanonicalRoot χ i * bwRepresentative q i =
      (bwCanonicalPairExponent χ q : ℝ) := by
  have hv (i) : (bwRepresentativeNumerator q i : ℝ) = 2 * bwRepresentative q i := by
    simp only [bwRepresentativeNumerator, bwRepresentative, Pi.add_apply, halfWord,
      intVec, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  calc
    _ = ((∑ i, bwRootNumerator χ i * bwRepresentativeNumerator q i : ℤ) : ℝ) / 2 := by
      simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div, Finset.mul_sum, hv,
        bwCanonicalRoot]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [((bwRoot_integer_arithmetic χ).2.2 q).1]
      push_cast
      ring

/-- The literal pairing gives precisely the binary quotient character, for an
arbitrary actual root and arbitrary vector of M. -/
theorem bwRootExponent_mod_two {r g : Fin 8 → ℝ} (hr : IsE8Root r)
    (hg : g ∈ bwMSet) (χ : BWCharacter)
    (hχ : (fun i => r i / 2) - bwCanonicalHole χ ∈ bwMSet)
    (q : BWQuotient) (hq : g - bwRepresentative q ∈ dPlusSet 8) :
    (bwRootExponent r g : ℝ) = 2 * ∑ i, r i * g i ∧
      (bwRootExponent r g : Binary) = bwCharacterEval χ q := by
  let m := (fun i => r i / 2) - bwCanonicalHole χ
  obtain ⟨a, ha, hea⟩ := e8_pairing_even (bwCanonicalRoot_isRoot χ).1 hq
  obtain ⟨b, hb, heb⟩ := bwM_pairing_even hχ hg
  change 4 * ∑ i, m i * g i = (b : ℝ) at heb
  let k : ℤ := a + bwCanonicalPairExponent χ q + b
  have he : 2 * ∑ i, r i * g i = (k : ℝ) := by
    have hi (i) : r i = bwCanonicalRoot χ i + 2 * m i := by
      have h := congrFun (bwCanonicalRoot_half χ) i
      dsimp [m]
      change bwCanonicalRoot χ i / 2 = bwCanonicalHole χ i at h
      linarith
    have hid : 2 * ∑ i, r i * g i =
        (2 * ∑ i, bwCanonicalRoot χ i * (g - bwRepresentative q) i) +
        (2 * ∑ i, bwCanonicalRoot χ i * bwRepresentative q i) +
        (4 * ∑ i, m i * g i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.sub_apply, hi]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hid, hea, bwCanonicalRoot_pairing, heb]
    simp only [k, Int.cast_add]
  have hk : bwRootExponent r g = k := by simp only [bwRootExponent, he, Int.floor_intCast]
  refine ⟨by rw [hk]; exact he.symm, ?_⟩
  rw [hk]
  simp only [k, Int.cast_add, ha.intCast_zmod_two, hb.intCast_zmod_two, zero_add, add_zero]
  exact ((bwRoot_integer_arithmetic χ).2.2 q).2

theorem bwRootExponent_integral {r g : Fin 8 → ℝ} (hr : IsE8Root r) (hg : g ∈ bwMSet) :
    (bwRootExponent r g : ℝ) = 2 * ∑ i, r i * g i := by
  obtain ⟨χ, hχ⟩ := e8Root_half_has_canonical_class hr
  obtain ⟨q, l, hl, he⟩ := bw_coset_coverage hg
  exact (bwRootExponent_mod_two hr hg χ hχ q (by rw [he, add_sub_cancel_right]; exact hl)).1

theorem bwRootExponent_eq_euclidean_pairing {r g : Fin 8 → ℝ}
    (hr : IsE8Root r) (hg : g ∈ bwMSet) :
    (bwRootExponent r g : ℝ) = 2 *
      inner ℝ (WithLp.toLp 2 r : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 g) := by
  rw [bwRootExponent_integral hr hg]
  simp [EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

theorem bwRootCharacter_eq_neg_one_iff {r g : Fin 8 → ℝ} (hr : IsE8Root r)
    (hg : g ∈ bwMSet) (χ : BWCharacter)
    (hχ : (fun i => r i / 2) - bwCanonicalHole χ ∈ bwMSet)
    (q : BWQuotient) (hq : g - bwRepresentative q ∈ dPlusSet 8) :
    bwRootCharacter r g = -1 ↔ bwCharacterEval χ q = 1 := by
  have h := (bwRootExponent_mod_two hr hg χ hχ q hq).2
  have he : Even (bwRootExponent r g) ↔ bwCharacterEval χ q = 0 := by
    rw [← ZMod.intCast_eq_zero_iff_even, h]
  simp only [bwRootCharacter, neg_one_zpow_eq_ite, he]
  rcases binary_eq_zero_or_one (bwCharacterEval χ q) with h0 | h0 <;> norm_num [h0]

/-- The complete union in §7.5, indexed by every actual E8 root and using the
literal character `(-1)^(2⟨r,t-s⟩)`. -/
theorem bwGamma_deepHole_iff_root_union (x y : Fin 8 → ℝ) :
    IsDeepHole bwGammaSet (Fin.append x y) ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧
        x = (fun i => r i / 2) + s ∧ y = (fun i => r i / 2) + t ∧
        bwRootCharacter r (t - s) = -1 := by
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := bwDeepHole_coset_coverage hz
    obtain ⟨hs, ht, hd⟩ := (bwGamma_mem_iff _).mp hp
    let s := x - bwCanonicalHole p.val.1
    let t := y - bwCanonicalHole p.val.1
    have hs' : s ∈ bwMSet := by
      have hleft : bwLeft (Fin.append x y - bwCanonicalDeepHole p) = s := by
        funext i
        simp only [bwLeft, bwCanonicalDeepHole, Pi.sub_apply, Fin.append_left, s]
      simpa only [hleft] using hs
    have ht' : t - bwRepresentative p.val.2 ∈ bwMSet := by
      convert ht using 1
      funext i
      simp only [bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply, Fin.append_right, t]
      ring
    have htM : t ∈ bwMSet := by
      simpa only [sub_add_cancel] using bwMSet_add ht' (bwRepresentative_mem p.val.2)
    have hq : (t - s) - bwRepresentative p.val.2 ∈ dPlusSet 8 := by
      convert dPlusSet_neg (by decide : Even 8) hd using 1
      funext i
      simp only [bwLeft, bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply,
        Pi.neg_apply, Fin.append_left, Fin.append_right, s, t]
      ring
    refine ⟨bwCanonicalRoot p.val.1, bwCanonicalRoot_isRoot _, s, t, hs', htM, ?_, ?_, ?_⟩
    · rw [bwCanonicalRoot_half]; dsimp [s]; abel
    · rw [bwCanonicalRoot_half]; dsimp [t]; abel
    · apply (bwRootCharacter_eq_neg_one_iff (bwCanonicalRoot_isRoot _)
        (bwMAddSubgroup.sub_mem htM hs') p.val.1 ?_ p.val.2 hq).mpr p.property
      rw [bwCanonicalRoot_half, sub_self]
      exact bwMSet_zero
  · rintro ⟨r, hr, s, t, hs, ht, hx, hy, hphase⟩
    obtain ⟨χ, hχ⟩ := e8Root_half_has_canonical_class hr
    obtain ⟨q, l, hl, he⟩ := bw_coset_coverage (bwMAddSubgroup.sub_mem ht hs)
    have hq : (t - s) - bwRepresentative q ∈ dPlusSet 8 := by
      rw [he, add_sub_cancel_right]
      exact hl
    have hp := (bwRootCharacter_eq_neg_one_iff hr (bwMAddSubgroup.sub_mem ht hs)
      χ hχ q hq).mp hphase
    apply (bwDeepHole_coset_iff _).mpr
    refine ⟨⟨(χ, q), hp⟩, (bwGamma_mem_iff _).mpr ?_⟩
    constructor
    · convert bwMSet_add hχ hs using 1
      funext i
      simp only [bwLeft, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply, Fin.append_left, hx]
      ring
    constructor
    · have hm : ((fun i => r i / 2) - bwCanonicalHole χ + t) - bwRepresentative q ∈ bwMSet :=
        bwMAddSubgroup.sub_mem (bwMSet_add hχ ht) (bwRepresentative_mem q)
      convert hm using 1
      funext i
      simp only [bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply, Fin.append_right, hy]
      ring
    · convert dPlusSet_neg (by decide : Even 8) hq using 1
      funext i
      simp only [bwLeft, bwRight, bwCanonicalDeepHole, Pi.sub_apply, Pi.add_apply,
        Pi.neg_apply, Fin.append_left, Fin.append_right, hx, hy]
      ring

theorem bwGamma_gaussian_equality_iff_root_union {α : ℝ} (hα : 0 < α) (x y : Fin 8 → ℝ) :
    setGaussian bwGammaSet α (Fin.append x y) = bwGammaMinimum α ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧
        x = (fun i => r i / 2) + s ∧ y = (fun i => r i / 2) + t ∧
        bwRootCharacter r (t - s) = -1 := by
  rw [← isColdSpot_bwGamma_iff_value hα, coldSpot_bwGamma_iff_deepHole hα,
    bwGamma_deepHole_iff_root_union]

/-- The identical full equality locus after the paper's √2 normalization. -/
theorem bw16_coldSpot_iff_root_union {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bw16Set α z ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  let w := scaleVec (Real.sqrt 2)⁻¹ z
  have hw : scaleVec (Real.sqrt 2) w = z := scaleVec_inv _ sqrt_two_ne_zero z
  have hdeep : IsColdSpot bw16Set α z ↔ IsDeepHole bwGammaSet w := by
    rw [coldSpot_bw16_iff_deepHole hα, ← hw, bw16Set_eq_scaledGamma,
      isDeepHole_scaled_iff _ sqrt_two_ne_zero _ bwGamma_nonempty]
  rw [hdeep, ← append_bw_blocks w, bwGamma_deepHole_iff_root_union]
  constructor
  · rintro ⟨r, hr, s, t, hs, ht, hx, hy, hp⟩
    refine ⟨r, hr, s, t, hs, ht, hp, ?_⟩
    rw [← hx, ← hy, append_bw_blocks, hw]
  · rintro ⟨r, hr, s, t, hs, ht, hp, hz⟩
    have he : w = Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t) :=
      scaleVec_injective _ sqrt_two_ne_zero (hw.trans hz)
    exact ⟨r, hr, s, t, hs, ht, by rw [he, bwLeft_append],
      by rw [he, bwRight_append], hp⟩

theorem bw16_deepHole_iff_root_union (z : Fin 16 → ℝ) :
    IsDeepHole bw16Set z ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  rw [← coldSpot_bw16_iff_deepHole (α := 1) (by norm_num),
    bw16_coldSpot_iff_root_union (by norm_num)]

theorem bw16_gaussian_equality_iff_root_union {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    setGaussian bw16Set α z = bwGammaMinimum (2 * α) ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  have hv : IsColdSpot bw16Set α z ↔ setGaussian bw16Set α z = bwGammaMinimum (2 * α) := by
    obtain ⟨hmin, w, hw⟩ := bw16_gaussian_minimum hα
    constructor
    · intro h
      have hz := h w
      rw [hw] at hz
      exact le_antisymm hz (hmin z)
    · intro hz y
      rw [hz]
      exact hmin y
  rw [← hv, bw16_coldSpot_iff_root_union hα]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwDeepHole_coset_iff
#print axioms PaperVerification.ColdSpots.bwGamma_deep_translation_class_count
#print axioms PaperVerification.ColdSpots.bw16_deep_translation_class_count
#print axioms PaperVerification.ColdSpots.bwRootExponent_integral
#print axioms PaperVerification.ColdSpots.bwGamma_deepHole_iff_root_union
#print axioms PaperVerification.ColdSpots.bwGamma_gaussian_equality_iff_root_union
#print axioms PaperVerification.ColdSpots.bw16_coldSpot_iff_root_union
#print axioms PaperVerification.ColdSpots.bw16_deepHole_iff_root_union
#print axioms PaperVerification.ColdSpots.bw16_gaussian_equality_iff_root_union
