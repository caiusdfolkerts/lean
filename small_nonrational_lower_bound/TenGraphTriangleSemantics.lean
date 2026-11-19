module

public import TenGraphTriangles
public import TenGraphMask
public import LiteralMaskGeometry
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-!
# Exact semantics of the ten-vertex triangle counter

The finite codec is a bijection with all three-element vertex subsets.
Its three pair bits are exactly the two-element subsets of that triangle.
Consequently the raw counter counts ordinary graph triangles, including
for graph masks obtained from an arbitrary actual polytope.
-/

noncomputable section
namespace Papers.RationalityTen.TenGraphTriangleSemantics

open Finset LiteralMaskGeometry TenGraphEdges TenGraphTriangles FiniteChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def triangleSet (i : Fin 120) : Finset (Fin 10) := maskSet (vertices i)

def indexOfSet (T : Finset (Fin 10)) : Fin 120 :=
  let ordered := (List.finRange 10).filter fun v => decide (v ∈ T)
  indexOf ⟨ordered[0]!, ordered[1]!, ordered[2]!⟩

def codecCheck (code : ℕ) : Bool :=
  let i := Fin.ofNat 120 code
  decide ((triangleSet i).card = 3 ∧ indexOfSet (triangleSet i) = i ∧
    pairs i < 2 ^ 45 ∧ ∀ e : Fin 45,
      (pairs i).testBit e.val = true ↔
        maskSet (edgeMask e) ∈ (triangleSet i).powersetCard 2)

private theorem codec_000 : Interval codecCheck 0 4 :=
  interval_of_check codecCheck 0 4 (by decide +kernel)

private theorem codec_004 : Interval codecCheck 4 8 :=
  interval_of_check codecCheck 4 4 (by decide +kernel)

private theorem codec_008 : Interval codecCheck 8 12 :=
  interval_of_check codecCheck 8 4 (by decide +kernel)

private theorem codec_012 : Interval codecCheck 12 16 :=
  interval_of_check codecCheck 12 4 (by decide +kernel)

private theorem codec_016 : Interval codecCheck 16 20 :=
  interval_of_check codecCheck 16 4 (by decide +kernel)

private theorem codec_020 : Interval codecCheck 20 24 :=
  interval_of_check codecCheck 20 4 (by decide +kernel)

private theorem codec_024 : Interval codecCheck 24 28 :=
  interval_of_check codecCheck 24 4 (by decide +kernel)

private theorem codec_028 : Interval codecCheck 28 32 :=
  interval_of_check codecCheck 28 4 (by decide +kernel)

private theorem codec_032 : Interval codecCheck 32 36 :=
  interval_of_check codecCheck 32 4 (by decide +kernel)

private theorem codec_036 : Interval codecCheck 36 40 :=
  interval_of_check codecCheck 36 4 (by decide +kernel)

private theorem codec_040 : Interval codecCheck 40 44 :=
  interval_of_check codecCheck 40 4 (by decide +kernel)

private theorem codec_044 : Interval codecCheck 44 48 :=
  interval_of_check codecCheck 44 4 (by decide +kernel)

private theorem codec_048 : Interval codecCheck 48 52 :=
  interval_of_check codecCheck 48 4 (by decide +kernel)

private theorem codec_052 : Interval codecCheck 52 56 :=
  interval_of_check codecCheck 52 4 (by decide +kernel)

private theorem codec_056 : Interval codecCheck 56 60 :=
  interval_of_check codecCheck 56 4 (by decide +kernel)

private theorem codec_060 : Interval codecCheck 60 64 :=
  interval_of_check codecCheck 60 4 (by decide +kernel)

private theorem codec_064 : Interval codecCheck 64 68 :=
  interval_of_check codecCheck 64 4 (by decide +kernel)

private theorem codec_068 : Interval codecCheck 68 72 :=
  interval_of_check codecCheck 68 4 (by decide +kernel)

private theorem codec_072 : Interval codecCheck 72 76 :=
  interval_of_check codecCheck 72 4 (by decide +kernel)

private theorem codec_076 : Interval codecCheck 76 80 :=
  interval_of_check codecCheck 76 4 (by decide +kernel)

private theorem codec_080 : Interval codecCheck 80 84 :=
  interval_of_check codecCheck 80 4 (by decide +kernel)

private theorem codec_084 : Interval codecCheck 84 88 :=
  interval_of_check codecCheck 84 4 (by decide +kernel)

private theorem codec_088 : Interval codecCheck 88 92 :=
  interval_of_check codecCheck 88 4 (by decide +kernel)

private theorem codec_092 : Interval codecCheck 92 96 :=
  interval_of_check codecCheck 92 4 (by decide +kernel)

private theorem codec_096 : Interval codecCheck 96 100 :=
  interval_of_check codecCheck 96 4 (by decide +kernel)

private theorem codec_100 : Interval codecCheck 100 104 :=
  interval_of_check codecCheck 100 4 (by decide +kernel)

private theorem codec_104 : Interval codecCheck 104 108 :=
  interval_of_check codecCheck 104 4 (by decide +kernel)

private theorem codec_108 : Interval codecCheck 108 112 :=
  interval_of_check codecCheck 108 4 (by decide +kernel)

private theorem codec_112 : Interval codecCheck 112 116 :=
  interval_of_check codecCheck 112 4 (by decide +kernel)

private theorem codec_116 : Interval codecCheck 116 120 :=
  interval_of_check codecCheck 116 4 (by decide +kernel)

private theorem codec_join_004_012 : Interval codecCheck 4 12 :=
  interval_append codecCheck 4 8 12 codec_004 codec_008

private theorem codec_join_000_012 : Interval codecCheck 0 12 :=
  interval_append codecCheck 0 4 12 codec_000 codec_join_004_012

private theorem codec_join_012_020 : Interval codecCheck 12 20 :=
  interval_append codecCheck 12 16 20 codec_012 codec_016

private theorem codec_join_020_028 : Interval codecCheck 20 28 :=
  interval_append codecCheck 20 24 28 codec_020 codec_024

private theorem codec_join_012_028 : Interval codecCheck 12 28 :=
  interval_append codecCheck 12 20 28 codec_join_012_020 codec_join_020_028

private theorem codec_join_000_028 : Interval codecCheck 0 28 :=
  interval_append codecCheck 0 12 28 codec_join_000_012 codec_join_012_028

private theorem codec_join_028_036 : Interval codecCheck 28 36 :=
  interval_append codecCheck 28 32 36 codec_028 codec_032

private theorem codec_join_036_044 : Interval codecCheck 36 44 :=
  interval_append codecCheck 36 40 44 codec_036 codec_040

private theorem codec_join_028_044 : Interval codecCheck 28 44 :=
  interval_append codecCheck 28 36 44 codec_join_028_036 codec_join_036_044

private theorem codec_join_044_052 : Interval codecCheck 44 52 :=
  interval_append codecCheck 44 48 52 codec_044 codec_048

private theorem codec_join_052_060 : Interval codecCheck 52 60 :=
  interval_append codecCheck 52 56 60 codec_052 codec_056

private theorem codec_join_044_060 : Interval codecCheck 44 60 :=
  interval_append codecCheck 44 52 60 codec_join_044_052 codec_join_052_060

private theorem codec_join_028_060 : Interval codecCheck 28 60 :=
  interval_append codecCheck 28 44 60 codec_join_028_044 codec_join_044_060

private theorem codec_join_000_060 : Interval codecCheck 0 60 :=
  interval_append codecCheck 0 28 60 codec_join_000_028 codec_join_028_060

private theorem codec_join_064_072 : Interval codecCheck 64 72 :=
  interval_append codecCheck 64 68 72 codec_064 codec_068

private theorem codec_join_060_072 : Interval codecCheck 60 72 :=
  interval_append codecCheck 60 64 72 codec_060 codec_join_064_072

private theorem codec_join_072_080 : Interval codecCheck 72 80 :=
  interval_append codecCheck 72 76 80 codec_072 codec_076

private theorem codec_join_080_088 : Interval codecCheck 80 88 :=
  interval_append codecCheck 80 84 88 codec_080 codec_084

private theorem codec_join_072_088 : Interval codecCheck 72 88 :=
  interval_append codecCheck 72 80 88 codec_join_072_080 codec_join_080_088

private theorem codec_join_060_088 : Interval codecCheck 60 88 :=
  interval_append codecCheck 60 72 88 codec_join_060_072 codec_join_072_088

private theorem codec_join_088_096 : Interval codecCheck 88 96 :=
  interval_append codecCheck 88 92 96 codec_088 codec_092

private theorem codec_join_096_104 : Interval codecCheck 96 104 :=
  interval_append codecCheck 96 100 104 codec_096 codec_100

private theorem codec_join_088_104 : Interval codecCheck 88 104 :=
  interval_append codecCheck 88 96 104 codec_join_088_096 codec_join_096_104

private theorem codec_join_104_112 : Interval codecCheck 104 112 :=
  interval_append codecCheck 104 108 112 codec_104 codec_108

private theorem codec_join_112_120 : Interval codecCheck 112 120 :=
  interval_append codecCheck 112 116 120 codec_112 codec_116

private theorem codec_join_104_120 : Interval codecCheck 104 120 :=
  interval_append codecCheck 104 112 120 codec_join_104_112 codec_join_112_120

private theorem codec_join_088_120 : Interval codecCheck 88 120 :=
  interval_append codecCheck 88 104 120 codec_join_088_104 codec_join_104_120

private theorem codec_join_060_120 : Interval codecCheck 60 120 :=
  interval_append codecCheck 60 88 120 codec_join_060_088 codec_join_088_120

private theorem codec_join_000_120 : Interval codecCheck 0 120 :=
  interval_append codecCheck 0 60 120 codec_join_000_060 codec_join_060_120

private theorem codec_complete : Interval codecCheck 0 120 := codec_join_000_120

private theorem codec_correct (i : Fin 120) :
    (triangleSet i).card = 3 ∧ indexOfSet (triangleSet i) = i ∧
      pairs i < 2 ^ 45 ∧ ∀ e : Fin 45,
        (pairs i).testBit e.val = true ↔
          maskSet (edgeMask e) ∈ (triangleSet i).powersetCard 2 := by
  simpa only [codecCheck, Fin.ofNat_val_eq_self, decide_eq_true_eq] using
    codec_complete i.val (Nat.zero_le _) i.isLt

theorem triangleSet_card (i : Fin 120) : (triangleSet i).card = 3 :=
  (codec_correct i).1

theorem triangleSet_injective : Function.Injective triangleSet := by
  intro i j hij
  have h := congrArg indexOfSet hij
  simpa only [(codec_correct i).2.1, (codec_correct j).2.1] using h

theorem triangleSet_surjective (T : Finset (Fin 10)) (hT : T.card = 3) :
    ∃ i : Fin 120, triangleSet i = T := by
  let U := (Finset.univ : Finset (Fin 10)).powersetCard 3
  let f : Fin 120 → U := fun i =>
    ⟨triangleSet i, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, triangleSet_card i⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact triangleSet_injective (congrArg Subtype.val hij)
  have hcard : Fintype.card (Fin 120) = Fintype.card U := by
    simp only [Fintype.card_fin, Fintype.card_coe, U, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
    decide
  have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  obtain ⟨i, hi⟩ := hbij.surjective
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem pairs_membership (i : Fin 120) (e : Fin 45) :
    (pairs i).testBit e.val = true ↔
      maskSet (edgeMask e) ∈ (triangleSet i).powersetCard 2 :=
  (codec_correct i).2.2.2 e

theorem pair_membership (e : Fin 45) (v : Fin 10) :
    v ∈ maskSet (edgeMask e) ↔ incidence e v = true := by
  have checked : ∀ e : Fin 45, ∀ v : Fin 10,
      (edgeMask e).testBit v.val = incidence e v := by decide +kernel
  rw [mem_maskSet, checked e v]

theorem pairSet_surjective (S : Finset (Fin 10)) (hS : S.card = 2) :
    ∃ e : Fin 45, maskSet (edgeMask e) = S := by
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hS
  refine ⟨encode a b, ?_⟩
  rw [hS]
  ext v
  rw [pair_membership, encode_incidence a b v hab]
  simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]

theorem land_zero_iff (complement mask : ℕ) (hmask : mask < 2 ^ 45) :
    Nat.land complement mask = 0 ↔
      ∀ e : Fin 45, mask.testBit e.val = true →
        complement.testBit e.val = false := by
  constructor
  · intro h e hbit
    have hh := congrArg (fun m : ℕ => m.testBit e.val) h
    change (complement &&& mask).testBit e.val = (0 : ℕ).testBit e.val at hh
    simpa only [Nat.testBit_and, hbit, Bool.and_true, Nat.zero_testBit] using hh
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro j
    change (complement &&& mask).testBit j = false
    rw [Nat.testBit_and]
    by_cases hj : j < 45
    · by_cases hbit : mask.testBit j = true
      · rw [hbit, h ⟨j, hj⟩ hbit]
        rfl
      · have hz : mask.testBit j = false := Bool.eq_false_iff.mpr hbit
        rw [hz, Bool.and_false]
    · have hpow : 2 ^ 45 ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (hmask.trans_le hpow), Bool.and_false]

theorem triangle_allowed_iff (edges : Finset (Finset (Fin 10))) (complement : ℕ)
    (hbits : ∀ e : Fin 45, complement.testBit e.val = false ↔
      maskSet (edgeMask e) ∈ edges) (i : Fin 120) :
    Nat.land complement (pairs i) = 0 ↔ (triangleSet i).powersetCard 2 ⊆ edges := by
  rw [land_zero_iff complement (pairs i) (codec_correct i).2.2.1]
  constructor
  · intro h S hS
    obtain ⟨e, rfl⟩ := pairSet_surjective S (Finset.mem_powersetCard.mp hS).2
    exact (hbits e).mp (h e ((pairs_membership i e).mpr hS))
  · intro h e he
    exact (hbits e).mpr (h ((pairs_membership i e).mp he))

/-- The raw120-triangle counter equals the ordinary finite graph count.
Only the explicit agreement of the45 unordered pair bits is required. -/
theorem count_eq_triangle_card (edges : Finset (Finset (Fin 10))) (complement : ℕ)
    (hbits : ∀ e : Fin 45, complement.testBit e.val = false ↔
      maskSet (edgeMask e) ∈ edges) :
    count complement =
      (((Finset.univ : Finset (Fin 10)).powersetCard 3).filter
        fun T => T.powersetCard 2 ⊆ edges).card := by
  let I : Finset (Fin 120) := Finset.univ.filter
    fun i => Nat.land complement (pairs i) = 0
  have hcount : count complement = I.card := by
    rw [count, ← List.toFinset_card_of_nodup ((List.nodup_finRange 120).filter _)]
    apply congrArg Finset.card
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange,
      decide_eq_true_eq, I, Finset.mem_filter, Finset.mem_univ, true_and]
  have himage : I.image triangleSet =
      ((Finset.univ : Finset (Fin 10)).powersetCard 3).filter
        fun T => T.powersetCard 2 ⊆ edges := by
    ext T
    constructor
    · intro hT
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hT
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, triangleSet_card i⟩,
          (triangle_allowed_iff edges complement hbits i).mp
            (Finset.mem_filter.mp hi).2⟩
    · intro hT
      obtain ⟨hT, hedges⟩ := Finset.mem_filter.mp hT
      obtain ⟨i, rfl⟩ := triangleSet_surjective T (Finset.mem_powersetCard.mp hT).2
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (triangle_allowed_iff edges complement hbits i).mpr hedges⟩, rfl⟩
  calc
    count complement = I.card := hcount
    _ = (I.image triangleSet).card :=
      (Finset.card_image_of_injective _ triangleSet_injective).symm
    _ = _ := congrArg Finset.card himage

#print axioms count_eq_triangle_card

end Papers.RationalityTen.TenGraphTriangleSemantics
