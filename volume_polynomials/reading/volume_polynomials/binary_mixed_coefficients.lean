module

public import VolumePolynomials.MixedVolumeMultilinearMap
public import VolumePolynomials.BinaryPolynomial
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Binomial coefficients and actual repeated mixed volumes

Minkowski multilinearity over the nonnegative reals expands the diagonal
volume into a sum over subsets. Permutation symmetry makes each summand
depend only on the subset cardinality, and counting the subsets supplies
the exact binomial coefficient. No normalization is postulated.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.BinaryMixed

def firstPattern (d i : ℕ) (j : Fin d) : Bool := decide (j.val < i)

def patternSet {d : ℕ} (p : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun j => p j = true)

def patternCount {d : ℕ} (p : Fin d → Bool) : ℕ := (patternSet p).card

def patternBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (A B : ConvexBody E) (p : Fin d → Bool) (j : Fin d) : ConvexBody E :=
  if p j = true then B else A

theorem patternCount_le {d : ℕ} (p : Fin d → Bool) : patternCount p ≤ d := by
  first
  | simpa only [patternCount, patternSet, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun j => p j = true) Finset.univ)

theorem patternCount_cons {d : ℕ} (b : Bool) (p : Fin d → Bool) :
    patternCount (Fin.cons b p) = (if b = true then 1 else 0) + patternCount p := by
  first
  | simp only [patternCount, patternSet, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem patternCount_first {d i : ℕ} (hi : i ≤ d) : patternCount (firstPattern d i) = i := by
  first
  | have hset : patternSet (firstPattern d i) = Finset.univ.filter (fun j : Fin d => j.val < i) := by
      first
      | ext j
        simp [patternSet, firstPattern]
    unfold patternCount
    rw [hset]
    rcases lt_or_eq_of_le hi with hid | heq
    · have he : Finset.univ.filter (fun j : Fin d => j.val < i) = Finset.Iio (⟨i, hid⟩ : Fin d) := by
        first
        | ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
          rfl
      rw [he, Fin.card_Iio]
    · subst i
      have he : Finset.univ.filter (fun j : Fin d => j.val < d) = Finset.univ := by
        first
        | ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact j.isLt
      simp only [he, Finset.card_univ, Fintype.card_fin]

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def coefficient (d : ℕ) (A B : ConvexBody E) (i : ℕ) : ℝ :=
  mixedVolume μ (patternBody A B (firstPattern d i))

theorem mixedVolume_pattern {d : ℕ} (A B : ConvexBody E) (p : Fin d → Bool) :
    mixedVolume μ (patternBody A B p) = coefficient μ d A B (patternCount p) := by
  first
  | classical
    let S := patternSet p
    let T := patternSet (firstPattern d (patternCount p))
    have hcard : S.card = T.card := (patternCount_first (patternCount_le p)).symm
    obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
    have hmem (j : Fin d) : e j ∈ T ↔ j ∈ S := by
      first
      | rw [← he]
        simp only [Finset.mem_map, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨k, hk, hkj⟩
          exact e.injective hkj ▸ hk
        · intro hj
          exact ⟨j, hj, rfl⟩
    have htuple : patternBody A B p =
        fun j => patternBody A B (firstPattern d (patternCount p)) (e j) := by
      first
      | funext j
        have hiff := hmem j
        simp only [S, T, patternSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiff
        simp only [patternBody, hiff]
    rw [htuple, mixedVolume_reindex]
    rfl

theorem mixedVolume_piecewise {d : ℕ} (A B : ConvexBody E) (S : Finset (Fin d)) :
    mixedVolume μ (S.piecewise (fun _ => B) (fun _ => A)) = coefficient μ d A B S.card := by
  first
  | let p : Fin d → Bool := fun j => decide (j ∈ S)
    have hc : patternCount p = S.card := by
      first
      | change (patternSet p).card = S.card
        apply congrArg Finset.card
        ext j
        simp [p, patternSet]
    have ht : S.piecewise (fun _ => B) (fun _ => A) = patternBody A B p := by
      first
      | funext j
        simp [Finset.piecewise, patternBody, p]
    rw [ht, mixedVolume_pattern, hc]

theorem mixedVolume_scaled_piecewise {d : ℕ} (A B : ConvexBody E)
    (S : Finset (Fin d)) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    mixedVolume μ (S.piecewise (fun _ => s • B) (fun _ => t • A)) =
      t ^ (d - S.card) * s ^ S.card * coefficient μ d A B S.card := by
  first
  | let r : Fin d → ℝ := fun j => if j ∈ S then s else t
    have hr : ∀ j, 0 ≤ r j := by intro j; dsimp [r]; split_ifs <;> assumption
    have htuple : S.piecewise (fun _ => s • B) (fun _ => t • A) =
        fun j => r j • S.piecewise (fun _ => B) (fun _ => A) j := by
      first
      | funext j
        by_cases hj : j ∈ S <;> simp [r, Finset.piecewise, hj]
    have hprod : ∏ j, r j = s ^ S.card * t ^ (d - S.card) := by
      first
      | dsimp only [r]
        rw [Finset.prod_ite]
        have hyes : Finset.univ.filter (fun j : Fin d => j ∈ S) = S := by ext j; simp
        have hno : Finset.univ.filter (fun j : Fin d => j ∉ S) = Sᶜ := by ext j; simp
        rw [hyes, hno, Finset.prod_const, Finset.prod_const, Finset.card_compl]
        simp only [Fintype.card_fin]
    rw [htuple, mixedVolume_independent_smul μ _ r hr, hprod, mixedVolume_piecewise]
    ring

theorem binary_volume_formula {d : ℕ} (hdim : finrank ℝ E = d)
    (A B : ConvexBody E) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    μ.real ((t • A + s • B : ConvexBody E) : Set E) =
      BinarySimplex.value d (coefficient μ d A B) t s := by
  first
  | rw [← mixedVolume_diagonal μ hdim]
    have hsum : (fun _ : Fin d => t • A + s • B) =
        (fun i => (fun _ : Fin d => s • B) i + (fun _ : Fin d => t • A) i) := by
      first
      | funext i
        exact add_comm _ _
    rw [hsum, mixedVolume_add_all]
    simp_rw [mixedVolume_scaled_piecewise μ A B _ ht hs]
    rw [← Finset.powerset_univ, Finset.sum_powerset]
    have hcardSum (i : ℕ) :
        (∑ S ∈ Finset.powersetCard i (Finset.univ : Finset (Fin d)),
          t ^ (d - S.card) * s ^ S.card * coefficient μ d A B S.card) =
        (d.choose i : ℝ) * (t ^ (d - i) * s ^ i * coefficient μ d A B i) := by
      simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        (Finset.sum_powersetCard i (Finset.univ : Finset (Fin d))
          (fun j => t ^ (d - j) * s ^ j * coefficient μ d A B j))
    simp_rw [hcardSum]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold BinarySimplex.value
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem coefficient_nonnegative (d : ℕ) (A B : ConvexBody E) (i : ℕ) :
    0 ≤ coefficient μ d A B i := mixedVolume_nonnegative μ _

theorem continuous_coefficient (d i : ℕ) :
    Continuous (fun p : ConvexBody E × ConvexBody E => coefficient μ d p.1 p.2 i) := by
  first
  | apply (continuous_mixedVolume μ d).comp
    apply continuous_pi
    intro j
    dsimp only [patternBody]
    split_ifs <;> first | exact continuous_fst | exact continuous_snd

end Measure

theorem realizes_mixedCoefficients (d : ℕ) (A B : Body d) :
    BinarySimplex.Realizes d (coefficient volume d A B) A B := by
  first
  | intro t s ht hs
    exact binary_volume_formula volume (by simp [Space]) A B ht hs

theorem realizing_sequence_eq {d : ℕ} {a : ℕ → ℝ} {A B : Body d}
    (h : BinarySimplex.Realizes d a A B) :
    ∀ i ≤ d, a i = coefficient volume d A B i :=
  h.unique (realizes_mixedCoefficients d A B)

end VolumePolynomials.BinaryMixed
