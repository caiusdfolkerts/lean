module

public import PaperVerification.AlternatingFormsEvenWalkCompression
public import PaperVerification.AlternatingFormsBooleanGraphWalks
public import PaperVerification.AlternatingFormsEvenMatchingGeneric
public import Mathlib.Data.Finset.Preimage

/-!
# Pairing the actual walks in the paper's even formula

The first and last steps are forced upward.  The remaining positions are
paired in their original order.  A selected letter is a downward step;
singletons give the two distinct loop colors, and a selected full pair is
a downward step of the compressed Boolean walk.  All maps below preserve
the literal selected sets and are proved inverse to one another.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.EvenSingletons

open BooleanWalks

/-- The two letters of pair i occupy positions 2i+1 and 2i+2 after the
fixed initial upward step.  Position 2k+1 is the final fixed upward step. -/
def pairPosition (k : ℕ) : (Fin k ⊕ Fin k) ↪ Fin (2 * k + 2) where
  toFun := Sum.elim
    (fun i => ⟨2 * i.val + 1, by have := i.isLt; omega⟩)
    (fun i => ⟨2 * i.val + 2, by have := i.isLt; omega⟩)
  inj' := by
    rintro (i | i) (j | j) h
    · apply congrArg Sum.inl
      apply Fin.ext
      have he := congrArg Fin.val h
      dsimp only [Sum.elim_inl] at he
      omega
    · have he := congrArg Fin.val h
      dsimp only [Sum.elim_inl, Sum.elim_inr] at he
      omega
    · have he := congrArg Fin.val h
      dsimp only [Sum.elim_inl, Sum.elim_inr] at he
      omega
    · apply congrArg Sum.inr
      apply Fin.ext
      have he := congrArg Fin.val h
      dsimp only [Sum.elim_inr] at he
      omega

theorem pairPosition_range (k : ℕ) (i : Fin (2 * k + 2)) :
    i ∈ Set.range (pairPosition k) ↔ 0 < i.val ∧ i.val < 2 * k + 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rcases x with j | j <;> change 0 < _ ∧ _ < 2 * k + 1 <;>
      have hj := j.isLt <;> dsimp [pairPosition] <;> omega
  · rintro ⟨hi0, hi⟩
    by_cases ho : i.val % 2 = 1
    · refine ⟨Sum.inl ⟨i.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      change 2 * (i.val / 2) + 1 = i.val
      omega
    · refine ⟨Sum.inr ⟨i.val / 2 - 1, by omega⟩, ?_⟩
      apply Fin.ext
      change 2 * (i.val / 2 - 1) + 2 = i.val
      omega

def expandedSet {k : ℕ} (T : PairedState (Fin k)) : Finset (Fin (2 * k + 2)) :=
  (supportEquiv T).map (pairPosition k)

theorem expandedSet_injective (k : ℕ) : Function.Injective (expandedSet (k := k)) :=
  fun _ _ h => supportEquiv.injective (Finset.map_injective (pairPosition k) h)

@[simp] theorem expandedSet_card {k : ℕ} (T : PairedState (Fin k)) :
    (expandedSet T).card = degree T := by
  rw [expandedSet, Finset.card_map, support_card]

/-- Complete pairs end at odd binary times. -/
theorem expandedSet_prefix_odd {k : ℕ} (T : PairedState (Fin k)) (j : ℕ) :
    prefixCount (expandedSet T) (2 * j + 1) = selectionPrefix T j := by
  rw [expandedSet, prefixCount, Finset.filter_map, Finset.card_map, supportEquiv_apply]
  have he : ((selection T).1.disjSum (selection T).2).filter
      (fun x => ((pairPosition k) x).val < 2 * j + 1) =
        ((selection T).1.filter fun i => i.val < j).disjSum
          ((selection T).2.filter fun i => i.val < j) := by
    apply Finset.ext
    rintro (i | i)
    · simp only [Finset.mem_filter, Finset.inl_mem_disjSum]
      change (i ∈ (selection T).1 ∧ 2 * i.val + 1 < 2 * j + 1) ↔
        (i ∈ (selection T).1 ∧ i.val < j)
      constructor <;> rintro ⟨hi, hlt⟩ <;> exact ⟨hi, by omega⟩
    · simp only [Finset.mem_filter, Finset.inr_mem_disjSum]
      change (i ∈ (selection T).2 ∧ 2 * i.val + 2 < 2 * j + 1) ↔
        (i ∈ (selection T).2 ∧ i.val < j)
      constructor <;> rintro ⟨hi, hlt⟩ <;> exact ⟨hi, by omega⟩
  simp only [Function.comp_apply]
  rw [he, Finset.card_disjSum]
  rfl

theorem selectionPrefix_final {k : ℕ} (T : PairedState (Fin k)) :
    selectionPrefix T k = degree T := by
  rw [selectionPrefix, prefixCount_all _ _ le_rfl, prefixCount_all _ _ le_rfl]
  have h := support_card T
  rw [supportEquiv_apply, Finset.card_disjSum] at h
  exact h

theorem pairedGood_degree_le {k : ℕ} {T : PairedState (Fin k)} (h : PairedGood T) :
    degree T ≤ k := by
  have hd := (h k le_rfl).1
  rwa [selectionPrefix_final] at hd

/-- Both walls for every half-step are equivalent to the walls at complete
pairs.  At odd height, either color of singleton remains inside the strip. -/
theorem expanded_good_iff {k : ℕ} (T : PairedState (Fin k)) :
    Good (⟨expandedSet T, expandedSet_card T⟩ : FixedSubsets (Fin (2*k+2)) (degree T)) ↔
      PairedGood T := by
  constructor
  · intro h j hj
    have hb := h (2*j+1) (by omega)
    rw [expandedSet_prefix_odd] at hb
    constructor <;> omega
  · intro h r hr
    have hd := pairedGood_degree_le h
    by_cases hr0 : r = 0
    · subst r
      simp only [prefixCount_zero, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      constructor <;> omega
    · by_cases hend : r = 2*k+2
      · subst r
        rw [prefixCount_all _ _ le_rfl, expandedSet_card]
        constructor <;> omega
      · let j := (r - 1) / 2
        have hj : j ≤ k := by dsimp [j]; omega
        have hb := h j hj
        by_cases hodd : r % 2 = 1
        · have he : r = 2*j+1 := by dsimp [j]; omega
          rw [he, expandedSet_prefix_odd]
          constructor <;> omega
        · have he : r = 2*j+2 := by dsimp [j]; omega
          have hp := prefixCount_succ (expandedSet T) (2*j+1)
          rw [expandedSet_prefix_odd] at hp
          have hδ := selectedAt_le_one (expandedSet T) (2*j+1)
          rw [he]
          change 2 * prefixCount (expandedSet T) (2*j+1+1) ≤ 2*j+2 ∧
            2*j+2+2*degree T ≤ 2*k+2+2*prefixCount (expandedSet T) (2*j+1+1)
          rw [hp]
          constructor <;> omega

theorem goodSubset_no_endpoints {k s : ℕ} (S : GoodSubset (2*k+2) s)
    (i : Fin (2*k+2)) (hi : i ∈ S.val.val) : 0 < i.val ∧ i.val < 2*k+1 := by
  have hfirst : 2 * prefixCount S.val.val 1 ≤ 1 := (S.property 1 (by omega)).1
  have hlast := (S.property (2*k+1) (by omega)).2
  have hl := prefixCount_succ S.val.val (2*k+1)
  have hdl := selectedAt_position S.val.val (Fin.last (2*k+1))
  simp only [Fin.val_last] at hdl
  change prefixCount S.val.val (2*k+2) =
    prefixCount S.val.val (2*k+1) + selectedAt S.val.val (2*k+1) at hl
  rw [prefixCount_all _ _ le_rfl, S.val.property, hdl] at hl
  have hn0 : (0 : Fin (2*k+2)) ∉ S.val.val := by
    intro hz
    have hd : selectedAt S.val.val 0 = 1 := by
      simpa only [Fin.val_zero, if_pos hz] using
        selectedAt_position S.val.val (0 : Fin (2*k+2))
    have hc := prefixCount_succ S.val.val 0
    have hc' : prefixCount S.val.val 1 = 1 := by
      simpa only [prefixCount_zero, hd, Nat.zero_add] using hc
    rw [hc'] at hfirst
    norm_num at hfirst
  have hnl : Fin.last (2*k+1) ∉ S.val.val := by
    intro hz
    rw [if_pos hz] at hl
    omega
  have hi0 : i.val ≠ 0 := by
    intro hz
    have he : i = (0 : Fin (2*k+2)) := Fin.ext hz
    exact hn0 (he ▸ hi)
  have hil : i.val ≠ 2*k+1 := by
    intro hz
    have he : i = Fin.last (2*k+1) := Fin.ext hz
    exact hnl (he ▸ hi)
  have hib := i.isLt
  omega

def goodPairedToFullSubset {k s : ℕ} (T : GoodDegreeState k s) : GoodSubset (2*k+2) s :=
  ⟨⟨expandedSet T.val.val, (expandedSet_card _).trans T.val.property⟩, by
    intro r hr
    have h := ((expanded_good_iff T.val.val).mpr T.property) r hr
    change 2 * prefixCount (expandedSet T.val.val) r ≤ r ∧
      r + 2 * s ≤ 2 * k + 2 + 2 * prefixCount (expandedSet T.val.val) r
    change 2 * prefixCount (expandedSet T.val.val) r ≤ r ∧
      r + 2 * degree T.val.val ≤ 2 * k + 2 + 2 * prefixCount (expandedSet T.val.val) r at h
    simpa only [T.val.property] using h⟩

theorem goodPairedToFullSubset_injective (k s : ℕ) :
    Function.Injective (goodPairedToFullSubset (k := k) (s := s)) := by
  intro T U h
  apply Subtype.ext
  apply Subtype.ext
  apply expandedSet_injective k
  exact congrArg (fun z : GoodSubset (2*k+2) s => z.val.val) h

theorem goodPairedToFullSubset_surjective (k s : ℕ) :
    Function.Surjective (goodPairedToFullSubset (k := k) (s := s)) := by
  intro S
  let U := S.val.val.preimage (pairPosition k) (pairPosition k).injective.injOn
  let T : PairedState (Fin k) := supportEquiv.symm U
  have hset : expandedSet T = S.val.val := by
    rw [expandedSet]
    change (supportEquiv (supportEquiv.symm U)).map (pairPosition k) = S.val.val
    rw [Equiv.apply_symm_apply]
    ext i
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact Finset.mem_preimage.mp hj
    · intro hi
      obtain ⟨j, hj⟩ := (pairPosition_range k i).mpr (goodSubset_no_endpoints S i hi)
      refine ⟨j, ?_, hj⟩
      apply Finset.mem_preimage.mpr
      rwa [hj]
  have hdeg : degree T = s := by
    rw [← expandedSet_card, hset]
    exact S.val.property
  have hg : PairedGood T := by
    apply (expanded_good_iff T).mp
    intro r hr
    change 2 * prefixCount (expandedSet T) r ≤ r ∧
      r + 2 * degree T ≤ 2 * k + 2 + 2 * prefixCount (expandedSet T) r
    rw [hset, hdeg]
    exact S.property r hr
  refine ⟨⟨⟨T, hdeg⟩, hg⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hset

def pairedFullGoodEquiv (k s : ℕ) : GoodDegreeState k s ≃ GoodSubset (2*k+2) s :=
  Equiv.ofBijective goodPairedToFullSubset
    ⟨goodPairedToFullSubset_injective k s, goodPairedToFullSubset_surjective k s⟩

/-- This is the required genuine bijection with the paper's actual graph
walks, including both walls, every singleton color, and all block sizes. -/
def blockGoodPaperWalkEquiv (k s : ℕ) (hs : s ≤ k) :
    ((J : DegreeBlock (Fin k) s) × BlockGoodSubsets J) ≃
      StripWalk (2*k+2-2*s) (2*k+2) :=
  ((blockGoodPairedEquiv k s).trans (pairedFullGoodEquiv k s)).trans
    (goodSubsetGraphWalkEquiv (2*k+2) s (by omega))

theorem blockWalkCount_eq_paperWalkCount (k s : ℕ) (hs : s ≤ k) :
    blockWalkCount (Fin k) s = StripWalks.paperWalkCount (2*k) s := by
  change (∑ J : DegreeBlock (Fin k) s, Fintype.card (BlockGoodSubsets J)) = _
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (blockGoodPaperWalkEquiv k s hs)

variable {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

theorem generic_matching_paperHilbert (k : ℕ) (b : Module.Basis (Fin k ⊕ Fin k) K M)
    (a c : Fin k → K)
    (h : BooleanQuotient.pairParameterEvaluation a c
      (matchingGenericPolynomial (K := K) (ι := Fin k)) ≠ 0)
    (s : ℕ) (hs : s ≤ k) :
    Module.finrank K (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) =
      StripWalks.paperWalkCount (2*k) s := by
  rw [matchingGenericPolynomial_spec b a c h s, blockWalkCount_eq_paperWalkCount k s hs]

end PaperVerification.AlternatingForms.EvenSingletons
