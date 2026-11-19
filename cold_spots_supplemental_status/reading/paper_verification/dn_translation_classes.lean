module

public import PaperVerification.LatticeTranslationClasses
public import PaperVerification.BWCode
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset


@[expose] public section
/-! # The binomial number of D_n^+ deep-hole translation classes

The representatives normalize the first coordinate to be integral and retain
one integer-parity bit.  Complementation identifies the two choices of half
coordinates.  The final quotient count is therefore exactly binomial(n,n/2),
with no restriction beyond even n>8.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

abbrev DnHoleIndex (n : ℕ) := {S : Finset (Fin n) // S.card = n / 2}

theorem card_dnHoleIndex (n : ℕ) : Fintype.card (DnHoleIndex n) = n.choose (n / 2) := by
  let e : DnHoleIndex n ≃ ((Finset.univ : Finset (Fin n)).powersetCard (n / 2)) :=
    { toFun := fun S => ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
      invFun := fun S => ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Finset.card_powersetCard]

def dnHalfSet (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 / 2 else 0

def dnUnit (hn : 0 < n) (ε : Binary) : Fin n → ℤ :=
  fun i => if i = ⟨0, hn⟩ then ε.val else 0

theorem sum_dnUnit (hn : 0 < n) (ε : Binary) : (∑ i, dnUnit hn ε i) = (ε.val : ℤ) := by
  simp [dnUnit]

def dnNormalizedSet (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if (⟨0, hn⟩ : Fin n) ∈ S then Sᶜ else S

def dnSetPhase (hn : 0 < n) (S : Finset (Fin n)) : Binary :=
  if (⟨0, hn⟩ : Fin n) ∈ S then 1 else 0

def dnClassPoint (hn : 0 < n) (S : DnHoleIndex n) : Fin n → ℝ :=
  dnHalfSet (dnNormalizedSet hn S.val) + intVec (dnUnit hn (dnSetPhase hn S.val))

theorem dnNormalizedSet_zero_not_mem (hn : 0 < n) (S : Finset (Fin n)) :
    (⟨0, hn⟩ : Fin n) ∉ dnNormalizedSet hn S := by
  classical
  unfold dnNormalizedSet
  split_ifs with h <;> simp [h]

theorem even_half_identity (heven : Even n) : n = n / 2 + n / 2 := by
  obtain ⟨k, hk⟩ := heven
  omega

theorem dnNormalizedSet_card (hn : 0 < n) (heven : Even n) (S : DnHoleIndex n) :
    (dnNormalizedSet hn S.val).card = n / 2 := by
  classical
  unfold dnNormalizedSet
  split_ifs
  · rw [Finset.card_compl, Fintype.card_fin, S.property]
    have := even_half_identity heven
    omega
  · exact S.property

theorem foldedRadius_halfSet_int (S : Finset (Fin n)) (m : Fin n → ℤ) (i : Fin n) :
    foldedRadius (dnHalfSet S + intVec m) i = if i ∈ S then 1 / 2 else 0 := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    apply (foldedRadius_eq_half_iff _ i).mpr
    exact ⟨m i, by simp [dnHalfSet, intVec, hi, add_comm]⟩
  · rw [if_neg hi]
    apply (foldedRadius_eq_zero_iff _ i).mpr
    exact ⟨m i, by simp [dnHalfSet, intVec, hi]⟩

theorem dnClassPoint_balanced (hn : 0 < n) (heven : Even n) (S : DnHoleIndex n) :
    BalancedHalfGrid (dnClassPoint hn S) := by
  classical
  constructor
  · intro i
    rw [dnClassPoint, foldedRadius_halfSet_int]
    split_ifs <;> simp
  · have hsum : (∑ i, foldedRadius (dnClassPoint hn S) i) =
        ((dnNormalizedSet hn S.val).card : ℝ) / 2 := by
      simp [dnClassPoint, foldedRadius_halfSet_int, Finset.sum_ite, div_eq_mul_inv]
    rw [hsum, dnNormalizedSet_card hn heven S]
    have hcast : (n : ℝ) = ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast even_half_identity heven
    linarith

theorem dnClassPoint_deep (hn : 8 < n) (heven : Even n) (S : DnHoleIndex n) :
    IsDeepHole (dPlusSet n) (dnClassPoint (by omega) S) := by
  apply (isDeepHole_dPlus_iff_depth hn.le heven _).mpr
  exact squaredDepth_dPlus_of_balanced hn.le (dnClassPoint_balanced (by omega) heven S)

theorem dnHalfGrid_normalForm {x : Fin n → ℝ} (hx : HalfIntegerGrid x) :
    ∃ m : Fin n → ℤ, ∃ S : Finset (Fin n), x = dnHalfSet S + intVec m := by
  classical
  choose w hw using hx
  let c : Fin n → Binary := fun i => (w i : Binary)
  let m : Fin n → ℤ := fun i => (w i - (c i).val) / 2
  let S : Finset (Fin n) := Finset.univ.filter (fun i => c i = 1)
  have hi (i : Fin n) : 2 * m i = w i - (c i).val := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sub, binary_val_cast, c, sub_self]
  refine ⟨m, S, ?_⟩
  funext i
  have h : 2 * (m i : ℝ) = (w i : ℝ) - ((c i).val : ℝ) := by exact_mod_cast hi i
  rw [hw i]
  rcases binary_eq_zero_or_one (c i) with hc | hc
  all_goals
    rw [hc] at h
    simp only [binary_one_val, ZMod.val_zero, Nat.cast_one, Nat.cast_zero] at h
    simp [dnHalfSet, S, intVec, hc]
    linarith

theorem nonintegerCount_halfSet_int (S : Finset (Fin n)) (m : Fin n → ℤ) :
    nonintegerCount (dnHalfSet S + intVec m) = S.card := by
  classical
  unfold nonintegerCount
  have he : (Finset.univ.filter fun i => ¬∃ k : ℤ, (dnHalfSet S + intVec m) i = (k : ℝ)) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← foldedRadius_eq_zero_iff,
      foldedRadius_halfSet_int]
    by_cases hi : i ∈ S <;> simp [hi]
  rw [he]

theorem dnNormalized_data_injective (hn : 0 < n) {S T : Finset (Fin n)}
    (hset : dnNormalizedSet hn S = dnNormalizedSet hn T)
    (hphase : dnSetPhase hn S = dnSetPhase hn T) : S = T := by
  classical
  by_cases hs : (⟨0, hn⟩ : Fin n) ∈ S <;> by_cases ht : (⟨0, hn⟩ : Fin n) ∈ T
  · have h : Sᶜ = Tᶜ := by simpa only [dnNormalizedSet, if_pos hs, if_pos ht] using hset
    simpa using congrArg (fun U : Finset (Fin n) => Uᶜ) h
  · norm_num [dnSetPhase, hs, ht] at hphase
  · norm_num [dnSetPhase, hs, ht] at hphase
  · simpa only [dnNormalizedSet, if_neg hs, if_neg ht] using hset

theorem dnHalfSet_integer_difference {S T : Finset (Fin n)} {m : Fin n → ℤ}
    (h : dnHalfSet S - dnHalfSet T = intVec m) : S = T := by
  classical
  ext i
  have hi := congrFun h i
  change (if i ∈ S then 1 / 2 else 0) - (if i ∈ T then 1 / 2 else 0) = (m i : ℝ) at hi
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T
  · simp [hs, ht]
  · have he : (m i : ℝ) = (0 : ℝ) + 1 / 2 := by norm_num [hs, ht] at hi ⊢; linarith
    exact (integer_ne_half_shift (m i) 0 (by simpa only [Int.cast_zero] using he)).elim
  · have he : (m i : ℝ) = (-1 : ℝ) + 1 / 2 := by norm_num [hs, ht] at hi ⊢; linarith
    exact (integer_ne_half_shift (m i) (-1)
      (by simpa only [Int.cast_neg, Int.cast_one] using he)).elim
  · simp [hs, ht]

theorem dnClassPoint_distinct (hn : 0 < n) (S T : DnHoleIndex n) :
    dnClassPoint hn S - dnClassPoint hn T ∈ dPlusSet n ↔ S = T := by
  classical
  constructor
  · rintro ⟨z, hz, h | h⟩
    · have hset : dnNormalizedSet hn S.val = dnNormalizedSet hn T.val := by
        apply dnHalfSet_integer_difference (m := z - dnUnit hn (dnSetPhase hn S.val) + dnUnit hn (dnSetPhase hn T.val))
        have he := h
        funext i
        have hi := congrFun he i
        simp only [dnClassPoint, Pi.sub_apply, Pi.add_apply, intVec, Int.cast_add, Int.cast_sub] at hi ⊢
        linarith
      have heq : z = dnUnit hn (dnSetPhase hn S.val) - dnUnit hn (dnSetPhase hn T.val) := by
        apply intVec_injective n
        rw [← h]
        funext i
        simp only [dnClassPoint, Pi.sub_apply, Pi.add_apply, intVec, Int.cast_sub, hset]
        ring
      simp only [heq, Pi.sub_apply, Finset.sum_sub_distrib, sum_dnUnit] at hz
      have hphase : dnSetPhase hn S.val = dnSetPhase hn T.val := by
        have hh := ZMod.intCast_eq_zero_iff_even.mpr hz
        simpa only [Int.cast_sub, binary_val_cast, sub_eq_zero] using hh
      exact Subtype.ext (dnNormalized_data_injective hn hset hphase)
    · have hi := congrFun h ⟨0, hn⟩
      have hs := dnNormalizedSet_zero_not_mem hn S.val
      have ht := dnNormalizedSet_zero_not_mem hn T.val
      simp only [dnClassPoint, Pi.sub_apply, Pi.add_apply, dnHalfSet, if_neg hs, if_neg ht,
        zero_add, intVec, dnUnit, if_pos rfl, ite_true] at hi
      apply False.elim
      apply integer_ne_half_shift
        (((dnSetPhase hn S.val).val : ℤ) - (dnSetPhase hn T.val).val) (z ⟨0, hn⟩)
      simpa only [Int.cast_sub, Int.cast_natCast] using hi
  · rintro rfl
    simpa only [sub_self] using zero_mem_dPlusSet n

def dnIndexOfNormalized (hn : 0 < n) (heven : Even n) (S : Finset (Fin n))
    (hS : S.card = n / 2) (ε : Binary) : DnHoleIndex n :=
  if ε = 0 then ⟨S, hS⟩ else ⟨Sᶜ, by
    rw [Finset.card_compl, Fintype.card_fin, hS]
    have := even_half_identity heven
    omega⟩

theorem dnIndexOfNormalized_point (hn : 0 < n) (heven : Even n) (S : Finset (Fin n))
    (hS : S.card = n / 2) (hzero : (⟨0, hn⟩ : Fin n) ∉ S) (ε : Binary) :
    dnClassPoint hn (dnIndexOfNormalized hn heven S hS ε) = dnHalfSet S + intVec (dnUnit hn ε) := by
  classical
  rcases binary_eq_zero_or_one ε with h | h <;>
    simp [dnIndexOfNormalized, dnClassPoint, dnNormalizedSet, dnSetPhase, hzero, h]

theorem dnDeepHole_coset_coverage (hn : 8 < n) (heven : Even n)
    {x : Fin n → ℝ} (hx : IsDeepHole (dPlusSet n) x) :
    ∃ S : DnHoleIndex n, x - dnClassPoint (by omega) S ∈ dPlusSet n := by
  classical
  have hgrid := (isDeepHole_dPlus_iff_paperHalfGrid hn heven x).mp hx
  obtain ⟨m, S, rfl⟩ := dnHalfGrid_normalForm hgrid.1
  have hS : S.card = n / 2 := by
    simpa only [nonintegerCount_halfSet_int] using hgrid.2
  let hn0 : 0 < n := by omega
  by_cases hs : (⟨0, hn0⟩ : Fin n) ∈ S
  · let z : Fin n → ℤ := fun i => m i + (if i ∈ S then 1 else 0) - 1
    let ε : Binary := (∑ i, z i : ℤ)
    have hSc : (Sᶜ).card = n / 2 := by
      rw [Finset.card_compl, Fintype.card_fin, hS]
      have := even_half_identity heven
      omega
    refine ⟨dnIndexOfNormalized hn0 heven Sᶜ hSc ε, ?_⟩
    rw [dnIndexOfNormalized_point hn0 heven Sᶜ hSc (by simpa using hs)]
    refine ⟨z - dnUnit hn0 ε, ?_, Or.inr ?_⟩
    · apply ZMod.intCast_eq_zero_iff_even.mp
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_dnUnit, Int.cast_sub, binary_val_cast, ε, sub_self]
    · funext i
      by_cases hi : i ∈ S <;>
        simp [dnHalfSet, intVec, z, hi] <;> ring
  · let ε : Binary := (∑ i, m i : ℤ)
    refine ⟨dnIndexOfNormalized hn0 heven S hS ε, ?_⟩
    rw [dnIndexOfNormalized_point hn0 heven S hS hs]
    refine ⟨m - dnUnit hn0 ε, ?_, Or.inl ?_⟩
    · apply ZMod.intCast_eq_zero_iff_even.mp
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_dnUnit, Int.cast_sub, binary_val_cast, ε, sub_self]
    · funext i
      simp only [Pi.add_apply, Pi.sub_apply, intVec, Int.cast_sub]
      ring

def dnDeepClassMap (hn : 8 < n) (heven : Even n) (S : DnHoleIndex n) :
    DeepTranslationClasses (dPlusAddSubgroup n heven) :=
  ⟨(dnClassPoint (by omega) S : (Fin n → ℝ) ⧸ dPlusAddSubgroup n heven),
    dnClassPoint (by omega) S, dnClassPoint_deep hn heven S, rfl⟩

theorem dnDeepClassMap_bijective (hn : 8 < n) (heven : Even n) :
    Function.Bijective (dnDeepClassMap hn heven) := by
  constructor
  · intro S T h
    apply (dnClassPoint_distinct (by omega) S T).mp
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, x, hx, hC⟩
    obtain ⟨S, hS⟩ := dnDeepHole_coset_coverage hn heven hx
    refine ⟨S, Subtype.ext ?_⟩
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hS).symm.trans hC

def dnDeepClassEquiv (hn : 8 < n) (heven : Even n) :
    DnHoleIndex n ≃ DeepTranslationClasses (dPlusAddSubgroup n heven) :=
  Equiv.ofBijective (dnDeepClassMap hn heven) (dnDeepClassMap_bijective hn heven)

/-- The full symbolic binomial count for every even n>8. -/
theorem dPlus_deep_translation_class_count (hn : 8 < n) (heven : Even n) :
    Nat.card (DeepTranslationClasses (dPlusAddSubgroup n heven)) = n.choose (n / 2) := by
  rw [← Nat.card_congr (dnDeepClassEquiv hn heven), Nat.card_eq_fintype_card, card_dnHoleIndex]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.dPlus_deep_translation_class_count
