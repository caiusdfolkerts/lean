module
prelude
public import GrowthBitsets
public import GrowthRenaming
public import Init.Data.List.Nat.Pairwise
public import Init.Data.List.Perm

@[expose] public section

/-!
# Finite sets represented by natural-number masks

Only the stated finite range contributes to cardinality.  The forcing lemma
below justifies selecting an uncovered feature when a checked possible set
has the same cardinality as the target's feature set.
-/

namespace Papers.RationalityTen.FiniteMaskSets

open GrowthRenaming

theorem testBit_land (a b i : Nat) :
    (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := by
  simpa only [GrowthBitsets.bitAt_eq_testBit] using GrowthBitsets.bitAt_and a b i

theorem testBit_lor (a b i : Nat) :
    (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := by
  simpa only [GrowthBitsets.bitAt_eq_testBit] using GrowthBitsets.bitAt_or a b i

def elements (n bits : Nat) : List (Fin n) :=
  (List.finRange n).filter fun a => bits.testBit a.val

def card (n bits : Nat) : Nat := (elements n bits).length

theorem mem_elements {n bits : Nat} (a : Fin n) :
    a ∈ elements n bits ↔ bits.testBit a.val = true := by
  simp only [elements, List.mem_filter, List.mem_finRange, true_and]

theorem elements_nodup (n bits : Nat) : (elements n bits).Nodup :=
  (List.nodup_finRange n).filter _

theorem subset_of_bit_imp {n a b : Nat}
    (h : ∀ i : Fin n, a.testBit i.val = true → b.testBit i.val = true) :
    elements n a ⊆ elements n b := by
  intro i hi
  exact (mem_elements i).mpr (h i ((mem_elements i).mp hi))

theorem card_le_of_bit_imp {n a b : Nat}
    (h : ∀ i : Fin n, a.testBit i.val = true → b.testBit i.val = true) :
    card n a ≤ card n b :=
  List.Nodup.length_le_of_subset (elements_nodup n a) (subset_of_bit_imp h)

/-- A subset with at least as many elements as its ambient finite set is equal
to that set.  This is the only cardinality argument behind forced nonedges. -/
theorem bit_imp_of_card_le {n a b : Nat}
    (hab : ∀ i : Fin n, a.testBit i.val = true → b.testBit i.val = true)
    (hcard : card n b ≤ card n a) (i : Fin n)
    (hi : b.testBit i.val = true) : a.testBit i.val = true := by
  by_cases ha : a.testBit i.val = true
  · exact ha
  · have hnot : i ∉ elements n a := fun h => ha ((mem_elements i).mp h)
    have hnd : (i :: elements n a).Nodup :=
      List.nodup_cons.mpr ⟨hnot, elements_nodup n a⟩
    have hsub : i :: elements n a ⊆ elements n b := by
      intro j hj
      rcases List.mem_cons.mp hj with heq | hj
      · exact heq ▸ (mem_elements i).mpr hi
      · exact subset_of_bit_imp hab hj
    have hlen := List.Nodup.length_le_of_subset hnd hsub
    change card n a + 1 ≤ card n b at hlen
    omega

theorem card_bijection {n a b : Nat} (p : Bijection (Fin n))
    (h : ∀ i, b.testBit (p.forward i).val = a.testBit i.val) :
    card n b = card n a := by
  have hnd : ((elements n a).map p.forward).Nodup :=
    List.Pairwise.map p.forward (fun _ _ hne heq => hne (p.injective heq)) (elements_nodup n a)
  have hp : List.Perm ((elements n a).map p.forward) (elements n b) := by
    apply (List.perm_ext_iff_of_nodup hnd (elements_nodup n b)).mpr
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      apply (mem_elements _).mpr
      rw [h]
      exact (mem_elements _).mp hj
    · intro hi
      refine List.mem_map.mpr ⟨p.inverse i, ?_, p.right_inverse i⟩
      apply (mem_elements _).mpr
      rw [← h, p.right_inverse]
      exact (mem_elements _).mp hi
  simpa only [card, List.length_map] using hp.length_eq.symm

def allMask (n : Nat) : Nat := Nat.shiftLeft 1 n - 1

theorem allMask_bit {n : Nat} (i : Fin n) :
    (allMask n).testBit i.val = true := by
  change ((1 <<< n) - 1).testBit i.val = true
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true i.isLt

/-- A finite mask cover preserves every element not present in the first mask. -/
theorem bit_of_cover {n blocked available : Nat}
    (h : Nat.land (allMask n) (Nat.lor blocked available) = allMask n)
    (i : Fin n) (hi : blocked.testBit i.val = false) :
    available.testBit i.val = true := by
  have hh := congrArg (fun mask => mask.testBit i.val) h
  simpa only [testBit_land, testBit_lor, allMask_bit i, hi,
    Bool.false_or, Bool.true_and] using hh

#print axioms bit_imp_of_card_le
#print axioms card_bijection

end Papers.RationalityTen.FiniteMaskSets
