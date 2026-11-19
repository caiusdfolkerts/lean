module
prelude
public import IntersectionIncompatibilityRows
public import Init.Data.Nat.Power2.Bitwise
import all Init.Data.Nat.Power2.Basic

@[expose] public section

/-!
# Compact proper-face rejection rows

A compatible cell meets the fixed cell in one of its actual proper faces.
It is therefore enough to union the good rows indexed by the empty face,
present singleton vertices, listed edges, and listed ridges. Complementing
this union gives a sound rejection row without enumerating all vertex subsets.
-/

namespace Papers.RationalityTen.ProperFaceComplementRows

open ConcreteGrowth GrowthBitsets FiniteMaskSets IntersectionIncompatibilityRows

variable {n v : Nat}

def singletonMasks (cell : Cell) (v : Nat) : List Nat :=
  ((List.finRange v).filter fun j => cell.vertices.testBit j.val).map fun j => 2 ^ j.val

def properMasks (cell : Cell) (v : Nat) : List Nat :=
  [0] ++ singletonMasks cell v ++ cell.edges ++ cell.ridgeMasks

theorem mem_properMasks_iff (cell : Cell) (v q : Nat) :
    q ∈ properMasks cell v ↔
      q = 0 ∨ q ∈ singletonMasks cell v ∨ q ∈ cell.edges ∨ q ∈ cell.ridgeMasks := by
  simp only [properMasks, List.mem_append, List.mem_singleton, or_assoc]

theorem small_subset_mem_singletons (cell : Cell) (v q : Nat)
    (hcell : cell.vertices < 2 ^ v) (hsubset : Nat.land q cell.vertices = q)
    (hzero : q ≠ 0) (hsmall : Nat.land q (q - 1) = 0) :
    q ∈ singletonMasks cell v := by
  obtain ⟨k, hpow⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hzero).mp hsmall
  have hqle : q ≤ cell.vertices := by
    calc
      q = Nat.land q cell.vertices := hsubset.symm
      _ ≤ cell.vertices := Nat.and_le_right
  have hpowlt : 2 ^ k < 2 ^ v := by
    rw [← hpow]
    exact Nat.lt_of_le_of_lt hqle hcell
  have hk : k < v := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpowlt
  have hbit : cell.vertices.testBit k = true := by
    have h := congrArg (fun mask => mask.testBit k) hsubset
    rw [hpow, testBit_land, Nat.testBit_two_pow_self, Bool.true_and] at h
    exact h
  apply List.mem_map.mpr
  exact ⟨⟨k, hk⟩, List.mem_filter.mpr ⟨List.mem_finRange _, hbit⟩, hpow.symm⟩

/-- Every actual common proper face occurs in the short face list. The
singleton case follows from the general proved power-of-two criterion. -/
theorem properMasks_complete (cell : Cell) (v q : Nat)
    (hcell : cell.vertices < 2 ^ v) (hsubset : Nat.land q cell.vertices = q)
    (hproper : proper cell q = true) : q ∈ properMasks cell v := by
  apply (mem_properMasks_iff cell v q).mpr
  obtain hhead | hridge := Bool.or_eq_true_iff.mp hproper
  · obtain hsmall | hedge := Bool.or_eq_true_iff.mp hhead
    · by_cases hzero : q = 0
      · exact Or.inl hzero
      · exact Or.inr (Or.inl (small_subset_mem_singletons cell v q hcell hsubset
          hzero (of_decide_eq_true hsmall)))
    · obtain ⟨e, he, heq⟩ := List.any_eq_true.mp hedge
      have heq : e = q := of_decide_eq_true heq
      exact Or.inr (Or.inr (Or.inl (heq ▸ he)))
  · obtain ⟨r, hr, heq⟩ := List.any_eq_true.mp hridge
    have heq : r = q := of_decide_eq_true heq
    exact Or.inr (Or.inr (Or.inr (heq ▸ hr)))

def goodTerm {cells : Fin n → Cell} (R : Rows cells v)
    (a : Fin n) (q : Nat) : Nat :=
  Nat.land (intersectionRow R a q) (properRow R q)

def goodRow {cells : Fin n → Cell} (R : Rows cells v) (a : Fin n) : Nat :=
  unionValues (goodTerm R a) (properMasks (cells a) v)

def badFaceRow {cells : Fin n → Cell} (R : Rows cells v) (a : Fin n) : Nat :=
  Nat.xor (allMask n) (goodRow R a)

theorem common_subset (a b : Nat) : Nat.land (Nat.land a b) a = Nat.land a b := by
  calc
    Nat.land (Nat.land a b) a = Nat.land a (Nat.land b a) := Nat.and_assoc a b a
    _ = Nat.land a (Nat.land a b) := congrArg (Nat.land a) (Nat.and_comm b a)
    _ = Nat.land (Nat.land a a) b := (Nat.and_assoc a a b).symm
    _ = Nat.land a b := congrArg (fun x => Nat.land x b) (Nat.and_self a)

theorem compatible_goodRow {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (ha : (cells a).vertices < 2 ^ v)
    (h : compatible (cells a) (cells b) = true) :
    (goodRow R a).testBit b.val = true := by
  let q := Nat.land (cells a).vertices (cells b).vertices
  have hsubset : Nat.land q (cells a).vertices = q := common_subset _ _
  obtain ⟨hproper, _⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hap, hbp⟩ := Bool.and_eq_true_iff.mp hproper
  change proper (cells a) q = true at hap
  change proper (cells b) q = true at hbp
  have hq := properMasks_complete (cells a) v q ha hsubset hap
  have hintersection := (intersectionRow_correct R a b q ha hsubset).mpr rfl
  have hface := properRow_complete R b q hbp
  have hterm : (goodTerm R a q).testBit b.val = true := by
    rw [goodTerm, testBit_land, hintersection, hface]
    rfl
  apply (bitAt_eq_testBit _ _).symm.trans
  exact (bitAt_unionValues _ _ _).mpr
    ⟨q, hq, (bitAt_eq_testBit _ _).trans hterm⟩

/-- This supplies the cache's one-sided incompatibility law using only the
short proper-face list of the fixed cell. -/
theorem badFaceRow_sound {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (ha : (cells a).vertices < 2 ^ v)
    (h : bitAt (badFaceRow R a) b.val = true) :
    compatible (cells a) (cells b) = false := by
  apply Bool.eq_false_of_ne_true
  intro hcompatible
  have hgood := compatible_goodRow R a b ha hcompatible
  rw [bitAt_eq_testBit, badFaceRow, IntersectionIncompatibilityRows.testBit_xor,
    allMask_bit b, hgood] at h
  exact Bool.noConfusion h

#print axioms badFaceRow_sound

end Papers.RationalityTen.ProperFaceComplementRows
