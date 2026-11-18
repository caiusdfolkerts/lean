module
prelude
public import TenGraphEdges
public import PrimitiveBitsetGrowth

@[expose] public section

/-!
# Exact matching of complete boundary families

Both facet and polygon families are compared in both directions.  An explicit
inverse certificate establishes that the ten vertex labels are permuted.
The checker is independent of the target table's size and storage layout.
-/

namespace Papers.RationalityTen.RawBoundaryMatch

open GrowthRenaming GrowthBitsets ConcreteGrowth

def renameMask {n : Nat} (p : Fin n → Fin n) (mask : Nat) : Nat :=
  unionValues (fun a => if mask.testBit a.val then
    PrimitiveBitsetGrowth.singleton (p a).val else 0) (List.finRange n)

theorem renameMask_bit {n : Nat} (p : Bijection (Fin n)) (mask : Nat) (a : Fin n) :
    (renameMask p.forward mask).testBit (p.forward a).val = mask.testBit a.val := by
  apply Bool.eq_iff_iff.mpr
  rw [← bitAt_eq_testBit, renameMask, bitAt_unionValues]
  constructor
  · rintro ⟨b, _, hb⟩
    by_cases hbit : mask.testBit b.val = true
    · simp only [hbit, ↓reduceIte, PrimitiveBitsetGrowth.singleton_eq, bitAt_power] at hb
      have heq : p.forward b = p.forward a := Fin.ext (of_decide_eq_true hb)
      exact p.injective heq ▸ hbit
    · have hz : mask.testBit b.val = false := Bool.eq_false_of_ne_true hbit
      simp only [hz, Bool.false_eq_true, ↓reduceIte, bitAt_zero] at hb
  · intro ha
    refine ⟨a, List.mem_finRange a, ?_⟩
    simp only [ha, ↓reduceIte, PrimitiveBitsetGrowth.singleton_eq, bitAt_power,
      decide_true]

def sameSetCheck (A B : List Nat) : Bool :=
  A.all (fun x => decide (x ∈ B)) && B.all (fun x => decide (x ∈ A))

theorem sameSetCheck_sound (A B : List Nat) (h : sameSetCheck A B = true) :
    ∀ x, x ∈ A ↔ x ∈ B := by
  obtain ⟨hab, hba⟩ := Bool.and_eq_true_iff.mp h
  intro x
  exact ⟨fun hx => of_decide_eq_true (List.all_eq_true.mp hab x hx),
    fun hx => of_decide_eq_true (List.all_eq_true.mp hba x hx)⟩

def matchCheck (p : Fin 10 → Fin 10)
    (facets polygons targetFacets targetPolygons : List Nat) : Bool :=
  sameSetCheck (facets.map (renameMask p)) targetFacets &&
    sameSetCheck (polygons.map (renameMask p)) targetPolygons

structure Witness where
  target : Nat
  permutation : Nat
  inverse : Nat

def witnessCheck (targetCount : Nat) (targetFacets targetPolygons : Nat → List Nat)
    (facets polygons : List Nat) (w : Witness) : Bool :=
  (TenGraphEdges.permutationCheck w.permutation w.inverse && decide (w.target < targetCount)) &&
    matchCheck (TenGraphEdges.vertexMap w.permutation) facets polygons
      (targetFacets w.target) (targetPolygons w.target)

theorem witnessCheck_sound (targetCount : Nat)
    (targetFacets targetPolygons : Nat → List Nat)
    (facets polygons : List Nat) (w : Witness)
    (h : witnessCheck targetCount targetFacets targetPolygons facets polygons w = true) :
    w.target < targetCount ∧ ∃ p : Bijection (Fin 10),
      (∀ x, x ∈ facets.map (renameMask p.forward) ↔ x ∈ targetFacets w.target) ∧
      (∀ x, x ∈ polygons.map (renameMask p.forward) ↔ x ∈ targetPolygons w.target) := by
  obtain ⟨hhead, hmatch⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hperm, hbound⟩ := Bool.and_eq_true_iff.mp hhead
  let p := TenGraphEdges.checkedBijection w.permutation w.inverse hperm
  refine ⟨of_decide_eq_true hbound, p, ?_⟩
  obtain ⟨hfacets, hpolygons⟩ := Bool.and_eq_true_iff.mp hmatch
  exact ⟨sameSetCheck_sound _ _ hfacets, sameSetCheck_sound _ _ hpolygons⟩

#print axioms witnessCheck_sound
#print axioms renameMask_bit

end Papers.RationalityTen.RawBoundaryMatch
