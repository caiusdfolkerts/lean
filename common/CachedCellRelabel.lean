module
prelude
public import RawGraphGrowthFrames
public import FiniteChecks
public import RawGrowthCacheCertificate

@[expose] public section

/-!
# A checked table for relabeling ten-bit face masks

A vertex permutation acts on only1,024 distinct masks. We verify that small
table once, and reuse its exact values for every edge and polygon of every
candidate cell. The theorem applies to all natural-number inputs because
the original relabeling operation itself reads only the first ten bits.
-/

namespace Papers.RationalityTen.CachedCellRelabel

open RawBoundaryMatch RawGraphGrowthFrames ConcreteGrowth GrowthBitsets

theorem renameMask_mod (p : Fin 10 → Fin 10) (mask : Nat) :
    renameMask p (mask % 1024) = renameMask p mask := by
  unfold renameMask
  congr 1
  funext a
  have hbit : (mask % 1024).testBit a.val = mask.testBit a.val := by
    change (mask % 2 ^ 10).testBit a.val = _
    rw [Nat.testBit_mod_two_pow, decide_eq_true a.isLt, Bool.true_and]
  rw [hbit]

def lookup (code mask : Nat) : Nat :=
  (code >>> (10 * (mask % 1024))) % 1024

theorem lookup_exact (p : Fin 10 → Fin 10) (code : Nat)
    (h : ∀ i : Fin 1024, lookup code i.val = renameMask p i.val) (mask : Nat) :
    lookup code mask = renameMask p mask := by
  have hh := h ⟨mask % 1024, Nat.mod_lt _ (by decide)⟩
  simpa only [lookup, Nat.mod_mod, renameMask_mod] using hh

def cellCheck (rename : Nat → Nat) (A B : Cell) : Bool :=
  ((decide (B.kind = A.kind) && decide (B.vertices = rename A.vertices)) &&
    sameSetCheck (A.edges.map rename) B.edges) &&
    sameSetCheck (A.ridgeMasks.map rename) B.ridgeMasks

theorem cellCheck_eq (p : Fin 10 → Fin 10) (rename : Nat → Nat)
    (h : ∀ mask, rename mask = renameMask p mask) (A B : Cell) :
    cellCheck rename A B = cellRelabelCheck p A B := by
  have heq : rename = renameMask p := funext h
  rw [heq]
  rfl

theorem cached_cellCheck_eq (p : Fin 10 → Fin 10) (code : Nat)
    (h : ∀ i : Fin 1024, lookup code i.val = renameMask p i.val) (A B : Cell) :
    cellCheck (lookup code) A B = cellRelabelCheck p A B :=
  cellCheck_eq p (lookup code) (lookup_exact p code h) A B

def sameSetBits (A B : List Nat) : Bool :=
  decide (RawNatGrowthCheck.mask A = RawNatGrowthCheck.mask B)

theorem sameSetBits_eq (A B : List Nat) : sameSetBits A B = sameSetCheck A B := by
  apply Bool.eq_iff_iff.mpr
  simp only [sameSetBits, decide_eq_true_eq]
  constructor
  · intro h
    have hm (x : Nat) : x ∈ A ↔ x ∈ B := by
      have hb := congrArg (fun mask : Nat => mask.testBit x) h
      rw [RawGrowthCacheCertificate.mask_bit, RawGrowthCacheCertificate.mask_bit] at hb
      simpa only [RawGrowthCacheCertificate.hasNat_true] using
        (Bool.eq_iff_iff.mp hb)
    exact Bool.and_eq_true_iff.mpr
      ⟨List.all_eq_true.mpr (fun x hx => decide_eq_true ((hm x).1 hx)),
       List.all_eq_true.mpr (fun x hx => decide_eq_true ((hm x).2 hx))⟩
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    rw [RawGrowthCacheCertificate.mask_bit, RawGrowthCacheCertificate.mask_bit]
    apply Bool.eq_iff_iff.mpr
    simp only [RawGrowthCacheCertificate.hasNat_true]
    exact sameSetCheck_sound A B h x

def bitsetCellCheck (rename : Nat → Nat) (A B : Cell) : Bool :=
  ((decide (B.kind = A.kind) && decide (B.vertices = rename A.vertices)) &&
    sameSetBits (A.edges.map rename) B.edges) &&
    sameSetBits (A.ridgeMasks.map rename) B.ridgeMasks

theorem bitsetCellCheck_eq (rename : Nat → Nat) (A B : Cell) :
    bitsetCellCheck rename A B = cellCheck rename A B := by
  simp only [bitsetCellCheck, cellCheck, sameSetBits_eq]

theorem cached_bitsetCellCheck_eq (p : Fin 10 → Fin 10) (code : Nat)
    (h : ∀ i : Fin 1024, lookup code i.val = renameMask p i.val) (A B : Cell) :
    bitsetCellCheck (lookup code) A B = cellRelabelCheck p A B := by
  rw [bitsetCellCheck_eq]
  exact cached_cellCheck_eq p code h A B

#print axioms cached_cellCheck_eq
#print axioms cached_bitsetCellCheck_eq

end Papers.RationalityTen.CachedCellRelabel
