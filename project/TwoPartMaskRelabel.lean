module
prelude
public import CachedCellRelabel

@[expose] public section

/-!
# Two small tables for the exact relabeling of every ten-bit mask

A ten-bit mask is the union of its two five-bit halves. Relabeling preserves
unions, so two tables of32 entries suffice. Their64 values are checked once
for a vertex map and then reused for every cell on which it acts. Exactness
applies to all natural numbers, including inputs above1023, because
the original definition reads only the first ten bits.
-/

namespace Papers.RationalityTen.TwoPartMaskRelabel

open GrowthBitsets RawBoundaryMatch ConcreteGrowth

theorem unionValues_or {α : Type} (f g : α → Nat) (items : List α) :
    unionValues (fun a => Nat.lor (f a) (g a)) items =
      Nat.lor (unionValues f items) (unionValues g items) := by
  induction items with
  | nil => simp [unionValues]
  | cons a rest ih =>
    change Nat.lor (Nat.lor (f a) (g a))
        (unionValues (fun b => Nat.lor (f b) (g b)) rest) =
      Nat.lor (Nat.lor (f a) (unionValues f rest))
        (Nat.lor (g a) (unionValues g rest))
    rw [ih]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [FiniteMaskSets.testBit_lor]
    cases (f a).testBit i <;> cases (g a).testBit i <;>
      cases (unionValues f rest).testBit i <;>
      cases (unionValues g rest).testBit i <;> rfl

theorem renameMask_or {n : Nat} (p : Fin n → Fin n) (a b : Nat) :
    renameMask p (Nat.lor a b) = Nat.lor (renameMask p a) (renameMask p b) := by
  unfold renameMask
  rw [← unionValues_or]
  congr 1
  funext i
  rw [FiniteMaskSets.testBit_lor]
  cases a.testBit i.val <;> cases b.testBit i.val <;>
    apply Nat.eq_of_testBit_eq <;> intro j <;>
    simp [FiniteMaskSets.testBit_lor]

def halfLookup (code : Nat) (i : Fin 32) : Nat :=
  (code >>> (10 * i.val)) % 1024

def rename (low high mask : Nat) : Nat :=
  let reduced := mask % 1024
  Nat.lor (halfLookup low (Fin.ofNat 32 reduced))
    (halfLookup high (Fin.ofNat 32 (reduced >>> 5)))

theorem split_ten_bits : ∀ i : Fin 1024,
    Nat.lor (Fin.ofNat 32 i.val).val
      ((Fin.ofNat 32 (i.val >>> 5)).val <<< 5) = i.val := by
  decide +kernel

/-- Only64 table values are hypotheses; they imply exactness on every mask. -/
theorem rename_exact (p : Fin 10 → Fin 10) (low high : Nat)
    (hlow : ∀ i : Fin 32, halfLookup low i = renameMask p i.val)
    (hhigh : ∀ i : Fin 32,
      halfLookup high i = renameMask p (i.val <<< 5)) (mask : Nat) :
    rename low high mask = renameMask p mask := by
  change Nat.lor (halfLookup low (Fin.ofNat 32 (mask % 1024)))
    (halfLookup high (Fin.ofNat 32 ((mask % 1024) >>> 5))) = renameMask p mask
  rw [hlow, hhigh, ← renameMask_or,
    split_ten_bits ⟨mask % 1024, Nat.mod_lt _ (by decide)⟩,
    CachedCellRelabel.renameMask_mod]

theorem cellCheck_exact (p : Fin 10 → Fin 10) (low high : Nat)
    (hlow : ∀ i : Fin 32, halfLookup low i = renameMask p i.val)
    (hhigh : ∀ i : Fin 32,
      halfLookup high i = renameMask p (i.val <<< 5)) (A B : Cell) :
    CachedCellRelabel.bitsetCellCheck (rename low high) A B =
      RawGraphGrowthFrames.cellRelabelCheck p A B := by
  rw [CachedCellRelabel.bitsetCellCheck_eq]
  exact CachedCellRelabel.cellCheck_eq p (rename low high)
    (rename_exact p low high hlow hhigh) A B

#print axioms rename_exact
#print axioms cellCheck_exact

end Papers.RationalityTen.TwoPartMaskRelabel
