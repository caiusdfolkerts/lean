module
prelude
public import SharedGraphCellPool

@[expose] public section

namespace Papers.RationalityTen.ResidualGraphKernel

open PackedGraphCertificate PackedRawNatGrowth FiniteChecks
open SharedGraphCellPool

/-- Only the vertex mask is needed by the face exclusion test. -/
def vertices (D : RawData) (c : Fin D.n) : Nat :=
  take 10 (drop 5 (D.cells.get c.val))

theorem vertices_eq (D : RawData) (c : Fin D.n) :
    vertices D c = (D.data.cells c).vertices := rfl

/-- Sharing the anchor reads avoids re-decoding them at every bad-list entry.
The remaining predicates are exactly those consumed by matrix_checked. -/
def localTest (D : RawData) (i : Nat) : Bool :=
  let c := Fin.ofNat D.n i
  let bad := D.data.badLists c
  let v := vertices D c
  let faces := D.data.faceMasks c
  decide (D.data.badMasks c = PrimitiveBitsetGrowth.mask bad) &&
    (bad.all (fun d =>
      let common := Nat.land v (vertices D d)
      !(FaceOnlyCompatibility.proper faces common &&
        FaceOnlyCompatibility.proper (D.data.faceMasks d) common)) &&
      (D.data.kindMasks (D.data.kind c)).testBit c.val)

theorem localTest_eq (D : RawData) (i : Nat) :
    localTest D i = localCheck D i := rfl

theorem localInterval (D : RawData) (lo hi : Nat)
    (h : Interval (localTest D) lo hi) : Interval (localCheck D) lo hi := by
  intro i hlo hhi
  rw [← localTest_eq]
  exact h i hlo hhi

/-- Combine the raw record's entire variable-length local interval with the
existing semantic checker. A generated theorem may be reused when these
projections are definitionally equal, including across budget rows. -/
theorem localChecked (D : RawData)
    (h : checkRange (localTest D) 0 D.n = true) :
    Interval (localCheck D) 0 D.n :=
  localInterval D 0 D.n
    (by simpa only [Nat.zero_add] using interval_of_check (localTest D) 0 D.n h)

/-- Dense ten-bit vertex masks keep repeated reads away from the large
serialized cell fields. The producer proposes the vector and Lean checks
it once per local slot. -/
def vertexAt (code : Nat) (i : Nat) : Nat :=
  take 10 (drop (10 * i) code)

def vertexTest (D : RawData) (code i : Nat) : Bool :=
  decide (vertexAt code i = vertices D (Fin.ofNat D.n i))

def indexedTest (D : RawData) (code i : Nat) : Bool :=
  let c := Fin.ofNat D.n i
  let bad := D.data.badLists c
  let v := vertexAt code c.val
  let faces := D.data.faceMasks c
  decide (D.data.badMasks c = PrimitiveBitsetGrowth.mask bad) &&
    (bad.all (fun d =>
      let common := Nat.land v (vertexAt code d.val)
      !(FaceOnlyCompatibility.proper faces common &&
        FaceOnlyCompatibility.proper (D.data.faceMasks d) common)) &&
      (D.data.kindMasks (D.data.kind c)).testBit c.val)

theorem indexedTest_eq (D : RawData) (code i : Nat)
    (h : Interval (vertexTest D code) 0 D.n) :
    indexedTest D code i = localTest D i := by
  have aligned (c : Fin D.n) : vertexAt code c.val = vertices D c := by
    have hc := h c.val (Nat.zero_le _) c.isLt
    simpa only [vertexTest, Fin.ofNat_val_eq_self, decide_eq_true_eq] using hc
  simp only [indexedTest, localTest, aligned]

def indexedCheck (D : RawData) (code : Nat) : Bool :=
  checkRange (vertexTest D code) 0 D.n && checkRange (indexedTest D code) 0 D.n

theorem indexedChecked (D : RawData) (code : Nat)
    (h : indexedCheck D code = true) : Interval (localCheck D) 0 D.n := by
  have checks := Bool.and_eq_true_iff.mp
    (show checkRange (vertexTest D code) 0 D.n &&
      checkRange (indexedTest D code) 0 D.n = true from h)
  have aligned : Interval (vertexTest D code) 0 D.n := by
    simpa only [Nat.zero_add] using interval_of_check _ 0 D.n checks.1
  apply localInterval
  intro i hi hn
  rw [← indexedTest_eq D code i aligned]
  exact checkRange_sound _ 0 D.n checks.2 i hi (by simpa only [Nat.zero_add] using hn)

#print axioms localChecked
#print axioms indexedChecked
end Papers.RationalityTen.ResidualGraphKernel
