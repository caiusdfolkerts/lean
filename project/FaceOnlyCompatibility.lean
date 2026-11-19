module
prelude
public import FastGrowthCompatibility
public import GrowthBitsets

@[expose] public section

/-!
# A necessary face-intersection test

These caches may overestimate proper faces. Consequently a failed face test
is always a sound incompatibility certificate. No equality of the two edge
restrictions is needed for this direction.
-/

namespace Papers.RationalityTen.FaceOnlyCompatibility

open ConcreteGrowth

def faceCheck (cell : Cell) (bits : Nat) : Bool :=
  cell.edges.all bits.testBit && cell.ridgeMasks.all bits.testBit

def proper (bits mask : Nat) : Bool :=
  decide (Nat.land mask (mask - 1) = 0) || bits.testBit mask

def compatible (a b : Cell) (aFaces bFaces : Nat) : Bool :=
  let common := Nat.land a.vertices b.vertices
  proper aFaces common && proper bFaces common

theorem faceCheck_eq (cell : Cell) (bits : Nat) :
    faceCheck cell bits = ConcreteGrowth.faceCacheCheck cell bits := by
  have h : bits.testBit = ConcreteGrowth.bitAt bits :=
    funext fun i => (GrowthBitsets.bitAt_eq_testBit bits i).symm
  simp only [faceCheck, ConcreteGrowth.faceCacheCheck, h]

theorem proper_of_proper (cell : Cell) (bits mask : Nat)
    (hcache : faceCheck cell bits = true)
    (hproper : ConcreteGrowth.proper cell mask = true) : proper bits mask = true := by
  have h := ConcreteGrowth.fastProper_of_proper cell bits mask
    ((faceCheck_eq cell bits).symm.trans hcache) hproper
  have hb : ConcreteGrowth.bitAt bits mask = bits.testBit mask :=
    GrowthBitsets.bitAt_eq_testBit bits mask
  simpa only [proper, ConcreteGrowth.fastProper, hb] using h

theorem necessary (a b : Cell) (aFaces bFaces : Nat)
    (ha : faceCheck a aFaces = true) (hb : faceCheck b bFaces = true)
    (hab : ConcreteGrowth.compatible a b = true) : compatible a b aFaces bFaces = true := by
  obtain ⟨hfaces, _⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨hfa, hfb⟩ := Bool.and_eq_true_iff.mp hfaces
  exact Bool.and_eq_true_iff.mpr
    ⟨proper_of_proper a aFaces _ ha hfa, proper_of_proper b bFaces _ hb hfb⟩

#print axioms necessary

end Papers.RationalityTen.FaceOnlyCompatibility
