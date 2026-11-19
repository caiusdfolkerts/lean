module
public import MatroidCatalogue.N0R0
public import MatroidCatalogue.N1R1
public import MatroidCatalogue.N2R1
public import MatroidCatalogue.N2R2
public import MatroidCatalogue.N3R1
public import MatroidCatalogue.N3R2
public import MatroidCatalogue.N3R3
public import MatroidCatalogue.N4R1
public import MatroidCatalogue.N4R2
public import MatroidCatalogue.N4R3
public import MatroidCatalogue.N4R4
public import MatroidCatalogue.N5R1
public import MatroidCatalogue.N5R2
public import MatroidCatalogue.N5R3
public import MatroidCatalogue.N5R4
public import MatroidCatalogue.N6R1
public import MatroidCatalogue.N6R2
public import MatroidCatalogue.N6R3
public import MatroidCatalogue.N6R4
public import MatroidCatalogue.N7R1
public import MatroidCatalogue.N7R2
public import MatroidCatalogue.N7R3
public import MatroidCatalogue.N7R4
public import MatroidCatalogue.N8R4

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue

def count : ℕ → ℕ → ℕ
  | 0,0 => N0R0.count
  | 1,1 => N1R1.count
  | 2,1 => N2R1.count
  | 2,2 => N2R2.count
  | 3,1 => N3R1.count
  | 3,2 => N3R2.count
  | 3,3 => N3R3.count
  | 4,1 => N4R1.count
  | 4,2 => N4R2.count
  | 4,3 => N4R3.count
  | 4,4 => N4R4.count
  | 5,1 => N5R1.count
  | 5,2 => N5R2.count
  | 5,3 => N5R3.count
  | 5,4 => N5R4.count
  | 6,1 => N6R1.count
  | 6,2 => N6R2.count
  | 6,3 => N6R3.count
  | 6,4 => N6R4.count
  | 7,1 => N7R1.count
  | 7,2 => N7R2.count
  | 7,3 => N7R3.count
  | 7,4 => N7R4.count
  | 8,4 => N8R4.count
  | _,_ => 0

def family : ℕ → ℕ → ℕ → Finset (Finset (Fin 8))
  | 0,0,i => N0R0.family i
  | 1,1,i => N1R1.family i
  | 2,1,i => N2R1.family i
  | 2,2,i => N2R2.family i
  | 3,1,i => N3R1.family i
  | 3,2,i => N3R2.family i
  | 3,3,i => N3R3.family i
  | 4,1,i => N4R1.family i
  | 4,2,i => N4R2.family i
  | 4,3,i => N4R3.family i
  | 4,4,i => N4R4.family i
  | 5,1,i => N5R1.family i
  | 5,2,i => N5R2.family i
  | 5,3,i => N5R3.family i
  | 5,4,i => N5R4.family i
  | 6,1,i => N6R1.family i
  | 6,2,i => N6R2.family i
  | 6,3,i => N6R3.family i
  | 6,4,i => N6R4.family i
  | 7,1,i => N7R1.family i
  | 7,2,i => N7R2.family i
  | 7,3,i => N7R3.family i
  | 7,4,i => N7R4.family i
  | 8,4,i => N8R4.family i
  | _,_,_ => ∅

def catalogue (n r : ℕ) : Finset (Finset (Finset (Fin 8))) := (Finset.range (count n r)).image (family n r)

theorem family_mem (n r i : ℕ) (hi : i < count n r) : family n r i ∈ catalogue n r :=
  Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩

end Papers.RationalityTen.MatroidCatalogue
