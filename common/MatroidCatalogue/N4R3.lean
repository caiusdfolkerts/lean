module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N4R3

def familyMasks : Table (List ℕ) :=
  (.node 1 (.leaf [13,14]) (.node 2 (.leaf [11,13,14]) (.leaf [7,11,13,14])))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 3

def gridMasks : Table ℕ := (.node 2 (.node 1 (.leaf 7) (.leaf 11)) (.node 3 (.leaf 13) (.leaf 14)))
def grid (i : Fin 4) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 4).powersetCard 3 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N4R3
