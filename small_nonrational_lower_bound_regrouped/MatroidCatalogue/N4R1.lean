module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N4R1

def familyMasks : Table (List ℕ) :=
  (.leaf [1,2,4,8])

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 1

def gridMasks : Table ℕ := (.node 2 (.node 1 (.leaf 1) (.leaf 2)) (.node 3 (.leaf 4) (.leaf 8)))
def grid (i : Fin 4) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 4).powersetCard 1 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N4R1
