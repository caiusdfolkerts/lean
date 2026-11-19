module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N3R2

def familyMasks : Table (List ℕ) :=
  (.node 1 (.leaf [5,6]) (.leaf [3,5,6]))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 2

def gridMasks : Table ℕ := (.node 1 (.leaf 3) (.node 2 (.leaf 5) (.leaf 6)))
def grid (i : Fin 3) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 3).powersetCard 2 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N3R2
