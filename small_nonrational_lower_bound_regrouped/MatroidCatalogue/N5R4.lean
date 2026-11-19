module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N5R4

def familyMasks : Table (List ℕ) :=
  (.node 2 (.node 1 (.leaf [29,30]) (.leaf [27,29,30])) (.node 3 (.leaf [23,27,29,30]) (.leaf [15,23,27,29,30])))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 4

def gridMasks : Table ℕ := (.node 2 (.node 1 (.leaf 15) (.leaf 23)) (.node 3 (.leaf 27) (.node 4 (.leaf 29) (.leaf 30))))
def grid (i : Fin 5) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 5).powersetCard 4 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N5R4
