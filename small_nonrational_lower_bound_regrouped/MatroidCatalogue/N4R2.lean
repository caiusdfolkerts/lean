module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N4R2

def familyMasks : Table (List ℕ) :=
  (.node 2 (.node 1 (.leaf [9,10,12]) (.leaf [5,6,9,10])) (.node 3 (.leaf [5,6,9,10,12]) (.leaf [3,5,6,9,10,12])))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 4

def gridMasks : Table ℕ := (.node 3 (.node 1 (.leaf 3) (.node 2 (.leaf 5) (.leaf 6))) (.node 4 (.leaf 9) (.node 5 (.leaf 10) (.leaf 12))))
def grid (i : Fin 6) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 4).powersetCard 2 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N4R2
