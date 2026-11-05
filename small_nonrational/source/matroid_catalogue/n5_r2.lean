module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N5R2

def familyMasks : Table (List ℕ) :=
  (.node 3 (.node 1 (.leaf [17,18,20,24]) (.node 2 (.leaf [9,10,12,17,18,20]) (.leaf [9,10,12,17,18,20,24]))) (.node 4 (.leaf [5,6,9,10,17,18,20,24]) (.node 5 (.leaf [5,6,9,10,12,17,18,20,24]) (.leaf [3,5,6,9,10,12,17,18,20,24]))))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 6

def gridMasks : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 3) (.leaf 5)) (.node 3 (.leaf 6) (.node 4 (.leaf 9) (.leaf 10)))) (.node 7 (.node 6 (.leaf 12) (.leaf 17)) (.node 8 (.leaf 18) (.node 9 (.leaf 20) (.leaf 24)))))
def grid (i : Fin 10) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 5).powersetCard 2 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N5R2
