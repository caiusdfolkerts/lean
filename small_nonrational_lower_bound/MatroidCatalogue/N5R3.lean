module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N5R3

def familyMasks : Table (List ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf [25,26,28]) (.leaf [21,22,25,26])) (.node 3 (.leaf [21,22,25,26,28]) (.leaf [19,21,22,25,26,28]))) (.node 6 (.node 5 (.leaf [13,14,21,22,25,26]) (.leaf [13,14,21,22,25,26,28])) (.node 7 (.leaf [11,13,14,19,21,22,26,28]) (.node 8 (.leaf [11,13,14,19,21,22,25,26,28]) (.leaf [7,11,13,14,19,21,22,25,26,28])))))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 9

def gridMasks : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 7) (.leaf 11)) (.node 3 (.leaf 13) (.node 4 (.leaf 14) (.leaf 19)))) (.node 7 (.node 6 (.leaf 21) (.leaf 22)) (.node 8 (.leaf 25) (.node 9 (.leaf 26) (.leaf 28)))))
def grid (i : Fin 10) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 5).powersetCard 3 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N5R3
