module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N6R2

def familyMasks : Table (List ℕ) :=
  (.node 5 (.node 2 (.node 1 (.leaf [33,34,36,40,48]) (.leaf [17,18,20,24,33,34,36,40])) (.node 3 (.leaf [17,18,20,24,33,34,36,40,48]) (.node 4 (.leaf [9,10,12,17,18,20,33,34,36]) (.leaf [9,10,12,17,18,20,33,34,36,40,48])))) (.node 7 (.node 6 (.leaf [9,10,12,17,18,20,24,33,34,36,40,48]) (.leaf [5,6,9,10,17,18,20,24,33,34,36,40])) (.node 8 (.leaf [5,6,9,10,17,18,20,24,33,34,36,40,48]) (.node 9 (.leaf [5,6,9,10,12,17,18,20,24,33,34,36,40,48]) (.leaf [3,5,6,9,10,12,17,18,20,24,33,34,36,40,48])))))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 10

def gridMasks : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 3) (.node 2 (.leaf 5) (.leaf 6))) (.node 5 (.node 4 (.leaf 9) (.leaf 10)) (.node 6 (.leaf 12) (.leaf 17)))) (.node 11 (.node 9 (.node 8 (.leaf 18) (.leaf 20)) (.node 10 (.leaf 24) (.leaf 33))) (.node 13 (.node 12 (.leaf 34) (.leaf 36)) (.node 14 (.leaf 40) (.leaf 48)))))
def grid (i : Fin 15) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 6).powersetCard 2 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N6R2
