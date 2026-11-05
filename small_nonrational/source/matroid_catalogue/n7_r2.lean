module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N7R2

def familyMasks : Table (List ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf [65,66,68,72,80,96]) (.node 2 (.leaf [33,34,36,40,48,65,66,68,72,80]) (.leaf [33,34,36,40,48,65,66,68,72,80,96]))) (.node 5 (.node 4 (.leaf [17,18,20,24,33,34,36,40,65,66,68,72]) (.leaf [17,18,20,24,33,34,36,40,65,66,68,72,80,96])) (.node 6 (.leaf [17,18,20,24,33,34,36,40,48,65,66,68,72,80,96]) (.leaf [9,10,12,17,18,20,33,34,36,65,66,68,72,80,96])))) (.node 10 (.node 8 (.leaf [9,10,12,17,18,20,24,33,34,36,40,65,66,68,80,96]) (.node 9 (.leaf [9,10,12,17,18,20,33,34,36,40,48,65,66,68,72,80,96]) (.leaf [9,10,12,17,18,20,24,33,34,36,40,48,65,66,68,72,80,96]))) (.node 12 (.node 11 (.leaf [5,6,9,10,17,18,20,24,33,34,36,40,65,66,68,72,80,96]) (.leaf [5,6,9,10,17,18,20,24,33,34,36,40,48,65,66,68,72,80,96])) (.node 13 (.leaf [5,6,9,10,12,17,18,20,24,33,34,36,40,48,65,66,68,72,80,96]) (.leaf [3,5,6,9,10,12,17,18,20,24,33,34,36,40,48,65,66,68,72,80,96])))))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 14

def gridMasks : Table ℕ := (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 3) (.leaf 5)) (.node 3 (.leaf 6) (.node 4 (.leaf 9) (.leaf 10)))) (.node 7 (.node 6 (.leaf 12) (.leaf 17)) (.node 8 (.leaf 18) (.node 9 (.leaf 20) (.leaf 24))))) (.node 15 (.node 12 (.node 11 (.leaf 33) (.leaf 34)) (.node 13 (.leaf 36) (.node 14 (.leaf 40) (.leaf 48)))) (.node 18 (.node 16 (.leaf 65) (.node 17 (.leaf 66) (.leaf 68))) (.node 19 (.leaf 72) (.node 20 (.leaf 80) (.leaf 96))))))
def grid (i : Fin 21) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 7).powersetCard 2 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N7R2
