module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N6R3

def familyMasks : Table (List ℕ) :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf [49,50,52,56]) (.node 2 (.leaf [41,42,44,49,50,52]) (.leaf [41,42,44,49,50,52,56]))) (.node 4 (.leaf [37,38,41,42,49,50,52,56]) (.node 5 (.leaf [37,38,41,42,44,49,50,52,56]) (.leaf [35,37,38,41,42,44,49,50,52,56])))) (.node 9 (.node 7 (.leaf [25,26,28,41,42,44,49,50,52]) (.node 8 (.leaf [25,26,28,41,42,44,49,50,52,56]) (.leaf [21,22,25,26,37,38,41,42]))) (.node 10 (.leaf [21,22,25,26,37,38,41,42,52,56]) (.node 11 (.leaf [21,22,25,26,37,38,41,42,49,50,52,56]) (.leaf [21,22,25,26,28,37,38,41,42,44,52,56]))))) (.node 18 (.node 15 (.node 13 (.leaf [21,22,25,26,28,37,38,41,42,44,49,50,56]) (.node 14 (.leaf [21,22,25,26,28,37,38,41,42,44,49,50,52,56]) (.leaf [13,14,21,22,25,26,37,38,41,42,49,50]))) (.node 16 (.leaf [19,21,22,25,26,28,35,37,38,41,42,44,50,52,56]) (.node 17 (.leaf [19,21,22,25,26,28,35,37,38,41,42,44,49,50,52,56]) (.leaf [13,14,21,22,25,26,37,38,41,42,44,49,50,52,56])))) (.node 21 (.node 19 (.leaf [13,14,21,22,25,26,28,37,38,41,42,44,49,50,52,56]) (.node 20 (.leaf [7,13,14,19,22,25,26,28,35,37,41,42,44,49,50,52]) (.leaf [7,13,14,19,22,25,26,28,35,37,41,42,44,49,50,52,56]))) (.node 23 (.node 22 (.leaf [11,13,14,19,21,22,26,28,35,37,38,41,42,44,49,50,52,56]) (.leaf [11,13,14,19,21,22,25,26,28,35,37,38,41,42,44,49,50,52])) (.node 24 (.leaf [11,13,14,19,21,22,25,26,28,35,37,38,41,42,44,49,50,52,56]) (.leaf [7,11,13,14,19,21,22,25,26,28,35,37,38,41,42,44,49,50,52,56]))))))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 25

def gridMasks : Table ℕ := (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 7) (.leaf 11)) (.node 3 (.leaf 13) (.node 4 (.leaf 14) (.leaf 19)))) (.node 7 (.node 6 (.leaf 21) (.leaf 22)) (.node 8 (.leaf 25) (.node 9 (.leaf 26) (.leaf 28))))) (.node 15 (.node 12 (.node 11 (.leaf 35) (.leaf 37)) (.node 13 (.leaf 38) (.node 14 (.leaf 41) (.leaf 42)))) (.node 17 (.node 16 (.leaf 44) (.leaf 49)) (.node 18 (.leaf 50) (.node 19 (.leaf 52) (.leaf 56))))))
def grid (i : Fin 20) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 6).powersetCard 3 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N6R3
