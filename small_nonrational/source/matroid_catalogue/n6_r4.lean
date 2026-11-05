module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

namespace Papers.RationalityTen.MatroidCatalogue.N6R4

def familyMasks : Table (List ℕ) :=
  (.node 9 (.node 4 (.node 2 (.node 1 (.leaf [57,58,60]) (.leaf [53,54,57,58])) (.node 3 (.leaf [53,54,57,58,60]) (.leaf [51,53,54,57,58,60]))) (.node 6 (.node 5 (.leaf [45,46,53,54,57,58]) (.leaf [45,46,53,54,57,58,60])) (.node 7 (.leaf [43,45,46,51,53,54,58,60]) (.node 8 (.leaf [43,45,46,51,53,54,57,58,60]) (.leaf [39,43,45,46,51,53,54,57,58,60]))))) (.node 13 (.node 11 (.node 10 (.leaf [29,30,45,46,53,54,57,58]) (.leaf [29,30,45,46,53,54,57,58,60])) (.node 12 (.leaf [27,29,30,43,45,46,51,53,54]) (.leaf [27,29,30,43,45,46,51,53,54,58,60]))) (.node 15 (.node 14 (.leaf [27,29,30,43,45,46,51,53,54,57,58,60]) (.leaf [23,27,29,30,39,43,45,46,53,54,57,58])) (.node 16 (.leaf [23,27,29,30,39,43,45,46,53,54,57,58,60]) (.node 17 (.leaf [23,27,29,30,39,43,45,46,51,53,54,57,58,60]) (.leaf [15,23,27,29,30,39,43,45,46,51,53,54,57,58,60]))))))

def family (i : ℕ) : Finset (Finset (Fin 8)) := familyOfMasks (familyMasks.get i)

def count : ℕ := 18

def gridMasks : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 23) (.leaf 27))) (.node 5 (.node 4 (.leaf 29) (.leaf 30)) (.node 6 (.leaf 39) (.leaf 43)))) (.node 11 (.node 9 (.node 8 (.leaf 45) (.leaf 46)) (.node 10 (.leaf 51) (.leaf 53))) (.node 13 (.node 12 (.leaf 54) (.leaf 57)) (.node 14 (.leaf 58) (.leaf 60)))))
def grid (i : Fin 15) : Finset (Fin 8) := maskPoints (gridMasks.get i.val)

theorem grid_complete : Finset.univ.image grid = (groundPrefix 6).powersetCard 4 := by
  decide +kernel

end Papers.RationalityTen.MatroidCatalogue.N6R4
