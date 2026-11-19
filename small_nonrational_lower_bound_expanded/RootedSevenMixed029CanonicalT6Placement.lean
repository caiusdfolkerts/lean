module
prelude
public import RootedSevenMixed029CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenMixed029.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 16 := i.isLt
  by_cases h_0_16 : i.val < 8
  · by_cases h_0_8 : i.val < 4
    · by_cases h_0_4 : i.val < 2
      · by_cases h_0_2 : i.val < 1
        · have heq : i = Fin.ofNat 16 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · have heq : i = Fin.ofNat 16 1 := Fin.ext (by change i.val = 1; omega)
          subst i
          exact block_0001
      · by_cases h_2_4 : i.val < 3
        · have heq : i = Fin.ofNat 16 2 := Fin.ext (by change i.val = 2; omega)
          subst i
          exact block_0002
        · have heq : i = Fin.ofNat 16 3 := Fin.ext (by change i.val = 3; omega)
          subst i
          exact block_0003
    · by_cases h_4_8 : i.val < 6
      · by_cases h_4_6 : i.val < 5
        · have heq : i = Fin.ofNat 16 4 := Fin.ext (by change i.val = 4; omega)
          subst i
          exact block_0004
        · have heq : i = Fin.ofNat 16 5 := Fin.ext (by change i.val = 5; omega)
          subst i
          exact block_0005
      · by_cases h_6_8 : i.val < 7
        · have heq : i = Fin.ofNat 16 6 := Fin.ext (by change i.val = 6; omega)
          subst i
          exact block_0006
        · have heq : i = Fin.ofNat 16 7 := Fin.ext (by change i.val = 7; omega)
          subst i
          exact block_0007
  · by_cases h_8_16 : i.val < 12
    · by_cases h_8_12 : i.val < 10
      · by_cases h_8_10 : i.val < 9
        · have heq : i = Fin.ofNat 16 8 := Fin.ext (by change i.val = 8; omega)
          subst i
          exact block_0008
        · have heq : i = Fin.ofNat 16 9 := Fin.ext (by change i.val = 9; omega)
          subst i
          exact block_0009
      · by_cases h_10_12 : i.val < 11
        · have heq : i = Fin.ofNat 16 10 := Fin.ext (by change i.val = 10; omega)
          subst i
          exact block_0010
        · have heq : i = Fin.ofNat 16 11 := Fin.ext (by change i.val = 11; omega)
          subst i
          exact block_0011
    · by_cases h_12_16 : i.val < 14
      · by_cases h_12_14 : i.val < 13
        · have heq : i = Fin.ofNat 16 12 := Fin.ext (by change i.val = 12; omega)
          subst i
          exact block_0012
        · have heq : i = Fin.ofNat 16 13 := Fin.ext (by change i.val = 13; omega)
          subst i
          exact block_0013
      · by_cases h_14_16 : i.val < 15
        · have heq : i = Fin.ofNat 16 14 := Fin.ext (by change i.val = 14; omega)
          subst i
          exact block_0014
        · have heq : i = Fin.ofNat 16 15 := Fin.ext (by change i.val = 15; omega)
          subst i
          exact block_0015
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.T6
