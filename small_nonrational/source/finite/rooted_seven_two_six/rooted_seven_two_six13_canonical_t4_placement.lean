module
prelude
public import RootedSevenTwoSix13CanonicalT4Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenTwoSix13.T4
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenTwoSix13.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 20 := i.isLt
  by_cases h_0_20 : i.val < 10
  · by_cases h_0_10 : i.val < 5
    · by_cases h_0_5 : i.val < 2
      · by_cases h_0_2 : i.val < 1
        · have heq : i = Fin.ofNat 20 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · have heq : i = Fin.ofNat 20 1 := Fin.ext (by change i.val = 1; omega)
          subst i
          exact block_0001
      · by_cases h_2_5 : i.val < 3
        · have heq : i = Fin.ofNat 20 2 := Fin.ext (by change i.val = 2; omega)
          subst i
          exact block_0002
        · by_cases h_3_5 : i.val < 4
          · have heq : i = Fin.ofNat 20 3 := Fin.ext (by change i.val = 3; omega)
            subst i
            exact block_0003
          · have heq : i = Fin.ofNat 20 4 := Fin.ext (by change i.val = 4; omega)
            subst i
            exact block_0004
    · by_cases h_5_10 : i.val < 7
      · by_cases h_5_7 : i.val < 6
        · have heq : i = Fin.ofNat 20 5 := Fin.ext (by change i.val = 5; omega)
          subst i
          exact block_0005
        · have heq : i = Fin.ofNat 20 6 := Fin.ext (by change i.val = 6; omega)
          subst i
          exact block_0006
      · by_cases h_7_10 : i.val < 8
        · have heq : i = Fin.ofNat 20 7 := Fin.ext (by change i.val = 7; omega)
          subst i
          exact block_0007
        · by_cases h_8_10 : i.val < 9
          · have heq : i = Fin.ofNat 20 8 := Fin.ext (by change i.val = 8; omega)
            subst i
            exact block_0008
          · have heq : i = Fin.ofNat 20 9 := Fin.ext (by change i.val = 9; omega)
            subst i
            exact block_0009
  · by_cases h_10_20 : i.val < 15
    · by_cases h_10_15 : i.val < 12
      · by_cases h_10_12 : i.val < 11
        · have heq : i = Fin.ofNat 20 10 := Fin.ext (by change i.val = 10; omega)
          subst i
          exact block_0010
        · have heq : i = Fin.ofNat 20 11 := Fin.ext (by change i.val = 11; omega)
          subst i
          exact block_0011
      · by_cases h_12_15 : i.val < 13
        · have heq : i = Fin.ofNat 20 12 := Fin.ext (by change i.val = 12; omega)
          subst i
          exact block_0012
        · by_cases h_13_15 : i.val < 14
          · have heq : i = Fin.ofNat 20 13 := Fin.ext (by change i.val = 13; omega)
            subst i
            exact block_0013
          · have heq : i = Fin.ofNat 20 14 := Fin.ext (by change i.val = 14; omega)
            subst i
            exact block_0014
    · by_cases h_15_20 : i.val < 17
      · by_cases h_15_17 : i.val < 16
        · have heq : i = Fin.ofNat 20 15 := Fin.ext (by change i.val = 15; omega)
          subst i
          exact block_0015
        · have heq : i = Fin.ofNat 20 16 := Fin.ext (by change i.val = 16; omega)
          subst i
          exact block_0016
      · by_cases h_17_20 : i.val < 18
        · have heq : i = Fin.ofNat 20 17 := Fin.ext (by change i.val = 17; omega)
          subst i
          exact block_0017
        · by_cases h_18_20 : i.val < 19
          · have heq : i = Fin.ofNat 20 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
          · have heq : i = Fin.ofNat 20 19 := Fin.ext (by change i.val = 19; omega)
            subst i
            exact block_0019
end Papers.RationalityTen.RootedCanonical.RootedSevenTwoSix13.T4
