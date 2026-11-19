module
prelude
public import RootedSevenTwoSix13CanonicalT3Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenTwoSix13.T3
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenTwoSix13.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 27 := i.isLt
  by_cases h_0_27 : i.val < 13
  · by_cases h_0_13 : i.val < 6
    · by_cases h_0_6 : i.val < 3
      · by_cases h_0_3 : i.val < 1
        · have heq : i = Fin.ofNat 27 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · by_cases h_1_3 : i.val < 2
          · have heq : i = Fin.ofNat 27 1 := Fin.ext (by change i.val = 1; omega)
            subst i
            exact block_0001
          · have heq : i = Fin.ofNat 27 2 := Fin.ext (by change i.val = 2; omega)
            subst i
            exact block_0002
      · by_cases h_3_6 : i.val < 4
        · have heq : i = Fin.ofNat 27 3 := Fin.ext (by change i.val = 3; omega)
          subst i
          exact block_0003
        · by_cases h_4_6 : i.val < 5
          · have heq : i = Fin.ofNat 27 4 := Fin.ext (by change i.val = 4; omega)
            subst i
            exact block_0004
          · have heq : i = Fin.ofNat 27 5 := Fin.ext (by change i.val = 5; omega)
            subst i
            exact block_0005
    · by_cases h_6_13 : i.val < 9
      · by_cases h_6_9 : i.val < 7
        · have heq : i = Fin.ofNat 27 6 := Fin.ext (by change i.val = 6; omega)
          subst i
          exact block_0006
        · by_cases h_7_9 : i.val < 8
          · have heq : i = Fin.ofNat 27 7 := Fin.ext (by change i.val = 7; omega)
            subst i
            exact block_0007
          · have heq : i = Fin.ofNat 27 8 := Fin.ext (by change i.val = 8; omega)
            subst i
            exact block_0008
      · by_cases h_9_13 : i.val < 11
        · by_cases h_9_11 : i.val < 10
          · have heq : i = Fin.ofNat 27 9 := Fin.ext (by change i.val = 9; omega)
            subst i
            exact block_0009
          · have heq : i = Fin.ofNat 27 10 := Fin.ext (by change i.val = 10; omega)
            subst i
            exact block_0010
        · by_cases h_11_13 : i.val < 12
          · have heq : i = Fin.ofNat 27 11 := Fin.ext (by change i.val = 11; omega)
            subst i
            exact block_0011
          · have heq : i = Fin.ofNat 27 12 := Fin.ext (by change i.val = 12; omega)
            subst i
            exact block_0012
  · by_cases h_13_27 : i.val < 20
    · by_cases h_13_20 : i.val < 16
      · by_cases h_13_16 : i.val < 14
        · have heq : i = Fin.ofNat 27 13 := Fin.ext (by change i.val = 13; omega)
          subst i
          exact block_0013
        · by_cases h_14_16 : i.val < 15
          · have heq : i = Fin.ofNat 27 14 := Fin.ext (by change i.val = 14; omega)
            subst i
            exact block_0014
          · have heq : i = Fin.ofNat 27 15 := Fin.ext (by change i.val = 15; omega)
            subst i
            exact block_0015
      · by_cases h_16_20 : i.val < 18
        · by_cases h_16_18 : i.val < 17
          · have heq : i = Fin.ofNat 27 16 := Fin.ext (by change i.val = 16; omega)
            subst i
            exact block_0016
          · have heq : i = Fin.ofNat 27 17 := Fin.ext (by change i.val = 17; omega)
            subst i
            exact block_0017
        · by_cases h_18_20 : i.val < 19
          · have heq : i = Fin.ofNat 27 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
          · have heq : i = Fin.ofNat 27 19 := Fin.ext (by change i.val = 19; omega)
            subst i
            exact block_0019
    · by_cases h_20_27 : i.val < 23
      · by_cases h_20_23 : i.val < 21
        · have heq : i = Fin.ofNat 27 20 := Fin.ext (by change i.val = 20; omega)
          subst i
          exact block_0020
        · by_cases h_21_23 : i.val < 22
          · have heq : i = Fin.ofNat 27 21 := Fin.ext (by change i.val = 21; omega)
            subst i
            exact block_0021
          · have heq : i = Fin.ofNat 27 22 := Fin.ext (by change i.val = 22; omega)
            subst i
            exact block_0022
      · by_cases h_23_27 : i.val < 25
        · by_cases h_23_25 : i.val < 24
          · have heq : i = Fin.ofNat 27 23 := Fin.ext (by change i.val = 23; omega)
            subst i
            exact block_0023
          · have heq : i = Fin.ofNat 27 24 := Fin.ext (by change i.val = 24; omega)
            subst i
            exact block_0024
        · by_cases h_25_27 : i.val < 26
          · have heq : i = Fin.ofNat 27 25 := Fin.ext (by change i.val = 25; omega)
            subst i
            exact block_0025
          · have heq : i = Fin.ofNat 27 26 := Fin.ext (by change i.val = 26; omega)
            subst i
            exact block_0026
end Papers.RationalityTen.RootedCanonical.RootedSevenTwoSix13.T3
