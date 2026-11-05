module
prelude
public import RootedSevenMixed032CanonicalT4Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenMixed032.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 26 := i.isLt
  by_cases h_0_26 : i.val < 13
  · by_cases h_0_13 : i.val < 6
    · by_cases h_0_6 : i.val < 3
      · by_cases h_0_3 : i.val < 1
        · have heq : i = Fin.ofNat 26 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · by_cases h_1_3 : i.val < 2
          · have heq : i = Fin.ofNat 26 1 := Fin.ext (by change i.val = 1; omega)
            subst i
            exact block_0001
          · have heq : i = Fin.ofNat 26 2 := Fin.ext (by change i.val = 2; omega)
            subst i
            exact block_0002
      · by_cases h_3_6 : i.val < 4
        · have heq : i = Fin.ofNat 26 3 := Fin.ext (by change i.val = 3; omega)
          subst i
          exact block_0003
        · by_cases h_4_6 : i.val < 5
          · have heq : i = Fin.ofNat 26 4 := Fin.ext (by change i.val = 4; omega)
            subst i
            exact block_0004
          · have heq : i = Fin.ofNat 26 5 := Fin.ext (by change i.val = 5; omega)
            subst i
            exact block_0005
    · by_cases h_6_13 : i.val < 9
      · by_cases h_6_9 : i.val < 7
        · have heq : i = Fin.ofNat 26 6 := Fin.ext (by change i.val = 6; omega)
          subst i
          exact block_0006
        · by_cases h_7_9 : i.val < 8
          · have heq : i = Fin.ofNat 26 7 := Fin.ext (by change i.val = 7; omega)
            subst i
            exact block_0007
          · have heq : i = Fin.ofNat 26 8 := Fin.ext (by change i.val = 8; omega)
            subst i
            exact block_0008
      · by_cases h_9_13 : i.val < 11
        · by_cases h_9_11 : i.val < 10
          · have heq : i = Fin.ofNat 26 9 := Fin.ext (by change i.val = 9; omega)
            subst i
            exact block_0009
          · have heq : i = Fin.ofNat 26 10 := Fin.ext (by change i.val = 10; omega)
            subst i
            exact block_0010
        · by_cases h_11_13 : i.val < 12
          · have heq : i = Fin.ofNat 26 11 := Fin.ext (by change i.val = 11; omega)
            subst i
            exact block_0011
          · have heq : i = Fin.ofNat 26 12 := Fin.ext (by change i.val = 12; omega)
            subst i
            exact block_0012
  · by_cases h_13_26 : i.val < 19
    · by_cases h_13_19 : i.val < 16
      · by_cases h_13_16 : i.val < 14
        · have heq : i = Fin.ofNat 26 13 := Fin.ext (by change i.val = 13; omega)
          subst i
          exact block_0013
        · by_cases h_14_16 : i.val < 15
          · have heq : i = Fin.ofNat 26 14 := Fin.ext (by change i.val = 14; omega)
            subst i
            exact block_0014
          · have heq : i = Fin.ofNat 26 15 := Fin.ext (by change i.val = 15; omega)
            subst i
            exact block_0015
      · by_cases h_16_19 : i.val < 17
        · have heq : i = Fin.ofNat 26 16 := Fin.ext (by change i.val = 16; omega)
          subst i
          exact block_0016
        · by_cases h_17_19 : i.val < 18
          · have heq : i = Fin.ofNat 26 17 := Fin.ext (by change i.val = 17; omega)
            subst i
            exact block_0017
          · have heq : i = Fin.ofNat 26 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
    · by_cases h_19_26 : i.val < 22
      · by_cases h_19_22 : i.val < 20
        · have heq : i = Fin.ofNat 26 19 := Fin.ext (by change i.val = 19; omega)
          subst i
          exact block_0019
        · by_cases h_20_22 : i.val < 21
          · have heq : i = Fin.ofNat 26 20 := Fin.ext (by change i.val = 20; omega)
            subst i
            exact block_0020
          · have heq : i = Fin.ofNat 26 21 := Fin.ext (by change i.val = 21; omega)
            subst i
            exact block_0021
      · by_cases h_22_26 : i.val < 24
        · by_cases h_22_24 : i.val < 23
          · have heq : i = Fin.ofNat 26 22 := Fin.ext (by change i.val = 22; omega)
            subst i
            exact block_0022
          · have heq : i = Fin.ofNat 26 23 := Fin.ext (by change i.val = 23; omega)
            subst i
            exact block_0023
        · by_cases h_24_26 : i.val < 25
          · have heq : i = Fin.ofNat 26 24 := Fin.ext (by change i.val = 24; omega)
            subst i
            exact block_0024
          · have heq : i = Fin.ofNat 26 25 := Fin.ext (by change i.val = 25; omega)
            subst i
            exact block_0025
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
