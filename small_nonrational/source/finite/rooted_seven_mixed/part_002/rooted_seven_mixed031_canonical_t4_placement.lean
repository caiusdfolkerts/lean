module
prelude
public import RootedSevenMixed031CanonicalT4Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenMixed031.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 36 := i.isLt
  by_cases h_0_36 : i.val < 18
  · by_cases h_0_18 : i.val < 9
    · by_cases h_0_9 : i.val < 4
      · by_cases h_0_4 : i.val < 2
        · by_cases h_0_2 : i.val < 1
          · have heq : i = Fin.ofNat 36 0 := Fin.ext (by change i.val = 0; omega)
            subst i
            exact block_0000
          · have heq : i = Fin.ofNat 36 1 := Fin.ext (by change i.val = 1; omega)
            subst i
            exact block_0001
        · by_cases h_2_4 : i.val < 3
          · have heq : i = Fin.ofNat 36 2 := Fin.ext (by change i.val = 2; omega)
            subst i
            exact block_0002
          · have heq : i = Fin.ofNat 36 3 := Fin.ext (by change i.val = 3; omega)
            subst i
            exact block_0003
      · by_cases h_4_9 : i.val < 6
        · by_cases h_4_6 : i.val < 5
          · have heq : i = Fin.ofNat 36 4 := Fin.ext (by change i.val = 4; omega)
            subst i
            exact block_0004
          · have heq : i = Fin.ofNat 36 5 := Fin.ext (by change i.val = 5; omega)
            subst i
            exact block_0005
        · by_cases h_6_9 : i.val < 7
          · have heq : i = Fin.ofNat 36 6 := Fin.ext (by change i.val = 6; omega)
            subst i
            exact block_0006
          · by_cases h_7_9 : i.val < 8
            · have heq : i = Fin.ofNat 36 7 := Fin.ext (by change i.val = 7; omega)
              subst i
              exact block_0007
            · have heq : i = Fin.ofNat 36 8 := Fin.ext (by change i.val = 8; omega)
              subst i
              exact block_0008
    · by_cases h_9_18 : i.val < 13
      · by_cases h_9_13 : i.val < 11
        · by_cases h_9_11 : i.val < 10
          · have heq : i = Fin.ofNat 36 9 := Fin.ext (by change i.val = 9; omega)
            subst i
            exact block_0009
          · have heq : i = Fin.ofNat 36 10 := Fin.ext (by change i.val = 10; omega)
            subst i
            exact block_0010
        · by_cases h_11_13 : i.val < 12
          · have heq : i = Fin.ofNat 36 11 := Fin.ext (by change i.val = 11; omega)
            subst i
            exact block_0011
          · have heq : i = Fin.ofNat 36 12 := Fin.ext (by change i.val = 12; omega)
            subst i
            exact block_0012
      · by_cases h_13_18 : i.val < 15
        · by_cases h_13_15 : i.val < 14
          · have heq : i = Fin.ofNat 36 13 := Fin.ext (by change i.val = 13; omega)
            subst i
            exact block_0013
          · have heq : i = Fin.ofNat 36 14 := Fin.ext (by change i.val = 14; omega)
            subst i
            exact block_0014
        · by_cases h_15_18 : i.val < 16
          · have heq : i = Fin.ofNat 36 15 := Fin.ext (by change i.val = 15; omega)
            subst i
            exact block_0015
          · by_cases h_16_18 : i.val < 17
            · have heq : i = Fin.ofNat 36 16 := Fin.ext (by change i.val = 16; omega)
              subst i
              exact block_0016
            · have heq : i = Fin.ofNat 36 17 := Fin.ext (by change i.val = 17; omega)
              subst i
              exact block_0017
  · by_cases h_18_36 : i.val < 27
    · by_cases h_18_27 : i.val < 22
      · by_cases h_18_22 : i.val < 20
        · by_cases h_18_20 : i.val < 19
          · have heq : i = Fin.ofNat 36 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
          · have heq : i = Fin.ofNat 36 19 := Fin.ext (by change i.val = 19; omega)
            subst i
            exact block_0019
        · by_cases h_20_22 : i.val < 21
          · have heq : i = Fin.ofNat 36 20 := Fin.ext (by change i.val = 20; omega)
            subst i
            exact block_0020
          · have heq : i = Fin.ofNat 36 21 := Fin.ext (by change i.val = 21; omega)
            subst i
            exact block_0021
      · by_cases h_22_27 : i.val < 24
        · by_cases h_22_24 : i.val < 23
          · have heq : i = Fin.ofNat 36 22 := Fin.ext (by change i.val = 22; omega)
            subst i
            exact block_0022
          · have heq : i = Fin.ofNat 36 23 := Fin.ext (by change i.val = 23; omega)
            subst i
            exact block_0023
        · by_cases h_24_27 : i.val < 25
          · have heq : i = Fin.ofNat 36 24 := Fin.ext (by change i.val = 24; omega)
            subst i
            exact block_0024
          · by_cases h_25_27 : i.val < 26
            · have heq : i = Fin.ofNat 36 25 := Fin.ext (by change i.val = 25; omega)
              subst i
              exact block_0025
            · have heq : i = Fin.ofNat 36 26 := Fin.ext (by change i.val = 26; omega)
              subst i
              exact block_0026
    · by_cases h_27_36 : i.val < 31
      · by_cases h_27_31 : i.val < 29
        · by_cases h_27_29 : i.val < 28
          · have heq : i = Fin.ofNat 36 27 := Fin.ext (by change i.val = 27; omega)
            subst i
            exact block_0027
          · have heq : i = Fin.ofNat 36 28 := Fin.ext (by change i.val = 28; omega)
            subst i
            exact block_0028
        · by_cases h_29_31 : i.val < 30
          · have heq : i = Fin.ofNat 36 29 := Fin.ext (by change i.val = 29; omega)
            subst i
            exact block_0029
          · have heq : i = Fin.ofNat 36 30 := Fin.ext (by change i.val = 30; omega)
            subst i
            exact block_0030
      · by_cases h_31_36 : i.val < 33
        · by_cases h_31_33 : i.val < 32
          · have heq : i = Fin.ofNat 36 31 := Fin.ext (by change i.val = 31; omega)
            subst i
            exact block_0031
          · have heq : i = Fin.ofNat 36 32 := Fin.ext (by change i.val = 32; omega)
            subst i
            exact block_0032
        · by_cases h_33_36 : i.val < 34
          · have heq : i = Fin.ofNat 36 33 := Fin.ext (by change i.val = 33; omega)
            subst i
            exact block_0033
          · by_cases h_34_36 : i.val < 35
            · have heq : i = Fin.ofNat 36 34 := Fin.ext (by change i.val = 34; omega)
              subst i
              exact block_0034
            · have heq : i = Fin.ofNat 36 35 := Fin.ext (by change i.val = 35; omega)
              subst i
              exact block_0035
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
