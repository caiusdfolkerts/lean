module
prelude
public import RootedSevenMixed010CanonicalT2Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenMixed010.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 32 := i.isLt
  by_cases h_0_32 : i.val < 16
  · by_cases h_0_16 : i.val < 8
    · by_cases h_0_8 : i.val < 4
      · by_cases h_0_4 : i.val < 2
        · by_cases h_0_2 : i.val < 1
          · have heq : i = Fin.ofNat 32 0 := Fin.ext (by change i.val = 0; omega)
            subst i
            exact block_0000
          · have heq : i = Fin.ofNat 32 1 := Fin.ext (by change i.val = 1; omega)
            subst i
            exact block_0001
        · by_cases h_2_4 : i.val < 3
          · have heq : i = Fin.ofNat 32 2 := Fin.ext (by change i.val = 2; omega)
            subst i
            exact block_0002
          · have heq : i = Fin.ofNat 32 3 := Fin.ext (by change i.val = 3; omega)
            subst i
            exact block_0003
      · by_cases h_4_8 : i.val < 6
        · by_cases h_4_6 : i.val < 5
          · have heq : i = Fin.ofNat 32 4 := Fin.ext (by change i.val = 4; omega)
            subst i
            exact block_0004
          · have heq : i = Fin.ofNat 32 5 := Fin.ext (by change i.val = 5; omega)
            subst i
            exact block_0005
        · by_cases h_6_8 : i.val < 7
          · have heq : i = Fin.ofNat 32 6 := Fin.ext (by change i.val = 6; omega)
            subst i
            exact block_0006
          · have heq : i = Fin.ofNat 32 7 := Fin.ext (by change i.val = 7; omega)
            subst i
            exact block_0007
    · by_cases h_8_16 : i.val < 12
      · by_cases h_8_12 : i.val < 10
        · by_cases h_8_10 : i.val < 9
          · have heq : i = Fin.ofNat 32 8 := Fin.ext (by change i.val = 8; omega)
            subst i
            exact block_0008
          · have heq : i = Fin.ofNat 32 9 := Fin.ext (by change i.val = 9; omega)
            subst i
            exact block_0009
        · by_cases h_10_12 : i.val < 11
          · have heq : i = Fin.ofNat 32 10 := Fin.ext (by change i.val = 10; omega)
            subst i
            exact block_0010
          · have heq : i = Fin.ofNat 32 11 := Fin.ext (by change i.val = 11; omega)
            subst i
            exact block_0011
      · by_cases h_12_16 : i.val < 14
        · by_cases h_12_14 : i.val < 13
          · have heq : i = Fin.ofNat 32 12 := Fin.ext (by change i.val = 12; omega)
            subst i
            exact block_0012
          · have heq : i = Fin.ofNat 32 13 := Fin.ext (by change i.val = 13; omega)
            subst i
            exact block_0013
        · by_cases h_14_16 : i.val < 15
          · have heq : i = Fin.ofNat 32 14 := Fin.ext (by change i.val = 14; omega)
            subst i
            exact block_0014
          · have heq : i = Fin.ofNat 32 15 := Fin.ext (by change i.val = 15; omega)
            subst i
            exact block_0015
  · by_cases h_16_32 : i.val < 24
    · by_cases h_16_24 : i.val < 20
      · by_cases h_16_20 : i.val < 18
        · by_cases h_16_18 : i.val < 17
          · have heq : i = Fin.ofNat 32 16 := Fin.ext (by change i.val = 16; omega)
            subst i
            exact block_0016
          · have heq : i = Fin.ofNat 32 17 := Fin.ext (by change i.val = 17; omega)
            subst i
            exact block_0017
        · by_cases h_18_20 : i.val < 19
          · have heq : i = Fin.ofNat 32 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
          · have heq : i = Fin.ofNat 32 19 := Fin.ext (by change i.val = 19; omega)
            subst i
            exact block_0019
      · by_cases h_20_24 : i.val < 22
        · by_cases h_20_22 : i.val < 21
          · have heq : i = Fin.ofNat 32 20 := Fin.ext (by change i.val = 20; omega)
            subst i
            exact block_0020
          · have heq : i = Fin.ofNat 32 21 := Fin.ext (by change i.val = 21; omega)
            subst i
            exact block_0021
        · by_cases h_22_24 : i.val < 23
          · have heq : i = Fin.ofNat 32 22 := Fin.ext (by change i.val = 22; omega)
            subst i
            exact block_0022
          · have heq : i = Fin.ofNat 32 23 := Fin.ext (by change i.val = 23; omega)
            subst i
            exact block_0023
    · by_cases h_24_32 : i.val < 28
      · by_cases h_24_28 : i.val < 26
        · by_cases h_24_26 : i.val < 25
          · have heq : i = Fin.ofNat 32 24 := Fin.ext (by change i.val = 24; omega)
            subst i
            exact block_0024
          · have heq : i = Fin.ofNat 32 25 := Fin.ext (by change i.val = 25; omega)
            subst i
            exact block_0025
        · by_cases h_26_28 : i.val < 27
          · have heq : i = Fin.ofNat 32 26 := Fin.ext (by change i.val = 26; omega)
            subst i
            exact block_0026
          · have heq : i = Fin.ofNat 32 27 := Fin.ext (by change i.val = 27; omega)
            subst i
            exact block_0027
      · by_cases h_28_32 : i.val < 30
        · by_cases h_28_30 : i.val < 29
          · have heq : i = Fin.ofNat 32 28 := Fin.ext (by change i.val = 28; omega)
            subst i
            exact block_0028
          · have heq : i = Fin.ofNat 32 29 := Fin.ext (by change i.val = 29; omega)
            subst i
            exact block_0029
        · by_cases h_30_32 : i.val < 31
          · have heq : i = Fin.ofNat 32 30 := Fin.ext (by change i.val = 30; omega)
            subst i
            exact block_0030
          · have heq : i = Fin.ofNat 32 31 := Fin.ext (by change i.val = 31; omega)
            subst i
            exact block_0031
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
