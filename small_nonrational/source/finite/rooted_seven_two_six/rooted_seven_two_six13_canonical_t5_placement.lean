module
prelude
public import RootedSevenTwoSix13CanonicalT5Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenTwoSix13.T5
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenTwoSix13.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 22 := i.isLt
  by_cases h_0_22 : i.val < 11
  · by_cases h_0_11 : i.val < 5
    · by_cases h_0_5 : i.val < 2
      · by_cases h_0_2 : i.val < 1
        · have heq : i = Fin.ofNat 22 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · have heq : i = Fin.ofNat 22 1 := Fin.ext (by change i.val = 1; omega)
          subst i
          exact block_0001
      · by_cases h_2_5 : i.val < 3
        · have heq : i = Fin.ofNat 22 2 := Fin.ext (by change i.val = 2; omega)
          subst i
          exact block_0002
        · by_cases h_3_5 : i.val < 4
          · have heq : i = Fin.ofNat 22 3 := Fin.ext (by change i.val = 3; omega)
            subst i
            exact block_0003
          · have heq : i = Fin.ofNat 22 4 := Fin.ext (by change i.val = 4; omega)
            subst i
            exact block_0004
    · by_cases h_5_11 : i.val < 8
      · by_cases h_5_8 : i.val < 6
        · have heq : i = Fin.ofNat 22 5 := Fin.ext (by change i.val = 5; omega)
          subst i
          exact block_0005
        · by_cases h_6_8 : i.val < 7
          · have heq : i = Fin.ofNat 22 6 := Fin.ext (by change i.val = 6; omega)
            subst i
            exact block_0006
          · have heq : i = Fin.ofNat 22 7 := Fin.ext (by change i.val = 7; omega)
            subst i
            exact block_0007
      · by_cases h_8_11 : i.val < 9
        · have heq : i = Fin.ofNat 22 8 := Fin.ext (by change i.val = 8; omega)
          subst i
          exact block_0008
        · by_cases h_9_11 : i.val < 10
          · have heq : i = Fin.ofNat 22 9 := Fin.ext (by change i.val = 9; omega)
            subst i
            exact block_0009
          · have heq : i = Fin.ofNat 22 10 := Fin.ext (by change i.val = 10; omega)
            subst i
            exact block_0010
  · by_cases h_11_22 : i.val < 16
    · by_cases h_11_16 : i.val < 13
      · by_cases h_11_13 : i.val < 12
        · have heq : i = Fin.ofNat 22 11 := Fin.ext (by change i.val = 11; omega)
          subst i
          exact block_0011
        · have heq : i = Fin.ofNat 22 12 := Fin.ext (by change i.val = 12; omega)
          subst i
          exact block_0012
      · by_cases h_13_16 : i.val < 14
        · have heq : i = Fin.ofNat 22 13 := Fin.ext (by change i.val = 13; omega)
          subst i
          exact block_0013
        · by_cases h_14_16 : i.val < 15
          · have heq : i = Fin.ofNat 22 14 := Fin.ext (by change i.val = 14; omega)
            subst i
            exact block_0014
          · have heq : i = Fin.ofNat 22 15 := Fin.ext (by change i.val = 15; omega)
            subst i
            exact block_0015
    · by_cases h_16_22 : i.val < 19
      · by_cases h_16_19 : i.val < 17
        · have heq : i = Fin.ofNat 22 16 := Fin.ext (by change i.val = 16; omega)
          subst i
          exact block_0016
        · by_cases h_17_19 : i.val < 18
          · have heq : i = Fin.ofNat 22 17 := Fin.ext (by change i.val = 17; omega)
            subst i
            exact block_0017
          · have heq : i = Fin.ofNat 22 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
      · by_cases h_19_22 : i.val < 20
        · have heq : i = Fin.ofNat 22 19 := Fin.ext (by change i.val = 19; omega)
          subst i
          exact block_0019
        · by_cases h_20_22 : i.val < 21
          · have heq : i = Fin.ofNat 22 20 := Fin.ext (by change i.val = 20; omega)
            subst i
            exact block_0020
          · have heq : i = Fin.ofNat 22 21 := Fin.ext (by change i.val = 21; omega)
            subst i
            exact block_0021
end Papers.RationalityTen.RootedCanonical.RootedSevenTwoSix13.T5
