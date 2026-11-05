module
prelude
public import RootedSevenMixed001CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenMixed001.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 19 := i.isLt
  by_cases h_0_19 : i.val < 9
  · by_cases h_0_9 : i.val < 4
    · by_cases h_0_4 : i.val < 2
      · by_cases h_0_2 : i.val < 1
        · have heq : i = Fin.ofNat 19 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · have heq : i = Fin.ofNat 19 1 := Fin.ext (by change i.val = 1; omega)
          subst i
          exact block_0001
      · by_cases h_2_4 : i.val < 3
        · have heq : i = Fin.ofNat 19 2 := Fin.ext (by change i.val = 2; omega)
          subst i
          exact block_0002
        · have heq : i = Fin.ofNat 19 3 := Fin.ext (by change i.val = 3; omega)
          subst i
          exact block_0003
    · by_cases h_4_9 : i.val < 6
      · by_cases h_4_6 : i.val < 5
        · have heq : i = Fin.ofNat 19 4 := Fin.ext (by change i.val = 4; omega)
          subst i
          exact block_0004
        · have heq : i = Fin.ofNat 19 5 := Fin.ext (by change i.val = 5; omega)
          subst i
          exact block_0005
      · by_cases h_6_9 : i.val < 7
        · have heq : i = Fin.ofNat 19 6 := Fin.ext (by change i.val = 6; omega)
          subst i
          exact block_0006
        · by_cases h_7_9 : i.val < 8
          · have heq : i = Fin.ofNat 19 7 := Fin.ext (by change i.val = 7; omega)
            subst i
            exact block_0007
          · have heq : i = Fin.ofNat 19 8 := Fin.ext (by change i.val = 8; omega)
            subst i
            exact block_0008
  · by_cases h_9_19 : i.val < 14
    · by_cases h_9_14 : i.val < 11
      · by_cases h_9_11 : i.val < 10
        · have heq : i = Fin.ofNat 19 9 := Fin.ext (by change i.val = 9; omega)
          subst i
          exact block_0009
        · have heq : i = Fin.ofNat 19 10 := Fin.ext (by change i.val = 10; omega)
          subst i
          exact block_0010
      · by_cases h_11_14 : i.val < 12
        · have heq : i = Fin.ofNat 19 11 := Fin.ext (by change i.val = 11; omega)
          subst i
          exact block_0011
        · by_cases h_12_14 : i.val < 13
          · have heq : i = Fin.ofNat 19 12 := Fin.ext (by change i.val = 12; omega)
            subst i
            exact block_0012
          · have heq : i = Fin.ofNat 19 13 := Fin.ext (by change i.val = 13; omega)
            subst i
            exact block_0013
    · by_cases h_14_19 : i.val < 16
      · by_cases h_14_16 : i.val < 15
        · have heq : i = Fin.ofNat 19 14 := Fin.ext (by change i.val = 14; omega)
          subst i
          exact block_0014
        · have heq : i = Fin.ofNat 19 15 := Fin.ext (by change i.val = 15; omega)
          subst i
          exact block_0015
      · by_cases h_16_19 : i.val < 17
        · have heq : i = Fin.ofNat 19 16 := Fin.ext (by change i.val = 16; omega)
          subst i
          exact block_0016
        · by_cases h_17_19 : i.val < 18
          · have heq : i = Fin.ofNat 19 17 := Fin.ext (by change i.val = 17; omega)
            subst i
            exact block_0017
          · have heq : i = Fin.ofNat 19 18 := Fin.ext (by change i.val = 18; omega)
            subst i
            exact block_0018
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed001.T6
