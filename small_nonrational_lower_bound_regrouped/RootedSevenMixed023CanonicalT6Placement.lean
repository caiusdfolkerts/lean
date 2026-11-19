module
prelude
public import RootedSevenMixed023CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSevenMixed023.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 18 := i.isLt
  by_cases h_0_18 : i.val < 9
  · by_cases h_0_9 : i.val < 4
    · by_cases h_0_4 : i.val < 2
      · by_cases h_0_2 : i.val < 1
        · have heq : i = Fin.ofNat 18 0 := Fin.ext (by change i.val = 0; omega)
          subst i
          exact block_0000
        · have heq : i = Fin.ofNat 18 1 := Fin.ext (by change i.val = 1; omega)
          subst i
          exact block_0001
      · by_cases h_2_4 : i.val < 3
        · have heq : i = Fin.ofNat 18 2 := Fin.ext (by change i.val = 2; omega)
          subst i
          exact block_0002
        · have heq : i = Fin.ofNat 18 3 := Fin.ext (by change i.val = 3; omega)
          subst i
          exact block_0003
    · by_cases h_4_9 : i.val < 6
      · by_cases h_4_6 : i.val < 5
        · have heq : i = Fin.ofNat 18 4 := Fin.ext (by change i.val = 4; omega)
          subst i
          exact block_0004
        · have heq : i = Fin.ofNat 18 5 := Fin.ext (by change i.val = 5; omega)
          subst i
          exact block_0005
      · by_cases h_6_9 : i.val < 7
        · have heq : i = Fin.ofNat 18 6 := Fin.ext (by change i.val = 6; omega)
          subst i
          exact block_0006
        · by_cases h_7_9 : i.val < 8
          · have heq : i = Fin.ofNat 18 7 := Fin.ext (by change i.val = 7; omega)
            subst i
            exact block_0007
          · have heq : i = Fin.ofNat 18 8 := Fin.ext (by change i.val = 8; omega)
            subst i
            exact block_0008
  · by_cases h_9_18 : i.val < 13
    · by_cases h_9_13 : i.val < 11
      · by_cases h_9_11 : i.val < 10
        · have heq : i = Fin.ofNat 18 9 := Fin.ext (by change i.val = 9; omega)
          subst i
          exact block_0009
        · have heq : i = Fin.ofNat 18 10 := Fin.ext (by change i.val = 10; omega)
          subst i
          exact block_0010
      · by_cases h_11_13 : i.val < 12
        · have heq : i = Fin.ofNat 18 11 := Fin.ext (by change i.val = 11; omega)
          subst i
          exact block_0011
        · have heq : i = Fin.ofNat 18 12 := Fin.ext (by change i.val = 12; omega)
          subst i
          exact block_0012
    · by_cases h_13_18 : i.val < 15
      · by_cases h_13_15 : i.val < 14
        · have heq : i = Fin.ofNat 18 13 := Fin.ext (by change i.val = 13; omega)
          subst i
          exact block_0013
        · have heq : i = Fin.ofNat 18 14 := Fin.ext (by change i.val = 14; omega)
          subst i
          exact block_0014
      · by_cases h_15_18 : i.val < 16
        · have heq : i = Fin.ofNat 18 15 := Fin.ext (by change i.val = 15; omega)
          subst i
          exact block_0015
        · by_cases h_16_18 : i.val < 17
          · have heq : i = Fin.ofNat 18 16 := Fin.ext (by change i.val = 16; omega)
            subst i
            exact block_0016
          · have heq : i = Fin.ofNat 18 17 := Fin.ext (by change i.val = 17; omega)
            subst i
            exact block_0017
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed023.T6
