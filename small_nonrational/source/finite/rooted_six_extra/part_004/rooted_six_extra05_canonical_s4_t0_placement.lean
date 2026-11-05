module
prelude
public import RootedSixExtra05CanonicalS4T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 4 (raw i) template root
      FacetUniverses.RootedSixExtra05.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 87 := i.isLt
  by_cases h_0_87 : i.val < 43
  · by_cases h_0_43 : i.val < 21
    · by_cases h_0_21 : i.val < 10
      · by_cases h_0_10 : i.val < 5
        · by_cases h_0_5 : i.val < 2
          · by_cases h_0_2 : i.val < 1
            · have heq : i = Fin.ofNat 87 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · have heq : i = Fin.ofNat 87 1 := Fin.ext (by change i.val = 1; omega)
              subst i
              exact block_0001
          · by_cases h_2_5 : i.val < 3
            · have heq : i = Fin.ofNat 87 2 := Fin.ext (by change i.val = 2; omega)
              subst i
              exact block_0002
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 87 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 87 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
        · by_cases h_5_10 : i.val < 7
          · by_cases h_5_7 : i.val < 6
            · have heq : i = Fin.ofNat 87 5 := Fin.ext (by change i.val = 5; omega)
              subst i
              exact block_0005
            · have heq : i = Fin.ofNat 87 6 := Fin.ext (by change i.val = 6; omega)
              subst i
              exact block_0006
          · by_cases h_7_10 : i.val < 8
            · have heq : i = Fin.ofNat 87 7 := Fin.ext (by change i.val = 7; omega)
              subst i
              exact block_0007
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 87 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 87 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
      · by_cases h_10_21 : i.val < 15
        · by_cases h_10_15 : i.val < 12
          · by_cases h_10_12 : i.val < 11
            · have heq : i = Fin.ofNat 87 10 := Fin.ext (by change i.val = 10; omega)
              subst i
              exact block_0010
            · have heq : i = Fin.ofNat 87 11 := Fin.ext (by change i.val = 11; omega)
              subst i
              exact block_0011
          · by_cases h_12_15 : i.val < 13
            · have heq : i = Fin.ofNat 87 12 := Fin.ext (by change i.val = 12; omega)
              subst i
              exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 87 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 87 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
        · by_cases h_15_21 : i.val < 18
          · by_cases h_15_18 : i.val < 16
            · have heq : i = Fin.ofNat 87 15 := Fin.ext (by change i.val = 15; omega)
              subst i
              exact block_0015
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 87 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 87 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
          · by_cases h_18_21 : i.val < 19
            · have heq : i = Fin.ofNat 87 18 := Fin.ext (by change i.val = 18; omega)
              subst i
              exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 87 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 87 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
    · by_cases h_21_43 : i.val < 32
      · by_cases h_21_32 : i.val < 26
        · by_cases h_21_26 : i.val < 23
          · by_cases h_21_23 : i.val < 22
            · have heq : i = Fin.ofNat 87 21 := Fin.ext (by change i.val = 21; omega)
              subst i
              exact block_0021
            · have heq : i = Fin.ofNat 87 22 := Fin.ext (by change i.val = 22; omega)
              subst i
              exact block_0022
          · by_cases h_23_26 : i.val < 24
            · have heq : i = Fin.ofNat 87 23 := Fin.ext (by change i.val = 23; omega)
              subst i
              exact block_0023
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 87 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 87 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
        · by_cases h_26_32 : i.val < 29
          · by_cases h_26_29 : i.val < 27
            · have heq : i = Fin.ofNat 87 26 := Fin.ext (by change i.val = 26; omega)
              subst i
              exact block_0026
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 87 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 87 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
          · by_cases h_29_32 : i.val < 30
            · have heq : i = Fin.ofNat 87 29 := Fin.ext (by change i.val = 29; omega)
              subst i
              exact block_0029
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 87 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 87 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
      · by_cases h_32_43 : i.val < 37
        · by_cases h_32_37 : i.val < 34
          · by_cases h_32_34 : i.val < 33
            · have heq : i = Fin.ofNat 87 32 := Fin.ext (by change i.val = 32; omega)
              subst i
              exact block_0032
            · have heq : i = Fin.ofNat 87 33 := Fin.ext (by change i.val = 33; omega)
              subst i
              exact block_0033
          · by_cases h_34_37 : i.val < 35
            · have heq : i = Fin.ofNat 87 34 := Fin.ext (by change i.val = 34; omega)
              subst i
              exact block_0034
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 87 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 87 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
        · by_cases h_37_43 : i.val < 40
          · by_cases h_37_40 : i.val < 38
            · have heq : i = Fin.ofNat 87 37 := Fin.ext (by change i.val = 37; omega)
              subst i
              exact block_0037
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 87 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 87 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
          · by_cases h_40_43 : i.val < 41
            · have heq : i = Fin.ofNat 87 40 := Fin.ext (by change i.val = 40; omega)
              subst i
              exact block_0040
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 87 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 87 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
  · by_cases h_43_87 : i.val < 65
    · by_cases h_43_65 : i.val < 54
      · by_cases h_43_54 : i.val < 48
        · by_cases h_43_48 : i.val < 45
          · by_cases h_43_45 : i.val < 44
            · have heq : i = Fin.ofNat 87 43 := Fin.ext (by change i.val = 43; omega)
              subst i
              exact block_0043
            · have heq : i = Fin.ofNat 87 44 := Fin.ext (by change i.val = 44; omega)
              subst i
              exact block_0044
          · by_cases h_45_48 : i.val < 46
            · have heq : i = Fin.ofNat 87 45 := Fin.ext (by change i.val = 45; omega)
              subst i
              exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 87 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 87 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
        · by_cases h_48_54 : i.val < 51
          · by_cases h_48_51 : i.val < 49
            · have heq : i = Fin.ofNat 87 48 := Fin.ext (by change i.val = 48; omega)
              subst i
              exact block_0048
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 87 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 87 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
          · by_cases h_51_54 : i.val < 52
            · have heq : i = Fin.ofNat 87 51 := Fin.ext (by change i.val = 51; omega)
              subst i
              exact block_0051
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 87 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 87 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
      · by_cases h_54_65 : i.val < 59
        · by_cases h_54_59 : i.val < 56
          · by_cases h_54_56 : i.val < 55
            · have heq : i = Fin.ofNat 87 54 := Fin.ext (by change i.val = 54; omega)
              subst i
              exact block_0054
            · have heq : i = Fin.ofNat 87 55 := Fin.ext (by change i.val = 55; omega)
              subst i
              exact block_0055
          · by_cases h_56_59 : i.val < 57
            · have heq : i = Fin.ofNat 87 56 := Fin.ext (by change i.val = 56; omega)
              subst i
              exact block_0056
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 87 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 87 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
        · by_cases h_59_65 : i.val < 62
          · by_cases h_59_62 : i.val < 60
            · have heq : i = Fin.ofNat 87 59 := Fin.ext (by change i.val = 59; omega)
              subst i
              exact block_0059
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 87 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 87 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
          · by_cases h_62_65 : i.val < 63
            · have heq : i = Fin.ofNat 87 62 := Fin.ext (by change i.val = 62; omega)
              subst i
              exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 87 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 87 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
    · by_cases h_65_87 : i.val < 76
      · by_cases h_65_76 : i.val < 70
        · by_cases h_65_70 : i.val < 67
          · by_cases h_65_67 : i.val < 66
            · have heq : i = Fin.ofNat 87 65 := Fin.ext (by change i.val = 65; omega)
              subst i
              exact block_0065
            · have heq : i = Fin.ofNat 87 66 := Fin.ext (by change i.val = 66; omega)
              subst i
              exact block_0066
          · by_cases h_67_70 : i.val < 68
            · have heq : i = Fin.ofNat 87 67 := Fin.ext (by change i.val = 67; omega)
              subst i
              exact block_0067
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 87 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 87 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
        · by_cases h_70_76 : i.val < 73
          · by_cases h_70_73 : i.val < 71
            · have heq : i = Fin.ofNat 87 70 := Fin.ext (by change i.val = 70; omega)
              subst i
              exact block_0070
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 87 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 87 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
          · by_cases h_73_76 : i.val < 74
            · have heq : i = Fin.ofNat 87 73 := Fin.ext (by change i.val = 73; omega)
              subst i
              exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 87 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 87 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
      · by_cases h_76_87 : i.val < 81
        · by_cases h_76_81 : i.val < 78
          · by_cases h_76_78 : i.val < 77
            · have heq : i = Fin.ofNat 87 76 := Fin.ext (by change i.val = 76; omega)
              subst i
              exact block_0076
            · have heq : i = Fin.ofNat 87 77 := Fin.ext (by change i.val = 77; omega)
              subst i
              exact block_0077
          · by_cases h_78_81 : i.val < 79
            · have heq : i = Fin.ofNat 87 78 := Fin.ext (by change i.val = 78; omega)
              subst i
              exact block_0078
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 87 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 87 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
        · by_cases h_81_87 : i.val < 84
          · by_cases h_81_84 : i.val < 82
            · have heq : i = Fin.ofNat 87 81 := Fin.ext (by change i.val = 81; omega)
              subst i
              exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 87 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 87 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
          · by_cases h_84_87 : i.val < 85
            · have heq : i = Fin.ofNat 87 84 := Fin.ext (by change i.val = 84; omega)
              subst i
              exact block_0084
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 87 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 87 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
