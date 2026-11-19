module
prelude
public import RootedSixExtra02CanonicalS4T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S4T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 4 (raw i) template root
      FacetUniverses.RootedSixExtra02.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 101 := i.isLt
  by_cases h_0_101 : i.val < 50
  · by_cases h_0_50 : i.val < 25
    · by_cases h_0_25 : i.val < 12
      · by_cases h_0_12 : i.val < 6
        · by_cases h_0_6 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 101 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 101 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 101 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_6 : i.val < 4
            · have heq : i = Fin.ofNat 101 3 := Fin.ext (by change i.val = 3; omega)
              subst i
              exact block_0003
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 101 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 101 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
        · by_cases h_6_12 : i.val < 9
          · by_cases h_6_9 : i.val < 7
            · have heq : i = Fin.ofNat 101 6 := Fin.ext (by change i.val = 6; omega)
              subst i
              exact block_0006
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 101 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 101 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
          · by_cases h_9_12 : i.val < 10
            · have heq : i = Fin.ofNat 101 9 := Fin.ext (by change i.val = 9; omega)
              subst i
              exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 101 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 101 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
      · by_cases h_12_25 : i.val < 18
        · by_cases h_12_18 : i.val < 15
          · by_cases h_12_15 : i.val < 13
            · have heq : i = Fin.ofNat 101 12 := Fin.ext (by change i.val = 12; omega)
              subst i
              exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 101 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 101 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
          · by_cases h_15_18 : i.val < 16
            · have heq : i = Fin.ofNat 101 15 := Fin.ext (by change i.val = 15; omega)
              subst i
              exact block_0015
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 101 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 101 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
        · by_cases h_18_25 : i.val < 21
          · by_cases h_18_21 : i.val < 19
            · have heq : i = Fin.ofNat 101 18 := Fin.ext (by change i.val = 18; omega)
              subst i
              exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 101 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 101 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
          · by_cases h_21_25 : i.val < 23
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 101 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 101 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 101 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 101 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
    · by_cases h_25_50 : i.val < 37
      · by_cases h_25_37 : i.val < 31
        · by_cases h_25_31 : i.val < 28
          · by_cases h_25_28 : i.val < 26
            · have heq : i = Fin.ofNat 101 25 := Fin.ext (by change i.val = 25; omega)
              subst i
              exact block_0025
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 101 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 101 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
          · by_cases h_28_31 : i.val < 29
            · have heq : i = Fin.ofNat 101 28 := Fin.ext (by change i.val = 28; omega)
              subst i
              exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 101 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 101 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
        · by_cases h_31_37 : i.val < 34
          · by_cases h_31_34 : i.val < 32
            · have heq : i = Fin.ofNat 101 31 := Fin.ext (by change i.val = 31; omega)
              subst i
              exact block_0031
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 101 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 101 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
          · by_cases h_34_37 : i.val < 35
            · have heq : i = Fin.ofNat 101 34 := Fin.ext (by change i.val = 34; omega)
              subst i
              exact block_0034
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 101 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 101 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
      · by_cases h_37_50 : i.val < 43
        · by_cases h_37_43 : i.val < 40
          · by_cases h_37_40 : i.val < 38
            · have heq : i = Fin.ofNat 101 37 := Fin.ext (by change i.val = 37; omega)
              subst i
              exact block_0037
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 101 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 101 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
          · by_cases h_40_43 : i.val < 41
            · have heq : i = Fin.ofNat 101 40 := Fin.ext (by change i.val = 40; omega)
              subst i
              exact block_0040
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 101 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 101 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
        · by_cases h_43_50 : i.val < 46
          · by_cases h_43_46 : i.val < 44
            · have heq : i = Fin.ofNat 101 43 := Fin.ext (by change i.val = 43; omega)
              subst i
              exact block_0043
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 101 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 101 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
          · by_cases h_46_50 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 101 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 101 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 101 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 101 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
  · by_cases h_50_101 : i.val < 75
    · by_cases h_50_75 : i.val < 62
      · by_cases h_50_62 : i.val < 56
        · by_cases h_50_56 : i.val < 53
          · by_cases h_50_53 : i.val < 51
            · have heq : i = Fin.ofNat 101 50 := Fin.ext (by change i.val = 50; omega)
              subst i
              exact block_0050
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 101 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 101 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
          · by_cases h_53_56 : i.val < 54
            · have heq : i = Fin.ofNat 101 53 := Fin.ext (by change i.val = 53; omega)
              subst i
              exact block_0053
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 101 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 101 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
        · by_cases h_56_62 : i.val < 59
          · by_cases h_56_59 : i.val < 57
            · have heq : i = Fin.ofNat 101 56 := Fin.ext (by change i.val = 56; omega)
              subst i
              exact block_0056
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 101 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 101 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
          · by_cases h_59_62 : i.val < 60
            · have heq : i = Fin.ofNat 101 59 := Fin.ext (by change i.val = 59; omega)
              subst i
              exact block_0059
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 101 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 101 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
      · by_cases h_62_75 : i.val < 68
        · by_cases h_62_68 : i.val < 65
          · by_cases h_62_65 : i.val < 63
            · have heq : i = Fin.ofNat 101 62 := Fin.ext (by change i.val = 62; omega)
              subst i
              exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 101 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 101 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
          · by_cases h_65_68 : i.val < 66
            · have heq : i = Fin.ofNat 101 65 := Fin.ext (by change i.val = 65; omega)
              subst i
              exact block_0065
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 101 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 101 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
        · by_cases h_68_75 : i.val < 71
          · by_cases h_68_71 : i.val < 69
            · have heq : i = Fin.ofNat 101 68 := Fin.ext (by change i.val = 68; omega)
              subst i
              exact block_0068
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 101 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 101 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
          · by_cases h_71_75 : i.val < 73
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 101 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 101 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 101 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 101 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
    · by_cases h_75_101 : i.val < 88
      · by_cases h_75_88 : i.val < 81
        · by_cases h_75_81 : i.val < 78
          · by_cases h_75_78 : i.val < 76
            · have heq : i = Fin.ofNat 101 75 := Fin.ext (by change i.val = 75; omega)
              subst i
              exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 101 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 101 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
          · by_cases h_78_81 : i.val < 79
            · have heq : i = Fin.ofNat 101 78 := Fin.ext (by change i.val = 78; omega)
              subst i
              exact block_0078
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 101 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 101 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
        · by_cases h_81_88 : i.val < 84
          · by_cases h_81_84 : i.val < 82
            · have heq : i = Fin.ofNat 101 81 := Fin.ext (by change i.val = 81; omega)
              subst i
              exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 101 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 101 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
          · by_cases h_84_88 : i.val < 86
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 101 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 101 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 101 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 101 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
      · by_cases h_88_101 : i.val < 94
        · by_cases h_88_94 : i.val < 91
          · by_cases h_88_91 : i.val < 89
            · have heq : i = Fin.ofNat 101 88 := Fin.ext (by change i.val = 88; omega)
              subst i
              exact block_0088
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 101 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 101 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
          · by_cases h_91_94 : i.val < 92
            · have heq : i = Fin.ofNat 101 91 := Fin.ext (by change i.val = 91; omega)
              subst i
              exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 101 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 101 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
        · by_cases h_94_101 : i.val < 97
          · by_cases h_94_97 : i.val < 95
            · have heq : i = Fin.ofNat 101 94 := Fin.ext (by change i.val = 94; omega)
              subst i
              exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 101 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 101 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
          · by_cases h_97_101 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 101 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 101 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 101 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 101 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.S4T0
