module
prelude
public import RootedSixExtra05CanonicalS5T1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSixExtra05.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 113 := i.isLt
  by_cases h_0_113 : i.val < 56
  · by_cases h_0_56 : i.val < 28
    · by_cases h_0_28 : i.val < 14
      · by_cases h_0_14 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 113 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 113 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 113 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 113 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 113 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 113 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 113 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_14 : i.val < 10
          · by_cases h_7_10 : i.val < 8
            · have heq : i = Fin.ofNat 113 7 := Fin.ext (by change i.val = 7; omega)
              subst i
              exact block_0007
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 113 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 113 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
          · by_cases h_10_14 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 113 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 113 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 113 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 113 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
      · by_cases h_14_28 : i.val < 21
        · by_cases h_14_21 : i.val < 17
          · by_cases h_14_17 : i.val < 15
            · have heq : i = Fin.ofNat 113 14 := Fin.ext (by change i.val = 14; omega)
              subst i
              exact block_0014
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 113 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 113 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 113 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 113 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 113 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 113 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
        · by_cases h_21_28 : i.val < 24
          · by_cases h_21_24 : i.val < 22
            · have heq : i = Fin.ofNat 113 21 := Fin.ext (by change i.val = 21; omega)
              subst i
              exact block_0021
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 113 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 113 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
          · by_cases h_24_28 : i.val < 26
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 113 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 113 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 113 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 113 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
    · by_cases h_28_56 : i.val < 42
      · by_cases h_28_42 : i.val < 35
        · by_cases h_28_35 : i.val < 31
          · by_cases h_28_31 : i.val < 29
            · have heq : i = Fin.ofNat 113 28 := Fin.ext (by change i.val = 28; omega)
              subst i
              exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 113 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 113 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
          · by_cases h_31_35 : i.val < 33
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 113 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 113 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 113 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 113 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
        · by_cases h_35_42 : i.val < 38
          · by_cases h_35_38 : i.val < 36
            · have heq : i = Fin.ofNat 113 35 := Fin.ext (by change i.val = 35; omega)
              subst i
              exact block_0035
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 113 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 113 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
          · by_cases h_38_42 : i.val < 40
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 113 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 113 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 113 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 113 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
      · by_cases h_42_56 : i.val < 49
        · by_cases h_42_49 : i.val < 45
          · by_cases h_42_45 : i.val < 43
            · have heq : i = Fin.ofNat 113 42 := Fin.ext (by change i.val = 42; omega)
              subst i
              exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 113 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 113 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
          · by_cases h_45_49 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 113 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 113 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 113 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 113 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
        · by_cases h_49_56 : i.val < 52
          · by_cases h_49_52 : i.val < 50
            · have heq : i = Fin.ofNat 113 49 := Fin.ext (by change i.val = 49; omega)
              subst i
              exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 113 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 113 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
          · by_cases h_52_56 : i.val < 54
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 113 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 113 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 113 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 113 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
  · by_cases h_56_113 : i.val < 84
    · by_cases h_56_84 : i.val < 70
      · by_cases h_56_70 : i.val < 63
        · by_cases h_56_63 : i.val < 59
          · by_cases h_56_59 : i.val < 57
            · have heq : i = Fin.ofNat 113 56 := Fin.ext (by change i.val = 56; omega)
              subst i
              exact block_0056
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 113 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 113 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
          · by_cases h_59_63 : i.val < 61
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 113 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 113 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 113 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 113 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
        · by_cases h_63_70 : i.val < 66
          · by_cases h_63_66 : i.val < 64
            · have heq : i = Fin.ofNat 113 63 := Fin.ext (by change i.val = 63; omega)
              subst i
              exact block_0063
            · by_cases h_64_66 : i.val < 65
              · have heq : i = Fin.ofNat 113 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · have heq : i = Fin.ofNat 113 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
          · by_cases h_66_70 : i.val < 68
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 113 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 113 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 113 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 113 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
      · by_cases h_70_84 : i.val < 77
        · by_cases h_70_77 : i.val < 73
          · by_cases h_70_73 : i.val < 71
            · have heq : i = Fin.ofNat 113 70 := Fin.ext (by change i.val = 70; omega)
              subst i
              exact block_0070
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 113 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 113 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
          · by_cases h_73_77 : i.val < 75
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 113 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 113 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 113 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 113 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
        · by_cases h_77_84 : i.val < 80
          · by_cases h_77_80 : i.val < 78
            · have heq : i = Fin.ofNat 113 77 := Fin.ext (by change i.val = 77; omega)
              subst i
              exact block_0077
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 113 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 113 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
          · by_cases h_80_84 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 113 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 113 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 113 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 113 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
    · by_cases h_84_113 : i.val < 98
      · by_cases h_84_98 : i.val < 91
        · by_cases h_84_91 : i.val < 87
          · by_cases h_84_87 : i.val < 85
            · have heq : i = Fin.ofNat 113 84 := Fin.ext (by change i.val = 84; omega)
              subst i
              exact block_0084
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 113 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 113 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
          · by_cases h_87_91 : i.val < 89
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 113 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 113 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 113 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 113 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
        · by_cases h_91_98 : i.val < 94
          · by_cases h_91_94 : i.val < 92
            · have heq : i = Fin.ofNat 113 91 := Fin.ext (by change i.val = 91; omega)
              subst i
              exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 113 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 113 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
          · by_cases h_94_98 : i.val < 96
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 113 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 113 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 113 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 113 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
      · by_cases h_98_113 : i.val < 105
        · by_cases h_98_105 : i.val < 101
          · by_cases h_98_101 : i.val < 99
            · have heq : i = Fin.ofNat 113 98 := Fin.ext (by change i.val = 98; omega)
              subst i
              exact block_0098
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 113 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 113 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
          · by_cases h_101_105 : i.val < 103
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 113 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 113 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 113 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 113 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
        · by_cases h_105_113 : i.val < 109
          · by_cases h_105_109 : i.val < 107
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 113 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 113 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 113 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 113 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
          · by_cases h_109_113 : i.val < 111
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 113 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 113 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 113 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 113 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T1
