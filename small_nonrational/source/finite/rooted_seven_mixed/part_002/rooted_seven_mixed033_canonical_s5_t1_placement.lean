module
prelude
public import RootedSevenMixed033CanonicalS5T1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.S5T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenMixed033.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 117 := i.isLt
  by_cases h_0_117 : i.val < 58
  · by_cases h_0_58 : i.val < 29
    · by_cases h_0_29 : i.val < 14
      · by_cases h_0_14 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 117 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 117 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 117 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 117 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 117 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 117 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 117 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_14 : i.val < 10
          · by_cases h_7_10 : i.val < 8
            · have heq : i = Fin.ofNat 117 7 := Fin.ext (by change i.val = 7; omega)
              subst i
              exact block_0007
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 117 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 117 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
          · by_cases h_10_14 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 117 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 117 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 117 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 117 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
      · by_cases h_14_29 : i.val < 21
        · by_cases h_14_21 : i.val < 17
          · by_cases h_14_17 : i.val < 15
            · have heq : i = Fin.ofNat 117 14 := Fin.ext (by change i.val = 14; omega)
              subst i
              exact block_0014
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 117 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 117 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 117 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 117 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 117 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 117 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
        · by_cases h_21_29 : i.val < 25
          · by_cases h_21_25 : i.val < 23
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 117 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 117 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 117 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 117 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
          · by_cases h_25_29 : i.val < 27
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 117 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 117 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 117 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 117 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
    · by_cases h_29_58 : i.val < 43
      · by_cases h_29_43 : i.val < 36
        · by_cases h_29_36 : i.val < 32
          · by_cases h_29_32 : i.val < 30
            · have heq : i = Fin.ofNat 117 29 := Fin.ext (by change i.val = 29; omega)
              subst i
              exact block_0029
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 117 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 117 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
          · by_cases h_32_36 : i.val < 34
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 117 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 117 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 117 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 117 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
        · by_cases h_36_43 : i.val < 39
          · by_cases h_36_39 : i.val < 37
            · have heq : i = Fin.ofNat 117 36 := Fin.ext (by change i.val = 36; omega)
              subst i
              exact block_0036
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 117 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 117 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
          · by_cases h_39_43 : i.val < 41
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 117 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 117 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 117 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 117 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
      · by_cases h_43_58 : i.val < 50
        · by_cases h_43_50 : i.val < 46
          · by_cases h_43_46 : i.val < 44
            · have heq : i = Fin.ofNat 117 43 := Fin.ext (by change i.val = 43; omega)
              subst i
              exact block_0043
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 117 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 117 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
          · by_cases h_46_50 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 117 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 117 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 117 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 117 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
        · by_cases h_50_58 : i.val < 54
          · by_cases h_50_54 : i.val < 52
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 117 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 117 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 117 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 117 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
          · by_cases h_54_58 : i.val < 56
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 117 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 117 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 117 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 117 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
  · by_cases h_58_117 : i.val < 87
    · by_cases h_58_87 : i.val < 72
      · by_cases h_58_72 : i.val < 65
        · by_cases h_58_65 : i.val < 61
          · by_cases h_58_61 : i.val < 59
            · have heq : i = Fin.ofNat 117 58 := Fin.ext (by change i.val = 58; omega)
              subst i
              exact block_0058
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 117 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 117 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
          · by_cases h_61_65 : i.val < 63
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 117 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 117 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 117 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 117 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
        · by_cases h_65_72 : i.val < 68
          · by_cases h_65_68 : i.val < 66
            · have heq : i = Fin.ofNat 117 65 := Fin.ext (by change i.val = 65; omega)
              subst i
              exact block_0065
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 117 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 117 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
          · by_cases h_68_72 : i.val < 70
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 117 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 117 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 117 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 117 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
      · by_cases h_72_87 : i.val < 79
        · by_cases h_72_79 : i.val < 75
          · by_cases h_72_75 : i.val < 73
            · have heq : i = Fin.ofNat 117 72 := Fin.ext (by change i.val = 72; omega)
              subst i
              exact block_0072
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 117 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 117 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
          · by_cases h_75_79 : i.val < 77
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 117 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 117 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
            · by_cases h_77_79 : i.val < 78
              · have heq : i = Fin.ofNat 117 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · have heq : i = Fin.ofNat 117 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
        · by_cases h_79_87 : i.val < 83
          · by_cases h_79_83 : i.val < 81
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 117 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 117 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 117 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 117 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
          · by_cases h_83_87 : i.val < 85
            · by_cases h_83_85 : i.val < 84
              · have heq : i = Fin.ofNat 117 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
              · have heq : i = Fin.ofNat 117 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 117 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 117 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
    · by_cases h_87_117 : i.val < 102
      · by_cases h_87_102 : i.val < 94
        · by_cases h_87_94 : i.val < 90
          · by_cases h_87_90 : i.val < 88
            · have heq : i = Fin.ofNat 117 87 := Fin.ext (by change i.val = 87; omega)
              subst i
              exact block_0087
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 117 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 117 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
          · by_cases h_90_94 : i.val < 92
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 117 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 117 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 117 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 117 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
        · by_cases h_94_102 : i.val < 98
          · by_cases h_94_98 : i.val < 96
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 117 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 117 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 117 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 117 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
          · by_cases h_98_102 : i.val < 100
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 117 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 117 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 117 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 117 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
      · by_cases h_102_117 : i.val < 109
        · by_cases h_102_109 : i.val < 105
          · by_cases h_102_105 : i.val < 103
            · have heq : i = Fin.ofNat 117 102 := Fin.ext (by change i.val = 102; omega)
              subst i
              exact block_0102
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 117 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 117 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
          · by_cases h_105_109 : i.val < 107
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 117 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 117 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 117 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 117 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
        · by_cases h_109_117 : i.val < 113
          · by_cases h_109_113 : i.val < 111
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 117 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 117 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 117 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 117 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
          · by_cases h_113_117 : i.val < 115
            · by_cases h_113_115 : i.val < 114
              · have heq : i = Fin.ofNat 117 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · have heq : i = Fin.ofNat 117 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
            · by_cases h_115_117 : i.val < 116
              · have heq : i = Fin.ofNat 117 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
              · have heq : i = Fin.ofNat 117 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.S5T1
