module
prelude
public import RootedSevenMixed029CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenMixed029.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 111 := i.isLt
  by_cases h_0_111 : i.val < 55
  · by_cases h_0_55 : i.val < 27
    · by_cases h_0_27 : i.val < 13
      · by_cases h_0_13 : i.val < 6
        · by_cases h_0_6 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 111 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 111 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 111 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_6 : i.val < 4
            · have heq : i = Fin.ofNat 111 3 := Fin.ext (by change i.val = 3; omega)
              subst i
              exact block_0003
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 111 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 111 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
        · by_cases h_6_13 : i.val < 9
          · by_cases h_6_9 : i.val < 7
            · have heq : i = Fin.ofNat 111 6 := Fin.ext (by change i.val = 6; omega)
              subst i
              exact block_0006
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 111 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 111 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
          · by_cases h_9_13 : i.val < 11
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 111 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 111 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 111 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 111 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
      · by_cases h_13_27 : i.val < 20
        · by_cases h_13_20 : i.val < 16
          · by_cases h_13_16 : i.val < 14
            · have heq : i = Fin.ofNat 111 13 := Fin.ext (by change i.val = 13; omega)
              subst i
              exact block_0013
            · by_cases h_14_16 : i.val < 15
              · have heq : i = Fin.ofNat 111 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · have heq : i = Fin.ofNat 111 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
          · by_cases h_16_20 : i.val < 18
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 111 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 111 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 111 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 111 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
        · by_cases h_20_27 : i.val < 23
          · by_cases h_20_23 : i.val < 21
            · have heq : i = Fin.ofNat 111 20 := Fin.ext (by change i.val = 20; omega)
              subst i
              exact block_0020
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 111 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 111 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
          · by_cases h_23_27 : i.val < 25
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 111 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 111 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 111 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 111 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
    · by_cases h_27_55 : i.val < 41
      · by_cases h_27_41 : i.val < 34
        · by_cases h_27_34 : i.val < 30
          · by_cases h_27_30 : i.val < 28
            · have heq : i = Fin.ofNat 111 27 := Fin.ext (by change i.val = 27; omega)
              subst i
              exact block_0027
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 111 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 111 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
          · by_cases h_30_34 : i.val < 32
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 111 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 111 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 111 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 111 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
        · by_cases h_34_41 : i.val < 37
          · by_cases h_34_37 : i.val < 35
            · have heq : i = Fin.ofNat 111 34 := Fin.ext (by change i.val = 34; omega)
              subst i
              exact block_0034
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 111 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 111 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
          · by_cases h_37_41 : i.val < 39
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 111 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 111 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 111 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 111 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
      · by_cases h_41_55 : i.val < 48
        · by_cases h_41_48 : i.val < 44
          · by_cases h_41_44 : i.val < 42
            · have heq : i = Fin.ofNat 111 41 := Fin.ext (by change i.val = 41; omega)
              subst i
              exact block_0041
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 111 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 111 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
          · by_cases h_44_48 : i.val < 46
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 111 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 111 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 111 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 111 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
        · by_cases h_48_55 : i.val < 51
          · by_cases h_48_51 : i.val < 49
            · have heq : i = Fin.ofNat 111 48 := Fin.ext (by change i.val = 48; omega)
              subst i
              exact block_0048
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 111 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 111 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
          · by_cases h_51_55 : i.val < 53
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 111 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 111 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 111 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 111 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
  · by_cases h_55_111 : i.val < 83
    · by_cases h_55_83 : i.val < 69
      · by_cases h_55_69 : i.val < 62
        · by_cases h_55_62 : i.val < 58
          · by_cases h_55_58 : i.val < 56
            · have heq : i = Fin.ofNat 111 55 := Fin.ext (by change i.val = 55; omega)
              subst i
              exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 111 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 111 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
          · by_cases h_58_62 : i.val < 60
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 111 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 111 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 111 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 111 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
        · by_cases h_62_69 : i.val < 65
          · by_cases h_62_65 : i.val < 63
            · have heq : i = Fin.ofNat 111 62 := Fin.ext (by change i.val = 62; omega)
              subst i
              exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 111 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 111 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
          · by_cases h_65_69 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 111 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 111 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 111 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 111 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
      · by_cases h_69_83 : i.val < 76
        · by_cases h_69_76 : i.val < 72
          · by_cases h_69_72 : i.val < 70
            · have heq : i = Fin.ofNat 111 69 := Fin.ext (by change i.val = 69; omega)
              subst i
              exact block_0069
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 111 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 111 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
          · by_cases h_72_76 : i.val < 74
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 111 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 111 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 111 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 111 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
        · by_cases h_76_83 : i.val < 79
          · by_cases h_76_79 : i.val < 77
            · have heq : i = Fin.ofNat 111 76 := Fin.ext (by change i.val = 76; omega)
              subst i
              exact block_0076
            · by_cases h_77_79 : i.val < 78
              · have heq : i = Fin.ofNat 111 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · have heq : i = Fin.ofNat 111 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
          · by_cases h_79_83 : i.val < 81
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 111 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 111 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 111 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 111 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
    · by_cases h_83_111 : i.val < 97
      · by_cases h_83_97 : i.val < 90
        · by_cases h_83_90 : i.val < 86
          · by_cases h_83_86 : i.val < 84
            · have heq : i = Fin.ofNat 111 83 := Fin.ext (by change i.val = 83; omega)
              subst i
              exact block_0083
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 111 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 111 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
          · by_cases h_86_90 : i.val < 88
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 111 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 111 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 111 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 111 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
        · by_cases h_90_97 : i.val < 93
          · by_cases h_90_93 : i.val < 91
            · have heq : i = Fin.ofNat 111 90 := Fin.ext (by change i.val = 90; omega)
              subst i
              exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 111 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 111 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
          · by_cases h_93_97 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 111 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 111 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 111 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 111 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
      · by_cases h_97_111 : i.val < 104
        · by_cases h_97_104 : i.val < 100
          · by_cases h_97_100 : i.val < 98
            · have heq : i = Fin.ofNat 111 97 := Fin.ext (by change i.val = 97; omega)
              subst i
              exact block_0097
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 111 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 111 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
          · by_cases h_100_104 : i.val < 102
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 111 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 111 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 111 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 111 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
        · by_cases h_104_111 : i.val < 107
          · by_cases h_104_107 : i.val < 105
            · have heq : i = Fin.ofNat 111 104 := Fin.ext (by change i.val = 104; omega)
              subst i
              exact block_0104
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 111 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 111 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
          · by_cases h_107_111 : i.val < 109
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 111 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 111 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 111 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 111 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed029.S5T0
