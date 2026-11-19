module
prelude
public import RootedSixBase04CanonicalS4T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 4 (raw i) template root
      FacetUniverses.RootedSixBase04.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 129 := i.isLt
  by_cases h_0_129 : i.val < 64
  · by_cases h_0_64 : i.val < 32
    · by_cases h_0_32 : i.val < 16
      · by_cases h_0_16 : i.val < 8
        · by_cases h_0_8 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 129 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 129 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 129 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 129 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_8 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 129 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 129 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_8 : i.val < 7
              · have heq : i = Fin.ofNat 129 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · have heq : i = Fin.ofNat 129 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
        · by_cases h_8_16 : i.val < 12
          · by_cases h_8_12 : i.val < 10
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 129 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 129 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 129 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 129 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
          · by_cases h_12_16 : i.val < 14
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 129 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 129 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
            · by_cases h_14_16 : i.val < 15
              · have heq : i = Fin.ofNat 129 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · have heq : i = Fin.ofNat 129 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
      · by_cases h_16_32 : i.val < 24
        · by_cases h_16_24 : i.val < 20
          · by_cases h_16_20 : i.val < 18
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 129 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 129 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 129 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 129 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
          · by_cases h_20_24 : i.val < 22
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 129 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 129 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 129 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 129 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
        · by_cases h_24_32 : i.val < 28
          · by_cases h_24_28 : i.val < 26
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 129 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 129 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 129 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 129 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
          · by_cases h_28_32 : i.val < 30
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 129 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 129 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 129 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 129 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
    · by_cases h_32_64 : i.val < 48
      · by_cases h_32_48 : i.val < 40
        · by_cases h_32_40 : i.val < 36
          · by_cases h_32_36 : i.val < 34
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 129 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 129 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 129 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 129 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
          · by_cases h_36_40 : i.val < 38
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 129 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 129 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 129 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 129 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
        · by_cases h_40_48 : i.val < 44
          · by_cases h_40_44 : i.val < 42
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 129 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 129 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 129 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 129 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
          · by_cases h_44_48 : i.val < 46
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 129 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 129 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 129 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 129 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
      · by_cases h_48_64 : i.val < 56
        · by_cases h_48_56 : i.val < 52
          · by_cases h_48_52 : i.val < 50
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 129 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 129 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 129 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 129 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
          · by_cases h_52_56 : i.val < 54
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 129 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 129 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 129 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 129 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
        · by_cases h_56_64 : i.val < 60
          · by_cases h_56_60 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 129 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 129 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 129 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 129 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
          · by_cases h_60_64 : i.val < 62
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 129 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 129 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 129 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 129 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
  · by_cases h_64_129 : i.val < 96
    · by_cases h_64_96 : i.val < 80
      · by_cases h_64_80 : i.val < 72
        · by_cases h_64_72 : i.val < 68
          · by_cases h_64_68 : i.val < 66
            · by_cases h_64_66 : i.val < 65
              · have heq : i = Fin.ofNat 129 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · have heq : i = Fin.ofNat 129 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 129 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 129 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
          · by_cases h_68_72 : i.val < 70
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 129 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 129 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 129 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 129 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
        · by_cases h_72_80 : i.val < 76
          · by_cases h_72_76 : i.val < 74
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 129 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 129 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 129 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 129 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
          · by_cases h_76_80 : i.val < 78
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 129 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 129 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 129 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 129 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
      · by_cases h_80_96 : i.val < 88
        · by_cases h_80_88 : i.val < 84
          · by_cases h_80_84 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 129 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 129 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 129 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 129 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
          · by_cases h_84_88 : i.val < 86
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 129 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 129 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 129 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 129 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
        · by_cases h_88_96 : i.val < 92
          · by_cases h_88_92 : i.val < 90
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 129 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 129 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 129 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 129 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
          · by_cases h_92_96 : i.val < 94
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 129 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 129 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 129 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 129 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
    · by_cases h_96_129 : i.val < 112
      · by_cases h_96_112 : i.val < 104
        · by_cases h_96_104 : i.val < 100
          · by_cases h_96_100 : i.val < 98
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 129 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 129 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 129 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 129 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
          · by_cases h_100_104 : i.val < 102
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 129 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 129 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 129 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 129 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
        · by_cases h_104_112 : i.val < 108
          · by_cases h_104_108 : i.val < 106
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 129 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 129 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
            · by_cases h_106_108 : i.val < 107
              · have heq : i = Fin.ofNat 129 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · have heq : i = Fin.ofNat 129 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
          · by_cases h_108_112 : i.val < 110
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 129 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 129 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 129 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 129 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
      · by_cases h_112_129 : i.val < 120
        · by_cases h_112_120 : i.val < 116
          · by_cases h_112_116 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 129 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 129 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 129 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 129 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
          · by_cases h_116_120 : i.val < 118
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 129 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 129 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
            · by_cases h_118_120 : i.val < 119
              · have heq : i = Fin.ofNat 129 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · have heq : i = Fin.ofNat 129 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
        · by_cases h_120_129 : i.val < 124
          · by_cases h_120_124 : i.val < 122
            · by_cases h_120_122 : i.val < 121
              · have heq : i = Fin.ofNat 129 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · have heq : i = Fin.ofNat 129 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
            · by_cases h_122_124 : i.val < 123
              · have heq : i = Fin.ofNat 129 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
              · have heq : i = Fin.ofNat 129 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
          · by_cases h_124_129 : i.val < 126
            · by_cases h_124_126 : i.val < 125
              · have heq : i = Fin.ofNat 129 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
              · have heq : i = Fin.ofNat 129 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
            · by_cases h_126_129 : i.val < 127
              · have heq : i = Fin.ofNat 129 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
              · by_cases h_127_129 : i.val < 128
                · have heq : i = Fin.ofNat 129 127 := Fin.ext (by change i.val = 127; omega)
                  subst i
                  exact block_0127
                · have heq : i = Fin.ofNat 129 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
