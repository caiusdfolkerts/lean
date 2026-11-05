module
prelude
public import RootedSevenPure008CanonicalS5T1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenPure008.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 160 := i.isLt
  by_cases h_0_160 : i.val < 80
  · by_cases h_0_80 : i.val < 40
    · by_cases h_0_40 : i.val < 20
      · by_cases h_0_20 : i.val < 10
        · by_cases h_0_10 : i.val < 5
          · by_cases h_0_5 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 160 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 160 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_5 : i.val < 3
              · have heq : i = Fin.ofNat 160 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · by_cases h_3_5 : i.val < 4
                · have heq : i = Fin.ofNat 160 3 := Fin.ext (by change i.val = 3; omega)
                  subst i
                  exact block_0003
                · have heq : i = Fin.ofNat 160 4 := Fin.ext (by change i.val = 4; omega)
                  subst i
                  exact block_0004
          · by_cases h_5_10 : i.val < 7
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 160 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 160 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
            · by_cases h_7_10 : i.val < 8
              · have heq : i = Fin.ofNat 160 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · by_cases h_8_10 : i.val < 9
                · have heq : i = Fin.ofNat 160 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
                · have heq : i = Fin.ofNat 160 9 := Fin.ext (by change i.val = 9; omega)
                  subst i
                  exact block_0009
        · by_cases h_10_20 : i.val < 15
          · by_cases h_10_15 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 160 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 160 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_15 : i.val < 13
              · have heq : i = Fin.ofNat 160 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · by_cases h_13_15 : i.val < 14
                · have heq : i = Fin.ofNat 160 13 := Fin.ext (by change i.val = 13; omega)
                  subst i
                  exact block_0013
                · have heq : i = Fin.ofNat 160 14 := Fin.ext (by change i.val = 14; omega)
                  subst i
                  exact block_0014
          · by_cases h_15_20 : i.val < 17
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 160 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 160 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
            · by_cases h_17_20 : i.val < 18
              · have heq : i = Fin.ofNat 160 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · by_cases h_18_20 : i.val < 19
                · have heq : i = Fin.ofNat 160 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
                · have heq : i = Fin.ofNat 160 19 := Fin.ext (by change i.val = 19; omega)
                  subst i
                  exact block_0019
      · by_cases h_20_40 : i.val < 30
        · by_cases h_20_30 : i.val < 25
          · by_cases h_20_25 : i.val < 22
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 160 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 160 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
            · by_cases h_22_25 : i.val < 23
              · have heq : i = Fin.ofNat 160 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · by_cases h_23_25 : i.val < 24
                · have heq : i = Fin.ofNat 160 23 := Fin.ext (by change i.val = 23; omega)
                  subst i
                  exact block_0023
                · have heq : i = Fin.ofNat 160 24 := Fin.ext (by change i.val = 24; omega)
                  subst i
                  exact block_0024
          · by_cases h_25_30 : i.val < 27
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 160 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 160 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
            · by_cases h_27_30 : i.val < 28
              · have heq : i = Fin.ofNat 160 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · by_cases h_28_30 : i.val < 29
                · have heq : i = Fin.ofNat 160 28 := Fin.ext (by change i.val = 28; omega)
                  subst i
                  exact block_0028
                · have heq : i = Fin.ofNat 160 29 := Fin.ext (by change i.val = 29; omega)
                  subst i
                  exact block_0029
        · by_cases h_30_40 : i.val < 35
          · by_cases h_30_35 : i.val < 32
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 160 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 160 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
            · by_cases h_32_35 : i.val < 33
              · have heq : i = Fin.ofNat 160 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · by_cases h_33_35 : i.val < 34
                · have heq : i = Fin.ofNat 160 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
                · have heq : i = Fin.ofNat 160 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
          · by_cases h_35_40 : i.val < 37
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 160 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 160 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
            · by_cases h_37_40 : i.val < 38
              · have heq : i = Fin.ofNat 160 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · by_cases h_38_40 : i.val < 39
                · have heq : i = Fin.ofNat 160 38 := Fin.ext (by change i.val = 38; omega)
                  subst i
                  exact block_0038
                · have heq : i = Fin.ofNat 160 39 := Fin.ext (by change i.val = 39; omega)
                  subst i
                  exact block_0039
    · by_cases h_40_80 : i.val < 60
      · by_cases h_40_60 : i.val < 50
        · by_cases h_40_50 : i.val < 45
          · by_cases h_40_45 : i.val < 42
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 160 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 160 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
            · by_cases h_42_45 : i.val < 43
              · have heq : i = Fin.ofNat 160 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · by_cases h_43_45 : i.val < 44
                · have heq : i = Fin.ofNat 160 43 := Fin.ext (by change i.val = 43; omega)
                  subst i
                  exact block_0043
                · have heq : i = Fin.ofNat 160 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
          · by_cases h_45_50 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 160 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 160 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_50 : i.val < 48
              · have heq : i = Fin.ofNat 160 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · by_cases h_48_50 : i.val < 49
                · have heq : i = Fin.ofNat 160 48 := Fin.ext (by change i.val = 48; omega)
                  subst i
                  exact block_0048
                · have heq : i = Fin.ofNat 160 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
        · by_cases h_50_60 : i.val < 55
          · by_cases h_50_55 : i.val < 52
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 160 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 160 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
            · by_cases h_52_55 : i.val < 53
              · have heq : i = Fin.ofNat 160 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · by_cases h_53_55 : i.val < 54
                · have heq : i = Fin.ofNat 160 53 := Fin.ext (by change i.val = 53; omega)
                  subst i
                  exact block_0053
                · have heq : i = Fin.ofNat 160 54 := Fin.ext (by change i.val = 54; omega)
                  subst i
                  exact block_0054
          · by_cases h_55_60 : i.val < 57
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 160 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 160 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
            · by_cases h_57_60 : i.val < 58
              · have heq : i = Fin.ofNat 160 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · by_cases h_58_60 : i.val < 59
                · have heq : i = Fin.ofNat 160 58 := Fin.ext (by change i.val = 58; omega)
                  subst i
                  exact block_0058
                · have heq : i = Fin.ofNat 160 59 := Fin.ext (by change i.val = 59; omega)
                  subst i
                  exact block_0059
      · by_cases h_60_80 : i.val < 70
        · by_cases h_60_70 : i.val < 65
          · by_cases h_60_65 : i.val < 62
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 160 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 160 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
            · by_cases h_62_65 : i.val < 63
              · have heq : i = Fin.ofNat 160 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · by_cases h_63_65 : i.val < 64
                · have heq : i = Fin.ofNat 160 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
                · have heq : i = Fin.ofNat 160 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
          · by_cases h_65_70 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 160 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 160 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_70 : i.val < 68
              · have heq : i = Fin.ofNat 160 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · by_cases h_68_70 : i.val < 69
                · have heq : i = Fin.ofNat 160 68 := Fin.ext (by change i.val = 68; omega)
                  subst i
                  exact block_0068
                · have heq : i = Fin.ofNat 160 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
        · by_cases h_70_80 : i.val < 75
          · by_cases h_70_75 : i.val < 72
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 160 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 160 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
            · by_cases h_72_75 : i.val < 73
              · have heq : i = Fin.ofNat 160 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · by_cases h_73_75 : i.val < 74
                · have heq : i = Fin.ofNat 160 73 := Fin.ext (by change i.val = 73; omega)
                  subst i
                  exact block_0073
                · have heq : i = Fin.ofNat 160 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
          · by_cases h_75_80 : i.val < 77
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 160 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 160 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
            · by_cases h_77_80 : i.val < 78
              · have heq : i = Fin.ofNat 160 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · by_cases h_78_80 : i.val < 79
                · have heq : i = Fin.ofNat 160 78 := Fin.ext (by change i.val = 78; omega)
                  subst i
                  exact block_0078
                · have heq : i = Fin.ofNat 160 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
  · by_cases h_80_160 : i.val < 120
    · by_cases h_80_120 : i.val < 100
      · by_cases h_80_100 : i.val < 90
        · by_cases h_80_90 : i.val < 85
          · by_cases h_80_85 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 160 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 160 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_85 : i.val < 83
              · have heq : i = Fin.ofNat 160 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · by_cases h_83_85 : i.val < 84
                · have heq : i = Fin.ofNat 160 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
                · have heq : i = Fin.ofNat 160 84 := Fin.ext (by change i.val = 84; omega)
                  subst i
                  exact block_0084
          · by_cases h_85_90 : i.val < 87
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 160 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 160 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
            · by_cases h_87_90 : i.val < 88
              · have heq : i = Fin.ofNat 160 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · by_cases h_88_90 : i.val < 89
                · have heq : i = Fin.ofNat 160 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
                · have heq : i = Fin.ofNat 160 89 := Fin.ext (by change i.val = 89; omega)
                  subst i
                  exact block_0089
        · by_cases h_90_100 : i.val < 95
          · by_cases h_90_95 : i.val < 92
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 160 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 160 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
            · by_cases h_92_95 : i.val < 93
              · have heq : i = Fin.ofNat 160 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · by_cases h_93_95 : i.val < 94
                · have heq : i = Fin.ofNat 160 93 := Fin.ext (by change i.val = 93; omega)
                  subst i
                  exact block_0093
                · have heq : i = Fin.ofNat 160 94 := Fin.ext (by change i.val = 94; omega)
                  subst i
                  exact block_0094
          · by_cases h_95_100 : i.val < 97
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 160 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 160 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
            · by_cases h_97_100 : i.val < 98
              · have heq : i = Fin.ofNat 160 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · by_cases h_98_100 : i.val < 99
                · have heq : i = Fin.ofNat 160 98 := Fin.ext (by change i.val = 98; omega)
                  subst i
                  exact block_0098
                · have heq : i = Fin.ofNat 160 99 := Fin.ext (by change i.val = 99; omega)
                  subst i
                  exact block_0099
      · by_cases h_100_120 : i.val < 110
        · by_cases h_100_110 : i.val < 105
          · by_cases h_100_105 : i.val < 102
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 160 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 160 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
            · by_cases h_102_105 : i.val < 103
              · have heq : i = Fin.ofNat 160 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · by_cases h_103_105 : i.val < 104
                · have heq : i = Fin.ofNat 160 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
                · have heq : i = Fin.ofNat 160 104 := Fin.ext (by change i.val = 104; omega)
                  subst i
                  exact block_0104
          · by_cases h_105_110 : i.val < 107
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 160 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 160 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
            · by_cases h_107_110 : i.val < 108
              · have heq : i = Fin.ofNat 160 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · by_cases h_108_110 : i.val < 109
                · have heq : i = Fin.ofNat 160 108 := Fin.ext (by change i.val = 108; omega)
                  subst i
                  exact block_0108
                · have heq : i = Fin.ofNat 160 109 := Fin.ext (by change i.val = 109; omega)
                  subst i
                  exact block_0109
        · by_cases h_110_120 : i.val < 115
          · by_cases h_110_115 : i.val < 112
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 160 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 160 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
            · by_cases h_112_115 : i.val < 113
              · have heq : i = Fin.ofNat 160 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · by_cases h_113_115 : i.val < 114
                · have heq : i = Fin.ofNat 160 113 := Fin.ext (by change i.val = 113; omega)
                  subst i
                  exact block_0113
                · have heq : i = Fin.ofNat 160 114 := Fin.ext (by change i.val = 114; omega)
                  subst i
                  exact block_0114
          · by_cases h_115_120 : i.val < 117
            · by_cases h_115_117 : i.val < 116
              · have heq : i = Fin.ofNat 160 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
              · have heq : i = Fin.ofNat 160 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
            · by_cases h_117_120 : i.val < 118
              · have heq : i = Fin.ofNat 160 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · by_cases h_118_120 : i.val < 119
                · have heq : i = Fin.ofNat 160 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
                · have heq : i = Fin.ofNat 160 119 := Fin.ext (by change i.val = 119; omega)
                  subst i
                  exact block_0119
    · by_cases h_120_160 : i.val < 140
      · by_cases h_120_140 : i.val < 130
        · by_cases h_120_130 : i.val < 125
          · by_cases h_120_125 : i.val < 122
            · by_cases h_120_122 : i.val < 121
              · have heq : i = Fin.ofNat 160 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · have heq : i = Fin.ofNat 160 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
            · by_cases h_122_125 : i.val < 123
              · have heq : i = Fin.ofNat 160 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
              · by_cases h_123_125 : i.val < 124
                · have heq : i = Fin.ofNat 160 123 := Fin.ext (by change i.val = 123; omega)
                  subst i
                  exact block_0123
                · have heq : i = Fin.ofNat 160 124 := Fin.ext (by change i.val = 124; omega)
                  subst i
                  exact block_0124
          · by_cases h_125_130 : i.val < 127
            · by_cases h_125_127 : i.val < 126
              · have heq : i = Fin.ofNat 160 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
              · have heq : i = Fin.ofNat 160 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
            · by_cases h_127_130 : i.val < 128
              · have heq : i = Fin.ofNat 160 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
              · by_cases h_128_130 : i.val < 129
                · have heq : i = Fin.ofNat 160 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
                · have heq : i = Fin.ofNat 160 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
        · by_cases h_130_140 : i.val < 135
          · by_cases h_130_135 : i.val < 132
            · by_cases h_130_132 : i.val < 131
              · have heq : i = Fin.ofNat 160 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · have heq : i = Fin.ofNat 160 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
            · by_cases h_132_135 : i.val < 133
              · have heq : i = Fin.ofNat 160 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
              · by_cases h_133_135 : i.val < 134
                · have heq : i = Fin.ofNat 160 133 := Fin.ext (by change i.val = 133; omega)
                  subst i
                  exact block_0133
                · have heq : i = Fin.ofNat 160 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
          · by_cases h_135_140 : i.val < 137
            · by_cases h_135_137 : i.val < 136
              · have heq : i = Fin.ofNat 160 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · have heq : i = Fin.ofNat 160 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
            · by_cases h_137_140 : i.val < 138
              · have heq : i = Fin.ofNat 160 137 := Fin.ext (by change i.val = 137; omega)
                subst i
                exact block_0137
              · by_cases h_138_140 : i.val < 139
                · have heq : i = Fin.ofNat 160 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
                · have heq : i = Fin.ofNat 160 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
      · by_cases h_140_160 : i.val < 150
        · by_cases h_140_150 : i.val < 145
          · by_cases h_140_145 : i.val < 142
            · by_cases h_140_142 : i.val < 141
              · have heq : i = Fin.ofNat 160 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
              · have heq : i = Fin.ofNat 160 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
            · by_cases h_142_145 : i.val < 143
              · have heq : i = Fin.ofNat 160 142 := Fin.ext (by change i.val = 142; omega)
                subst i
                exact block_0142
              · by_cases h_143_145 : i.val < 144
                · have heq : i = Fin.ofNat 160 143 := Fin.ext (by change i.val = 143; omega)
                  subst i
                  exact block_0143
                · have heq : i = Fin.ofNat 160 144 := Fin.ext (by change i.val = 144; omega)
                  subst i
                  exact block_0144
          · by_cases h_145_150 : i.val < 147
            · by_cases h_145_147 : i.val < 146
              · have heq : i = Fin.ofNat 160 145 := Fin.ext (by change i.val = 145; omega)
                subst i
                exact block_0145
              · have heq : i = Fin.ofNat 160 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
            · by_cases h_147_150 : i.val < 148
              · have heq : i = Fin.ofNat 160 147 := Fin.ext (by change i.val = 147; omega)
                subst i
                exact block_0147
              · by_cases h_148_150 : i.val < 149
                · have heq : i = Fin.ofNat 160 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
                · have heq : i = Fin.ofNat 160 149 := Fin.ext (by change i.val = 149; omega)
                  subst i
                  exact block_0149
        · by_cases h_150_160 : i.val < 155
          · by_cases h_150_155 : i.val < 152
            · by_cases h_150_152 : i.val < 151
              · have heq : i = Fin.ofNat 160 150 := Fin.ext (by change i.val = 150; omega)
                subst i
                exact block_0150
              · have heq : i = Fin.ofNat 160 151 := Fin.ext (by change i.val = 151; omega)
                subst i
                exact block_0151
            · by_cases h_152_155 : i.val < 153
              · have heq : i = Fin.ofNat 160 152 := Fin.ext (by change i.val = 152; omega)
                subst i
                exact block_0152
              · by_cases h_153_155 : i.val < 154
                · have heq : i = Fin.ofNat 160 153 := Fin.ext (by change i.val = 153; omega)
                  subst i
                  exact block_0153
                · have heq : i = Fin.ofNat 160 154 := Fin.ext (by change i.val = 154; omega)
                  subst i
                  exact block_0154
          · by_cases h_155_160 : i.val < 157
            · by_cases h_155_157 : i.val < 156
              · have heq : i = Fin.ofNat 160 155 := Fin.ext (by change i.val = 155; omega)
                subst i
                exact block_0155
              · have heq : i = Fin.ofNat 160 156 := Fin.ext (by change i.val = 156; omega)
                subst i
                exact block_0156
            · by_cases h_157_160 : i.val < 158
              · have heq : i = Fin.ofNat 160 157 := Fin.ext (by change i.val = 157; omega)
                subst i
                exact block_0157
              · by_cases h_158_160 : i.val < 159
                · have heq : i = Fin.ofNat 160 158 := Fin.ext (by change i.val = 158; omega)
                  subst i
                  exact block_0158
                · have heq : i = Fin.ofNat 160 159 := Fin.ext (by change i.val = 159; omega)
                  subst i
                  exact block_0159
end Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
