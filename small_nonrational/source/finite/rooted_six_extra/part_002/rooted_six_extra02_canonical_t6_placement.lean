module
prelude
public import RootedSixExtra02CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixExtra02.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 104 := i.isLt
  by_cases h_0_104 : i.val < 52
  · by_cases h_0_52 : i.val < 26
    · by_cases h_0_26 : i.val < 13
      · by_cases h_0_13 : i.val < 6
        · by_cases h_0_6 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 104 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 104 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 104 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_6 : i.val < 4
            · have heq : i = Fin.ofNat 104 3 := Fin.ext (by change i.val = 3; omega)
              subst i
              exact block_0003
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 104 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 104 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
        · by_cases h_6_13 : i.val < 9
          · by_cases h_6_9 : i.val < 7
            · have heq : i = Fin.ofNat 104 6 := Fin.ext (by change i.val = 6; omega)
              subst i
              exact block_0006
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 104 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 104 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
          · by_cases h_9_13 : i.val < 11
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 104 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 104 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 104 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 104 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
      · by_cases h_13_26 : i.val < 19
        · by_cases h_13_19 : i.val < 16
          · by_cases h_13_16 : i.val < 14
            · have heq : i = Fin.ofNat 104 13 := Fin.ext (by change i.val = 13; omega)
              subst i
              exact block_0013
            · by_cases h_14_16 : i.val < 15
              · have heq : i = Fin.ofNat 104 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · have heq : i = Fin.ofNat 104 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
          · by_cases h_16_19 : i.val < 17
            · have heq : i = Fin.ofNat 104 16 := Fin.ext (by change i.val = 16; omega)
              subst i
              exact block_0016
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 104 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 104 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
        · by_cases h_19_26 : i.val < 22
          · by_cases h_19_22 : i.val < 20
            · have heq : i = Fin.ofNat 104 19 := Fin.ext (by change i.val = 19; omega)
              subst i
              exact block_0019
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 104 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 104 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
          · by_cases h_22_26 : i.val < 24
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 104 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 104 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 104 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 104 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
    · by_cases h_26_52 : i.val < 39
      · by_cases h_26_39 : i.val < 32
        · by_cases h_26_32 : i.val < 29
          · by_cases h_26_29 : i.val < 27
            · have heq : i = Fin.ofNat 104 26 := Fin.ext (by change i.val = 26; omega)
              subst i
              exact block_0026
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 104 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 104 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
          · by_cases h_29_32 : i.val < 30
            · have heq : i = Fin.ofNat 104 29 := Fin.ext (by change i.val = 29; omega)
              subst i
              exact block_0029
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 104 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 104 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
        · by_cases h_32_39 : i.val < 35
          · by_cases h_32_35 : i.val < 33
            · have heq : i = Fin.ofNat 104 32 := Fin.ext (by change i.val = 32; omega)
              subst i
              exact block_0032
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 104 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 104 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
          · by_cases h_35_39 : i.val < 37
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 104 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 104 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 104 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 104 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
      · by_cases h_39_52 : i.val < 45
        · by_cases h_39_45 : i.val < 42
          · by_cases h_39_42 : i.val < 40
            · have heq : i = Fin.ofNat 104 39 := Fin.ext (by change i.val = 39; omega)
              subst i
              exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 104 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 104 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
          · by_cases h_42_45 : i.val < 43
            · have heq : i = Fin.ofNat 104 42 := Fin.ext (by change i.val = 42; omega)
              subst i
              exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 104 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 104 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
        · by_cases h_45_52 : i.val < 48
          · by_cases h_45_48 : i.val < 46
            · have heq : i = Fin.ofNat 104 45 := Fin.ext (by change i.val = 45; omega)
              subst i
              exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 104 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 104 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
          · by_cases h_48_52 : i.val < 50
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 104 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 104 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 104 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 104 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
  · by_cases h_52_104 : i.val < 78
    · by_cases h_52_78 : i.val < 65
      · by_cases h_52_65 : i.val < 58
        · by_cases h_52_58 : i.val < 55
          · by_cases h_52_55 : i.val < 53
            · have heq : i = Fin.ofNat 104 52 := Fin.ext (by change i.val = 52; omega)
              subst i
              exact block_0052
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 104 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 104 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
          · by_cases h_55_58 : i.val < 56
            · have heq : i = Fin.ofNat 104 55 := Fin.ext (by change i.val = 55; omega)
              subst i
              exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 104 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 104 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
        · by_cases h_58_65 : i.val < 61
          · by_cases h_58_61 : i.val < 59
            · have heq : i = Fin.ofNat 104 58 := Fin.ext (by change i.val = 58; omega)
              subst i
              exact block_0058
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 104 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 104 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
          · by_cases h_61_65 : i.val < 63
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 104 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 104 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 104 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 104 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
      · by_cases h_65_78 : i.val < 71
        · by_cases h_65_71 : i.val < 68
          · by_cases h_65_68 : i.val < 66
            · have heq : i = Fin.ofNat 104 65 := Fin.ext (by change i.val = 65; omega)
              subst i
              exact block_0065
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 104 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 104 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
          · by_cases h_68_71 : i.val < 69
            · have heq : i = Fin.ofNat 104 68 := Fin.ext (by change i.val = 68; omega)
              subst i
              exact block_0068
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 104 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 104 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
        · by_cases h_71_78 : i.val < 74
          · by_cases h_71_74 : i.val < 72
            · have heq : i = Fin.ofNat 104 71 := Fin.ext (by change i.val = 71; omega)
              subst i
              exact block_0071
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 104 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 104 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
          · by_cases h_74_78 : i.val < 76
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 104 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 104 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 104 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 104 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
    · by_cases h_78_104 : i.val < 91
      · by_cases h_78_91 : i.val < 84
        · by_cases h_78_84 : i.val < 81
          · by_cases h_78_81 : i.val < 79
            · have heq : i = Fin.ofNat 104 78 := Fin.ext (by change i.val = 78; omega)
              subst i
              exact block_0078
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 104 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 104 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
          · by_cases h_81_84 : i.val < 82
            · have heq : i = Fin.ofNat 104 81 := Fin.ext (by change i.val = 81; omega)
              subst i
              exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 104 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 104 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
        · by_cases h_84_91 : i.val < 87
          · by_cases h_84_87 : i.val < 85
            · have heq : i = Fin.ofNat 104 84 := Fin.ext (by change i.val = 84; omega)
              subst i
              exact block_0084
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 104 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 104 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
          · by_cases h_87_91 : i.val < 89
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 104 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 104 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 104 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 104 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
      · by_cases h_91_104 : i.val < 97
        · by_cases h_91_97 : i.val < 94
          · by_cases h_91_94 : i.val < 92
            · have heq : i = Fin.ofNat 104 91 := Fin.ext (by change i.val = 91; omega)
              subst i
              exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 104 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 104 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
          · by_cases h_94_97 : i.val < 95
            · have heq : i = Fin.ofNat 104 94 := Fin.ext (by change i.val = 94; omega)
              subst i
              exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 104 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 104 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
        · by_cases h_97_104 : i.val < 100
          · by_cases h_97_100 : i.val < 98
            · have heq : i = Fin.ofNat 104 97 := Fin.ext (by change i.val = 97; omega)
              subst i
              exact block_0097
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 104 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 104 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
          · by_cases h_100_104 : i.val < 102
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 104 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 104 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 104 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 104 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
