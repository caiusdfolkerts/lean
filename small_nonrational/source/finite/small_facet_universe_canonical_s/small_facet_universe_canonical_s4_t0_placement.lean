module
prelude
public import SmallFacetUniverseCanonicalS4T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 4 (raw i) template root
      FacetUniverses.Small.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 99 := i.isLt
  by_cases h_0_99 : i.val < 49
  · by_cases h_0_49 : i.val < 24
    · by_cases h_0_24 : i.val < 12
      · by_cases h_0_12 : i.val < 6
        · by_cases h_0_6 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 99 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 99 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 99 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_6 : i.val < 4
            · have heq : i = Fin.ofNat 99 3 := Fin.ext (by change i.val = 3; omega)
              subst i
              exact block_0003
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 99 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 99 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
        · by_cases h_6_12 : i.val < 9
          · by_cases h_6_9 : i.val < 7
            · have heq : i = Fin.ofNat 99 6 := Fin.ext (by change i.val = 6; omega)
              subst i
              exact block_0006
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 99 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 99 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
          · by_cases h_9_12 : i.val < 10
            · have heq : i = Fin.ofNat 99 9 := Fin.ext (by change i.val = 9; omega)
              subst i
              exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 99 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 99 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
      · by_cases h_12_24 : i.val < 18
        · by_cases h_12_18 : i.val < 15
          · by_cases h_12_15 : i.val < 13
            · have heq : i = Fin.ofNat 99 12 := Fin.ext (by change i.val = 12; omega)
              subst i
              exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 99 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 99 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
          · by_cases h_15_18 : i.val < 16
            · have heq : i = Fin.ofNat 99 15 := Fin.ext (by change i.val = 15; omega)
              subst i
              exact block_0015
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 99 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 99 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
        · by_cases h_18_24 : i.val < 21
          · by_cases h_18_21 : i.val < 19
            · have heq : i = Fin.ofNat 99 18 := Fin.ext (by change i.val = 18; omega)
              subst i
              exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 99 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 99 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
          · by_cases h_21_24 : i.val < 22
            · have heq : i = Fin.ofNat 99 21 := Fin.ext (by change i.val = 21; omega)
              subst i
              exact block_0021
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 99 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 99 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
    · by_cases h_24_49 : i.val < 36
      · by_cases h_24_36 : i.val < 30
        · by_cases h_24_30 : i.val < 27
          · by_cases h_24_27 : i.val < 25
            · have heq : i = Fin.ofNat 99 24 := Fin.ext (by change i.val = 24; omega)
              subst i
              exact block_0024
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 99 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 99 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
          · by_cases h_27_30 : i.val < 28
            · have heq : i = Fin.ofNat 99 27 := Fin.ext (by change i.val = 27; omega)
              subst i
              exact block_0027
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 99 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 99 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
        · by_cases h_30_36 : i.val < 33
          · by_cases h_30_33 : i.val < 31
            · have heq : i = Fin.ofNat 99 30 := Fin.ext (by change i.val = 30; omega)
              subst i
              exact block_0030
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 99 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 99 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
          · by_cases h_33_36 : i.val < 34
            · have heq : i = Fin.ofNat 99 33 := Fin.ext (by change i.val = 33; omega)
              subst i
              exact block_0033
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 99 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 99 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
      · by_cases h_36_49 : i.val < 42
        · by_cases h_36_42 : i.val < 39
          · by_cases h_36_39 : i.val < 37
            · have heq : i = Fin.ofNat 99 36 := Fin.ext (by change i.val = 36; omega)
              subst i
              exact block_0036
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 99 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 99 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
          · by_cases h_39_42 : i.val < 40
            · have heq : i = Fin.ofNat 99 39 := Fin.ext (by change i.val = 39; omega)
              subst i
              exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 99 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 99 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
        · by_cases h_42_49 : i.val < 45
          · by_cases h_42_45 : i.val < 43
            · have heq : i = Fin.ofNat 99 42 := Fin.ext (by change i.val = 42; omega)
              subst i
              exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 99 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 99 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
          · by_cases h_45_49 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 99 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 99 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 99 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 99 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
  · by_cases h_49_99 : i.val < 74
    · by_cases h_49_74 : i.val < 61
      · by_cases h_49_61 : i.val < 55
        · by_cases h_49_55 : i.val < 52
          · by_cases h_49_52 : i.val < 50
            · have heq : i = Fin.ofNat 99 49 := Fin.ext (by change i.val = 49; omega)
              subst i
              exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 99 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 99 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
          · by_cases h_52_55 : i.val < 53
            · have heq : i = Fin.ofNat 99 52 := Fin.ext (by change i.val = 52; omega)
              subst i
              exact block_0052
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 99 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 99 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
        · by_cases h_55_61 : i.val < 58
          · by_cases h_55_58 : i.val < 56
            · have heq : i = Fin.ofNat 99 55 := Fin.ext (by change i.val = 55; omega)
              subst i
              exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 99 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 99 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
          · by_cases h_58_61 : i.val < 59
            · have heq : i = Fin.ofNat 99 58 := Fin.ext (by change i.val = 58; omega)
              subst i
              exact block_0058
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 99 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 99 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
      · by_cases h_61_74 : i.val < 67
        · by_cases h_61_67 : i.val < 64
          · by_cases h_61_64 : i.val < 62
            · have heq : i = Fin.ofNat 99 61 := Fin.ext (by change i.val = 61; omega)
              subst i
              exact block_0061
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 99 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 99 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
          · by_cases h_64_67 : i.val < 65
            · have heq : i = Fin.ofNat 99 64 := Fin.ext (by change i.val = 64; omega)
              subst i
              exact block_0064
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 99 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 99 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
        · by_cases h_67_74 : i.val < 70
          · by_cases h_67_70 : i.val < 68
            · have heq : i = Fin.ofNat 99 67 := Fin.ext (by change i.val = 67; omega)
              subst i
              exact block_0067
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 99 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 99 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
          · by_cases h_70_74 : i.val < 72
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 99 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 99 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 99 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 99 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
    · by_cases h_74_99 : i.val < 86
      · by_cases h_74_86 : i.val < 80
        · by_cases h_74_80 : i.val < 77
          · by_cases h_74_77 : i.val < 75
            · have heq : i = Fin.ofNat 99 74 := Fin.ext (by change i.val = 74; omega)
              subst i
              exact block_0074
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 99 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 99 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
          · by_cases h_77_80 : i.val < 78
            · have heq : i = Fin.ofNat 99 77 := Fin.ext (by change i.val = 77; omega)
              subst i
              exact block_0077
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 99 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 99 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
        · by_cases h_80_86 : i.val < 83
          · by_cases h_80_83 : i.val < 81
            · have heq : i = Fin.ofNat 99 80 := Fin.ext (by change i.val = 80; omega)
              subst i
              exact block_0080
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 99 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 99 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
          · by_cases h_83_86 : i.val < 84
            · have heq : i = Fin.ofNat 99 83 := Fin.ext (by change i.val = 83; omega)
              subst i
              exact block_0083
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 99 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 99 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
      · by_cases h_86_99 : i.val < 92
        · by_cases h_86_92 : i.val < 89
          · by_cases h_86_89 : i.val < 87
            · have heq : i = Fin.ofNat 99 86 := Fin.ext (by change i.val = 86; omega)
              subst i
              exact block_0086
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 99 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 99 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
          · by_cases h_89_92 : i.val < 90
            · have heq : i = Fin.ofNat 99 89 := Fin.ext (by change i.val = 89; omega)
              subst i
              exact block_0089
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 99 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 99 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
        · by_cases h_92_99 : i.val < 95
          · by_cases h_92_95 : i.val < 93
            · have heq : i = Fin.ofNat 99 92 := Fin.ext (by change i.val = 92; omega)
              subst i
              exact block_0092
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 99 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 99 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
          · by_cases h_95_99 : i.val < 97
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 99 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 99 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 99 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 99 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
