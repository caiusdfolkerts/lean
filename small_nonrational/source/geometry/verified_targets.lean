module
import ProjectionTargets.B000
import Batches.B001
import ProjectionTargets.B002
import Batches.B003
import Batches.B004
import Batches.B005
import Batches.B006
import Batches.B007
import Batches.B008
import Batches.B009
import Batches.B010
import Batches.B011
import Batches.B012
import Batches.B013
import Batches.B014
import Batches.B015
import Batches.B016
import Batches.B017
import Batches.B018
import Batches.B019
import Batches.B020
import Batches.B021
import Batches.B022
import Batches.B023
import Batches.B024
import Batches.B025
import Batches.B026
import Batches.B027
import Batches.B028
import Batches.B029
import Batches.B030
import Batches.B031
import Batches.B032
import Batches.B033
import Batches.B034
import Batches.B035
import Batches.B036
import Batches.B037
import Batches.B038
import Batches.B039
import Batches.B040
import Batches.B041
import Batches.B042
import Batches.B043
import Batches.B044
import Batches.B045
import Batches.B046
import Batches.B047
import Batches.B048
import Batches.B049
import Batches.B050
import Batches.B051
import Batches.B052
import Batches.B053
import Batches.B054
import Batches.B055
import Batches.B056
import Batches.B057
import Batches.B058
import Batches.B059
import Batches.B060
import Batches.B061
import Batches.B062
import Batches.B063
import Batches.B064
import Batches.B065
import Batches.B066
import Batches.B067
import Batches.B068
import Batches.B069
import Batches.B070
import Batches.B071
import Batches.B072
import Batches.B073
import Batches.B074
import Batches.B075
import Batches.B076
import Batches.B077
import Batches.B078
import Batches.B079
import Batches.B080
import Batches.B081
import Batches.B082
import Batches.B083
import Batches.B084
import Batches.B085
import Batches.B086
import Batches.B087
import Batches.B088
import Batches.B089
import Batches.B090
import Batches.B091
import Batches.B092
import Batches.B093
import Batches.B094
import Batches.B095
import Batches.B096
import Batches.B097
import Batches.B098
import Batches.B099
import Batches.B100
import Batches.B101
import Batches.B102
import Batches.B103
import Batches.B104
import Batches.B105
import Batches.B106
import Batches.B107
import Batches.B108
import Batches.B109
import Batches.B110
import Batches.B111
import Batches.B112
import Batches.B113
import Batches.B114
import Batches.B115
import Batches.B116
import Batches.B117
import Batches.B118
import Batches.B119
import Batches.B120
import Batches.B121
import Batches.B122
import Batches.B123
import Batches.B124
import Batches.B125
import Batches.B126
import Batches.B127
import Batches.B128
import Batches.B129
import Batches.B130
import Batches.B131
import Batches.B132
import Batches.B133
import Batches.B134
import Batches.B135
import Batches.B136
import Batches.B137
import Batches.B138
import Batches.B139
import Batches.B140
import Batches.B141
import Batches.B142
import Batches.B143
import Batches.B144
import Batches.B145
import Batches.B146
import Batches.B147
import Batches.B148
import Batches.B149
import Batches.B150
import Batches.B151
import Batches.B152
import Batches.B153
import Batches.B154
import Batches.B155
import Batches.B156
import ExceptionalTargets
public import TerminalRealization

@[expose] public section
namespace Nonrational.TerminalVerification
open Nonrational.TerminalData
set_option maxHeartbeats 1000000

theorem targets_valid (j : Nat) (hj : j < targetCount) : ValidTarget j := by
  by_cases h0 : 0 ≤ j ∧ j < 30
  · have h := certified_B000 ⟨j - 0, by omega⟩
    have heq : 0 + (j - 0) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h1 : 30 ≤ j ∧ j < 60
  · have h := certified_B001 ⟨j - 30, by omega⟩
    have heq : 30 + (j - 30) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h2 : 60 ≤ j ∧ j < 90
  · have h := certified_B002 ⟨j - 60, by omega⟩
    have heq : 60 + (j - 60) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h3 : 90 ≤ j ∧ j < 120
  · have h := certified_B003 ⟨j - 90, by omega⟩
    have heq : 90 + (j - 90) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h4 : 120 ≤ j ∧ j < 150
  · have h := certified_B004 ⟨j - 120, by omega⟩
    have heq : 120 + (j - 120) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h5 : 150 ≤ j ∧ j < 180
  · have h := certified_B005 ⟨j - 150, by omega⟩
    have heq : 150 + (j - 150) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h6 : 180 ≤ j ∧ j < 210
  · have h := certified_B006 ⟨j - 180, by omega⟩
    have heq : 180 + (j - 180) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h7 : 210 ≤ j ∧ j < 240
  · have h := certified_B007 ⟨j - 210, by omega⟩
    have heq : 210 + (j - 210) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h8 : 240 ≤ j ∧ j < 270
  · have h := certified_B008 ⟨j - 240, by omega⟩
    have heq : 240 + (j - 240) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h9 : 270 ≤ j ∧ j < 300
  · have h := certified_B009 ⟨j - 270, by omega⟩
    have heq : 270 + (j - 270) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h10 : 300 ≤ j ∧ j < 330
  · have h := certified_B010 ⟨j - 300, by omega⟩
    have heq : 300 + (j - 300) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h11 : 330 ≤ j ∧ j < 360
  · have h := certified_B011 ⟨j - 330, by omega⟩
    have heq : 330 + (j - 330) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h12 : 360 ≤ j ∧ j < 390
  · have h := certified_B012 ⟨j - 360, by omega⟩
    have heq : 360 + (j - 360) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h13 : 390 ≤ j ∧ j < 420
  · have h := certified_B013 ⟨j - 390, by omega⟩
    have heq : 390 + (j - 390) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h14 : 420 ≤ j ∧ j < 450
  · have h := certified_B014 ⟨j - 420, by omega⟩
    have heq : 420 + (j - 420) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h15 : 450 ≤ j ∧ j < 480
  · have h := certified_B015 ⟨j - 450, by omega⟩
    have heq : 450 + (j - 450) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h16 : 480 ≤ j ∧ j < 510
  · have h := certified_B016 ⟨j - 480, by omega⟩
    have heq : 480 + (j - 480) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h17 : 510 ≤ j ∧ j < 540
  · have h := certified_B017 ⟨j - 510, by omega⟩
    have heq : 510 + (j - 510) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h18 : 540 ≤ j ∧ j < 570
  · have h := certified_B018 ⟨j - 540, by omega⟩
    have heq : 540 + (j - 540) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h19 : 570 ≤ j ∧ j < 600
  · have h := certified_B019 ⟨j - 570, by omega⟩
    have heq : 570 + (j - 570) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h20 : 600 ≤ j ∧ j < 630
  · have h := certified_B020 ⟨j - 600, by omega⟩
    have heq : 600 + (j - 600) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h21 : 630 ≤ j ∧ j < 660
  · have h := certified_B021 ⟨j - 630, by omega⟩
    have heq : 630 + (j - 630) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h22 : 660 ≤ j ∧ j < 690
  · have h := certified_B022 ⟨j - 660, by omega⟩
    have heq : 660 + (j - 660) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h23 : 690 ≤ j ∧ j < 720
  · have h := certified_B023 ⟨j - 690, by omega⟩
    have heq : 690 + (j - 690) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h24 : 720 ≤ j ∧ j < 750
  · have h := certified_B024 ⟨j - 720, by omega⟩
    have heq : 720 + (j - 720) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h25 : 750 ≤ j ∧ j < 780
  · have h := certified_B025 ⟨j - 750, by omega⟩
    have heq : 750 + (j - 750) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h26 : 780 ≤ j ∧ j < 810
  · have h := certified_B026 ⟨j - 780, by omega⟩
    have heq : 780 + (j - 780) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h27 : 810 ≤ j ∧ j < 840
  · have h := certified_B027 ⟨j - 810, by omega⟩
    have heq : 810 + (j - 810) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h28 : 840 ≤ j ∧ j < 870
  · have h := certified_B028 ⟨j - 840, by omega⟩
    have heq : 840 + (j - 840) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h29 : 870 ≤ j ∧ j < 900
  · have h := certified_B029 ⟨j - 870, by omega⟩
    have heq : 870 + (j - 870) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h30 : 900 ≤ j ∧ j < 930
  · have h := certified_B030 ⟨j - 900, by omega⟩
    have heq : 900 + (j - 900) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h31 : 930 ≤ j ∧ j < 960
  · have h := certified_B031 ⟨j - 930, by omega⟩
    have heq : 930 + (j - 930) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h32 : 960 ≤ j ∧ j < 990
  · have h := certified_B032 ⟨j - 960, by omega⟩
    have heq : 960 + (j - 960) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h33 : 990 ≤ j ∧ j < 1020
  · have h := certified_B033 ⟨j - 990, by omega⟩
    have heq : 990 + (j - 990) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h34 : 1020 ≤ j ∧ j < 1050
  · have h := certified_B034 ⟨j - 1020, by omega⟩
    have heq : 1020 + (j - 1020) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h35 : 1050 ≤ j ∧ j < 1080
  · have h := certified_B035 ⟨j - 1050, by omega⟩
    have heq : 1050 + (j - 1050) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h36 : 1080 ≤ j ∧ j < 1110
  · have h := certified_B036 ⟨j - 1080, by omega⟩
    have heq : 1080 + (j - 1080) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h37 : 1110 ≤ j ∧ j < 1140
  · have h := certified_B037 ⟨j - 1110, by omega⟩
    have heq : 1110 + (j - 1110) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h38 : 1140 ≤ j ∧ j < 1170
  · have h := certified_B038 ⟨j - 1140, by omega⟩
    have heq : 1140 + (j - 1140) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h39 : 1170 ≤ j ∧ j < 1200
  · have h := certified_B039 ⟨j - 1170, by omega⟩
    have heq : 1170 + (j - 1170) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h40 : 1200 ≤ j ∧ j < 1230
  · have h := certified_B040 ⟨j - 1200, by omega⟩
    have heq : 1200 + (j - 1200) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h41 : 1230 ≤ j ∧ j < 1260
  · have h := certified_B041 ⟨j - 1230, by omega⟩
    have heq : 1230 + (j - 1230) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h42 : 1260 ≤ j ∧ j < 1290
  · have h := certified_B042 ⟨j - 1260, by omega⟩
    have heq : 1260 + (j - 1260) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h43 : 1290 ≤ j ∧ j < 1320
  · have h := certified_B043 ⟨j - 1290, by omega⟩
    have heq : 1290 + (j - 1290) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h44 : 1320 ≤ j ∧ j < 1350
  · have h := certified_B044 ⟨j - 1320, by omega⟩
    have heq : 1320 + (j - 1320) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h45 : 1350 ≤ j ∧ j < 1380
  · have h := certified_B045 ⟨j - 1350, by omega⟩
    have heq : 1350 + (j - 1350) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h46 : 1380 ≤ j ∧ j < 1410
  · have h := certified_B046 ⟨j - 1380, by omega⟩
    have heq : 1380 + (j - 1380) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h47 : 1410 ≤ j ∧ j < 1440
  · have h := certified_B047 ⟨j - 1410, by omega⟩
    have heq : 1410 + (j - 1410) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h48 : 1440 ≤ j ∧ j < 1470
  · have h := certified_B048 ⟨j - 1440, by omega⟩
    have heq : 1440 + (j - 1440) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h49 : 1470 ≤ j ∧ j < 1500
  · have h := certified_B049 ⟨j - 1470, by omega⟩
    have heq : 1470 + (j - 1470) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h50 : 1500 ≤ j ∧ j < 1530
  · have h := certified_B050 ⟨j - 1500, by omega⟩
    have heq : 1500 + (j - 1500) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h51 : 1530 ≤ j ∧ j < 1560
  · have h := certified_B051 ⟨j - 1530, by omega⟩
    have heq : 1530 + (j - 1530) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h52 : 1560 ≤ j ∧ j < 1590
  · have h := certified_B052 ⟨j - 1560, by omega⟩
    have heq : 1560 + (j - 1560) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h53 : 1590 ≤ j ∧ j < 1620
  · have h := certified_B053 ⟨j - 1590, by omega⟩
    have heq : 1590 + (j - 1590) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h54 : 1620 ≤ j ∧ j < 1650
  · have h := certified_B054 ⟨j - 1620, by omega⟩
    have heq : 1620 + (j - 1620) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h55 : 1650 ≤ j ∧ j < 1680
  · have h := certified_B055 ⟨j - 1650, by omega⟩
    have heq : 1650 + (j - 1650) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h56 : 1680 ≤ j ∧ j < 1710
  · have h := certified_B056 ⟨j - 1680, by omega⟩
    have heq : 1680 + (j - 1680) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h57 : 1710 ≤ j ∧ j < 1740
  · have h := certified_B057 ⟨j - 1710, by omega⟩
    have heq : 1710 + (j - 1710) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h58 : 1740 ≤ j ∧ j < 1770
  · have h := certified_B058 ⟨j - 1740, by omega⟩
    have heq : 1740 + (j - 1740) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h59 : 1770 ≤ j ∧ j < 1800
  · have h := certified_B059 ⟨j - 1770, by omega⟩
    have heq : 1770 + (j - 1770) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h60 : 1800 ≤ j ∧ j < 1830
  · have h := certified_B060 ⟨j - 1800, by omega⟩
    have heq : 1800 + (j - 1800) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h61 : 1830 ≤ j ∧ j < 1860
  · have h := certified_B061 ⟨j - 1830, by omega⟩
    have heq : 1830 + (j - 1830) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h62 : 1860 ≤ j ∧ j < 1890
  · have h := certified_B062 ⟨j - 1860, by omega⟩
    have heq : 1860 + (j - 1860) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h63 : 1890 ≤ j ∧ j < 1920
  · have h := certified_B063 ⟨j - 1890, by omega⟩
    have heq : 1890 + (j - 1890) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h64 : 1920 ≤ j ∧ j < 1950
  · have h := certified_B064 ⟨j - 1920, by omega⟩
    have heq : 1920 + (j - 1920) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h65 : 1950 ≤ j ∧ j < 1980
  · have h := certified_B065 ⟨j - 1950, by omega⟩
    have heq : 1950 + (j - 1950) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h66 : 1980 ≤ j ∧ j < 1983
  · have h := certified_B066 ⟨j - 1980, by omega⟩
    have heq : 1980 + (j - 1980) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h67 : 2043 ≤ j ∧ j < 2073
  · have h := certified_B067 ⟨j - 2043, by omega⟩
    have heq : 2043 + (j - 2043) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h68 : 2073 ≤ j ∧ j < 2103
  · have h := certified_B068 ⟨j - 2073, by omega⟩
    have heq : 2073 + (j - 2073) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h69 : 2103 ≤ j ∧ j < 2133
  · have h := certified_B069 ⟨j - 2103, by omega⟩
    have heq : 2103 + (j - 2103) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h70 : 2133 ≤ j ∧ j < 2163
  · have h := certified_B070 ⟨j - 2133, by omega⟩
    have heq : 2133 + (j - 2133) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h71 : 2163 ≤ j ∧ j < 2193
  · have h := certified_B071 ⟨j - 2163, by omega⟩
    have heq : 2163 + (j - 2163) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h72 : 2193 ≤ j ∧ j < 2223
  · have h := certified_B072 ⟨j - 2193, by omega⟩
    have heq : 2193 + (j - 2193) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h73 : 2223 ≤ j ∧ j < 2253
  · have h := certified_B073 ⟨j - 2223, by omega⟩
    have heq : 2223 + (j - 2223) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h74 : 2253 ≤ j ∧ j < 2283
  · have h := certified_B074 ⟨j - 2253, by omega⟩
    have heq : 2253 + (j - 2253) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h75 : 2283 ≤ j ∧ j < 2313
  · have h := certified_B075 ⟨j - 2283, by omega⟩
    have heq : 2283 + (j - 2283) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h76 : 2313 ≤ j ∧ j < 2343
  · have h := certified_B076 ⟨j - 2313, by omega⟩
    have heq : 2313 + (j - 2313) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h77 : 2343 ≤ j ∧ j < 2373
  · have h := certified_B077 ⟨j - 2343, by omega⟩
    have heq : 2343 + (j - 2343) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h78 : 2373 ≤ j ∧ j < 2403
  · have h := certified_B078 ⟨j - 2373, by omega⟩
    have heq : 2373 + (j - 2373) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h79 : 2403 ≤ j ∧ j < 2433
  · have h := certified_B079 ⟨j - 2403, by omega⟩
    have heq : 2403 + (j - 2403) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h80 : 2433 ≤ j ∧ j < 2463
  · have h := certified_B080 ⟨j - 2433, by omega⟩
    have heq : 2433 + (j - 2433) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h81 : 2463 ≤ j ∧ j < 2493
  · have h := certified_B081 ⟨j - 2463, by omega⟩
    have heq : 2463 + (j - 2463) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h82 : 2493 ≤ j ∧ j < 2523
  · have h := certified_B082 ⟨j - 2493, by omega⟩
    have heq : 2493 + (j - 2493) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h83 : 2523 ≤ j ∧ j < 2553
  · have h := certified_B083 ⟨j - 2523, by omega⟩
    have heq : 2523 + (j - 2523) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h84 : 2553 ≤ j ∧ j < 2583
  · have h := certified_B084 ⟨j - 2553, by omega⟩
    have heq : 2553 + (j - 2553) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h85 : 2583 ≤ j ∧ j < 2613
  · have h := certified_B085 ⟨j - 2583, by omega⟩
    have heq : 2583 + (j - 2583) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h86 : 2613 ≤ j ∧ j < 2643
  · have h := certified_B086 ⟨j - 2613, by omega⟩
    have heq : 2613 + (j - 2613) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h87 : 2643 ≤ j ∧ j < 2673
  · have h := certified_B087 ⟨j - 2643, by omega⟩
    have heq : 2643 + (j - 2643) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h88 : 2673 ≤ j ∧ j < 2703
  · have h := certified_B088 ⟨j - 2673, by omega⟩
    have heq : 2673 + (j - 2673) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h89 : 2703 ≤ j ∧ j < 2733
  · have h := certified_B089 ⟨j - 2703, by omega⟩
    have heq : 2703 + (j - 2703) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h90 : 2733 ≤ j ∧ j < 2763
  · have h := certified_B090 ⟨j - 2733, by omega⟩
    have heq : 2733 + (j - 2733) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h91 : 2763 ≤ j ∧ j < 2793
  · have h := certified_B091 ⟨j - 2763, by omega⟩
    have heq : 2763 + (j - 2763) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h92 : 2793 ≤ j ∧ j < 2823
  · have h := certified_B092 ⟨j - 2793, by omega⟩
    have heq : 2793 + (j - 2793) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h93 : 2823 ≤ j ∧ j < 2853
  · have h := certified_B093 ⟨j - 2823, by omega⟩
    have heq : 2823 + (j - 2823) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h94 : 2853 ≤ j ∧ j < 2883
  · have h := certified_B094 ⟨j - 2853, by omega⟩
    have heq : 2853 + (j - 2853) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h95 : 2883 ≤ j ∧ j < 2913
  · have h := certified_B095 ⟨j - 2883, by omega⟩
    have heq : 2883 + (j - 2883) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h96 : 2913 ≤ j ∧ j < 2943
  · have h := certified_B096 ⟨j - 2913, by omega⟩
    have heq : 2913 + (j - 2913) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h97 : 2943 ≤ j ∧ j < 2973
  · have h := certified_B097 ⟨j - 2943, by omega⟩
    have heq : 2943 + (j - 2943) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h98 : 2973 ≤ j ∧ j < 3003
  · have h := certified_B098 ⟨j - 2973, by omega⟩
    have heq : 2973 + (j - 2973) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h99 : 3003 ≤ j ∧ j < 3033
  · have h := certified_B099 ⟨j - 3003, by omega⟩
    have heq : 3003 + (j - 3003) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h100 : 3033 ≤ j ∧ j < 3063
  · have h := certified_B100 ⟨j - 3033, by omega⟩
    have heq : 3033 + (j - 3033) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h101 : 3063 ≤ j ∧ j < 3093
  · have h := certified_B101 ⟨j - 3063, by omega⟩
    have heq : 3063 + (j - 3063) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h102 : 3093 ≤ j ∧ j < 3123
  · have h := certified_B102 ⟨j - 3093, by omega⟩
    have heq : 3093 + (j - 3093) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h103 : 3123 ≤ j ∧ j < 3153
  · have h := certified_B103 ⟨j - 3123, by omega⟩
    have heq : 3123 + (j - 3123) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h104 : 3153 ≤ j ∧ j < 3183
  · have h := certified_B104 ⟨j - 3153, by omega⟩
    have heq : 3153 + (j - 3153) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h105 : 3183 ≤ j ∧ j < 3213
  · have h := certified_B105 ⟨j - 3183, by omega⟩
    have heq : 3183 + (j - 3183) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h106 : 3213 ≤ j ∧ j < 3243
  · have h := certified_B106 ⟨j - 3213, by omega⟩
    have heq : 3213 + (j - 3213) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h107 : 3243 ≤ j ∧ j < 3273
  · have h := certified_B107 ⟨j - 3243, by omega⟩
    have heq : 3243 + (j - 3243) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h108 : 3273 ≤ j ∧ j < 3303
  · have h := certified_B108 ⟨j - 3273, by omega⟩
    have heq : 3273 + (j - 3273) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h109 : 3303 ≤ j ∧ j < 3333
  · have h := certified_B109 ⟨j - 3303, by omega⟩
    have heq : 3303 + (j - 3303) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h110 : 3333 ≤ j ∧ j < 3363
  · have h := certified_B110 ⟨j - 3333, by omega⟩
    have heq : 3333 + (j - 3333) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h111 : 3363 ≤ j ∧ j < 3393
  · have h := certified_B111 ⟨j - 3363, by omega⟩
    have heq : 3363 + (j - 3363) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h112 : 3393 ≤ j ∧ j < 3423
  · have h := certified_B112 ⟨j - 3393, by omega⟩
    have heq : 3393 + (j - 3393) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h113 : 3423 ≤ j ∧ j < 3453
  · have h := certified_B113 ⟨j - 3423, by omega⟩
    have heq : 3423 + (j - 3423) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h114 : 3453 ≤ j ∧ j < 3483
  · have h := certified_B114 ⟨j - 3453, by omega⟩
    have heq : 3453 + (j - 3453) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h115 : 3483 ≤ j ∧ j < 3513
  · have h := certified_B115 ⟨j - 3483, by omega⟩
    have heq : 3483 + (j - 3483) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h116 : 3513 ≤ j ∧ j < 3543
  · have h := certified_B116 ⟨j - 3513, by omega⟩
    have heq : 3513 + (j - 3513) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h117 : 3543 ≤ j ∧ j < 3573
  · have h := certified_B117 ⟨j - 3543, by omega⟩
    have heq : 3543 + (j - 3543) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h118 : 3573 ≤ j ∧ j < 3603
  · have h := certified_B118 ⟨j - 3573, by omega⟩
    have heq : 3573 + (j - 3573) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h119 : 3603 ≤ j ∧ j < 3633
  · have h := certified_B119 ⟨j - 3603, by omega⟩
    have heq : 3603 + (j - 3603) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h120 : 3633 ≤ j ∧ j < 3663
  · have h := certified_B120 ⟨j - 3633, by omega⟩
    have heq : 3633 + (j - 3633) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h121 : 3663 ≤ j ∧ j < 3693
  · have h := certified_B121 ⟨j - 3663, by omega⟩
    have heq : 3663 + (j - 3663) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h122 : 3693 ≤ j ∧ j < 3723
  · have h := certified_B122 ⟨j - 3693, by omega⟩
    have heq : 3693 + (j - 3693) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h123 : 3723 ≤ j ∧ j < 3753
  · have h := certified_B123 ⟨j - 3723, by omega⟩
    have heq : 3723 + (j - 3723) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h124 : 3753 ≤ j ∧ j < 3783
  · have h := certified_B124 ⟨j - 3753, by omega⟩
    have heq : 3753 + (j - 3753) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h125 : 3783 ≤ j ∧ j < 3813
  · have h := certified_B125 ⟨j - 3783, by omega⟩
    have heq : 3783 + (j - 3783) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h126 : 3813 ≤ j ∧ j < 3843
  · have h := certified_B126 ⟨j - 3813, by omega⟩
    have heq : 3813 + (j - 3813) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h127 : 3843 ≤ j ∧ j < 3873
  · have h := certified_B127 ⟨j - 3843, by omega⟩
    have heq : 3843 + (j - 3843) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h128 : 3873 ≤ j ∧ j < 3903
  · have h := certified_B128 ⟨j - 3873, by omega⟩
    have heq : 3873 + (j - 3873) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h129 : 3903 ≤ j ∧ j < 3933
  · have h := certified_B129 ⟨j - 3903, by omega⟩
    have heq : 3903 + (j - 3903) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h130 : 3933 ≤ j ∧ j < 3963
  · have h := certified_B130 ⟨j - 3933, by omega⟩
    have heq : 3933 + (j - 3933) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h131 : 3963 ≤ j ∧ j < 3993
  · have h := certified_B131 ⟨j - 3963, by omega⟩
    have heq : 3963 + (j - 3963) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h132 : 3993 ≤ j ∧ j < 4023
  · have h := certified_B132 ⟨j - 3993, by omega⟩
    have heq : 3993 + (j - 3993) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h133 : 4023 ≤ j ∧ j < 4053
  · have h := certified_B133 ⟨j - 4023, by omega⟩
    have heq : 4023 + (j - 4023) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h134 : 4053 ≤ j ∧ j < 4083
  · have h := certified_B134 ⟨j - 4053, by omega⟩
    have heq : 4053 + (j - 4053) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h135 : 4083 ≤ j ∧ j < 4113
  · have h := certified_B135 ⟨j - 4083, by omega⟩
    have heq : 4083 + (j - 4083) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h136 : 4113 ≤ j ∧ j < 4143
  · have h := certified_B136 ⟨j - 4113, by omega⟩
    have heq : 4113 + (j - 4113) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h137 : 4143 ≤ j ∧ j < 4173
  · have h := certified_B137 ⟨j - 4143, by omega⟩
    have heq : 4143 + (j - 4143) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h138 : 4173 ≤ j ∧ j < 4203
  · have h := certified_B138 ⟨j - 4173, by omega⟩
    have heq : 4173 + (j - 4173) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h139 : 4203 ≤ j ∧ j < 4233
  · have h := certified_B139 ⟨j - 4203, by omega⟩
    have heq : 4203 + (j - 4203) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h140 : 4233 ≤ j ∧ j < 4263
  · have h := certified_B140 ⟨j - 4233, by omega⟩
    have heq : 4233 + (j - 4233) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h141 : 4263 ≤ j ∧ j < 4293
  · have h := certified_B141 ⟨j - 4263, by omega⟩
    have heq : 4263 + (j - 4263) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h142 : 4293 ≤ j ∧ j < 4323
  · have h := certified_B142 ⟨j - 4293, by omega⟩
    have heq : 4293 + (j - 4293) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h143 : 4323 ≤ j ∧ j < 4353
  · have h := certified_B143 ⟨j - 4323, by omega⟩
    have heq : 4323 + (j - 4323) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h144 : 4353 ≤ j ∧ j < 4383
  · have h := certified_B144 ⟨j - 4353, by omega⟩
    have heq : 4353 + (j - 4353) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h145 : 4383 ≤ j ∧ j < 4413
  · have h := certified_B145 ⟨j - 4383, by omega⟩
    have heq : 4383 + (j - 4383) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h146 : 4413 ≤ j ∧ j < 4443
  · have h := certified_B146 ⟨j - 4413, by omega⟩
    have heq : 4413 + (j - 4413) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h147 : 4443 ≤ j ∧ j < 4473
  · have h := certified_B147 ⟨j - 4443, by omega⟩
    have heq : 4443 + (j - 4443) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h148 : 4473 ≤ j ∧ j < 4503
  · have h := certified_B148 ⟨j - 4473, by omega⟩
    have heq : 4473 + (j - 4473) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h149 : 4503 ≤ j ∧ j < 4533
  · have h := certified_B149 ⟨j - 4503, by omega⟩
    have heq : 4503 + (j - 4503) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h150 : 4533 ≤ j ∧ j < 4563
  · have h := certified_B150 ⟨j - 4533, by omega⟩
    have heq : 4533 + (j - 4533) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h151 : 4563 ≤ j ∧ j < 4593
  · have h := certified_B151 ⟨j - 4563, by omega⟩
    have heq : 4563 + (j - 4563) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h152 : 4593 ≤ j ∧ j < 4623
  · have h := certified_B152 ⟨j - 4593, by omega⟩
    have heq : 4593 + (j - 4593) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h153 : 4623 ≤ j ∧ j < 4653
  · have h := certified_B153 ⟨j - 4623, by omega⟩
    have heq : 4623 + (j - 4623) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h154 : 4653 ≤ j ∧ j < 4683
  · have h := certified_B154 ⟨j - 4653, by omega⟩
    have heq : 4653 + (j - 4653) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h155 : 4685 ≤ j ∧ j < 4715
  · have h := certified_B155 ⟨j - 4685, by omega⟩
    have heq : 4685 + (j - 4685) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases h156 : 4715 ≤ j ∧ j < 4726
  · have h := certified_B156 ⟨j - 4715, by omega⟩
    have heq : 4715 + (j - 4715) = j := by omega
    exact valid_of_certifies (by simpa only [heq] using h)
  by_cases e1983 : j = 1983
  · simpa only [e1983] using valid_1983
  by_cases e1984 : j = 1984
  · simpa only [e1984] using valid_1984
  by_cases e1985 : j = 1985
  · simpa only [e1985] using valid_1985
  by_cases e1986 : j = 1986
  · simpa only [e1986] using valid_1986
  by_cases e1987 : j = 1987
  · simpa only [e1987] using valid_1987
  by_cases e1988 : j = 1988
  · simpa only [e1988] using valid_1988
  by_cases e1989 : j = 1989
  · simpa only [e1989] using valid_1989
  by_cases e1990 : j = 1990
  · simpa only [e1990] using valid_1990
  by_cases e1991 : j = 1991
  · simpa only [e1991] using valid_1991
  by_cases e1992 : j = 1992
  · simpa only [e1992] using valid_1992
  by_cases e1993 : j = 1993
  · simpa only [e1993] using valid_1993
  by_cases e1994 : j = 1994
  · simpa only [e1994] using valid_1994
  by_cases e1995 : j = 1995
  · simpa only [e1995] using valid_1995
  by_cases e1996 : j = 1996
  · simpa only [e1996] using valid_1996
  by_cases e1997 : j = 1997
  · simpa only [e1997] using valid_1997
  by_cases e1998 : j = 1998
  · simpa only [e1998] using valid_1998
  by_cases e1999 : j = 1999
  · simpa only [e1999] using valid_1999
  by_cases e2000 : j = 2000
  · simpa only [e2000] using valid_2000
  by_cases e2001 : j = 2001
  · simpa only [e2001] using valid_2001
  by_cases e2002 : j = 2002
  · simpa only [e2002] using valid_2002
  by_cases e2003 : j = 2003
  · simpa only [e2003] using valid_2003
  by_cases e2004 : j = 2004
  · simpa only [e2004] using valid_2004
  by_cases e2005 : j = 2005
  · simpa only [e2005] using valid_2005
  by_cases e2006 : j = 2006
  · simpa only [e2006] using valid_2006
  by_cases e2007 : j = 2007
  · simpa only [e2007] using valid_2007
  by_cases e2008 : j = 2008
  · simpa only [e2008] using valid_2008
  by_cases e2009 : j = 2009
  · simpa only [e2009] using valid_2009
  by_cases e2010 : j = 2010
  · simpa only [e2010] using valid_2010
  by_cases e2011 : j = 2011
  · simpa only [e2011] using valid_2011
  by_cases e2012 : j = 2012
  · simpa only [e2012] using valid_2012
  by_cases e2013 : j = 2013
  · simpa only [e2013] using valid_2013
  by_cases e2014 : j = 2014
  · simpa only [e2014] using valid_2014
  by_cases e2015 : j = 2015
  · simpa only [e2015] using valid_2015
  by_cases e2016 : j = 2016
  · simpa only [e2016] using valid_2016
  by_cases e2017 : j = 2017
  · simpa only [e2017] using valid_2017
  by_cases e2018 : j = 2018
  · simpa only [e2018] using valid_2018
  by_cases e2019 : j = 2019
  · simpa only [e2019] using valid_2019
  by_cases e2020 : j = 2020
  · simpa only [e2020] using valid_2020
  by_cases e2021 : j = 2021
  · simpa only [e2021] using valid_2021
  by_cases e2022 : j = 2022
  · simpa only [e2022] using valid_2022
  by_cases e2023 : j = 2023
  · simpa only [e2023] using valid_2023
  by_cases e2024 : j = 2024
  · simpa only [e2024] using valid_2024
  by_cases e2025 : j = 2025
  · simpa only [e2025] using valid_2025
  by_cases e2026 : j = 2026
  · simpa only [e2026] using valid_2026
  by_cases e2027 : j = 2027
  · simpa only [e2027] using valid_2027
  by_cases e2028 : j = 2028
  · simpa only [e2028] using valid_2028
  by_cases e2029 : j = 2029
  · simpa only [e2029] using valid_2029
  by_cases e2030 : j = 2030
  · simpa only [e2030] using valid_2030
  by_cases e2031 : j = 2031
  · simpa only [e2031] using valid_2031
  by_cases e2032 : j = 2032
  · simpa only [e2032] using valid_2032
  by_cases e2033 : j = 2033
  · simpa only [e2033] using valid_2033
  by_cases e2034 : j = 2034
  · simpa only [e2034] using valid_2034
  by_cases e2035 : j = 2035
  · simpa only [e2035] using valid_2035
  by_cases e2036 : j = 2036
  · simpa only [e2036] using valid_2036
  by_cases e2037 : j = 2037
  · simpa only [e2037] using valid_2037
  by_cases e2038 : j = 2038
  · simpa only [e2038] using valid_2038
  by_cases e2039 : j = 2039
  · simpa only [e2039] using valid_2039
  by_cases e2040 : j = 2040
  · simpa only [e2040] using valid_2040
  by_cases e2041 : j = 2041
  · simpa only [e2041] using valid_2041
  by_cases e2042 : j = 2042
  · simpa only [e2042] using valid_2042
  by_cases e4683 : j = 4683
  · simpa only [e4683] using valid_4683
  by_cases e4684 : j = 4684
  · simpa only [e4684] using valid_4684
  change j < 4726 at hj
  omega

end Nonrational.TerminalVerification
