module
prelude
public import GraphInputsRow29Part00035Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M035
public import InducedTerminalMatches.M036
public import InducedTerminalMatches.M037
public import InducedTerminalMatches.M038
public import InducedTerminalMatches.M039

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00035
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1129))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1130)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1131))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1132))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1133))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1134)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1135))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1136))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1137))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1138))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1139)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1140))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1141))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1142))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1143)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1144))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1145))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1146)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1147))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1148)))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1149))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1150))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1151))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1152)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1153))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1154))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1155))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1156))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1157)))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1158))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1159))))
 (.branch 33
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1160))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1161)))
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1162))
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1163))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1164))))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1165))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1166)))
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1167))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1168))))
 (.branch 42
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1169))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1170)))
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1171))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1172))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1173))))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1174))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1175)))
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1176))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1177))))
 (.branch 51
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1178))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1179)))
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1180))
 (.branch 53
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1181))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1182)))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (.matching Nonrational.InducedTerminalMatches.M036.r1183))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1184)))
 (.branch 57
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1185))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1186))))
 (.branch 60
 (.branch 59
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1187))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1188)))
 (.branch 61
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1189))
 (.branch 62
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1190))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1191))))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1192))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1193)))
 (.branch 66
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1194))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1195))))
 (.branch 69
 (.branch 68
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1196))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1197)))
 (.branch 70
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1198))
 (.branch 71
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1199))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1200)))))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M035.r1129) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M035.r1129
    Nonrational.InducedTerminalMatches.M035.r1129_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M035.r1130) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M035.r1130
    Nonrational.InducedTerminalMatches.M035.r1130_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M035.r1131) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M035.r1131
    Nonrational.InducedTerminalMatches.M035.r1131_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M035.r1132) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M035.r1132
    Nonrational.InducedTerminalMatches.M035.r1132_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M035.r1133) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M035.r1133
    Nonrational.InducedTerminalMatches.M035.r1133_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M035.r1134) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M035.r1134
    Nonrational.InducedTerminalMatches.M035.r1134_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M035.r1135) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M035.r1135
    Nonrational.InducedTerminalMatches.M035.r1135_checked (by decide +kernel)
theorem record000_leaf_checked_7 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
      (record000_certificates 7) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M035.r1136) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 7) Nonrational.InducedTerminalMatches.M035.r1136
    Nonrational.InducedTerminalMatches.M035.r1136_checked (by decide +kernel)
theorem record000_leaf_checked_8 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
      (record000_certificates 8) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M035.r1137) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 8) Nonrational.InducedTerminalMatches.M035.r1137
    Nonrational.InducedTerminalMatches.M035.r1137_checked (by decide +kernel)
theorem record000_leaf_checked_9 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
      (record000_certificates 9) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M035.r1138) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 9) Nonrational.InducedTerminalMatches.M035.r1138
    Nonrational.InducedTerminalMatches.M035.r1138_checked (by decide +kernel)
theorem record000_leaf_checked_10 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
      (record000_certificates 10) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M035.r1139) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 10) Nonrational.InducedTerminalMatches.M035.r1139
    Nonrational.InducedTerminalMatches.M035.r1139_checked (by decide +kernel)
theorem record000_leaf_checked_11 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
      (record000_certificates 11) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M035.r1140) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 11) Nonrational.InducedTerminalMatches.M035.r1140
    Nonrational.InducedTerminalMatches.M035.r1140_checked (by decide +kernel)
theorem record000_leaf_checked_12 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
      (record000_certificates 12) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M035.r1141) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 12) Nonrational.InducedTerminalMatches.M035.r1141
    Nonrational.InducedTerminalMatches.M035.r1141_checked (by decide +kernel)
theorem record000_leaf_checked_13 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
      (record000_certificates 13) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M035.r1142) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 13) Nonrational.InducedTerminalMatches.M035.r1142
    Nonrational.InducedTerminalMatches.M035.r1142_checked (by decide +kernel)
theorem record000_leaf_checked_14 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
      (record000_certificates 14) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M035.r1143) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 14) Nonrational.InducedTerminalMatches.M035.r1143
    Nonrational.InducedTerminalMatches.M035.r1143_checked (by decide +kernel)
theorem record000_leaf_checked_15 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
      (record000_certificates 15) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M035.r1144) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 15) Nonrational.InducedTerminalMatches.M035.r1144
    Nonrational.InducedTerminalMatches.M035.r1144_checked (by decide +kernel)
theorem record000_leaf_checked_16 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
      (record000_certificates 16) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M035.r1145) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 16) Nonrational.InducedTerminalMatches.M035.r1145
    Nonrational.InducedTerminalMatches.M035.r1145_checked (by decide +kernel)
theorem record000_leaf_checked_17 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
      (record000_certificates 17) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M035.r1146) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 17) Nonrational.InducedTerminalMatches.M035.r1146
    Nonrational.InducedTerminalMatches.M035.r1146_checked (by decide +kernel)
theorem record000_leaf_checked_18 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
      (record000_certificates 18) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M035.r1147) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 18) Nonrational.InducedTerminalMatches.M035.r1147
    Nonrational.InducedTerminalMatches.M035.r1147_checked (by decide +kernel)
theorem record000_leaf_checked_19 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
      (record000_certificates 19) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M035.r1148) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 19) Nonrational.InducedTerminalMatches.M035.r1148
    Nonrational.InducedTerminalMatches.M035.r1148_checked (by decide +kernel)
theorem record000_leaf_checked_20 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
      (record000_certificates 20) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M035.r1149) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 20) Nonrational.InducedTerminalMatches.M035.r1149
    Nonrational.InducedTerminalMatches.M035.r1149_checked (by decide +kernel)
theorem record000_leaf_checked_21 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
      (record000_certificates 21) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M035.r1150) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 21) Nonrational.InducedTerminalMatches.M035.r1150
    Nonrational.InducedTerminalMatches.M035.r1150_checked (by decide +kernel)
theorem record000_leaf_checked_22 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
      (record000_certificates 22) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M035.r1151) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 22) Nonrational.InducedTerminalMatches.M035.r1151
    Nonrational.InducedTerminalMatches.M035.r1151_checked (by decide +kernel)
theorem record000_leaf_checked_23 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
      (record000_certificates 23) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M036.r1152) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 23) Nonrational.InducedTerminalMatches.M036.r1152
    Nonrational.InducedTerminalMatches.M036.r1152_checked (by decide +kernel)
theorem record000_leaf_checked_24 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
      (record000_certificates 24) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M036.r1153) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 24) Nonrational.InducedTerminalMatches.M036.r1153
    Nonrational.InducedTerminalMatches.M036.r1153_checked (by decide +kernel)
theorem record000_leaf_checked_25 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
      (record000_certificates 25) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M036.r1154) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 25) Nonrational.InducedTerminalMatches.M036.r1154
    Nonrational.InducedTerminalMatches.M036.r1154_checked (by decide +kernel)
theorem record000_leaf_checked_26 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
      (record000_certificates 26) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M036.r1155) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 26) Nonrational.InducedTerminalMatches.M036.r1155
    Nonrational.InducedTerminalMatches.M036.r1155_checked (by decide +kernel)
theorem record000_leaf_checked_27 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
      (record000_certificates 27) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M036.r1156) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 27) Nonrational.InducedTerminalMatches.M036.r1156
    Nonrational.InducedTerminalMatches.M036.r1156_checked (by decide +kernel)
theorem record000_leaf_checked_28 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
      (record000_certificates 28) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M036.r1157) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 28) Nonrational.InducedTerminalMatches.M036.r1157
    Nonrational.InducedTerminalMatches.M036.r1157_checked (by decide +kernel)
theorem record000_leaf_checked_29 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
      (record000_certificates 29) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M036.r1158) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 29) Nonrational.InducedTerminalMatches.M036.r1158
    Nonrational.InducedTerminalMatches.M036.r1158_checked (by decide +kernel)
theorem record000_leaf_checked_30 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
      (record000_certificates 30) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M036.r1159) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 30) Nonrational.InducedTerminalMatches.M036.r1159
    Nonrational.InducedTerminalMatches.M036.r1159_checked (by decide +kernel)
theorem record000_leaf_checked_31 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
      (record000_certificates 31) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M036.r1160) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 31) Nonrational.InducedTerminalMatches.M036.r1160
    Nonrational.InducedTerminalMatches.M036.r1160_checked (by decide +kernel)
theorem record000_leaf_checked_32 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
      (record000_certificates 32) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M036.r1161) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 32) Nonrational.InducedTerminalMatches.M036.r1161
    Nonrational.InducedTerminalMatches.M036.r1161_checked (by decide +kernel)
theorem record000_leaf_checked_33 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
      (record000_certificates 33) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M036.r1162) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 33) Nonrational.InducedTerminalMatches.M036.r1162
    Nonrational.InducedTerminalMatches.M036.r1162_checked (by decide +kernel)
theorem record000_leaf_checked_34 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
      (record000_certificates 34) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M036.r1163) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 34) Nonrational.InducedTerminalMatches.M036.r1163
    Nonrational.InducedTerminalMatches.M036.r1163_checked (by decide +kernel)
theorem record000_leaf_checked_35 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
      (record000_certificates 35) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M036.r1164) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 35) Nonrational.InducedTerminalMatches.M036.r1164
    Nonrational.InducedTerminalMatches.M036.r1164_checked (by decide +kernel)
theorem record000_leaf_checked_36 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
      (record000_certificates 36) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M036.r1165) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 36) Nonrational.InducedTerminalMatches.M036.r1165
    Nonrational.InducedTerminalMatches.M036.r1165_checked (by decide +kernel)
theorem record000_leaf_checked_37 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
      (record000_certificates 37) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M036.r1166) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 37) Nonrational.InducedTerminalMatches.M036.r1166
    Nonrational.InducedTerminalMatches.M036.r1166_checked (by decide +kernel)
theorem record000_leaf_checked_38 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
      (record000_certificates 38) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M036.r1167) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 38) Nonrational.InducedTerminalMatches.M036.r1167
    Nonrational.InducedTerminalMatches.M036.r1167_checked (by decide +kernel)
theorem record000_leaf_checked_39 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
      (record000_certificates 39) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M036.r1168) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 39) Nonrational.InducedTerminalMatches.M036.r1168
    Nonrational.InducedTerminalMatches.M036.r1168_checked (by decide +kernel)
theorem record000_leaf_checked_40 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
      (record000_certificates 40) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M036.r1169) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 40) Nonrational.InducedTerminalMatches.M036.r1169
    Nonrational.InducedTerminalMatches.M036.r1169_checked (by decide +kernel)
theorem record000_leaf_checked_41 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
      (record000_certificates 41) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M036.r1170) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 41) Nonrational.InducedTerminalMatches.M036.r1170
    Nonrational.InducedTerminalMatches.M036.r1170_checked (by decide +kernel)
theorem record000_leaf_checked_42 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
      (record000_certificates 42) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M036.r1171) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 42) Nonrational.InducedTerminalMatches.M036.r1171
    Nonrational.InducedTerminalMatches.M036.r1171_checked (by decide +kernel)
theorem record000_leaf_checked_43 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
      (record000_certificates 43) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M036.r1172) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 43) Nonrational.InducedTerminalMatches.M036.r1172
    Nonrational.InducedTerminalMatches.M036.r1172_checked (by decide +kernel)
theorem record000_leaf_checked_44 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
      (record000_certificates 44) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M036.r1173) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 44) Nonrational.InducedTerminalMatches.M036.r1173
    Nonrational.InducedTerminalMatches.M036.r1173_checked (by decide +kernel)
theorem record000_leaf_checked_45 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
      (record000_certificates 45) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M036.r1174) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 45) Nonrational.InducedTerminalMatches.M036.r1174
    Nonrational.InducedTerminalMatches.M036.r1174_checked (by decide +kernel)
theorem record000_leaf_checked_46 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
      (record000_certificates 46) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M036.r1175) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 46) Nonrational.InducedTerminalMatches.M036.r1175
    Nonrational.InducedTerminalMatches.M036.r1175_checked (by decide +kernel)
theorem record000_leaf_checked_47 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
      (record000_certificates 47) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M036.r1176) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 47) Nonrational.InducedTerminalMatches.M036.r1176
    Nonrational.InducedTerminalMatches.M036.r1176_checked (by decide +kernel)
theorem record000_leaf_checked_48 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 48)
      (record000_certificates 48) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M036.r1177) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 48) Nonrational.InducedTerminalMatches.M036.r1177
    Nonrational.InducedTerminalMatches.M036.r1177_checked (by decide +kernel)
theorem record000_leaf_checked_49 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 49)
      (record000_certificates 49) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M036.r1178) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 49) Nonrational.InducedTerminalMatches.M036.r1178
    Nonrational.InducedTerminalMatches.M036.r1178_checked (by decide +kernel)
theorem record000_leaf_checked_50 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 50)
      (record000_certificates 50) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M036.r1179) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 50) Nonrational.InducedTerminalMatches.M036.r1179
    Nonrational.InducedTerminalMatches.M036.r1179_checked (by decide +kernel)
theorem record000_leaf_checked_51 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 51)
      (record000_certificates 51) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M036.r1180) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 51) Nonrational.InducedTerminalMatches.M036.r1180
    Nonrational.InducedTerminalMatches.M036.r1180_checked (by decide +kernel)
theorem record000_leaf_checked_52 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 52)
      (record000_certificates 52) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M036.r1181) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 52) Nonrational.InducedTerminalMatches.M036.r1181
    Nonrational.InducedTerminalMatches.M036.r1181_checked (by decide +kernel)
theorem record000_leaf_checked_53 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 53)
      (record000_certificates 53) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M036.r1182) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 53) Nonrational.InducedTerminalMatches.M036.r1182
    Nonrational.InducedTerminalMatches.M036.r1182_checked (by decide +kernel)
theorem record000_leaf_checked_54 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 54)
      (record000_certificates 54) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 54)
    (.matching Nonrational.InducedTerminalMatches.M036.r1183) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 54) Nonrational.InducedTerminalMatches.M036.r1183
    Nonrational.InducedTerminalMatches.M036.r1183_checked (by decide +kernel)
theorem record000_leaf_checked_55 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 55)
      (record000_certificates 55) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 55)
    (.matching Nonrational.InducedTerminalMatches.M037.r1184) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 55) Nonrational.InducedTerminalMatches.M037.r1184
    Nonrational.InducedTerminalMatches.M037.r1184_checked (by decide +kernel)
theorem record000_leaf_checked_56 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 56)
      (record000_certificates 56) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 56)
    (.matching Nonrational.InducedTerminalMatches.M037.r1185) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 56) Nonrational.InducedTerminalMatches.M037.r1185
    Nonrational.InducedTerminalMatches.M037.r1185_checked (by decide +kernel)
theorem record000_leaf_checked_57 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 57)
      (record000_certificates 57) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 57)
    (.matching Nonrational.InducedTerminalMatches.M037.r1186) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 57) Nonrational.InducedTerminalMatches.M037.r1186
    Nonrational.InducedTerminalMatches.M037.r1186_checked (by decide +kernel)
theorem record000_leaf_checked_58 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 58)
      (record000_certificates 58) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 58)
    (.matching Nonrational.InducedTerminalMatches.M037.r1187) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 58) Nonrational.InducedTerminalMatches.M037.r1187
    Nonrational.InducedTerminalMatches.M037.r1187_checked (by decide +kernel)
theorem record000_leaf_checked_59 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 59)
      (record000_certificates 59) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 59)
    (.matching Nonrational.InducedTerminalMatches.M037.r1188) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 59) Nonrational.InducedTerminalMatches.M037.r1188
    Nonrational.InducedTerminalMatches.M037.r1188_checked (by decide +kernel)
theorem record000_leaf_checked_60 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 60)
      (record000_certificates 60) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 60)
    (.matching Nonrational.InducedTerminalMatches.M037.r1189) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 60) Nonrational.InducedTerminalMatches.M037.r1189
    Nonrational.InducedTerminalMatches.M037.r1189_checked (by decide +kernel)
theorem record000_leaf_checked_61 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 61)
      (record000_certificates 61) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 61)
    (.matching Nonrational.InducedTerminalMatches.M037.r1190) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 61) Nonrational.InducedTerminalMatches.M037.r1190
    Nonrational.InducedTerminalMatches.M037.r1190_checked (by decide +kernel)
theorem record000_leaf_checked_62 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 62)
      (record000_certificates 62) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 62)
    (.matching Nonrational.InducedTerminalMatches.M037.r1191) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 62) Nonrational.InducedTerminalMatches.M037.r1191
    Nonrational.InducedTerminalMatches.M037.r1191_checked (by decide +kernel)
theorem record000_leaf_checked_63 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 63)
      (record000_certificates 63) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 63)
    (.matching Nonrational.InducedTerminalMatches.M037.r1192) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 63) Nonrational.InducedTerminalMatches.M037.r1192
    Nonrational.InducedTerminalMatches.M037.r1192_checked (by decide +kernel)
theorem record000_leaf_checked_64 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 64)
      (record000_certificates 64) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 64)
    (.matching Nonrational.InducedTerminalMatches.M037.r1193) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 64) Nonrational.InducedTerminalMatches.M037.r1193
    Nonrational.InducedTerminalMatches.M037.r1193_checked (by decide +kernel)
theorem record000_leaf_checked_65 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 65)
      (record000_certificates 65) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 65)
    (.matching Nonrational.InducedTerminalMatches.M037.r1194) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 65) Nonrational.InducedTerminalMatches.M037.r1194
    Nonrational.InducedTerminalMatches.M037.r1194_checked (by decide +kernel)
theorem record000_leaf_checked_66 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 66)
      (record000_certificates 66) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 66)
    (.matching Nonrational.InducedTerminalMatches.M037.r1195) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 66) Nonrational.InducedTerminalMatches.M037.r1195
    Nonrational.InducedTerminalMatches.M037.r1195_checked (by decide +kernel)
theorem record000_leaf_checked_67 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 67)
      (record000_certificates 67) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 67)
    (.matching Nonrational.InducedTerminalMatches.M037.r1196) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 67) Nonrational.InducedTerminalMatches.M037.r1196
    Nonrational.InducedTerminalMatches.M037.r1196_checked (by decide +kernel)
theorem record000_leaf_checked_68 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 68)
      (record000_certificates 68) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 68)
    (.matching Nonrational.InducedTerminalMatches.M037.r1197) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 68) Nonrational.InducedTerminalMatches.M037.r1197
    Nonrational.InducedTerminalMatches.M037.r1197_checked (by decide +kernel)
theorem record000_leaf_checked_69 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 69)
      (record000_certificates 69) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 69)
    (.matching Nonrational.InducedTerminalMatches.M037.r1198) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 69) Nonrational.InducedTerminalMatches.M037.r1198
    Nonrational.InducedTerminalMatches.M037.r1198_checked (by decide +kernel)
theorem record000_leaf_checked_70 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 70)
      (record000_certificates 70) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 70)
    (.matching Nonrational.InducedTerminalMatches.M037.r1199) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 70) Nonrational.InducedTerminalMatches.M037.r1199
    Nonrational.InducedTerminalMatches.M037.r1199_checked (by decide +kernel)
theorem record000_leaf_checked_71 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 71)
      (record000_certificates 71) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 71)
    (.matching Nonrational.InducedTerminalMatches.M037.r1200) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 71) Nonrational.InducedTerminalMatches.M037.r1200
    Nonrational.InducedTerminalMatches.M037.r1200_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (Fin.cases record000_leaf_checked_30 (Fin.cases record000_leaf_checked_31 (Fin.cases record000_leaf_checked_32 (Fin.cases record000_leaf_checked_33 (Fin.cases record000_leaf_checked_34 (Fin.cases record000_leaf_checked_35 (Fin.cases record000_leaf_checked_36 (Fin.cases record000_leaf_checked_37 (Fin.cases record000_leaf_checked_38 (Fin.cases record000_leaf_checked_39 (Fin.cases record000_leaf_checked_40 (Fin.cases record000_leaf_checked_41 (Fin.cases record000_leaf_checked_42 (Fin.cases record000_leaf_checked_43 (Fin.cases record000_leaf_checked_44 (Fin.cases record000_leaf_checked_45 (Fin.cases record000_leaf_checked_46 (Fin.cases record000_leaf_checked_47 (Fin.cases record000_leaf_checked_48 (Fin.cases record000_leaf_checked_49 (Fin.cases record000_leaf_checked_50 (Fin.cases record000_leaf_checked_51 (Fin.cases record000_leaf_checked_52 (Fin.cases record000_leaf_checked_53 (Fin.cases record000_leaf_checked_54 (Fin.cases record000_leaf_checked_55 (Fin.cases record000_leaf_checked_56 (Fin.cases record000_leaf_checked_57 (Fin.cases record000_leaf_checked_58 (Fin.cases record000_leaf_checked_59 (Fin.cases record000_leaf_checked_60 (Fin.cases record000_leaf_checked_61 (Fin.cases record000_leaf_checked_62 (Fin.cases record000_leaf_checked_63 (Fin.cases record000_leaf_checked_64 (Fin.cases record000_leaf_checked_65 (Fin.cases record000_leaf_checked_66 (Fin.cases record000_leaf_checked_67 (Fin.cases record000_leaf_checked_68 (Fin.cases record000_leaf_checked_69 (Fin.cases record000_leaf_checked_70 (Fin.cases record000_leaf_checked_71 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1201))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1202))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1203))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1204))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1205)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1206))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1207)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1208))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1209))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1210))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1211))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1212)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1213))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1214))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M037.r1215))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1216))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1217))))
 (.branch 19
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1218))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1219)))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1220))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1221)))))
 (.branch 24
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1222))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1223))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1224))))
 (.branch 26
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1225))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1226)))
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1227))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1228)))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1229))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1230))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1231))))
 (.branch 33
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1232))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1233)))
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1234))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1235)))))
 (.branch 38
 (.branch 36
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1236))
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1237))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1238))))
 (.branch 40
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1239))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1240)))
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1241))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1242))))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1243))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1244))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1245))))
 (.branch 47
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1246))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M038.r1247)))
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1248))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1249)))))
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1250))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1251)))
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1252))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1253))))
 (.branch 55
 (.branch 54
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1254))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1255)))
 (.branch 56
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1256))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1257))))))))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M037.r1201) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M037.r1201
    Nonrational.InducedTerminalMatches.M037.r1201_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M037.r1202) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M037.r1202
    Nonrational.InducedTerminalMatches.M037.r1202_checked (by decide +kernel)
theorem record001_leaf_checked_2 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
      (record001_certificates 2) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M037.r1203) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 2) Nonrational.InducedTerminalMatches.M037.r1203
    Nonrational.InducedTerminalMatches.M037.r1203_checked (by decide +kernel)
theorem record001_leaf_checked_3 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
      (record001_certificates 3) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M037.r1204) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 3) Nonrational.InducedTerminalMatches.M037.r1204
    Nonrational.InducedTerminalMatches.M037.r1204_checked (by decide +kernel)
theorem record001_leaf_checked_4 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
      (record001_certificates 4) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M037.r1205) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 4) Nonrational.InducedTerminalMatches.M037.r1205
    Nonrational.InducedTerminalMatches.M037.r1205_checked (by decide +kernel)
theorem record001_leaf_checked_5 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
      (record001_certificates 5) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M037.r1206) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 5) Nonrational.InducedTerminalMatches.M037.r1206
    Nonrational.InducedTerminalMatches.M037.r1206_checked (by decide +kernel)
theorem record001_leaf_checked_6 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
      (record001_certificates 6) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M037.r1207) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 6) Nonrational.InducedTerminalMatches.M037.r1207
    Nonrational.InducedTerminalMatches.M037.r1207_checked (by decide +kernel)
theorem record001_leaf_checked_7 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
      (record001_certificates 7) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M037.r1208) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 7) Nonrational.InducedTerminalMatches.M037.r1208
    Nonrational.InducedTerminalMatches.M037.r1208_checked (by decide +kernel)
theorem record001_leaf_checked_8 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
      (record001_certificates 8) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M037.r1209) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 8) Nonrational.InducedTerminalMatches.M037.r1209
    Nonrational.InducedTerminalMatches.M037.r1209_checked (by decide +kernel)
theorem record001_leaf_checked_9 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
      (record001_certificates 9) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M037.r1210) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 9) Nonrational.InducedTerminalMatches.M037.r1210
    Nonrational.InducedTerminalMatches.M037.r1210_checked (by decide +kernel)
theorem record001_leaf_checked_10 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
      (record001_certificates 10) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M037.r1211) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 10) Nonrational.InducedTerminalMatches.M037.r1211
    Nonrational.InducedTerminalMatches.M037.r1211_checked (by decide +kernel)
theorem record001_leaf_checked_11 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
      (record001_certificates 11) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M037.r1212) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 11) Nonrational.InducedTerminalMatches.M037.r1212
    Nonrational.InducedTerminalMatches.M037.r1212_checked (by decide +kernel)
theorem record001_leaf_checked_12 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 12)
      (record001_certificates 12) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M037.r1213) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 12) Nonrational.InducedTerminalMatches.M037.r1213
    Nonrational.InducedTerminalMatches.M037.r1213_checked (by decide +kernel)
theorem record001_leaf_checked_13 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 13)
      (record001_certificates 13) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M037.r1214) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 13) Nonrational.InducedTerminalMatches.M037.r1214
    Nonrational.InducedTerminalMatches.M037.r1214_checked (by decide +kernel)
theorem record001_leaf_checked_14 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 14)
      (record001_certificates 14) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M037.r1215) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 14) Nonrational.InducedTerminalMatches.M037.r1215
    Nonrational.InducedTerminalMatches.M037.r1215_checked (by decide +kernel)
theorem record001_leaf_checked_15 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 15)
      (record001_certificates 15) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M038.r1216) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 15) Nonrational.InducedTerminalMatches.M038.r1216
    Nonrational.InducedTerminalMatches.M038.r1216_checked (by decide +kernel)
theorem record001_leaf_checked_16 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 16)
      (record001_certificates 16) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M038.r1217) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 16) Nonrational.InducedTerminalMatches.M038.r1217
    Nonrational.InducedTerminalMatches.M038.r1217_checked (by decide +kernel)
theorem record001_leaf_checked_17 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 17)
      (record001_certificates 17) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M038.r1218) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 17) Nonrational.InducedTerminalMatches.M038.r1218
    Nonrational.InducedTerminalMatches.M038.r1218_checked (by decide +kernel)
theorem record001_leaf_checked_18 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 18)
      (record001_certificates 18) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M038.r1219) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 18) Nonrational.InducedTerminalMatches.M038.r1219
    Nonrational.InducedTerminalMatches.M038.r1219_checked (by decide +kernel)
theorem record001_leaf_checked_19 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 19)
      (record001_certificates 19) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M038.r1220) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 19) Nonrational.InducedTerminalMatches.M038.r1220
    Nonrational.InducedTerminalMatches.M038.r1220_checked (by decide +kernel)
theorem record001_leaf_checked_20 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 20)
      (record001_certificates 20) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M038.r1221) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 20) Nonrational.InducedTerminalMatches.M038.r1221
    Nonrational.InducedTerminalMatches.M038.r1221_checked (by decide +kernel)
theorem record001_leaf_checked_21 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 21)
      (record001_certificates 21) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M038.r1222) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 21) Nonrational.InducedTerminalMatches.M038.r1222
    Nonrational.InducedTerminalMatches.M038.r1222_checked (by decide +kernel)
theorem record001_leaf_checked_22 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 22)
      (record001_certificates 22) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M038.r1223) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 22) Nonrational.InducedTerminalMatches.M038.r1223
    Nonrational.InducedTerminalMatches.M038.r1223_checked (by decide +kernel)
theorem record001_leaf_checked_23 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 23)
      (record001_certificates 23) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M038.r1224) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 23) Nonrational.InducedTerminalMatches.M038.r1224
    Nonrational.InducedTerminalMatches.M038.r1224_checked (by decide +kernel)
theorem record001_leaf_checked_24 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 24)
      (record001_certificates 24) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M038.r1225) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 24) Nonrational.InducedTerminalMatches.M038.r1225
    Nonrational.InducedTerminalMatches.M038.r1225_checked (by decide +kernel)
theorem record001_leaf_checked_25 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 25)
      (record001_certificates 25) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M038.r1226) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 25) Nonrational.InducedTerminalMatches.M038.r1226
    Nonrational.InducedTerminalMatches.M038.r1226_checked (by decide +kernel)
theorem record001_leaf_checked_26 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 26)
      (record001_certificates 26) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M038.r1227) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 26) Nonrational.InducedTerminalMatches.M038.r1227
    Nonrational.InducedTerminalMatches.M038.r1227_checked (by decide +kernel)
theorem record001_leaf_checked_27 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 27)
      (record001_certificates 27) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M038.r1228) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 27) Nonrational.InducedTerminalMatches.M038.r1228
    Nonrational.InducedTerminalMatches.M038.r1228_checked (by decide +kernel)
theorem record001_leaf_checked_28 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 28)
      (record001_certificates 28) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M038.r1229) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 28) Nonrational.InducedTerminalMatches.M038.r1229
    Nonrational.InducedTerminalMatches.M038.r1229_checked (by decide +kernel)
theorem record001_leaf_checked_29 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 29)
      (record001_certificates 29) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M038.r1230) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 29) Nonrational.InducedTerminalMatches.M038.r1230
    Nonrational.InducedTerminalMatches.M038.r1230_checked (by decide +kernel)
theorem record001_leaf_checked_30 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 30)
      (record001_certificates 30) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M038.r1231) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 30) Nonrational.InducedTerminalMatches.M038.r1231
    Nonrational.InducedTerminalMatches.M038.r1231_checked (by decide +kernel)
theorem record001_leaf_checked_31 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 31)
      (record001_certificates 31) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M038.r1232) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 31) Nonrational.InducedTerminalMatches.M038.r1232
    Nonrational.InducedTerminalMatches.M038.r1232_checked (by decide +kernel)
theorem record001_leaf_checked_32 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 32)
      (record001_certificates 32) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M038.r1233) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 32) Nonrational.InducedTerminalMatches.M038.r1233
    Nonrational.InducedTerminalMatches.M038.r1233_checked (by decide +kernel)
theorem record001_leaf_checked_33 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 33)
      (record001_certificates 33) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M038.r1234) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 33) Nonrational.InducedTerminalMatches.M038.r1234
    Nonrational.InducedTerminalMatches.M038.r1234_checked (by decide +kernel)
theorem record001_leaf_checked_34 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 34)
      (record001_certificates 34) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M038.r1235) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 34) Nonrational.InducedTerminalMatches.M038.r1235
    Nonrational.InducedTerminalMatches.M038.r1235_checked (by decide +kernel)
theorem record001_leaf_checked_35 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 35)
      (record001_certificates 35) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M038.r1236) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 35) Nonrational.InducedTerminalMatches.M038.r1236
    Nonrational.InducedTerminalMatches.M038.r1236_checked (by decide +kernel)
theorem record001_leaf_checked_36 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 36)
      (record001_certificates 36) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M038.r1237) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 36) Nonrational.InducedTerminalMatches.M038.r1237
    Nonrational.InducedTerminalMatches.M038.r1237_checked (by decide +kernel)
theorem record001_leaf_checked_37 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 37)
      (record001_certificates 37) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M038.r1238) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 37) Nonrational.InducedTerminalMatches.M038.r1238
    Nonrational.InducedTerminalMatches.M038.r1238_checked (by decide +kernel)
theorem record001_leaf_checked_38 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 38)
      (record001_certificates 38) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M038.r1239) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 38) Nonrational.InducedTerminalMatches.M038.r1239
    Nonrational.InducedTerminalMatches.M038.r1239_checked (by decide +kernel)
theorem record001_leaf_checked_39 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 39)
      (record001_certificates 39) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M038.r1240) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 39) Nonrational.InducedTerminalMatches.M038.r1240
    Nonrational.InducedTerminalMatches.M038.r1240_checked (by decide +kernel)
theorem record001_leaf_checked_40 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 40)
      (record001_certificates 40) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M038.r1241) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 40) Nonrational.InducedTerminalMatches.M038.r1241
    Nonrational.InducedTerminalMatches.M038.r1241_checked (by decide +kernel)
theorem record001_leaf_checked_41 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 41)
      (record001_certificates 41) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M038.r1242) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 41) Nonrational.InducedTerminalMatches.M038.r1242
    Nonrational.InducedTerminalMatches.M038.r1242_checked (by decide +kernel)
theorem record001_leaf_checked_42 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 42)
      (record001_certificates 42) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M038.r1243) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 42) Nonrational.InducedTerminalMatches.M038.r1243
    Nonrational.InducedTerminalMatches.M038.r1243_checked (by decide +kernel)
theorem record001_leaf_checked_43 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 43)
      (record001_certificates 43) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M038.r1244) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 43) Nonrational.InducedTerminalMatches.M038.r1244
    Nonrational.InducedTerminalMatches.M038.r1244_checked (by decide +kernel)
theorem record001_leaf_checked_44 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 44)
      (record001_certificates 44) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M038.r1245) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 44) Nonrational.InducedTerminalMatches.M038.r1245
    Nonrational.InducedTerminalMatches.M038.r1245_checked (by decide +kernel)
theorem record001_leaf_checked_45 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 45)
      (record001_certificates 45) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M038.r1246) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 45) Nonrational.InducedTerminalMatches.M038.r1246
    Nonrational.InducedTerminalMatches.M038.r1246_checked (by decide +kernel)
theorem record001_leaf_checked_46 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 46)
      (record001_certificates 46) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M038.r1247) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 46) Nonrational.InducedTerminalMatches.M038.r1247
    Nonrational.InducedTerminalMatches.M038.r1247_checked (by decide +kernel)
theorem record001_leaf_checked_47 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 47)
      (record001_certificates 47) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M039.r1248) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 47) Nonrational.InducedTerminalMatches.M039.r1248
    Nonrational.InducedTerminalMatches.M039.r1248_checked (by decide +kernel)
theorem record001_leaf_checked_48 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 48)
      (record001_certificates 48) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M039.r1249) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 48) Nonrational.InducedTerminalMatches.M039.r1249
    Nonrational.InducedTerminalMatches.M039.r1249_checked (by decide +kernel)
theorem record001_leaf_checked_49 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 49)
      (record001_certificates 49) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M039.r1250) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 49) Nonrational.InducedTerminalMatches.M039.r1250
    Nonrational.InducedTerminalMatches.M039.r1250_checked (by decide +kernel)
theorem record001_leaf_checked_50 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 50)
      (record001_certificates 50) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M039.r1251) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 50) Nonrational.InducedTerminalMatches.M039.r1251
    Nonrational.InducedTerminalMatches.M039.r1251_checked (by decide +kernel)
theorem record001_leaf_checked_51 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 51)
      (record001_certificates 51) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M039.r1252) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 51) Nonrational.InducedTerminalMatches.M039.r1252
    Nonrational.InducedTerminalMatches.M039.r1252_checked (by decide +kernel)
theorem record001_leaf_checked_52 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 52)
      (record001_certificates 52) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M039.r1253) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 52) Nonrational.InducedTerminalMatches.M039.r1253
    Nonrational.InducedTerminalMatches.M039.r1253_checked (by decide +kernel)
theorem record001_leaf_checked_53 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 53)
      (record001_certificates 53) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M039.r1254) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 53) Nonrational.InducedTerminalMatches.M039.r1254
    Nonrational.InducedTerminalMatches.M039.r1254_checked (by decide +kernel)
theorem record001_leaf_checked_54 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 54)
      (record001_certificates 54) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 54)
    (.matching Nonrational.InducedTerminalMatches.M039.r1255) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 54) Nonrational.InducedTerminalMatches.M039.r1255
    Nonrational.InducedTerminalMatches.M039.r1255_checked (by decide +kernel)
theorem record001_leaf_checked_55 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 55)
      (record001_certificates 55) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 55)
    (.matching Nonrational.InducedTerminalMatches.M039.r1256) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 55) Nonrational.InducedTerminalMatches.M039.r1256
    Nonrational.InducedTerminalMatches.M039.r1256_checked (by decide +kernel)
theorem record001_leaf_checked_56 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 56)
      (record001_certificates 56) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 56)
    (.matching Nonrational.InducedTerminalMatches.M039.r1257) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 56) Nonrational.InducedTerminalMatches.M039.r1257
    Nonrational.InducedTerminalMatches.M039.r1257_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (Fin.cases record001_leaf_checked_15 (Fin.cases record001_leaf_checked_16 (Fin.cases record001_leaf_checked_17 (Fin.cases record001_leaf_checked_18 (Fin.cases record001_leaf_checked_19 (Fin.cases record001_leaf_checked_20 (Fin.cases record001_leaf_checked_21 (Fin.cases record001_leaf_checked_22 (Fin.cases record001_leaf_checked_23 (Fin.cases record001_leaf_checked_24 (Fin.cases record001_leaf_checked_25 (Fin.cases record001_leaf_checked_26 (Fin.cases record001_leaf_checked_27 (Fin.cases record001_leaf_checked_28 (Fin.cases record001_leaf_checked_29 (Fin.cases record001_leaf_checked_30 (Fin.cases record001_leaf_checked_31 (Fin.cases record001_leaf_checked_32 (Fin.cases record001_leaf_checked_33 (Fin.cases record001_leaf_checked_34 (Fin.cases record001_leaf_checked_35 (Fin.cases record001_leaf_checked_36 (Fin.cases record001_leaf_checked_37 (Fin.cases record001_leaf_checked_38 (Fin.cases record001_leaf_checked_39 (Fin.cases record001_leaf_checked_40 (Fin.cases record001_leaf_checked_41 (Fin.cases record001_leaf_checked_42 (Fin.cases record001_leaf_checked_43 (Fin.cases record001_leaf_checked_44 (Fin.cases record001_leaf_checked_45 (Fin.cases record001_leaf_checked_46 (Fin.cases record001_leaf_checked_47 (Fin.cases record001_leaf_checked_48 (Fin.cases record001_leaf_checked_49 (Fin.cases record001_leaf_checked_50 (Fin.cases record001_leaf_checked_51 (Fin.cases record001_leaf_checked_52 (Fin.cases record001_leaf_checked_53 (Fin.cases record001_leaf_checked_54 (Fin.cases record001_leaf_checked_55 (Fin.cases record001_leaf_checked_56 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record001_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00035
