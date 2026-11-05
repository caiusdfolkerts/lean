module
prelude
public import GraphInputsRow29Part00014Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M033
public import InducedTerminalMatches.M034

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota [] (.quota 1) = true
  exact empty_checked record000.data.quota 1 (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota [] (.quota 1) = true
  exact empty_checked record001.data.quota 1 (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record001_leaf_certificates_checked

noncomputable def record002_rawLeaves (j : Fin record002.l) : List Cell :=
  (record002.leaf j).map record002.data.cells
theorem record002_raw_exact (j : Fin record002.l) :
    (record002.leaf j).map record002.data.cells = record002_rawLeaves j := rfl
noncomputable def record002_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1081))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1082))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1083))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1084))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1085)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1086))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1087)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1088))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1089)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1090))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1091))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1092))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1093)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1094))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1095))))))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M033.r1081) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 0) Nonrational.InducedTerminalMatches.M033.r1081
    Nonrational.InducedTerminalMatches.M033.r1081_checked (by decide +kernel)
theorem record002_leaf_checked_1 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 1)
      (record002_certificates 1) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M033.r1082) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 1) Nonrational.InducedTerminalMatches.M033.r1082
    Nonrational.InducedTerminalMatches.M033.r1082_checked (by decide +kernel)
theorem record002_leaf_checked_2 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 2)
      (record002_certificates 2) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M033.r1083) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 2) Nonrational.InducedTerminalMatches.M033.r1083
    Nonrational.InducedTerminalMatches.M033.r1083_checked (by decide +kernel)
theorem record002_leaf_checked_3 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 3)
      (record002_certificates 3) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M033.r1084) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 3) Nonrational.InducedTerminalMatches.M033.r1084
    Nonrational.InducedTerminalMatches.M033.r1084_checked (by decide +kernel)
theorem record002_leaf_checked_4 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 4)
      (record002_certificates 4) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M033.r1085) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 4) Nonrational.InducedTerminalMatches.M033.r1085
    Nonrational.InducedTerminalMatches.M033.r1085_checked (by decide +kernel)
theorem record002_leaf_checked_5 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 5)
      (record002_certificates 5) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M033.r1086) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 5) Nonrational.InducedTerminalMatches.M033.r1086
    Nonrational.InducedTerminalMatches.M033.r1086_checked (by decide +kernel)
theorem record002_leaf_checked_6 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 6)
      (record002_certificates 6) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M033.r1087) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 6) Nonrational.InducedTerminalMatches.M033.r1087
    Nonrational.InducedTerminalMatches.M033.r1087_checked (by decide +kernel)
theorem record002_leaf_checked_7 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 7)
      (record002_certificates 7) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M034.r1088) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 7) Nonrational.InducedTerminalMatches.M034.r1088
    Nonrational.InducedTerminalMatches.M034.r1088_checked (by decide +kernel)
theorem record002_leaf_checked_8 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 8)
      (record002_certificates 8) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M034.r1089) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 8) Nonrational.InducedTerminalMatches.M034.r1089
    Nonrational.InducedTerminalMatches.M034.r1089_checked (by decide +kernel)
theorem record002_leaf_checked_9 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 9)
      (record002_certificates 9) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M034.r1090) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 9) Nonrational.InducedTerminalMatches.M034.r1090
    Nonrational.InducedTerminalMatches.M034.r1090_checked (by decide +kernel)
theorem record002_leaf_checked_10 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 10)
      (record002_certificates 10) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M034.r1091) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 10) Nonrational.InducedTerminalMatches.M034.r1091
    Nonrational.InducedTerminalMatches.M034.r1091_checked (by decide +kernel)
theorem record002_leaf_checked_11 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 11)
      (record002_certificates 11) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M034.r1092) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 11) Nonrational.InducedTerminalMatches.M034.r1092
    Nonrational.InducedTerminalMatches.M034.r1092_checked (by decide +kernel)
theorem record002_leaf_checked_12 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 12)
      (record002_certificates 12) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M034.r1093) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 12) Nonrational.InducedTerminalMatches.M034.r1093
    Nonrational.InducedTerminalMatches.M034.r1093_checked (by decide +kernel)
theorem record002_leaf_checked_13 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 13)
      (record002_certificates 13) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M034.r1094) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 13) Nonrational.InducedTerminalMatches.M034.r1094
    Nonrational.InducedTerminalMatches.M034.r1094_checked (by decide +kernel)
theorem record002_leaf_checked_14 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 14)
      (record002_certificates 14) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M034.r1095) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 14) Nonrational.InducedTerminalMatches.M034.r1095
    Nonrational.InducedTerminalMatches.M034.r1095_checked (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (Fin.cases record002_leaf_checked_14 (fun j => Fin.elim0 j))))))))))))))))
#print axioms record002_leaf_certificates_checked

noncomputable def record003_rawLeaves (j : Fin record003.l) : List Cell :=
  (record003.leaf j).map record003.data.cells
theorem record003_raw_exact (j : Fin record003.l) :
    (record003.leaf j).map record003.data.cells = record003_rawLeaves j := rfl
noncomputable def record003_certificateTable : Table Certificate :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1096))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1097)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1098))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1099))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1100))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1101)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1102))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1103))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1104))))))
noncomputable def record003_certificates (j : Fin record003.l) : Certificate :=
  record003_certificateTable.get j.val
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M034.r1096) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 0) Nonrational.InducedTerminalMatches.M034.r1096
    Nonrational.InducedTerminalMatches.M034.r1096_checked (by decide +kernel)
theorem record003_leaf_checked_1 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 1)
      (record003_certificates 1) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M034.r1097) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 1) Nonrational.InducedTerminalMatches.M034.r1097
    Nonrational.InducedTerminalMatches.M034.r1097_checked (by decide +kernel)
theorem record003_leaf_checked_2 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 2)
      (record003_certificates 2) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M034.r1098) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 2) Nonrational.InducedTerminalMatches.M034.r1098
    Nonrational.InducedTerminalMatches.M034.r1098_checked (by decide +kernel)
theorem record003_leaf_checked_3 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 3)
      (record003_certificates 3) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M034.r1099) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 3) Nonrational.InducedTerminalMatches.M034.r1099
    Nonrational.InducedTerminalMatches.M034.r1099_checked (by decide +kernel)
theorem record003_leaf_checked_4 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 4)
      (record003_certificates 4) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M034.r1100) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 4) Nonrational.InducedTerminalMatches.M034.r1100
    Nonrational.InducedTerminalMatches.M034.r1100_checked (by decide +kernel)
theorem record003_leaf_checked_5 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 5)
      (record003_certificates 5) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M034.r1101) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 5) Nonrational.InducedTerminalMatches.M034.r1101
    Nonrational.InducedTerminalMatches.M034.r1101_checked (by decide +kernel)
theorem record003_leaf_checked_6 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 6)
      (record003_certificates 6) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M034.r1102) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 6) Nonrational.InducedTerminalMatches.M034.r1102
    Nonrational.InducedTerminalMatches.M034.r1102_checked (by decide +kernel)
theorem record003_leaf_checked_7 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 7)
      (record003_certificates 7) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M034.r1103) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 7) Nonrational.InducedTerminalMatches.M034.r1103
    Nonrational.InducedTerminalMatches.M034.r1103_checked (by decide +kernel)
theorem record003_leaf_checked_8 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 8)
      (record003_certificates 8) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M034.r1104) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 8) Nonrational.InducedTerminalMatches.M034.r1104
    Nonrational.InducedTerminalMatches.M034.r1104_checked (by decide +kernel)
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (fun j => Fin.elim0 j))))))))))
#print axioms record003_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014
