module
prelude
public import GraphInputsRow31Part00124Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M096
public import InducedTerminalMatches.M097

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124
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
(.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3077))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3078)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3079))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3080))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3081)))))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M096.r3077) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M096.r3077
    Nonrational.InducedTerminalMatches.M096.r3077_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M096.r3078) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M096.r3078
    Nonrational.InducedTerminalMatches.M096.r3078_checked (by decide +kernel)
theorem record001_leaf_checked_2 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
      (record001_certificates 2) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M096.r3079) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 2) Nonrational.InducedTerminalMatches.M096.r3079
    Nonrational.InducedTerminalMatches.M096.r3079_checked (by decide +kernel)
theorem record001_leaf_checked_3 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
      (record001_certificates 3) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M096.r3080) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 3) Nonrational.InducedTerminalMatches.M096.r3080
    Nonrational.InducedTerminalMatches.M096.r3080_checked (by decide +kernel)
theorem record001_leaf_checked_4 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
      (record001_certificates 4) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M096.r3081) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 4) Nonrational.InducedTerminalMatches.M096.r3081
    Nonrational.InducedTerminalMatches.M096.r3081_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (fun j => Fin.elim0 j))))))
#print axioms record001_leaf_certificates_checked

noncomputable def record002_rawLeaves (j : Fin record002.l) : List Cell :=
  (record002.leaf j).map record002.data.cells
theorem record002_raw_exact (j : Fin record002.l) :
    (record002.leaf j).map record002.data.cells = record002_rawLeaves j := rfl
noncomputable def record002_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota [] (.quota 1) = true
  exact empty_checked record002.data.quota 1 (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record002_leaf_certificates_checked

noncomputable def record003_rawLeaves (j : Fin record003.l) : List Cell :=
  (record003.leaf j).map record003.data.cells
theorem record003_raw_exact (j : Fin record003.l) :
    (record003.leaf j).map record003.data.cells = record003_rawLeaves j := rfl
noncomputable def record003_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record003_certificates (j : Fin record003.l) : Certificate :=
  record003_certificateTable.get j.val
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  change RawLeafCertificate.check record003.data.quota [] (.quota 1) = true
  exact empty_checked record003.data.quota 1 (by decide +kernel)
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record003_leaf_certificates_checked

noncomputable def record004_rawLeaves (j : Fin record004.l) : List Cell :=
  (record004.leaf j).map record004.data.cells
theorem record004_raw_exact (j : Fin record004.l) :
    (record004.leaf j).map record004.data.cells = record004_rawLeaves j := rfl
noncomputable def record004_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota [] (.quota 1) = true
  exact empty_checked record004.data.quota 1 (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record004_leaf_certificates_checked

noncomputable def record005_rawLeaves (j : Fin record005.l) : List Cell :=
  (record005.leaf j).map record005.data.cells
theorem record005_raw_exact (j : Fin record005.l) :
    (record005.leaf j).map record005.data.cells = record005_rawLeaves j := rfl
noncomputable def record005_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota [] (.quota 1) = true
  exact empty_checked record005.data.quota 1 (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record005_leaf_certificates_checked

noncomputable def record006_rawLeaves (j : Fin record006.l) : List Cell :=
  (record006.leaf j).map record006.data.cells
theorem record006_raw_exact (j : Fin record006.l) :
    (record006.leaf j).map record006.data.cells = record006_rawLeaves j := rfl
noncomputable def record006_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record006_certificates (j : Fin record006.l) : Certificate :=
  record006_certificateTable.get j.val
theorem record006_leaf_checked_0 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
      (record006_certificates 0) = true := by
  change RawLeafCertificate.check record006.data.quota [] (.quota 1) = true
  exact empty_checked record006.data.quota 1 (by decide +kernel)
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record006_leaf_certificates_checked

noncomputable def record007_rawLeaves (j : Fin record007.l) : List Cell :=
  (record007.leaf j).map record007.data.cells
theorem record007_raw_exact (j : Fin record007.l) :
    (record007.leaf j).map record007.data.cells = record007_rawLeaves j := rfl
noncomputable def record007_certificateTable : Table Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3082))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3083))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3084))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3085))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3086))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3087)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3088))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3089))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3090))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3091))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3092))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3093))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3094))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3095))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3096))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3097))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3098))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3099)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3100))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3101))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3102))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3103))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M097.r3104))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M097.r3105)))))))
noncomputable def record007_certificates (j : Fin record007.l) : Certificate :=
  record007_certificateTable.get j.val
theorem record007_leaf_checked_0 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
      (record007_certificates 0) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M096.r3082) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 0) Nonrational.InducedTerminalMatches.M096.r3082
    Nonrational.InducedTerminalMatches.M096.r3082_checked (by decide +kernel)
theorem record007_leaf_checked_1 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 1)
      (record007_certificates 1) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M096.r3083) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 1) Nonrational.InducedTerminalMatches.M096.r3083
    Nonrational.InducedTerminalMatches.M096.r3083_checked (by decide +kernel)
theorem record007_leaf_checked_2 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 2)
      (record007_certificates 2) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M096.r3084) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 2) Nonrational.InducedTerminalMatches.M096.r3084
    Nonrational.InducedTerminalMatches.M096.r3084_checked (by decide +kernel)
theorem record007_leaf_checked_3 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 3)
      (record007_certificates 3) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M096.r3085) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 3) Nonrational.InducedTerminalMatches.M096.r3085
    Nonrational.InducedTerminalMatches.M096.r3085_checked (by decide +kernel)
theorem record007_leaf_checked_4 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 4)
      (record007_certificates 4) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M096.r3086) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 4) Nonrational.InducedTerminalMatches.M096.r3086
    Nonrational.InducedTerminalMatches.M096.r3086_checked (by decide +kernel)
theorem record007_leaf_checked_5 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 5)
      (record007_certificates 5) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M096.r3087) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 5) Nonrational.InducedTerminalMatches.M096.r3087
    Nonrational.InducedTerminalMatches.M096.r3087_checked (by decide +kernel)
theorem record007_leaf_checked_6 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 6)
      (record007_certificates 6) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M096.r3088) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 6) Nonrational.InducedTerminalMatches.M096.r3088
    Nonrational.InducedTerminalMatches.M096.r3088_checked (by decide +kernel)
theorem record007_leaf_checked_7 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 7)
      (record007_certificates 7) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M096.r3089) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 7) Nonrational.InducedTerminalMatches.M096.r3089
    Nonrational.InducedTerminalMatches.M096.r3089_checked (by decide +kernel)
theorem record007_leaf_checked_8 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 8)
      (record007_certificates 8) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M096.r3090) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 8) Nonrational.InducedTerminalMatches.M096.r3090
    Nonrational.InducedTerminalMatches.M096.r3090_checked (by decide +kernel)
theorem record007_leaf_checked_9 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 9)
      (record007_certificates 9) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M096.r3091) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 9) Nonrational.InducedTerminalMatches.M096.r3091
    Nonrational.InducedTerminalMatches.M096.r3091_checked (by decide +kernel)
theorem record007_leaf_checked_10 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 10)
      (record007_certificates 10) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M096.r3092) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 10) Nonrational.InducedTerminalMatches.M096.r3092
    Nonrational.InducedTerminalMatches.M096.r3092_checked (by decide +kernel)
theorem record007_leaf_checked_11 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 11)
      (record007_certificates 11) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M096.r3093) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 11) Nonrational.InducedTerminalMatches.M096.r3093
    Nonrational.InducedTerminalMatches.M096.r3093_checked (by decide +kernel)
theorem record007_leaf_checked_12 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 12)
      (record007_certificates 12) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M096.r3094) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 12) Nonrational.InducedTerminalMatches.M096.r3094
    Nonrational.InducedTerminalMatches.M096.r3094_checked (by decide +kernel)
theorem record007_leaf_checked_13 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 13)
      (record007_certificates 13) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M096.r3095) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 13) Nonrational.InducedTerminalMatches.M096.r3095
    Nonrational.InducedTerminalMatches.M096.r3095_checked (by decide +kernel)
theorem record007_leaf_checked_14 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 14)
      (record007_certificates 14) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M096.r3096) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 14) Nonrational.InducedTerminalMatches.M096.r3096
    Nonrational.InducedTerminalMatches.M096.r3096_checked (by decide +kernel)
theorem record007_leaf_checked_15 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 15)
      (record007_certificates 15) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M096.r3097) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 15) Nonrational.InducedTerminalMatches.M096.r3097
    Nonrational.InducedTerminalMatches.M096.r3097_checked (by decide +kernel)
theorem record007_leaf_checked_16 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 16)
      (record007_certificates 16) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M096.r3098) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 16) Nonrational.InducedTerminalMatches.M096.r3098
    Nonrational.InducedTerminalMatches.M096.r3098_checked (by decide +kernel)
theorem record007_leaf_checked_17 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 17)
      (record007_certificates 17) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M096.r3099) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 17) Nonrational.InducedTerminalMatches.M096.r3099
    Nonrational.InducedTerminalMatches.M096.r3099_checked (by decide +kernel)
theorem record007_leaf_checked_18 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 18)
      (record007_certificates 18) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M096.r3100) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 18) Nonrational.InducedTerminalMatches.M096.r3100
    Nonrational.InducedTerminalMatches.M096.r3100_checked (by decide +kernel)
theorem record007_leaf_checked_19 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 19)
      (record007_certificates 19) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M096.r3101) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 19) Nonrational.InducedTerminalMatches.M096.r3101
    Nonrational.InducedTerminalMatches.M096.r3101_checked (by decide +kernel)
theorem record007_leaf_checked_20 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 20)
      (record007_certificates 20) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M096.r3102) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 20) Nonrational.InducedTerminalMatches.M096.r3102
    Nonrational.InducedTerminalMatches.M096.r3102_checked (by decide +kernel)
theorem record007_leaf_checked_21 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 21)
      (record007_certificates 21) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M096.r3103) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 21) Nonrational.InducedTerminalMatches.M096.r3103
    Nonrational.InducedTerminalMatches.M096.r3103_checked (by decide +kernel)
theorem record007_leaf_checked_22 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 22)
      (record007_certificates 22) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M097.r3104) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 22) Nonrational.InducedTerminalMatches.M097.r3104
    Nonrational.InducedTerminalMatches.M097.r3104_checked (by decide +kernel)
theorem record007_leaf_checked_23 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 23)
      (record007_certificates 23) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M097.r3105) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 23) Nonrational.InducedTerminalMatches.M097.r3105
    Nonrational.InducedTerminalMatches.M097.r3105_checked (by decide +kernel)
theorem record007_leaf_certificates_checked : ∀ j : Fin record007.l,
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves j)
      (record007_certificates j) = true :=
  (Fin.cases record007_leaf_checked_0 (Fin.cases record007_leaf_checked_1 (Fin.cases record007_leaf_checked_2 (Fin.cases record007_leaf_checked_3 (Fin.cases record007_leaf_checked_4 (Fin.cases record007_leaf_checked_5 (Fin.cases record007_leaf_checked_6 (Fin.cases record007_leaf_checked_7 (Fin.cases record007_leaf_checked_8 (Fin.cases record007_leaf_checked_9 (Fin.cases record007_leaf_checked_10 (Fin.cases record007_leaf_checked_11 (Fin.cases record007_leaf_checked_12 (Fin.cases record007_leaf_checked_13 (Fin.cases record007_leaf_checked_14 (Fin.cases record007_leaf_checked_15 (Fin.cases record007_leaf_checked_16 (Fin.cases record007_leaf_checked_17 (Fin.cases record007_leaf_checked_18 (Fin.cases record007_leaf_checked_19 (Fin.cases record007_leaf_checked_20 (Fin.cases record007_leaf_checked_21 (Fin.cases record007_leaf_checked_22 (Fin.cases record007_leaf_checked_23 (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record007_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124
