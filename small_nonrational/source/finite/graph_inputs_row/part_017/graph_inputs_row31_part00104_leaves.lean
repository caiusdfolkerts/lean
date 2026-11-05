module
prelude
public import GraphInputsRow31Part00104Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M093

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
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
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2977))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2978)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2979))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2980))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2981))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2982)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2983))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2984)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2985))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2986)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2987))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2988))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2989))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2990)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2991))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2992))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2993)))))))
noncomputable def record003_certificates (j : Fin record003.l) : Certificate :=
  record003_certificateTable.get j.val
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M093.r2977) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 0) Nonrational.InducedTerminalMatches.M093.r2977
    Nonrational.InducedTerminalMatches.M093.r2977_checked (by decide +kernel)
theorem record003_leaf_checked_1 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 1)
      (record003_certificates 1) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M093.r2978) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 1) Nonrational.InducedTerminalMatches.M093.r2978
    Nonrational.InducedTerminalMatches.M093.r2978_checked (by decide +kernel)
theorem record003_leaf_checked_2 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 2)
      (record003_certificates 2) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M093.r2979) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 2) Nonrational.InducedTerminalMatches.M093.r2979
    Nonrational.InducedTerminalMatches.M093.r2979_checked (by decide +kernel)
theorem record003_leaf_checked_3 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 3)
      (record003_certificates 3) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M093.r2980) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 3) Nonrational.InducedTerminalMatches.M093.r2980
    Nonrational.InducedTerminalMatches.M093.r2980_checked (by decide +kernel)
theorem record003_leaf_checked_4 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 4)
      (record003_certificates 4) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M093.r2981) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 4) Nonrational.InducedTerminalMatches.M093.r2981
    Nonrational.InducedTerminalMatches.M093.r2981_checked (by decide +kernel)
theorem record003_leaf_checked_5 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 5)
      (record003_certificates 5) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M093.r2982) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 5) Nonrational.InducedTerminalMatches.M093.r2982
    Nonrational.InducedTerminalMatches.M093.r2982_checked (by decide +kernel)
theorem record003_leaf_checked_6 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 6)
      (record003_certificates 6) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M093.r2983) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 6) Nonrational.InducedTerminalMatches.M093.r2983
    Nonrational.InducedTerminalMatches.M093.r2983_checked (by decide +kernel)
theorem record003_leaf_checked_7 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 7)
      (record003_certificates 7) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M093.r2984) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 7) Nonrational.InducedTerminalMatches.M093.r2984
    Nonrational.InducedTerminalMatches.M093.r2984_checked (by decide +kernel)
theorem record003_leaf_checked_8 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 8)
      (record003_certificates 8) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M093.r2985) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 8) Nonrational.InducedTerminalMatches.M093.r2985
    Nonrational.InducedTerminalMatches.M093.r2985_checked (by decide +kernel)
theorem record003_leaf_checked_9 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 9)
      (record003_certificates 9) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M093.r2986) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 9) Nonrational.InducedTerminalMatches.M093.r2986
    Nonrational.InducedTerminalMatches.M093.r2986_checked (by decide +kernel)
theorem record003_leaf_checked_10 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 10)
      (record003_certificates 10) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M093.r2987) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 10) Nonrational.InducedTerminalMatches.M093.r2987
    Nonrational.InducedTerminalMatches.M093.r2987_checked (by decide +kernel)
theorem record003_leaf_checked_11 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 11)
      (record003_certificates 11) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M093.r2988) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 11) Nonrational.InducedTerminalMatches.M093.r2988
    Nonrational.InducedTerminalMatches.M093.r2988_checked (by decide +kernel)
theorem record003_leaf_checked_12 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 12)
      (record003_certificates 12) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M093.r2989) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 12) Nonrational.InducedTerminalMatches.M093.r2989
    Nonrational.InducedTerminalMatches.M093.r2989_checked (by decide +kernel)
theorem record003_leaf_checked_13 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 13)
      (record003_certificates 13) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M093.r2990) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 13) Nonrational.InducedTerminalMatches.M093.r2990
    Nonrational.InducedTerminalMatches.M093.r2990_checked (by decide +kernel)
theorem record003_leaf_checked_14 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 14)
      (record003_certificates 14) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M093.r2991) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 14) Nonrational.InducedTerminalMatches.M093.r2991
    Nonrational.InducedTerminalMatches.M093.r2991_checked (by decide +kernel)
theorem record003_leaf_checked_15 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 15)
      (record003_certificates 15) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M093.r2992) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 15) Nonrational.InducedTerminalMatches.M093.r2992
    Nonrational.InducedTerminalMatches.M093.r2992_checked (by decide +kernel)
theorem record003_leaf_checked_16 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 16)
      (record003_certificates 16) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M093.r2993) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 16) Nonrational.InducedTerminalMatches.M093.r2993
    Nonrational.InducedTerminalMatches.M093.r2993_checked (by decide +kernel)
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (Fin.cases record003_leaf_checked_9 (Fin.cases record003_leaf_checked_10 (Fin.cases record003_leaf_checked_11 (Fin.cases record003_leaf_checked_12 (Fin.cases record003_leaf_checked_13 (Fin.cases record003_leaf_checked_14 (Fin.cases record003_leaf_checked_15 (Fin.cases record003_leaf_checked_16 (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record003_leaf_certificates_checked

noncomputable def record004_rawLeaves (j : Fin record004.l) : List Cell :=
  (record004.leaf j).map record004.data.cells
theorem record004_raw_exact (j : Fin record004.l) :
    (record004.leaf j).map record004.data.cells = record004_rawLeaves j := rfl
noncomputable def record004_certificateTable : Table Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2994))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2995))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2996))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2997))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2998))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2999)))))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M093.r2994) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 0) Nonrational.InducedTerminalMatches.M093.r2994
    Nonrational.InducedTerminalMatches.M093.r2994_checked (by decide +kernel)
theorem record004_leaf_checked_1 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
      (record004_certificates 1) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M093.r2995) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 1) Nonrational.InducedTerminalMatches.M093.r2995
    Nonrational.InducedTerminalMatches.M093.r2995_checked (by decide +kernel)
theorem record004_leaf_checked_2 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 2)
      (record004_certificates 2) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M093.r2996) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 2) Nonrational.InducedTerminalMatches.M093.r2996
    Nonrational.InducedTerminalMatches.M093.r2996_checked (by decide +kernel)
theorem record004_leaf_checked_3 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 3)
      (record004_certificates 3) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M093.r2997) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 3) Nonrational.InducedTerminalMatches.M093.r2997
    Nonrational.InducedTerminalMatches.M093.r2997_checked (by decide +kernel)
theorem record004_leaf_checked_4 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 4)
      (record004_certificates 4) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M093.r2998) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 4) Nonrational.InducedTerminalMatches.M093.r2998
    Nonrational.InducedTerminalMatches.M093.r2998_checked (by decide +kernel)
theorem record004_leaf_checked_5 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 5)
      (record004_certificates 5) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M093.r2999) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 5) Nonrational.InducedTerminalMatches.M093.r2999
    Nonrational.InducedTerminalMatches.M093.r2999_checked (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (Fin.cases record004_leaf_checked_1 (Fin.cases record004_leaf_checked_2 (Fin.cases record004_leaf_checked_3 (Fin.cases record004_leaf_checked_4 (Fin.cases record004_leaf_checked_5 (fun j => Fin.elim0 j)))))))
#print axioms record004_leaf_certificates_checked

noncomputable def record005_rawLeaves (j : Fin record005.l) : List Cell :=
  (record005.leaf j).map record005.data.cells
theorem record005_raw_exact (j : Fin record005.l) :
    (record005.leaf j).map record005.data.cells = record005_rawLeaves j := rfl
noncomputable def record005_certificateTable : Table Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r3000))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r3001)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r3002))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r3003))))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M093.r3000) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 0) Nonrational.InducedTerminalMatches.M093.r3000
    Nonrational.InducedTerminalMatches.M093.r3000_checked (by decide +kernel)
theorem record005_leaf_checked_1 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
      (record005_certificates 1) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M093.r3001) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 1) Nonrational.InducedTerminalMatches.M093.r3001
    Nonrational.InducedTerminalMatches.M093.r3001_checked (by decide +kernel)
theorem record005_leaf_checked_2 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
      (record005_certificates 2) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M093.r3002) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 2) Nonrational.InducedTerminalMatches.M093.r3002
    Nonrational.InducedTerminalMatches.M093.r3002_checked (by decide +kernel)
theorem record005_leaf_checked_3 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 3)
      (record005_certificates 3) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M093.r3003) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 3) Nonrational.InducedTerminalMatches.M093.r3003
    Nonrational.InducedTerminalMatches.M093.r3003_checked (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (Fin.cases record005_leaf_checked_1 (Fin.cases record005_leaf_checked_2 (Fin.cases record005_leaf_checked_3 (fun j => Fin.elim0 j)))))
#print axioms record005_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
