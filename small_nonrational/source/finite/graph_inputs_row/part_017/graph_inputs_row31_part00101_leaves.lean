module
prelude
public import GraphInputsRow31Part00101Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M092

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101
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
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2958))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2959))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2960))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2961))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2962))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2963)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2964))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2965))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2966))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2967))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2968))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2969))))))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M092.r2958) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M092.r2958
    Nonrational.InducedTerminalMatches.M092.r2958_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M092.r2959) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M092.r2959
    Nonrational.InducedTerminalMatches.M092.r2959_checked (by decide +kernel)
theorem record001_leaf_checked_2 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
      (record001_certificates 2) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M092.r2960) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 2) Nonrational.InducedTerminalMatches.M092.r2960
    Nonrational.InducedTerminalMatches.M092.r2960_checked (by decide +kernel)
theorem record001_leaf_checked_3 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
      (record001_certificates 3) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M092.r2961) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 3) Nonrational.InducedTerminalMatches.M092.r2961
    Nonrational.InducedTerminalMatches.M092.r2961_checked (by decide +kernel)
theorem record001_leaf_checked_4 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
      (record001_certificates 4) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M092.r2962) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 4) Nonrational.InducedTerminalMatches.M092.r2962
    Nonrational.InducedTerminalMatches.M092.r2962_checked (by decide +kernel)
theorem record001_leaf_checked_5 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
      (record001_certificates 5) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M092.r2963) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 5) Nonrational.InducedTerminalMatches.M092.r2963
    Nonrational.InducedTerminalMatches.M092.r2963_checked (by decide +kernel)
theorem record001_leaf_checked_6 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
      (record001_certificates 6) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M092.r2964) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 6) Nonrational.InducedTerminalMatches.M092.r2964
    Nonrational.InducedTerminalMatches.M092.r2964_checked (by decide +kernel)
theorem record001_leaf_checked_7 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
      (record001_certificates 7) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M092.r2965) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 7) Nonrational.InducedTerminalMatches.M092.r2965
    Nonrational.InducedTerminalMatches.M092.r2965_checked (by decide +kernel)
theorem record001_leaf_checked_8 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
      (record001_certificates 8) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M092.r2966) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 8) Nonrational.InducedTerminalMatches.M092.r2966
    Nonrational.InducedTerminalMatches.M092.r2966_checked (by decide +kernel)
theorem record001_leaf_checked_9 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
      (record001_certificates 9) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M092.r2967) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 9) Nonrational.InducedTerminalMatches.M092.r2967
    Nonrational.InducedTerminalMatches.M092.r2967_checked (by decide +kernel)
theorem record001_leaf_checked_10 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
      (record001_certificates 10) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M092.r2968) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 10) Nonrational.InducedTerminalMatches.M092.r2968
    Nonrational.InducedTerminalMatches.M092.r2968_checked (by decide +kernel)
theorem record001_leaf_checked_11 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
      (record001_certificates 11) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M092.r2969) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 11) Nonrational.InducedTerminalMatches.M092.r2969
    Nonrational.InducedTerminalMatches.M092.r2969_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (fun j => Fin.elim0 j)))))))))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101
