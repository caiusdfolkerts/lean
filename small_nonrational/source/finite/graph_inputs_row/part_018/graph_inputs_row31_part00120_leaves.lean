module
prelude
public import GraphInputsRow31Part00120Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M095

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120
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
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3051))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3052)))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M095.r3051) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M095.r3051
    Nonrational.InducedTerminalMatches.M095.r3051_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M095.r3052) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M095.r3052
    Nonrational.InducedTerminalMatches.M095.r3052_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (fun j => Fin.elim0 j)))
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
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3053))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3054)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3055))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3056))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3057))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3058)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3059))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M095.r3060)))))
noncomputable def record006_certificates (j : Fin record006.l) : Certificate :=
  record006_certificateTable.get j.val
theorem record006_leaf_checked_0 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
      (record006_certificates 0) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M095.r3053) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 0) Nonrational.InducedTerminalMatches.M095.r3053
    Nonrational.InducedTerminalMatches.M095.r3053_checked (by decide +kernel)
theorem record006_leaf_checked_1 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 1)
      (record006_certificates 1) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M095.r3054) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 1) Nonrational.InducedTerminalMatches.M095.r3054
    Nonrational.InducedTerminalMatches.M095.r3054_checked (by decide +kernel)
theorem record006_leaf_checked_2 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 2)
      (record006_certificates 2) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M095.r3055) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 2) Nonrational.InducedTerminalMatches.M095.r3055
    Nonrational.InducedTerminalMatches.M095.r3055_checked (by decide +kernel)
theorem record006_leaf_checked_3 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 3)
      (record006_certificates 3) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M095.r3056) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 3) Nonrational.InducedTerminalMatches.M095.r3056
    Nonrational.InducedTerminalMatches.M095.r3056_checked (by decide +kernel)
theorem record006_leaf_checked_4 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 4)
      (record006_certificates 4) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M095.r3057) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 4) Nonrational.InducedTerminalMatches.M095.r3057
    Nonrational.InducedTerminalMatches.M095.r3057_checked (by decide +kernel)
theorem record006_leaf_checked_5 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 5)
      (record006_certificates 5) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M095.r3058) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 5) Nonrational.InducedTerminalMatches.M095.r3058
    Nonrational.InducedTerminalMatches.M095.r3058_checked (by decide +kernel)
theorem record006_leaf_checked_6 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 6)
      (record006_certificates 6) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M095.r3059) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 6) Nonrational.InducedTerminalMatches.M095.r3059
    Nonrational.InducedTerminalMatches.M095.r3059_checked (by decide +kernel)
theorem record006_leaf_checked_7 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 7)
      (record006_certificates 7) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M095.r3060) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 7) Nonrational.InducedTerminalMatches.M095.r3060
    Nonrational.InducedTerminalMatches.M095.r3060_checked (by decide +kernel)
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (Fin.cases record006_leaf_checked_1 (Fin.cases record006_leaf_checked_2 (Fin.cases record006_leaf_checked_3 (Fin.cases record006_leaf_checked_4 (Fin.cases record006_leaf_checked_5 (Fin.cases record006_leaf_checked_6 (Fin.cases record006_leaf_checked_7 (fun j => Fin.elim0 j)))))))))
#print axioms record006_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120
