module
prelude
public import GraphInputsRow29Part00218Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M067
public import InducedTerminalMatches.M068

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218
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
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2168))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2169))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2170))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2171))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2172)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2173))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2174)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2175))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2176)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2177))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2178))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2179))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2180)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2181))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2182))))))
noncomputable def record006_certificates (j : Fin record006.l) : Certificate :=
  record006_certificateTable.get j.val
theorem record006_leaf_checked_0 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
      (record006_certificates 0) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M067.r2168) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 0) Nonrational.InducedTerminalMatches.M067.r2168
    Nonrational.InducedTerminalMatches.M067.r2168_checked (by decide +kernel)
theorem record006_leaf_checked_1 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 1)
      (record006_certificates 1) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M067.r2169) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 1) Nonrational.InducedTerminalMatches.M067.r2169
    Nonrational.InducedTerminalMatches.M067.r2169_checked (by decide +kernel)
theorem record006_leaf_checked_2 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 2)
      (record006_certificates 2) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M067.r2170) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 2) Nonrational.InducedTerminalMatches.M067.r2170
    Nonrational.InducedTerminalMatches.M067.r2170_checked (by decide +kernel)
theorem record006_leaf_checked_3 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 3)
      (record006_certificates 3) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M067.r2171) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 3) Nonrational.InducedTerminalMatches.M067.r2171
    Nonrational.InducedTerminalMatches.M067.r2171_checked (by decide +kernel)
theorem record006_leaf_checked_4 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 4)
      (record006_certificates 4) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M067.r2172) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 4) Nonrational.InducedTerminalMatches.M067.r2172
    Nonrational.InducedTerminalMatches.M067.r2172_checked (by decide +kernel)
theorem record006_leaf_checked_5 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 5)
      (record006_certificates 5) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M067.r2173) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 5) Nonrational.InducedTerminalMatches.M067.r2173
    Nonrational.InducedTerminalMatches.M067.r2173_checked (by decide +kernel)
theorem record006_leaf_checked_6 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 6)
      (record006_certificates 6) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M067.r2174) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 6) Nonrational.InducedTerminalMatches.M067.r2174
    Nonrational.InducedTerminalMatches.M067.r2174_checked (by decide +kernel)
theorem record006_leaf_checked_7 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 7)
      (record006_certificates 7) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M067.r2175) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 7) Nonrational.InducedTerminalMatches.M067.r2175
    Nonrational.InducedTerminalMatches.M067.r2175_checked (by decide +kernel)
theorem record006_leaf_checked_8 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 8)
      (record006_certificates 8) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M068.r2176) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 8) Nonrational.InducedTerminalMatches.M068.r2176
    Nonrational.InducedTerminalMatches.M068.r2176_checked (by decide +kernel)
theorem record006_leaf_checked_9 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 9)
      (record006_certificates 9) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M068.r2177) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 9) Nonrational.InducedTerminalMatches.M068.r2177
    Nonrational.InducedTerminalMatches.M068.r2177_checked (by decide +kernel)
theorem record006_leaf_checked_10 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 10)
      (record006_certificates 10) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M068.r2178) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 10) Nonrational.InducedTerminalMatches.M068.r2178
    Nonrational.InducedTerminalMatches.M068.r2178_checked (by decide +kernel)
theorem record006_leaf_checked_11 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 11)
      (record006_certificates 11) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M068.r2179) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 11) Nonrational.InducedTerminalMatches.M068.r2179
    Nonrational.InducedTerminalMatches.M068.r2179_checked (by decide +kernel)
theorem record006_leaf_checked_12 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 12)
      (record006_certificates 12) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M068.r2180) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 12) Nonrational.InducedTerminalMatches.M068.r2180
    Nonrational.InducedTerminalMatches.M068.r2180_checked (by decide +kernel)
theorem record006_leaf_checked_13 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 13)
      (record006_certificates 13) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M068.r2181) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 13) Nonrational.InducedTerminalMatches.M068.r2181
    Nonrational.InducedTerminalMatches.M068.r2181_checked (by decide +kernel)
theorem record006_leaf_checked_14 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 14)
      (record006_certificates 14) = true := by
  change RawLeafCertificate.check record006.data.quota (record006_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M068.r2182) = true
  exact matching_checked record006.data.quota (record006_rawLeaves 14) Nonrational.InducedTerminalMatches.M068.r2182
    Nonrational.InducedTerminalMatches.M068.r2182_checked (by decide +kernel)
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (Fin.cases record006_leaf_checked_1 (Fin.cases record006_leaf_checked_2 (Fin.cases record006_leaf_checked_3 (Fin.cases record006_leaf_checked_4 (Fin.cases record006_leaf_checked_5 (Fin.cases record006_leaf_checked_6 (Fin.cases record006_leaf_checked_7 (Fin.cases record006_leaf_checked_8 (Fin.cases record006_leaf_checked_9 (Fin.cases record006_leaf_checked_10 (Fin.cases record006_leaf_checked_11 (Fin.cases record006_leaf_checked_12 (Fin.cases record006_leaf_checked_13 (Fin.cases record006_leaf_checked_14 (fun j => Fin.elim0 j))))))))))))))))
#print axioms record006_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218
