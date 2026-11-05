module
prelude
public import GraphInputsRow31Part00076Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M086

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2763))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2764)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2765))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2766))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M086.r2763) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M086.r2763
    Nonrational.InducedTerminalMatches.M086.r2763_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M086.r2764) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M086.r2764
    Nonrational.InducedTerminalMatches.M086.r2764_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M086.r2765) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M086.r2765
    Nonrational.InducedTerminalMatches.M086.r2765_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M086.r2766) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M086.r2766
    Nonrational.InducedTerminalMatches.M086.r2766_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (fun j => Fin.elim0 j)))))
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
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2767))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2768)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2769))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2770))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2771)))))
 (.branch 7
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2772))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2773)))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2774))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2775))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2776))))))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M086.r2767) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 0) Nonrational.InducedTerminalMatches.M086.r2767
    Nonrational.InducedTerminalMatches.M086.r2767_checked (by decide +kernel)
theorem record004_leaf_checked_1 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
      (record004_certificates 1) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M086.r2768) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 1) Nonrational.InducedTerminalMatches.M086.r2768
    Nonrational.InducedTerminalMatches.M086.r2768_checked (by decide +kernel)
theorem record004_leaf_checked_2 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 2)
      (record004_certificates 2) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M086.r2769) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 2) Nonrational.InducedTerminalMatches.M086.r2769
    Nonrational.InducedTerminalMatches.M086.r2769_checked (by decide +kernel)
theorem record004_leaf_checked_3 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 3)
      (record004_certificates 3) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M086.r2770) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 3) Nonrational.InducedTerminalMatches.M086.r2770
    Nonrational.InducedTerminalMatches.M086.r2770_checked (by decide +kernel)
theorem record004_leaf_checked_4 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 4)
      (record004_certificates 4) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M086.r2771) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 4) Nonrational.InducedTerminalMatches.M086.r2771
    Nonrational.InducedTerminalMatches.M086.r2771_checked (by decide +kernel)
theorem record004_leaf_checked_5 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 5)
      (record004_certificates 5) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M086.r2772) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 5) Nonrational.InducedTerminalMatches.M086.r2772
    Nonrational.InducedTerminalMatches.M086.r2772_checked (by decide +kernel)
theorem record004_leaf_checked_6 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 6)
      (record004_certificates 6) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M086.r2773) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 6) Nonrational.InducedTerminalMatches.M086.r2773
    Nonrational.InducedTerminalMatches.M086.r2773_checked (by decide +kernel)
theorem record004_leaf_checked_7 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 7)
      (record004_certificates 7) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M086.r2774) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 7) Nonrational.InducedTerminalMatches.M086.r2774
    Nonrational.InducedTerminalMatches.M086.r2774_checked (by decide +kernel)
theorem record004_leaf_checked_8 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 8)
      (record004_certificates 8) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M086.r2775) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 8) Nonrational.InducedTerminalMatches.M086.r2775
    Nonrational.InducedTerminalMatches.M086.r2775_checked (by decide +kernel)
theorem record004_leaf_checked_9 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 9)
      (record004_certificates 9) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M086.r2776) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 9) Nonrational.InducedTerminalMatches.M086.r2776
    Nonrational.InducedTerminalMatches.M086.r2776_checked (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (Fin.cases record004_leaf_checked_1 (Fin.cases record004_leaf_checked_2 (Fin.cases record004_leaf_checked_3 (Fin.cases record004_leaf_checked_4 (Fin.cases record004_leaf_checked_5 (Fin.cases record004_leaf_checked_6 (Fin.cases record004_leaf_checked_7 (Fin.cases record004_leaf_checked_8 (Fin.cases record004_leaf_checked_9 (fun j => Fin.elim0 j)))))))))))
#print axioms record004_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076
