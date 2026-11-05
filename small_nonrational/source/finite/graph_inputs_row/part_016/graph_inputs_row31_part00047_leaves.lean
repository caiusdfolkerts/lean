module
prelude
public import GraphInputsRow31Part00047Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M080
public import InducedTerminalMatches.M081

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2584))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2585))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2586))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2587))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2588))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2589)))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M080.r2584) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M080.r2584
    Nonrational.InducedTerminalMatches.M080.r2584_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M080.r2585) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M080.r2585
    Nonrational.InducedTerminalMatches.M080.r2585_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M080.r2586) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M080.r2586
    Nonrational.InducedTerminalMatches.M080.r2586_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M080.r2587) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M080.r2587
    Nonrational.InducedTerminalMatches.M080.r2587_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M080.r2588) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M080.r2588
    Nonrational.InducedTerminalMatches.M080.r2588_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M080.r2589) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M080.r2589
    Nonrational.InducedTerminalMatches.M080.r2589_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (fun j => Fin.elim0 j)))))))
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
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2590))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2591))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2592))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2593))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2594)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2595))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2596)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2597))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2598))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2599))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2600))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2601)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2602))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2603))))))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M080.r2590) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 0) Nonrational.InducedTerminalMatches.M080.r2590
    Nonrational.InducedTerminalMatches.M080.r2590_checked (by decide +kernel)
theorem record002_leaf_checked_1 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 1)
      (record002_certificates 1) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M080.r2591) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 1) Nonrational.InducedTerminalMatches.M080.r2591
    Nonrational.InducedTerminalMatches.M080.r2591_checked (by decide +kernel)
theorem record002_leaf_checked_2 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 2)
      (record002_certificates 2) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M081.r2592) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 2) Nonrational.InducedTerminalMatches.M081.r2592
    Nonrational.InducedTerminalMatches.M081.r2592_checked (by decide +kernel)
theorem record002_leaf_checked_3 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 3)
      (record002_certificates 3) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M081.r2593) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 3) Nonrational.InducedTerminalMatches.M081.r2593
    Nonrational.InducedTerminalMatches.M081.r2593_checked (by decide +kernel)
theorem record002_leaf_checked_4 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 4)
      (record002_certificates 4) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M081.r2594) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 4) Nonrational.InducedTerminalMatches.M081.r2594
    Nonrational.InducedTerminalMatches.M081.r2594_checked (by decide +kernel)
theorem record002_leaf_checked_5 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 5)
      (record002_certificates 5) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M081.r2595) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 5) Nonrational.InducedTerminalMatches.M081.r2595
    Nonrational.InducedTerminalMatches.M081.r2595_checked (by decide +kernel)
theorem record002_leaf_checked_6 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 6)
      (record002_certificates 6) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M081.r2596) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 6) Nonrational.InducedTerminalMatches.M081.r2596
    Nonrational.InducedTerminalMatches.M081.r2596_checked (by decide +kernel)
theorem record002_leaf_checked_7 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 7)
      (record002_certificates 7) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M081.r2597) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 7) Nonrational.InducedTerminalMatches.M081.r2597
    Nonrational.InducedTerminalMatches.M081.r2597_checked (by decide +kernel)
theorem record002_leaf_checked_8 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 8)
      (record002_certificates 8) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M081.r2598) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 8) Nonrational.InducedTerminalMatches.M081.r2598
    Nonrational.InducedTerminalMatches.M081.r2598_checked (by decide +kernel)
theorem record002_leaf_checked_9 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 9)
      (record002_certificates 9) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M081.r2599) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 9) Nonrational.InducedTerminalMatches.M081.r2599
    Nonrational.InducedTerminalMatches.M081.r2599_checked (by decide +kernel)
theorem record002_leaf_checked_10 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 10)
      (record002_certificates 10) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M081.r2600) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 10) Nonrational.InducedTerminalMatches.M081.r2600
    Nonrational.InducedTerminalMatches.M081.r2600_checked (by decide +kernel)
theorem record002_leaf_checked_11 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 11)
      (record002_certificates 11) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M081.r2601) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 11) Nonrational.InducedTerminalMatches.M081.r2601
    Nonrational.InducedTerminalMatches.M081.r2601_checked (by decide +kernel)
theorem record002_leaf_checked_12 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 12)
      (record002_certificates 12) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M081.r2602) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 12) Nonrational.InducedTerminalMatches.M081.r2602
    Nonrational.InducedTerminalMatches.M081.r2602_checked (by decide +kernel)
theorem record002_leaf_checked_13 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 13)
      (record002_certificates 13) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M081.r2603) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 13) Nonrational.InducedTerminalMatches.M081.r2603
    Nonrational.InducedTerminalMatches.M081.r2603_checked (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))
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
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2604))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2605))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2606))))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M081.r2604) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 0) Nonrational.InducedTerminalMatches.M081.r2604
    Nonrational.InducedTerminalMatches.M081.r2604_checked (by decide +kernel)
theorem record005_leaf_checked_1 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
      (record005_certificates 1) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M081.r2605) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 1) Nonrational.InducedTerminalMatches.M081.r2605
    Nonrational.InducedTerminalMatches.M081.r2605_checked (by decide +kernel)
theorem record005_leaf_checked_2 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
      (record005_certificates 2) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M081.r2606) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 2) Nonrational.InducedTerminalMatches.M081.r2606
    Nonrational.InducedTerminalMatches.M081.r2606_checked (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (Fin.cases record005_leaf_checked_1 (Fin.cases record005_leaf_checked_2 (fun j => Fin.elim0 j))))
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
(.leaf (.quota 1))
noncomputable def record007_certificates (j : Fin record007.l) : Certificate :=
  record007_certificateTable.get j.val
theorem record007_leaf_checked_0 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
      (record007_certificates 0) = true := by
  change RawLeafCertificate.check record007.data.quota [] (.quota 1) = true
  exact empty_checked record007.data.quota 1 (by decide +kernel)
theorem record007_leaf_certificates_checked : ∀ j : Fin record007.l,
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves j)
      (record007_certificates j) = true :=
  (Fin.cases record007_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record007_leaf_certificates_checked

noncomputable def record008_rawLeaves (j : Fin record008.l) : List Cell :=
  (record008.leaf j).map record008.data.cells
theorem record008_raw_exact (j : Fin record008.l) :
    (record008.leaf j).map record008.data.cells = record008_rawLeaves j := rfl
noncomputable def record008_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record008_certificates (j : Fin record008.l) : Certificate :=
  record008_certificateTable.get j.val
theorem record008_leaf_checked_0 :
    RawLeafCertificate.check record008.data.quota (record008_rawLeaves 0)
      (record008_certificates 0) = true := by
  change RawLeafCertificate.check record008.data.quota [] (.quota 1) = true
  exact empty_checked record008.data.quota 1 (by decide +kernel)
theorem record008_leaf_certificates_checked : ∀ j : Fin record008.l,
    RawLeafCertificate.check record008.data.quota (record008_rawLeaves j)
      (record008_certificates j) = true :=
  (Fin.cases record008_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record008_leaf_certificates_checked

noncomputable def record009_rawLeaves (j : Fin record009.l) : List Cell :=
  (record009.leaf j).map record009.data.cells
theorem record009_raw_exact (j : Fin record009.l) :
    (record009.leaf j).map record009.data.cells = record009_rawLeaves j := rfl
noncomputable def record009_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record009_certificates (j : Fin record009.l) : Certificate :=
  record009_certificateTable.get j.val
theorem record009_leaf_checked_0 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 0)
      (record009_certificates 0) = true := by
  change RawLeafCertificate.check record009.data.quota [] (.quota 1) = true
  exact empty_checked record009.data.quota 1 (by decide +kernel)
theorem record009_leaf_certificates_checked : ∀ j : Fin record009.l,
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves j)
      (record009_certificates j) = true :=
  (Fin.cases record009_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record009_leaf_certificates_checked

noncomputable def record010_rawLeaves (j : Fin record010.l) : List Cell :=
  (record010.leaf j).map record010.data.cells
theorem record010_raw_exact (j : Fin record010.l) :
    (record010.leaf j).map record010.data.cells = record010_rawLeaves j := rfl
noncomputable def record010_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record010_certificates (j : Fin record010.l) : Certificate :=
  record010_certificateTable.get j.val
theorem record010_leaf_checked_0 :
    RawLeafCertificate.check record010.data.quota (record010_rawLeaves 0)
      (record010_certificates 0) = true := by
  change RawLeafCertificate.check record010.data.quota [] (.quota 1) = true
  exact empty_checked record010.data.quota 1 (by decide +kernel)
theorem record010_leaf_certificates_checked : ∀ j : Fin record010.l,
    RawLeafCertificate.check record010.data.quota (record010_rawLeaves j)
      (record010_certificates j) = true :=
  (Fin.cases record010_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record010_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047
