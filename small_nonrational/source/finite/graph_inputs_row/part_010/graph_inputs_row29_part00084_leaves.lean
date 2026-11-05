module
prelude
public import GraphInputsRow29Part00084Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M045
public import InducedTerminalMatches.M046

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084
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
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1459))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1460))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1461))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1462))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1463)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1464))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1465)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1466))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1467)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1468))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1469))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1470))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1471)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1472))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1473))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1474))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1475))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1476))))
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1477))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1478)))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1479))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1480)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1481))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1482)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1483))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1484))))
 (.branch 28
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1485))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1486)))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1487))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1488)))))))
noncomputable def record009_certificates (j : Fin record009.l) : Certificate :=
  record009_certificateTable.get j.val
theorem record009_leaf_checked_0 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 0)
      (record009_certificates 0) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M045.r1459) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 0) Nonrational.InducedTerminalMatches.M045.r1459
    Nonrational.InducedTerminalMatches.M045.r1459_checked (by decide +kernel)
theorem record009_leaf_checked_1 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 1)
      (record009_certificates 1) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M045.r1460) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 1) Nonrational.InducedTerminalMatches.M045.r1460
    Nonrational.InducedTerminalMatches.M045.r1460_checked (by decide +kernel)
theorem record009_leaf_checked_2 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 2)
      (record009_certificates 2) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M045.r1461) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 2) Nonrational.InducedTerminalMatches.M045.r1461
    Nonrational.InducedTerminalMatches.M045.r1461_checked (by decide +kernel)
theorem record009_leaf_checked_3 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 3)
      (record009_certificates 3) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M045.r1462) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 3) Nonrational.InducedTerminalMatches.M045.r1462
    Nonrational.InducedTerminalMatches.M045.r1462_checked (by decide +kernel)
theorem record009_leaf_checked_4 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 4)
      (record009_certificates 4) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M045.r1463) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 4) Nonrational.InducedTerminalMatches.M045.r1463
    Nonrational.InducedTerminalMatches.M045.r1463_checked (by decide +kernel)
theorem record009_leaf_checked_5 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 5)
      (record009_certificates 5) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M045.r1464) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 5) Nonrational.InducedTerminalMatches.M045.r1464
    Nonrational.InducedTerminalMatches.M045.r1464_checked (by decide +kernel)
theorem record009_leaf_checked_6 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 6)
      (record009_certificates 6) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M045.r1465) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 6) Nonrational.InducedTerminalMatches.M045.r1465
    Nonrational.InducedTerminalMatches.M045.r1465_checked (by decide +kernel)
theorem record009_leaf_checked_7 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 7)
      (record009_certificates 7) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M045.r1466) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 7) Nonrational.InducedTerminalMatches.M045.r1466
    Nonrational.InducedTerminalMatches.M045.r1466_checked (by decide +kernel)
theorem record009_leaf_checked_8 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 8)
      (record009_certificates 8) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M045.r1467) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 8) Nonrational.InducedTerminalMatches.M045.r1467
    Nonrational.InducedTerminalMatches.M045.r1467_checked (by decide +kernel)
theorem record009_leaf_checked_9 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 9)
      (record009_certificates 9) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M045.r1468) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 9) Nonrational.InducedTerminalMatches.M045.r1468
    Nonrational.InducedTerminalMatches.M045.r1468_checked (by decide +kernel)
theorem record009_leaf_checked_10 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 10)
      (record009_certificates 10) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M045.r1469) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 10) Nonrational.InducedTerminalMatches.M045.r1469
    Nonrational.InducedTerminalMatches.M045.r1469_checked (by decide +kernel)
theorem record009_leaf_checked_11 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 11)
      (record009_certificates 11) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M045.r1470) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 11) Nonrational.InducedTerminalMatches.M045.r1470
    Nonrational.InducedTerminalMatches.M045.r1470_checked (by decide +kernel)
theorem record009_leaf_checked_12 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 12)
      (record009_certificates 12) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M045.r1471) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 12) Nonrational.InducedTerminalMatches.M045.r1471
    Nonrational.InducedTerminalMatches.M045.r1471_checked (by decide +kernel)
theorem record009_leaf_checked_13 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 13)
      (record009_certificates 13) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M046.r1472) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 13) Nonrational.InducedTerminalMatches.M046.r1472
    Nonrational.InducedTerminalMatches.M046.r1472_checked (by decide +kernel)
theorem record009_leaf_checked_14 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 14)
      (record009_certificates 14) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M046.r1473) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 14) Nonrational.InducedTerminalMatches.M046.r1473
    Nonrational.InducedTerminalMatches.M046.r1473_checked (by decide +kernel)
theorem record009_leaf_checked_15 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 15)
      (record009_certificates 15) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M046.r1474) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 15) Nonrational.InducedTerminalMatches.M046.r1474
    Nonrational.InducedTerminalMatches.M046.r1474_checked (by decide +kernel)
theorem record009_leaf_checked_16 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 16)
      (record009_certificates 16) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M046.r1475) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 16) Nonrational.InducedTerminalMatches.M046.r1475
    Nonrational.InducedTerminalMatches.M046.r1475_checked (by decide +kernel)
theorem record009_leaf_checked_17 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 17)
      (record009_certificates 17) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M046.r1476) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 17) Nonrational.InducedTerminalMatches.M046.r1476
    Nonrational.InducedTerminalMatches.M046.r1476_checked (by decide +kernel)
theorem record009_leaf_checked_18 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 18)
      (record009_certificates 18) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M046.r1477) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 18) Nonrational.InducedTerminalMatches.M046.r1477
    Nonrational.InducedTerminalMatches.M046.r1477_checked (by decide +kernel)
theorem record009_leaf_checked_19 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 19)
      (record009_certificates 19) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M046.r1478) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 19) Nonrational.InducedTerminalMatches.M046.r1478
    Nonrational.InducedTerminalMatches.M046.r1478_checked (by decide +kernel)
theorem record009_leaf_checked_20 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 20)
      (record009_certificates 20) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M046.r1479) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 20) Nonrational.InducedTerminalMatches.M046.r1479
    Nonrational.InducedTerminalMatches.M046.r1479_checked (by decide +kernel)
theorem record009_leaf_checked_21 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 21)
      (record009_certificates 21) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M046.r1480) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 21) Nonrational.InducedTerminalMatches.M046.r1480
    Nonrational.InducedTerminalMatches.M046.r1480_checked (by decide +kernel)
theorem record009_leaf_checked_22 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 22)
      (record009_certificates 22) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M046.r1481) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 22) Nonrational.InducedTerminalMatches.M046.r1481
    Nonrational.InducedTerminalMatches.M046.r1481_checked (by decide +kernel)
theorem record009_leaf_checked_23 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 23)
      (record009_certificates 23) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M046.r1482) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 23) Nonrational.InducedTerminalMatches.M046.r1482
    Nonrational.InducedTerminalMatches.M046.r1482_checked (by decide +kernel)
theorem record009_leaf_checked_24 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 24)
      (record009_certificates 24) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M046.r1483) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 24) Nonrational.InducedTerminalMatches.M046.r1483
    Nonrational.InducedTerminalMatches.M046.r1483_checked (by decide +kernel)
theorem record009_leaf_checked_25 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 25)
      (record009_certificates 25) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M046.r1484) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 25) Nonrational.InducedTerminalMatches.M046.r1484
    Nonrational.InducedTerminalMatches.M046.r1484_checked (by decide +kernel)
theorem record009_leaf_checked_26 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 26)
      (record009_certificates 26) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M046.r1485) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 26) Nonrational.InducedTerminalMatches.M046.r1485
    Nonrational.InducedTerminalMatches.M046.r1485_checked (by decide +kernel)
theorem record009_leaf_checked_27 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 27)
      (record009_certificates 27) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M046.r1486) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 27) Nonrational.InducedTerminalMatches.M046.r1486
    Nonrational.InducedTerminalMatches.M046.r1486_checked (by decide +kernel)
theorem record009_leaf_checked_28 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 28)
      (record009_certificates 28) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M046.r1487) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 28) Nonrational.InducedTerminalMatches.M046.r1487
    Nonrational.InducedTerminalMatches.M046.r1487_checked (by decide +kernel)
theorem record009_leaf_checked_29 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 29)
      (record009_certificates 29) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M046.r1488) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 29) Nonrational.InducedTerminalMatches.M046.r1488
    Nonrational.InducedTerminalMatches.M046.r1488_checked (by decide +kernel)
theorem record009_leaf_certificates_checked : ∀ j : Fin record009.l,
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves j)
      (record009_certificates j) = true :=
  (Fin.cases record009_leaf_checked_0 (Fin.cases record009_leaf_checked_1 (Fin.cases record009_leaf_checked_2 (Fin.cases record009_leaf_checked_3 (Fin.cases record009_leaf_checked_4 (Fin.cases record009_leaf_checked_5 (Fin.cases record009_leaf_checked_6 (Fin.cases record009_leaf_checked_7 (Fin.cases record009_leaf_checked_8 (Fin.cases record009_leaf_checked_9 (Fin.cases record009_leaf_checked_10 (Fin.cases record009_leaf_checked_11 (Fin.cases record009_leaf_checked_12 (Fin.cases record009_leaf_checked_13 (Fin.cases record009_leaf_checked_14 (Fin.cases record009_leaf_checked_15 (Fin.cases record009_leaf_checked_16 (Fin.cases record009_leaf_checked_17 (Fin.cases record009_leaf_checked_18 (Fin.cases record009_leaf_checked_19 (Fin.cases record009_leaf_checked_20 (Fin.cases record009_leaf_checked_21 (Fin.cases record009_leaf_checked_22 (Fin.cases record009_leaf_checked_23 (Fin.cases record009_leaf_checked_24 (Fin.cases record009_leaf_checked_25 (Fin.cases record009_leaf_checked_26 (Fin.cases record009_leaf_checked_27 (Fin.cases record009_leaf_checked_28 (Fin.cases record009_leaf_checked_29 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084
