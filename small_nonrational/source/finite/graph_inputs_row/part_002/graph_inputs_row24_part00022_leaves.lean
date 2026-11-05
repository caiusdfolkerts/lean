module
prelude
public import GraphInputsRow24Part00022Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M008
public import InducedTerminalMatches.M009

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022
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

noncomputable def record011_rawLeaves (j : Fin record011.l) : List Cell :=
  (record011.leaf j).map record011.data.cells
theorem record011_raw_exact (j : Fin record011.l) :
    (record011.leaf j).map record011.data.cells = record011_rawLeaves j := rfl
noncomputable def record011_certificateTable : Table Certificate :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0260))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0261)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0262))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0263))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0264))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0265)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0266))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0267))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0268))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0269))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0270)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0271))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0272))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0273)))))
 (.branch 16
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0274))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0275)))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0276))
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0277))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0278)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0279))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0280)))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0281))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0282))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0283)))))
 (.branch 26
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0284))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0285)))
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0286))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0287))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0288))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0289))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0290)))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0291))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0292))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0293)))))
 (.branch 36
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0294))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0295)))
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0296))
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0297))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M009.r0298))))))))
noncomputable def record011_certificates (j : Fin record011.l) : Certificate :=
  record011_certificateTable.get j.val
theorem record011_leaf_checked_0 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 0)
      (record011_certificates 0) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M008.r0260) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 0) Nonrational.InducedTerminalMatches.M008.r0260
    Nonrational.InducedTerminalMatches.M008.r0260_checked (by decide +kernel)
theorem record011_leaf_checked_1 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 1)
      (record011_certificates 1) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M008.r0261) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 1) Nonrational.InducedTerminalMatches.M008.r0261
    Nonrational.InducedTerminalMatches.M008.r0261_checked (by decide +kernel)
theorem record011_leaf_checked_2 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 2)
      (record011_certificates 2) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M008.r0262) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 2) Nonrational.InducedTerminalMatches.M008.r0262
    Nonrational.InducedTerminalMatches.M008.r0262_checked (by decide +kernel)
theorem record011_leaf_checked_3 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 3)
      (record011_certificates 3) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M008.r0263) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 3) Nonrational.InducedTerminalMatches.M008.r0263
    Nonrational.InducedTerminalMatches.M008.r0263_checked (by decide +kernel)
theorem record011_leaf_checked_4 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 4)
      (record011_certificates 4) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M008.r0264) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 4) Nonrational.InducedTerminalMatches.M008.r0264
    Nonrational.InducedTerminalMatches.M008.r0264_checked (by decide +kernel)
theorem record011_leaf_checked_5 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 5)
      (record011_certificates 5) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M008.r0265) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 5) Nonrational.InducedTerminalMatches.M008.r0265
    Nonrational.InducedTerminalMatches.M008.r0265_checked (by decide +kernel)
theorem record011_leaf_checked_6 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 6)
      (record011_certificates 6) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M008.r0266) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 6) Nonrational.InducedTerminalMatches.M008.r0266
    Nonrational.InducedTerminalMatches.M008.r0266_checked (by decide +kernel)
theorem record011_leaf_checked_7 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 7)
      (record011_certificates 7) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M008.r0267) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 7) Nonrational.InducedTerminalMatches.M008.r0267
    Nonrational.InducedTerminalMatches.M008.r0267_checked (by decide +kernel)
theorem record011_leaf_checked_8 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 8)
      (record011_certificates 8) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M008.r0268) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 8) Nonrational.InducedTerminalMatches.M008.r0268
    Nonrational.InducedTerminalMatches.M008.r0268_checked (by decide +kernel)
theorem record011_leaf_checked_9 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 9)
      (record011_certificates 9) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M008.r0269) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 9) Nonrational.InducedTerminalMatches.M008.r0269
    Nonrational.InducedTerminalMatches.M008.r0269_checked (by decide +kernel)
theorem record011_leaf_checked_10 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 10)
      (record011_certificates 10) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M008.r0270) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 10) Nonrational.InducedTerminalMatches.M008.r0270
    Nonrational.InducedTerminalMatches.M008.r0270_checked (by decide +kernel)
theorem record011_leaf_checked_11 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 11)
      (record011_certificates 11) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M008.r0271) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 11) Nonrational.InducedTerminalMatches.M008.r0271
    Nonrational.InducedTerminalMatches.M008.r0271_checked (by decide +kernel)
theorem record011_leaf_checked_12 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 12)
      (record011_certificates 12) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M008.r0272) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 12) Nonrational.InducedTerminalMatches.M008.r0272
    Nonrational.InducedTerminalMatches.M008.r0272_checked (by decide +kernel)
theorem record011_leaf_checked_13 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 13)
      (record011_certificates 13) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M008.r0273) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 13) Nonrational.InducedTerminalMatches.M008.r0273
    Nonrational.InducedTerminalMatches.M008.r0273_checked (by decide +kernel)
theorem record011_leaf_checked_14 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 14)
      (record011_certificates 14) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M008.r0274) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 14) Nonrational.InducedTerminalMatches.M008.r0274
    Nonrational.InducedTerminalMatches.M008.r0274_checked (by decide +kernel)
theorem record011_leaf_checked_15 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 15)
      (record011_certificates 15) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M008.r0275) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 15) Nonrational.InducedTerminalMatches.M008.r0275
    Nonrational.InducedTerminalMatches.M008.r0275_checked (by decide +kernel)
theorem record011_leaf_checked_16 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 16)
      (record011_certificates 16) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M008.r0276) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 16) Nonrational.InducedTerminalMatches.M008.r0276
    Nonrational.InducedTerminalMatches.M008.r0276_checked (by decide +kernel)
theorem record011_leaf_checked_17 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 17)
      (record011_certificates 17) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M008.r0277) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 17) Nonrational.InducedTerminalMatches.M008.r0277
    Nonrational.InducedTerminalMatches.M008.r0277_checked (by decide +kernel)
theorem record011_leaf_checked_18 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 18)
      (record011_certificates 18) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M008.r0278) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 18) Nonrational.InducedTerminalMatches.M008.r0278
    Nonrational.InducedTerminalMatches.M008.r0278_checked (by decide +kernel)
theorem record011_leaf_checked_19 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 19)
      (record011_certificates 19) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M008.r0279) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 19) Nonrational.InducedTerminalMatches.M008.r0279
    Nonrational.InducedTerminalMatches.M008.r0279_checked (by decide +kernel)
theorem record011_leaf_checked_20 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 20)
      (record011_certificates 20) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M008.r0280) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 20) Nonrational.InducedTerminalMatches.M008.r0280
    Nonrational.InducedTerminalMatches.M008.r0280_checked (by decide +kernel)
theorem record011_leaf_checked_21 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 21)
      (record011_certificates 21) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M008.r0281) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 21) Nonrational.InducedTerminalMatches.M008.r0281
    Nonrational.InducedTerminalMatches.M008.r0281_checked (by decide +kernel)
theorem record011_leaf_checked_22 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 22)
      (record011_certificates 22) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M008.r0282) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 22) Nonrational.InducedTerminalMatches.M008.r0282
    Nonrational.InducedTerminalMatches.M008.r0282_checked (by decide +kernel)
theorem record011_leaf_checked_23 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 23)
      (record011_certificates 23) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M008.r0283) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 23) Nonrational.InducedTerminalMatches.M008.r0283
    Nonrational.InducedTerminalMatches.M008.r0283_checked (by decide +kernel)
theorem record011_leaf_checked_24 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 24)
      (record011_certificates 24) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M008.r0284) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 24) Nonrational.InducedTerminalMatches.M008.r0284
    Nonrational.InducedTerminalMatches.M008.r0284_checked (by decide +kernel)
theorem record011_leaf_checked_25 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 25)
      (record011_certificates 25) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M008.r0285) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 25) Nonrational.InducedTerminalMatches.M008.r0285
    Nonrational.InducedTerminalMatches.M008.r0285_checked (by decide +kernel)
theorem record011_leaf_checked_26 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 26)
      (record011_certificates 26) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M008.r0286) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 26) Nonrational.InducedTerminalMatches.M008.r0286
    Nonrational.InducedTerminalMatches.M008.r0286_checked (by decide +kernel)
theorem record011_leaf_checked_27 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 27)
      (record011_certificates 27) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M008.r0287) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 27) Nonrational.InducedTerminalMatches.M008.r0287
    Nonrational.InducedTerminalMatches.M008.r0287_checked (by decide +kernel)
theorem record011_leaf_checked_28 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 28)
      (record011_certificates 28) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M009.r0288) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 28) Nonrational.InducedTerminalMatches.M009.r0288
    Nonrational.InducedTerminalMatches.M009.r0288_checked (by decide +kernel)
theorem record011_leaf_checked_29 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 29)
      (record011_certificates 29) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M009.r0289) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 29) Nonrational.InducedTerminalMatches.M009.r0289
    Nonrational.InducedTerminalMatches.M009.r0289_checked (by decide +kernel)
theorem record011_leaf_checked_30 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 30)
      (record011_certificates 30) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M009.r0290) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 30) Nonrational.InducedTerminalMatches.M009.r0290
    Nonrational.InducedTerminalMatches.M009.r0290_checked (by decide +kernel)
theorem record011_leaf_checked_31 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 31)
      (record011_certificates 31) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M009.r0291) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 31) Nonrational.InducedTerminalMatches.M009.r0291
    Nonrational.InducedTerminalMatches.M009.r0291_checked (by decide +kernel)
theorem record011_leaf_checked_32 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 32)
      (record011_certificates 32) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M009.r0292) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 32) Nonrational.InducedTerminalMatches.M009.r0292
    Nonrational.InducedTerminalMatches.M009.r0292_checked (by decide +kernel)
theorem record011_leaf_checked_33 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 33)
      (record011_certificates 33) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M009.r0293) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 33) Nonrational.InducedTerminalMatches.M009.r0293
    Nonrational.InducedTerminalMatches.M009.r0293_checked (by decide +kernel)
theorem record011_leaf_checked_34 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 34)
      (record011_certificates 34) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M009.r0294) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 34) Nonrational.InducedTerminalMatches.M009.r0294
    Nonrational.InducedTerminalMatches.M009.r0294_checked (by decide +kernel)
theorem record011_leaf_checked_35 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 35)
      (record011_certificates 35) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M009.r0295) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 35) Nonrational.InducedTerminalMatches.M009.r0295
    Nonrational.InducedTerminalMatches.M009.r0295_checked (by decide +kernel)
theorem record011_leaf_checked_36 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 36)
      (record011_certificates 36) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M009.r0296) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 36) Nonrational.InducedTerminalMatches.M009.r0296
    Nonrational.InducedTerminalMatches.M009.r0296_checked (by decide +kernel)
theorem record011_leaf_checked_37 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 37)
      (record011_certificates 37) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M009.r0297) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 37) Nonrational.InducedTerminalMatches.M009.r0297
    Nonrational.InducedTerminalMatches.M009.r0297_checked (by decide +kernel)
theorem record011_leaf_checked_38 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 38)
      (record011_certificates 38) = true := by
  change RawLeafCertificate.check record011.data.quota (record011_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M009.r0298) = true
  exact matching_checked record011.data.quota (record011_rawLeaves 38) Nonrational.InducedTerminalMatches.M009.r0298
    Nonrational.InducedTerminalMatches.M009.r0298_checked (by decide +kernel)
theorem record011_leaf_certificates_checked : ∀ j : Fin record011.l,
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves j)
      (record011_certificates j) = true :=
  (Fin.cases record011_leaf_checked_0 (Fin.cases record011_leaf_checked_1 (Fin.cases record011_leaf_checked_2 (Fin.cases record011_leaf_checked_3 (Fin.cases record011_leaf_checked_4 (Fin.cases record011_leaf_checked_5 (Fin.cases record011_leaf_checked_6 (Fin.cases record011_leaf_checked_7 (Fin.cases record011_leaf_checked_8 (Fin.cases record011_leaf_checked_9 (Fin.cases record011_leaf_checked_10 (Fin.cases record011_leaf_checked_11 (Fin.cases record011_leaf_checked_12 (Fin.cases record011_leaf_checked_13 (Fin.cases record011_leaf_checked_14 (Fin.cases record011_leaf_checked_15 (Fin.cases record011_leaf_checked_16 (Fin.cases record011_leaf_checked_17 (Fin.cases record011_leaf_checked_18 (Fin.cases record011_leaf_checked_19 (Fin.cases record011_leaf_checked_20 (Fin.cases record011_leaf_checked_21 (Fin.cases record011_leaf_checked_22 (Fin.cases record011_leaf_checked_23 (Fin.cases record011_leaf_checked_24 (Fin.cases record011_leaf_checked_25 (Fin.cases record011_leaf_checked_26 (Fin.cases record011_leaf_checked_27 (Fin.cases record011_leaf_checked_28 (Fin.cases record011_leaf_checked_29 (Fin.cases record011_leaf_checked_30 (Fin.cases record011_leaf_checked_31 (Fin.cases record011_leaf_checked_32 (Fin.cases record011_leaf_checked_33 (Fin.cases record011_leaf_checked_34 (Fin.cases record011_leaf_checked_35 (Fin.cases record011_leaf_checked_36 (Fin.cases record011_leaf_checked_37 (Fin.cases record011_leaf_checked_38 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))
#print axioms record011_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022
