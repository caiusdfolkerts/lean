module
prelude
public import GraphInputsRow24Part00114Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M021
public import InducedTerminalMatches.M022
public import InducedTerminalMatches.M023

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114
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
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0678))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0679)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0680))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0681))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0682))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0683)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0684))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0685)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0686))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0687)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0688))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0689))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0690))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0691)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0692))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0693))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0694)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0695))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0696)))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0697))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0698))))
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0699))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0700)))
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0701))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0702)))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M021.r0703))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0704)))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0705))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0706))))
 (.branch 31
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0707))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0708)))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0709))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0710))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0711))))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0712))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0713)))
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0714))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0715))))
 (.branch 40
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0716))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0717)))
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0718))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0719)))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0720))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0721)))
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0722))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0723))))
 (.branch 48
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0724))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0725)))
 (.branch 49
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0726))
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0727))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0728)))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0729))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0730)))
 (.branch 54
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0731))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0732))))
 (.branch 57
 (.branch 56
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0733))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0734)))
 (.branch 58
 (.leaf (.matching Nonrational.InducedTerminalMatches.M022.r0735))
 (.branch 59
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0736))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0737))))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0738))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0739)))
 (.branch 63
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0740))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0741))))
 (.branch 66
 (.branch 65
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0742))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0743)))
 (.branch 67
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0744))
 (.branch 68
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0745))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M023.r0746)))))))))
noncomputable def record009_certificates (j : Fin record009.l) : Certificate :=
  record009_certificateTable.get j.val
theorem record009_leaf_checked_0 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 0)
      (record009_certificates 0) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M021.r0678) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 0) Nonrational.InducedTerminalMatches.M021.r0678
    Nonrational.InducedTerminalMatches.M021.r0678_checked (by decide +kernel)
theorem record009_leaf_checked_1 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 1)
      (record009_certificates 1) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M021.r0679) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 1) Nonrational.InducedTerminalMatches.M021.r0679
    Nonrational.InducedTerminalMatches.M021.r0679_checked (by decide +kernel)
theorem record009_leaf_checked_2 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 2)
      (record009_certificates 2) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M021.r0680) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 2) Nonrational.InducedTerminalMatches.M021.r0680
    Nonrational.InducedTerminalMatches.M021.r0680_checked (by decide +kernel)
theorem record009_leaf_checked_3 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 3)
      (record009_certificates 3) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M021.r0681) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 3) Nonrational.InducedTerminalMatches.M021.r0681
    Nonrational.InducedTerminalMatches.M021.r0681_checked (by decide +kernel)
theorem record009_leaf_checked_4 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 4)
      (record009_certificates 4) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M021.r0682) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 4) Nonrational.InducedTerminalMatches.M021.r0682
    Nonrational.InducedTerminalMatches.M021.r0682_checked (by decide +kernel)
theorem record009_leaf_checked_5 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 5)
      (record009_certificates 5) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M021.r0683) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 5) Nonrational.InducedTerminalMatches.M021.r0683
    Nonrational.InducedTerminalMatches.M021.r0683_checked (by decide +kernel)
theorem record009_leaf_checked_6 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 6)
      (record009_certificates 6) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M021.r0684) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 6) Nonrational.InducedTerminalMatches.M021.r0684
    Nonrational.InducedTerminalMatches.M021.r0684_checked (by decide +kernel)
theorem record009_leaf_checked_7 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 7)
      (record009_certificates 7) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M021.r0685) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 7) Nonrational.InducedTerminalMatches.M021.r0685
    Nonrational.InducedTerminalMatches.M021.r0685_checked (by decide +kernel)
theorem record009_leaf_checked_8 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 8)
      (record009_certificates 8) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M021.r0686) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 8) Nonrational.InducedTerminalMatches.M021.r0686
    Nonrational.InducedTerminalMatches.M021.r0686_checked (by decide +kernel)
theorem record009_leaf_checked_9 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 9)
      (record009_certificates 9) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M021.r0687) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 9) Nonrational.InducedTerminalMatches.M021.r0687
    Nonrational.InducedTerminalMatches.M021.r0687_checked (by decide +kernel)
theorem record009_leaf_checked_10 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 10)
      (record009_certificates 10) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M021.r0688) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 10) Nonrational.InducedTerminalMatches.M021.r0688
    Nonrational.InducedTerminalMatches.M021.r0688_checked (by decide +kernel)
theorem record009_leaf_checked_11 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 11)
      (record009_certificates 11) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M021.r0689) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 11) Nonrational.InducedTerminalMatches.M021.r0689
    Nonrational.InducedTerminalMatches.M021.r0689_checked (by decide +kernel)
theorem record009_leaf_checked_12 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 12)
      (record009_certificates 12) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M021.r0690) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 12) Nonrational.InducedTerminalMatches.M021.r0690
    Nonrational.InducedTerminalMatches.M021.r0690_checked (by decide +kernel)
theorem record009_leaf_checked_13 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 13)
      (record009_certificates 13) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M021.r0691) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 13) Nonrational.InducedTerminalMatches.M021.r0691
    Nonrational.InducedTerminalMatches.M021.r0691_checked (by decide +kernel)
theorem record009_leaf_checked_14 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 14)
      (record009_certificates 14) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M021.r0692) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 14) Nonrational.InducedTerminalMatches.M021.r0692
    Nonrational.InducedTerminalMatches.M021.r0692_checked (by decide +kernel)
theorem record009_leaf_checked_15 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 15)
      (record009_certificates 15) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M021.r0693) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 15) Nonrational.InducedTerminalMatches.M021.r0693
    Nonrational.InducedTerminalMatches.M021.r0693_checked (by decide +kernel)
theorem record009_leaf_checked_16 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 16)
      (record009_certificates 16) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M021.r0694) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 16) Nonrational.InducedTerminalMatches.M021.r0694
    Nonrational.InducedTerminalMatches.M021.r0694_checked (by decide +kernel)
theorem record009_leaf_checked_17 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 17)
      (record009_certificates 17) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M021.r0695) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 17) Nonrational.InducedTerminalMatches.M021.r0695
    Nonrational.InducedTerminalMatches.M021.r0695_checked (by decide +kernel)
theorem record009_leaf_checked_18 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 18)
      (record009_certificates 18) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M021.r0696) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 18) Nonrational.InducedTerminalMatches.M021.r0696
    Nonrational.InducedTerminalMatches.M021.r0696_checked (by decide +kernel)
theorem record009_leaf_checked_19 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 19)
      (record009_certificates 19) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M021.r0697) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 19) Nonrational.InducedTerminalMatches.M021.r0697
    Nonrational.InducedTerminalMatches.M021.r0697_checked (by decide +kernel)
theorem record009_leaf_checked_20 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 20)
      (record009_certificates 20) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M021.r0698) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 20) Nonrational.InducedTerminalMatches.M021.r0698
    Nonrational.InducedTerminalMatches.M021.r0698_checked (by decide +kernel)
theorem record009_leaf_checked_21 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 21)
      (record009_certificates 21) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M021.r0699) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 21) Nonrational.InducedTerminalMatches.M021.r0699
    Nonrational.InducedTerminalMatches.M021.r0699_checked (by decide +kernel)
theorem record009_leaf_checked_22 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 22)
      (record009_certificates 22) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M021.r0700) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 22) Nonrational.InducedTerminalMatches.M021.r0700
    Nonrational.InducedTerminalMatches.M021.r0700_checked (by decide +kernel)
theorem record009_leaf_checked_23 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 23)
      (record009_certificates 23) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M021.r0701) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 23) Nonrational.InducedTerminalMatches.M021.r0701
    Nonrational.InducedTerminalMatches.M021.r0701_checked (by decide +kernel)
theorem record009_leaf_checked_24 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 24)
      (record009_certificates 24) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M021.r0702) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 24) Nonrational.InducedTerminalMatches.M021.r0702
    Nonrational.InducedTerminalMatches.M021.r0702_checked (by decide +kernel)
theorem record009_leaf_checked_25 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 25)
      (record009_certificates 25) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M021.r0703) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 25) Nonrational.InducedTerminalMatches.M021.r0703
    Nonrational.InducedTerminalMatches.M021.r0703_checked (by decide +kernel)
theorem record009_leaf_checked_26 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 26)
      (record009_certificates 26) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M022.r0704) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 26) Nonrational.InducedTerminalMatches.M022.r0704
    Nonrational.InducedTerminalMatches.M022.r0704_checked (by decide +kernel)
theorem record009_leaf_checked_27 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 27)
      (record009_certificates 27) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M022.r0705) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 27) Nonrational.InducedTerminalMatches.M022.r0705
    Nonrational.InducedTerminalMatches.M022.r0705_checked (by decide +kernel)
theorem record009_leaf_checked_28 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 28)
      (record009_certificates 28) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M022.r0706) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 28) Nonrational.InducedTerminalMatches.M022.r0706
    Nonrational.InducedTerminalMatches.M022.r0706_checked (by decide +kernel)
theorem record009_leaf_checked_29 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 29)
      (record009_certificates 29) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M022.r0707) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 29) Nonrational.InducedTerminalMatches.M022.r0707
    Nonrational.InducedTerminalMatches.M022.r0707_checked (by decide +kernel)
theorem record009_leaf_checked_30 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 30)
      (record009_certificates 30) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M022.r0708) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 30) Nonrational.InducedTerminalMatches.M022.r0708
    Nonrational.InducedTerminalMatches.M022.r0708_checked (by decide +kernel)
theorem record009_leaf_checked_31 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 31)
      (record009_certificates 31) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M022.r0709) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 31) Nonrational.InducedTerminalMatches.M022.r0709
    Nonrational.InducedTerminalMatches.M022.r0709_checked (by decide +kernel)
theorem record009_leaf_checked_32 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 32)
      (record009_certificates 32) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M022.r0710) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 32) Nonrational.InducedTerminalMatches.M022.r0710
    Nonrational.InducedTerminalMatches.M022.r0710_checked (by decide +kernel)
theorem record009_leaf_checked_33 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 33)
      (record009_certificates 33) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M022.r0711) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 33) Nonrational.InducedTerminalMatches.M022.r0711
    Nonrational.InducedTerminalMatches.M022.r0711_checked (by decide +kernel)
theorem record009_leaf_checked_34 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 34)
      (record009_certificates 34) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M022.r0712) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 34) Nonrational.InducedTerminalMatches.M022.r0712
    Nonrational.InducedTerminalMatches.M022.r0712_checked (by decide +kernel)
theorem record009_leaf_checked_35 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 35)
      (record009_certificates 35) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M022.r0713) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 35) Nonrational.InducedTerminalMatches.M022.r0713
    Nonrational.InducedTerminalMatches.M022.r0713_checked (by decide +kernel)
theorem record009_leaf_checked_36 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 36)
      (record009_certificates 36) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M022.r0714) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 36) Nonrational.InducedTerminalMatches.M022.r0714
    Nonrational.InducedTerminalMatches.M022.r0714_checked (by decide +kernel)
theorem record009_leaf_checked_37 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 37)
      (record009_certificates 37) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M022.r0715) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 37) Nonrational.InducedTerminalMatches.M022.r0715
    Nonrational.InducedTerminalMatches.M022.r0715_checked (by decide +kernel)
theorem record009_leaf_checked_38 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 38)
      (record009_certificates 38) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M022.r0716) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 38) Nonrational.InducedTerminalMatches.M022.r0716
    Nonrational.InducedTerminalMatches.M022.r0716_checked (by decide +kernel)
theorem record009_leaf_checked_39 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 39)
      (record009_certificates 39) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M022.r0717) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 39) Nonrational.InducedTerminalMatches.M022.r0717
    Nonrational.InducedTerminalMatches.M022.r0717_checked (by decide +kernel)
theorem record009_leaf_checked_40 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 40)
      (record009_certificates 40) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M022.r0718) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 40) Nonrational.InducedTerminalMatches.M022.r0718
    Nonrational.InducedTerminalMatches.M022.r0718_checked (by decide +kernel)
theorem record009_leaf_checked_41 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 41)
      (record009_certificates 41) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M022.r0719) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 41) Nonrational.InducedTerminalMatches.M022.r0719
    Nonrational.InducedTerminalMatches.M022.r0719_checked (by decide +kernel)
theorem record009_leaf_checked_42 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 42)
      (record009_certificates 42) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M022.r0720) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 42) Nonrational.InducedTerminalMatches.M022.r0720
    Nonrational.InducedTerminalMatches.M022.r0720_checked (by decide +kernel)
theorem record009_leaf_checked_43 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 43)
      (record009_certificates 43) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M022.r0721) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 43) Nonrational.InducedTerminalMatches.M022.r0721
    Nonrational.InducedTerminalMatches.M022.r0721_checked (by decide +kernel)
theorem record009_leaf_checked_44 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 44)
      (record009_certificates 44) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M022.r0722) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 44) Nonrational.InducedTerminalMatches.M022.r0722
    Nonrational.InducedTerminalMatches.M022.r0722_checked (by decide +kernel)
theorem record009_leaf_checked_45 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 45)
      (record009_certificates 45) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M022.r0723) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 45) Nonrational.InducedTerminalMatches.M022.r0723
    Nonrational.InducedTerminalMatches.M022.r0723_checked (by decide +kernel)
theorem record009_leaf_checked_46 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 46)
      (record009_certificates 46) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M022.r0724) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 46) Nonrational.InducedTerminalMatches.M022.r0724
    Nonrational.InducedTerminalMatches.M022.r0724_checked (by decide +kernel)
theorem record009_leaf_checked_47 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 47)
      (record009_certificates 47) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M022.r0725) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 47) Nonrational.InducedTerminalMatches.M022.r0725
    Nonrational.InducedTerminalMatches.M022.r0725_checked (by decide +kernel)
theorem record009_leaf_checked_48 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 48)
      (record009_certificates 48) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M022.r0726) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 48) Nonrational.InducedTerminalMatches.M022.r0726
    Nonrational.InducedTerminalMatches.M022.r0726_checked (by decide +kernel)
theorem record009_leaf_checked_49 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 49)
      (record009_certificates 49) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M022.r0727) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 49) Nonrational.InducedTerminalMatches.M022.r0727
    Nonrational.InducedTerminalMatches.M022.r0727_checked (by decide +kernel)
theorem record009_leaf_checked_50 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 50)
      (record009_certificates 50) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M022.r0728) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 50) Nonrational.InducedTerminalMatches.M022.r0728
    Nonrational.InducedTerminalMatches.M022.r0728_checked (by decide +kernel)
theorem record009_leaf_checked_51 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 51)
      (record009_certificates 51) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M022.r0729) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 51) Nonrational.InducedTerminalMatches.M022.r0729
    Nonrational.InducedTerminalMatches.M022.r0729_checked (by decide +kernel)
theorem record009_leaf_checked_52 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 52)
      (record009_certificates 52) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M022.r0730) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 52) Nonrational.InducedTerminalMatches.M022.r0730
    Nonrational.InducedTerminalMatches.M022.r0730_checked (by decide +kernel)
theorem record009_leaf_checked_53 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 53)
      (record009_certificates 53) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M022.r0731) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 53) Nonrational.InducedTerminalMatches.M022.r0731
    Nonrational.InducedTerminalMatches.M022.r0731_checked (by decide +kernel)
theorem record009_leaf_checked_54 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 54)
      (record009_certificates 54) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 54)
    (.matching Nonrational.InducedTerminalMatches.M022.r0732) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 54) Nonrational.InducedTerminalMatches.M022.r0732
    Nonrational.InducedTerminalMatches.M022.r0732_checked (by decide +kernel)
theorem record009_leaf_checked_55 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 55)
      (record009_certificates 55) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 55)
    (.matching Nonrational.InducedTerminalMatches.M022.r0733) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 55) Nonrational.InducedTerminalMatches.M022.r0733
    Nonrational.InducedTerminalMatches.M022.r0733_checked (by decide +kernel)
theorem record009_leaf_checked_56 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 56)
      (record009_certificates 56) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 56)
    (.matching Nonrational.InducedTerminalMatches.M022.r0734) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 56) Nonrational.InducedTerminalMatches.M022.r0734
    Nonrational.InducedTerminalMatches.M022.r0734_checked (by decide +kernel)
theorem record009_leaf_checked_57 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 57)
      (record009_certificates 57) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 57)
    (.matching Nonrational.InducedTerminalMatches.M022.r0735) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 57) Nonrational.InducedTerminalMatches.M022.r0735
    Nonrational.InducedTerminalMatches.M022.r0735_checked (by decide +kernel)
theorem record009_leaf_checked_58 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 58)
      (record009_certificates 58) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 58)
    (.matching Nonrational.InducedTerminalMatches.M023.r0736) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 58) Nonrational.InducedTerminalMatches.M023.r0736
    Nonrational.InducedTerminalMatches.M023.r0736_checked (by decide +kernel)
theorem record009_leaf_checked_59 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 59)
      (record009_certificates 59) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 59)
    (.matching Nonrational.InducedTerminalMatches.M023.r0737) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 59) Nonrational.InducedTerminalMatches.M023.r0737
    Nonrational.InducedTerminalMatches.M023.r0737_checked (by decide +kernel)
theorem record009_leaf_checked_60 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 60)
      (record009_certificates 60) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 60)
    (.matching Nonrational.InducedTerminalMatches.M023.r0738) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 60) Nonrational.InducedTerminalMatches.M023.r0738
    Nonrational.InducedTerminalMatches.M023.r0738_checked (by decide +kernel)
theorem record009_leaf_checked_61 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 61)
      (record009_certificates 61) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 61)
    (.matching Nonrational.InducedTerminalMatches.M023.r0739) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 61) Nonrational.InducedTerminalMatches.M023.r0739
    Nonrational.InducedTerminalMatches.M023.r0739_checked (by decide +kernel)
theorem record009_leaf_checked_62 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 62)
      (record009_certificates 62) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 62)
    (.matching Nonrational.InducedTerminalMatches.M023.r0740) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 62) Nonrational.InducedTerminalMatches.M023.r0740
    Nonrational.InducedTerminalMatches.M023.r0740_checked (by decide +kernel)
theorem record009_leaf_checked_63 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 63)
      (record009_certificates 63) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 63)
    (.matching Nonrational.InducedTerminalMatches.M023.r0741) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 63) Nonrational.InducedTerminalMatches.M023.r0741
    Nonrational.InducedTerminalMatches.M023.r0741_checked (by decide +kernel)
theorem record009_leaf_checked_64 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 64)
      (record009_certificates 64) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 64)
    (.matching Nonrational.InducedTerminalMatches.M023.r0742) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 64) Nonrational.InducedTerminalMatches.M023.r0742
    Nonrational.InducedTerminalMatches.M023.r0742_checked (by decide +kernel)
theorem record009_leaf_checked_65 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 65)
      (record009_certificates 65) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 65)
    (.matching Nonrational.InducedTerminalMatches.M023.r0743) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 65) Nonrational.InducedTerminalMatches.M023.r0743
    Nonrational.InducedTerminalMatches.M023.r0743_checked (by decide +kernel)
theorem record009_leaf_checked_66 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 66)
      (record009_certificates 66) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 66)
    (.matching Nonrational.InducedTerminalMatches.M023.r0744) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 66) Nonrational.InducedTerminalMatches.M023.r0744
    Nonrational.InducedTerminalMatches.M023.r0744_checked (by decide +kernel)
theorem record009_leaf_checked_67 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 67)
      (record009_certificates 67) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 67)
    (.matching Nonrational.InducedTerminalMatches.M023.r0745) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 67) Nonrational.InducedTerminalMatches.M023.r0745
    Nonrational.InducedTerminalMatches.M023.r0745_checked (by decide +kernel)
theorem record009_leaf_checked_68 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 68)
      (record009_certificates 68) = true := by
  change RawLeafCertificate.check record009.data.quota (record009_rawLeaves 68)
    (.matching Nonrational.InducedTerminalMatches.M023.r0746) = true
  exact matching_checked record009.data.quota (record009_rawLeaves 68) Nonrational.InducedTerminalMatches.M023.r0746
    Nonrational.InducedTerminalMatches.M023.r0746_checked (by decide +kernel)
theorem record009_leaf_certificates_checked : ∀ j : Fin record009.l,
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves j)
      (record009_certificates j) = true :=
  (Fin.cases record009_leaf_checked_0 (Fin.cases record009_leaf_checked_1 (Fin.cases record009_leaf_checked_2 (Fin.cases record009_leaf_checked_3 (Fin.cases record009_leaf_checked_4 (Fin.cases record009_leaf_checked_5 (Fin.cases record009_leaf_checked_6 (Fin.cases record009_leaf_checked_7 (Fin.cases record009_leaf_checked_8 (Fin.cases record009_leaf_checked_9 (Fin.cases record009_leaf_checked_10 (Fin.cases record009_leaf_checked_11 (Fin.cases record009_leaf_checked_12 (Fin.cases record009_leaf_checked_13 (Fin.cases record009_leaf_checked_14 (Fin.cases record009_leaf_checked_15 (Fin.cases record009_leaf_checked_16 (Fin.cases record009_leaf_checked_17 (Fin.cases record009_leaf_checked_18 (Fin.cases record009_leaf_checked_19 (Fin.cases record009_leaf_checked_20 (Fin.cases record009_leaf_checked_21 (Fin.cases record009_leaf_checked_22 (Fin.cases record009_leaf_checked_23 (Fin.cases record009_leaf_checked_24 (Fin.cases record009_leaf_checked_25 (Fin.cases record009_leaf_checked_26 (Fin.cases record009_leaf_checked_27 (Fin.cases record009_leaf_checked_28 (Fin.cases record009_leaf_checked_29 (Fin.cases record009_leaf_checked_30 (Fin.cases record009_leaf_checked_31 (Fin.cases record009_leaf_checked_32 (Fin.cases record009_leaf_checked_33 (Fin.cases record009_leaf_checked_34 (Fin.cases record009_leaf_checked_35 (Fin.cases record009_leaf_checked_36 (Fin.cases record009_leaf_checked_37 (Fin.cases record009_leaf_checked_38 (Fin.cases record009_leaf_checked_39 (Fin.cases record009_leaf_checked_40 (Fin.cases record009_leaf_checked_41 (Fin.cases record009_leaf_checked_42 (Fin.cases record009_leaf_checked_43 (Fin.cases record009_leaf_checked_44 (Fin.cases record009_leaf_checked_45 (Fin.cases record009_leaf_checked_46 (Fin.cases record009_leaf_checked_47 (Fin.cases record009_leaf_checked_48 (Fin.cases record009_leaf_checked_49 (Fin.cases record009_leaf_checked_50 (Fin.cases record009_leaf_checked_51 (Fin.cases record009_leaf_checked_52 (Fin.cases record009_leaf_checked_53 (Fin.cases record009_leaf_checked_54 (Fin.cases record009_leaf_checked_55 (Fin.cases record009_leaf_checked_56 (Fin.cases record009_leaf_checked_57 (Fin.cases record009_leaf_checked_58 (Fin.cases record009_leaf_checked_59 (Fin.cases record009_leaf_checked_60 (Fin.cases record009_leaf_checked_61 (Fin.cases record009_leaf_checked_62 (Fin.cases record009_leaf_checked_63 (Fin.cases record009_leaf_checked_64 (Fin.cases record009_leaf_checked_65 (Fin.cases record009_leaf_checked_66 (Fin.cases record009_leaf_checked_67 (Fin.cases record009_leaf_checked_68 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record009_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00114
