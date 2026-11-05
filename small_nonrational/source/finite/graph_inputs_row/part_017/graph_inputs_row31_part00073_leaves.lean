module
prelude
public import GraphInputsRow31Part00073Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M084
public import InducedTerminalMatches.M085

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2708))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2709))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2710))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2711))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2712))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2713)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2714))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2715))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2716))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2717))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2718))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2719))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2720))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2721))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2722))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2723))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2724))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2725)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2726))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2727))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2728))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2729))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2730))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2731)))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M084.r2708) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M084.r2708
    Nonrational.InducedTerminalMatches.M084.r2708_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M084.r2709) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M084.r2709
    Nonrational.InducedTerminalMatches.M084.r2709_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M084.r2710) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M084.r2710
    Nonrational.InducedTerminalMatches.M084.r2710_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M084.r2711) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M084.r2711
    Nonrational.InducedTerminalMatches.M084.r2711_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M084.r2712) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M084.r2712
    Nonrational.InducedTerminalMatches.M084.r2712_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M084.r2713) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M084.r2713
    Nonrational.InducedTerminalMatches.M084.r2713_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M084.r2714) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M084.r2714
    Nonrational.InducedTerminalMatches.M084.r2714_checked (by decide +kernel)
theorem record000_leaf_checked_7 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
      (record000_certificates 7) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M084.r2715) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 7) Nonrational.InducedTerminalMatches.M084.r2715
    Nonrational.InducedTerminalMatches.M084.r2715_checked (by decide +kernel)
theorem record000_leaf_checked_8 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
      (record000_certificates 8) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M084.r2716) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 8) Nonrational.InducedTerminalMatches.M084.r2716
    Nonrational.InducedTerminalMatches.M084.r2716_checked (by decide +kernel)
theorem record000_leaf_checked_9 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
      (record000_certificates 9) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M084.r2717) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 9) Nonrational.InducedTerminalMatches.M084.r2717
    Nonrational.InducedTerminalMatches.M084.r2717_checked (by decide +kernel)
theorem record000_leaf_checked_10 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
      (record000_certificates 10) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M084.r2718) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 10) Nonrational.InducedTerminalMatches.M084.r2718
    Nonrational.InducedTerminalMatches.M084.r2718_checked (by decide +kernel)
theorem record000_leaf_checked_11 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
      (record000_certificates 11) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M084.r2719) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 11) Nonrational.InducedTerminalMatches.M084.r2719
    Nonrational.InducedTerminalMatches.M084.r2719_checked (by decide +kernel)
theorem record000_leaf_checked_12 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
      (record000_certificates 12) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M085.r2720) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 12) Nonrational.InducedTerminalMatches.M085.r2720
    Nonrational.InducedTerminalMatches.M085.r2720_checked (by decide +kernel)
theorem record000_leaf_checked_13 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
      (record000_certificates 13) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M085.r2721) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 13) Nonrational.InducedTerminalMatches.M085.r2721
    Nonrational.InducedTerminalMatches.M085.r2721_checked (by decide +kernel)
theorem record000_leaf_checked_14 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
      (record000_certificates 14) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M085.r2722) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 14) Nonrational.InducedTerminalMatches.M085.r2722
    Nonrational.InducedTerminalMatches.M085.r2722_checked (by decide +kernel)
theorem record000_leaf_checked_15 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
      (record000_certificates 15) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M085.r2723) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 15) Nonrational.InducedTerminalMatches.M085.r2723
    Nonrational.InducedTerminalMatches.M085.r2723_checked (by decide +kernel)
theorem record000_leaf_checked_16 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
      (record000_certificates 16) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M085.r2724) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 16) Nonrational.InducedTerminalMatches.M085.r2724
    Nonrational.InducedTerminalMatches.M085.r2724_checked (by decide +kernel)
theorem record000_leaf_checked_17 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
      (record000_certificates 17) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M085.r2725) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 17) Nonrational.InducedTerminalMatches.M085.r2725
    Nonrational.InducedTerminalMatches.M085.r2725_checked (by decide +kernel)
theorem record000_leaf_checked_18 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
      (record000_certificates 18) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M085.r2726) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 18) Nonrational.InducedTerminalMatches.M085.r2726
    Nonrational.InducedTerminalMatches.M085.r2726_checked (by decide +kernel)
theorem record000_leaf_checked_19 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
      (record000_certificates 19) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M085.r2727) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 19) Nonrational.InducedTerminalMatches.M085.r2727
    Nonrational.InducedTerminalMatches.M085.r2727_checked (by decide +kernel)
theorem record000_leaf_checked_20 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
      (record000_certificates 20) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M085.r2728) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 20) Nonrational.InducedTerminalMatches.M085.r2728
    Nonrational.InducedTerminalMatches.M085.r2728_checked (by decide +kernel)
theorem record000_leaf_checked_21 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
      (record000_certificates 21) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M085.r2729) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 21) Nonrational.InducedTerminalMatches.M085.r2729
    Nonrational.InducedTerminalMatches.M085.r2729_checked (by decide +kernel)
theorem record000_leaf_checked_22 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
      (record000_certificates 22) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M085.r2730) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 22) Nonrational.InducedTerminalMatches.M085.r2730
    Nonrational.InducedTerminalMatches.M085.r2730_checked (by decide +kernel)
theorem record000_leaf_checked_23 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
      (record000_certificates 23) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M085.r2731) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 23) Nonrational.InducedTerminalMatches.M085.r2731
    Nonrational.InducedTerminalMatches.M085.r2731_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2732))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2733))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2734))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2735))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2736))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2737)))))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M085.r2732) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M085.r2732
    Nonrational.InducedTerminalMatches.M085.r2732_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M085.r2733) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M085.r2733
    Nonrational.InducedTerminalMatches.M085.r2733_checked (by decide +kernel)
theorem record001_leaf_checked_2 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
      (record001_certificates 2) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M085.r2734) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 2) Nonrational.InducedTerminalMatches.M085.r2734
    Nonrational.InducedTerminalMatches.M085.r2734_checked (by decide +kernel)
theorem record001_leaf_checked_3 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
      (record001_certificates 3) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M085.r2735) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 3) Nonrational.InducedTerminalMatches.M085.r2735
    Nonrational.InducedTerminalMatches.M085.r2735_checked (by decide +kernel)
theorem record001_leaf_checked_4 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
      (record001_certificates 4) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M085.r2736) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 4) Nonrational.InducedTerminalMatches.M085.r2736
    Nonrational.InducedTerminalMatches.M085.r2736_checked (by decide +kernel)
theorem record001_leaf_checked_5 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
      (record001_certificates 5) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M085.r2737) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 5) Nonrational.InducedTerminalMatches.M085.r2737
    Nonrational.InducedTerminalMatches.M085.r2737_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (fun j => Fin.elim0 j)))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073
