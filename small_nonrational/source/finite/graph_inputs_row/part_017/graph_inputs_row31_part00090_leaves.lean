module
prelude
public import GraphInputsRow31Part00090Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M088
public import InducedTerminalMatches.M089

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090
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
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2834))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2835)))
noncomputable def record003_certificates (j : Fin record003.l) : Certificate :=
  record003_certificateTable.get j.val
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M088.r2834) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 0) Nonrational.InducedTerminalMatches.M088.r2834
    Nonrational.InducedTerminalMatches.M088.r2834_checked (by decide +kernel)
theorem record003_leaf_checked_1 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 1)
      (record003_certificates 1) = true := by
  change RawLeafCertificate.check record003.data.quota (record003_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M088.r2835) = true
  exact matching_checked record003.data.quota (record003_rawLeaves 1) Nonrational.InducedTerminalMatches.M088.r2835
    Nonrational.InducedTerminalMatches.M088.r2835_checked (by decide +kernel)
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (fun j => Fin.elim0 j)))
#print axioms record003_leaf_certificates_checked

noncomputable def record004_rawLeaves (j : Fin record004.l) : List Cell :=
  (record004.leaf j).map record004.data.cells
theorem record004_raw_exact (j : Fin record004.l) :
    (record004.leaf j).map record004.data.cells = record004_rawLeaves j := rfl
noncomputable def record004_certificateTable : Table Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2836))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2837))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2838))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2839))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2840))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2841)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2842))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2843))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2844))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2845))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2846))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2847))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2848))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2849))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2850))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2851))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2852))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2853)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2854))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2855))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2856))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2857))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2858))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2859)))))))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M088.r2836) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 0) Nonrational.InducedTerminalMatches.M088.r2836
    Nonrational.InducedTerminalMatches.M088.r2836_checked (by decide +kernel)
theorem record004_leaf_checked_1 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
      (record004_certificates 1) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M088.r2837) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 1) Nonrational.InducedTerminalMatches.M088.r2837
    Nonrational.InducedTerminalMatches.M088.r2837_checked (by decide +kernel)
theorem record004_leaf_checked_2 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 2)
      (record004_certificates 2) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M088.r2838) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 2) Nonrational.InducedTerminalMatches.M088.r2838
    Nonrational.InducedTerminalMatches.M088.r2838_checked (by decide +kernel)
theorem record004_leaf_checked_3 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 3)
      (record004_certificates 3) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M088.r2839) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 3) Nonrational.InducedTerminalMatches.M088.r2839
    Nonrational.InducedTerminalMatches.M088.r2839_checked (by decide +kernel)
theorem record004_leaf_checked_4 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 4)
      (record004_certificates 4) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M088.r2840) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 4) Nonrational.InducedTerminalMatches.M088.r2840
    Nonrational.InducedTerminalMatches.M088.r2840_checked (by decide +kernel)
theorem record004_leaf_checked_5 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 5)
      (record004_certificates 5) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M088.r2841) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 5) Nonrational.InducedTerminalMatches.M088.r2841
    Nonrational.InducedTerminalMatches.M088.r2841_checked (by decide +kernel)
theorem record004_leaf_checked_6 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 6)
      (record004_certificates 6) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M088.r2842) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 6) Nonrational.InducedTerminalMatches.M088.r2842
    Nonrational.InducedTerminalMatches.M088.r2842_checked (by decide +kernel)
theorem record004_leaf_checked_7 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 7)
      (record004_certificates 7) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M088.r2843) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 7) Nonrational.InducedTerminalMatches.M088.r2843
    Nonrational.InducedTerminalMatches.M088.r2843_checked (by decide +kernel)
theorem record004_leaf_checked_8 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 8)
      (record004_certificates 8) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M088.r2844) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 8) Nonrational.InducedTerminalMatches.M088.r2844
    Nonrational.InducedTerminalMatches.M088.r2844_checked (by decide +kernel)
theorem record004_leaf_checked_9 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 9)
      (record004_certificates 9) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M088.r2845) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 9) Nonrational.InducedTerminalMatches.M088.r2845
    Nonrational.InducedTerminalMatches.M088.r2845_checked (by decide +kernel)
theorem record004_leaf_checked_10 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 10)
      (record004_certificates 10) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M088.r2846) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 10) Nonrational.InducedTerminalMatches.M088.r2846
    Nonrational.InducedTerminalMatches.M088.r2846_checked (by decide +kernel)
theorem record004_leaf_checked_11 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 11)
      (record004_certificates 11) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M088.r2847) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 11) Nonrational.InducedTerminalMatches.M088.r2847
    Nonrational.InducedTerminalMatches.M088.r2847_checked (by decide +kernel)
theorem record004_leaf_checked_12 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 12)
      (record004_certificates 12) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M089.r2848) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 12) Nonrational.InducedTerminalMatches.M089.r2848
    Nonrational.InducedTerminalMatches.M089.r2848_checked (by decide +kernel)
theorem record004_leaf_checked_13 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 13)
      (record004_certificates 13) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M089.r2849) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 13) Nonrational.InducedTerminalMatches.M089.r2849
    Nonrational.InducedTerminalMatches.M089.r2849_checked (by decide +kernel)
theorem record004_leaf_checked_14 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 14)
      (record004_certificates 14) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M089.r2850) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 14) Nonrational.InducedTerminalMatches.M089.r2850
    Nonrational.InducedTerminalMatches.M089.r2850_checked (by decide +kernel)
theorem record004_leaf_checked_15 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 15)
      (record004_certificates 15) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M089.r2851) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 15) Nonrational.InducedTerminalMatches.M089.r2851
    Nonrational.InducedTerminalMatches.M089.r2851_checked (by decide +kernel)
theorem record004_leaf_checked_16 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 16)
      (record004_certificates 16) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M089.r2852) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 16) Nonrational.InducedTerminalMatches.M089.r2852
    Nonrational.InducedTerminalMatches.M089.r2852_checked (by decide +kernel)
theorem record004_leaf_checked_17 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 17)
      (record004_certificates 17) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M089.r2853) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 17) Nonrational.InducedTerminalMatches.M089.r2853
    Nonrational.InducedTerminalMatches.M089.r2853_checked (by decide +kernel)
theorem record004_leaf_checked_18 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 18)
      (record004_certificates 18) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M089.r2854) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 18) Nonrational.InducedTerminalMatches.M089.r2854
    Nonrational.InducedTerminalMatches.M089.r2854_checked (by decide +kernel)
theorem record004_leaf_checked_19 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 19)
      (record004_certificates 19) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M089.r2855) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 19) Nonrational.InducedTerminalMatches.M089.r2855
    Nonrational.InducedTerminalMatches.M089.r2855_checked (by decide +kernel)
theorem record004_leaf_checked_20 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 20)
      (record004_certificates 20) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M089.r2856) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 20) Nonrational.InducedTerminalMatches.M089.r2856
    Nonrational.InducedTerminalMatches.M089.r2856_checked (by decide +kernel)
theorem record004_leaf_checked_21 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 21)
      (record004_certificates 21) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M089.r2857) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 21) Nonrational.InducedTerminalMatches.M089.r2857
    Nonrational.InducedTerminalMatches.M089.r2857_checked (by decide +kernel)
theorem record004_leaf_checked_22 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 22)
      (record004_certificates 22) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M089.r2858) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 22) Nonrational.InducedTerminalMatches.M089.r2858
    Nonrational.InducedTerminalMatches.M089.r2858_checked (by decide +kernel)
theorem record004_leaf_checked_23 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 23)
      (record004_certificates 23) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M089.r2859) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 23) Nonrational.InducedTerminalMatches.M089.r2859
    Nonrational.InducedTerminalMatches.M089.r2859_checked (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (Fin.cases record004_leaf_checked_1 (Fin.cases record004_leaf_checked_2 (Fin.cases record004_leaf_checked_3 (Fin.cases record004_leaf_checked_4 (Fin.cases record004_leaf_checked_5 (Fin.cases record004_leaf_checked_6 (Fin.cases record004_leaf_checked_7 (Fin.cases record004_leaf_checked_8 (Fin.cases record004_leaf_checked_9 (Fin.cases record004_leaf_checked_10 (Fin.cases record004_leaf_checked_11 (Fin.cases record004_leaf_checked_12 (Fin.cases record004_leaf_checked_13 (Fin.cases record004_leaf_checked_14 (Fin.cases record004_leaf_checked_15 (Fin.cases record004_leaf_checked_16 (Fin.cases record004_leaf_checked_17 (Fin.cases record004_leaf_checked_18 (Fin.cases record004_leaf_checked_19 (Fin.cases record004_leaf_checked_20 (Fin.cases record004_leaf_checked_21 (Fin.cases record004_leaf_checked_22 (Fin.cases record004_leaf_checked_23 (fun j => Fin.elim0 j)))))))))))))))))))))))))
#print axioms record004_leaf_certificates_checked

noncomputable def record005_rawLeaves (j : Fin record005.l) : List Cell :=
  (record005.leaf j).map record005.data.cells
theorem record005_raw_exact (j : Fin record005.l) :
    (record005.leaf j).map record005.data.cells = record005_rawLeaves j := rfl
noncomputable def record005_certificateTable : Table Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2860))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2861))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2862))))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M089.r2860) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 0) Nonrational.InducedTerminalMatches.M089.r2860
    Nonrational.InducedTerminalMatches.M089.r2860_checked (by decide +kernel)
theorem record005_leaf_checked_1 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
      (record005_certificates 1) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M089.r2861) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 1) Nonrational.InducedTerminalMatches.M089.r2861
    Nonrational.InducedTerminalMatches.M089.r2861_checked (by decide +kernel)
theorem record005_leaf_checked_2 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
      (record005_certificates 2) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M089.r2862) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 2) Nonrational.InducedTerminalMatches.M089.r2862
    Nonrational.InducedTerminalMatches.M089.r2862_checked (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (Fin.cases record005_leaf_checked_1 (Fin.cases record005_leaf_checked_2 (fun j => Fin.elim0 j))))
#print axioms record005_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090
