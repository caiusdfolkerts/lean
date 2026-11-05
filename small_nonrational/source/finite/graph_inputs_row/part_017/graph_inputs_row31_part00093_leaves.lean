module
prelude
public import GraphInputsRow31Part00093Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M089
public import InducedTerminalMatches.M090
public import InducedTerminalMatches.M091

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093
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
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2863))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2864))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2865))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2866))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2867))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2868)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2869))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2870))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2871))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2872))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2873)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2874))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2875))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2876))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2877))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2878))))
 (.branch 18
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2879))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2880)))
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2881))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2882)))))
 (.branch 23
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2883))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2884))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2885))))
 (.branch 25
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2886))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2887)))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2888))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2889)))))))
 (.branch 40
 (.branch 33
 (.branch 30
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2890))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2891))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2892))))
 (.branch 31
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2893))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2894))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2895)))))
 (.branch 36
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2896))
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2897))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2898))))
 (.branch 38
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2899))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2900)))
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2901))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2902))))))
 (.branch 47
 (.branch 43
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2903))
 (.branch 42
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2904))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2905))))
 (.branch 45
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2906))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2907)))
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2908))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2909)))))
 (.branch 50
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2910))
 (.branch 49
 (.leaf (.matching Nonrational.InducedTerminalMatches.M090.r2911))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2912))))
 (.branch 52
 (.branch 51
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2913))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2914)))
 (.branch 53
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2915))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2916))))))))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M089.r2863) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 0) Nonrational.InducedTerminalMatches.M089.r2863
    Nonrational.InducedTerminalMatches.M089.r2863_checked (by decide +kernel)
theorem record002_leaf_checked_1 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 1)
      (record002_certificates 1) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M089.r2864) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 1) Nonrational.InducedTerminalMatches.M089.r2864
    Nonrational.InducedTerminalMatches.M089.r2864_checked (by decide +kernel)
theorem record002_leaf_checked_2 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 2)
      (record002_certificates 2) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M089.r2865) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 2) Nonrational.InducedTerminalMatches.M089.r2865
    Nonrational.InducedTerminalMatches.M089.r2865_checked (by decide +kernel)
theorem record002_leaf_checked_3 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 3)
      (record002_certificates 3) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M089.r2866) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 3) Nonrational.InducedTerminalMatches.M089.r2866
    Nonrational.InducedTerminalMatches.M089.r2866_checked (by decide +kernel)
theorem record002_leaf_checked_4 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 4)
      (record002_certificates 4) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M089.r2867) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 4) Nonrational.InducedTerminalMatches.M089.r2867
    Nonrational.InducedTerminalMatches.M089.r2867_checked (by decide +kernel)
theorem record002_leaf_checked_5 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 5)
      (record002_certificates 5) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M089.r2868) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 5) Nonrational.InducedTerminalMatches.M089.r2868
    Nonrational.InducedTerminalMatches.M089.r2868_checked (by decide +kernel)
theorem record002_leaf_checked_6 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 6)
      (record002_certificates 6) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M089.r2869) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 6) Nonrational.InducedTerminalMatches.M089.r2869
    Nonrational.InducedTerminalMatches.M089.r2869_checked (by decide +kernel)
theorem record002_leaf_checked_7 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 7)
      (record002_certificates 7) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M089.r2870) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 7) Nonrational.InducedTerminalMatches.M089.r2870
    Nonrational.InducedTerminalMatches.M089.r2870_checked (by decide +kernel)
theorem record002_leaf_checked_8 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 8)
      (record002_certificates 8) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M089.r2871) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 8) Nonrational.InducedTerminalMatches.M089.r2871
    Nonrational.InducedTerminalMatches.M089.r2871_checked (by decide +kernel)
theorem record002_leaf_checked_9 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 9)
      (record002_certificates 9) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M089.r2872) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 9) Nonrational.InducedTerminalMatches.M089.r2872
    Nonrational.InducedTerminalMatches.M089.r2872_checked (by decide +kernel)
theorem record002_leaf_checked_10 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 10)
      (record002_certificates 10) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M089.r2873) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 10) Nonrational.InducedTerminalMatches.M089.r2873
    Nonrational.InducedTerminalMatches.M089.r2873_checked (by decide +kernel)
theorem record002_leaf_checked_11 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 11)
      (record002_certificates 11) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M089.r2874) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 11) Nonrational.InducedTerminalMatches.M089.r2874
    Nonrational.InducedTerminalMatches.M089.r2874_checked (by decide +kernel)
theorem record002_leaf_checked_12 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 12)
      (record002_certificates 12) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M089.r2875) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 12) Nonrational.InducedTerminalMatches.M089.r2875
    Nonrational.InducedTerminalMatches.M089.r2875_checked (by decide +kernel)
theorem record002_leaf_checked_13 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 13)
      (record002_certificates 13) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M089.r2876) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 13) Nonrational.InducedTerminalMatches.M089.r2876
    Nonrational.InducedTerminalMatches.M089.r2876_checked (by decide +kernel)
theorem record002_leaf_checked_14 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 14)
      (record002_certificates 14) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M089.r2877) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 14) Nonrational.InducedTerminalMatches.M089.r2877
    Nonrational.InducedTerminalMatches.M089.r2877_checked (by decide +kernel)
theorem record002_leaf_checked_15 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 15)
      (record002_certificates 15) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M089.r2878) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 15) Nonrational.InducedTerminalMatches.M089.r2878
    Nonrational.InducedTerminalMatches.M089.r2878_checked (by decide +kernel)
theorem record002_leaf_checked_16 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 16)
      (record002_certificates 16) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M089.r2879) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 16) Nonrational.InducedTerminalMatches.M089.r2879
    Nonrational.InducedTerminalMatches.M089.r2879_checked (by decide +kernel)
theorem record002_leaf_checked_17 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 17)
      (record002_certificates 17) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M090.r2880) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 17) Nonrational.InducedTerminalMatches.M090.r2880
    Nonrational.InducedTerminalMatches.M090.r2880_checked (by decide +kernel)
theorem record002_leaf_checked_18 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 18)
      (record002_certificates 18) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M090.r2881) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 18) Nonrational.InducedTerminalMatches.M090.r2881
    Nonrational.InducedTerminalMatches.M090.r2881_checked (by decide +kernel)
theorem record002_leaf_checked_19 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 19)
      (record002_certificates 19) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M090.r2882) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 19) Nonrational.InducedTerminalMatches.M090.r2882
    Nonrational.InducedTerminalMatches.M090.r2882_checked (by decide +kernel)
theorem record002_leaf_checked_20 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 20)
      (record002_certificates 20) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M090.r2883) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 20) Nonrational.InducedTerminalMatches.M090.r2883
    Nonrational.InducedTerminalMatches.M090.r2883_checked (by decide +kernel)
theorem record002_leaf_checked_21 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 21)
      (record002_certificates 21) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M090.r2884) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 21) Nonrational.InducedTerminalMatches.M090.r2884
    Nonrational.InducedTerminalMatches.M090.r2884_checked (by decide +kernel)
theorem record002_leaf_checked_22 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 22)
      (record002_certificates 22) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M090.r2885) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 22) Nonrational.InducedTerminalMatches.M090.r2885
    Nonrational.InducedTerminalMatches.M090.r2885_checked (by decide +kernel)
theorem record002_leaf_checked_23 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 23)
      (record002_certificates 23) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M090.r2886) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 23) Nonrational.InducedTerminalMatches.M090.r2886
    Nonrational.InducedTerminalMatches.M090.r2886_checked (by decide +kernel)
theorem record002_leaf_checked_24 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 24)
      (record002_certificates 24) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M090.r2887) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 24) Nonrational.InducedTerminalMatches.M090.r2887
    Nonrational.InducedTerminalMatches.M090.r2887_checked (by decide +kernel)
theorem record002_leaf_checked_25 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 25)
      (record002_certificates 25) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M090.r2888) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 25) Nonrational.InducedTerminalMatches.M090.r2888
    Nonrational.InducedTerminalMatches.M090.r2888_checked (by decide +kernel)
theorem record002_leaf_checked_26 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 26)
      (record002_certificates 26) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M090.r2889) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 26) Nonrational.InducedTerminalMatches.M090.r2889
    Nonrational.InducedTerminalMatches.M090.r2889_checked (by decide +kernel)
theorem record002_leaf_checked_27 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 27)
      (record002_certificates 27) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M090.r2890) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 27) Nonrational.InducedTerminalMatches.M090.r2890
    Nonrational.InducedTerminalMatches.M090.r2890_checked (by decide +kernel)
theorem record002_leaf_checked_28 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 28)
      (record002_certificates 28) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M090.r2891) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 28) Nonrational.InducedTerminalMatches.M090.r2891
    Nonrational.InducedTerminalMatches.M090.r2891_checked (by decide +kernel)
theorem record002_leaf_checked_29 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 29)
      (record002_certificates 29) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M090.r2892) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 29) Nonrational.InducedTerminalMatches.M090.r2892
    Nonrational.InducedTerminalMatches.M090.r2892_checked (by decide +kernel)
theorem record002_leaf_checked_30 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 30)
      (record002_certificates 30) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M090.r2893) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 30) Nonrational.InducedTerminalMatches.M090.r2893
    Nonrational.InducedTerminalMatches.M090.r2893_checked (by decide +kernel)
theorem record002_leaf_checked_31 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 31)
      (record002_certificates 31) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M090.r2894) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 31) Nonrational.InducedTerminalMatches.M090.r2894
    Nonrational.InducedTerminalMatches.M090.r2894_checked (by decide +kernel)
theorem record002_leaf_checked_32 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 32)
      (record002_certificates 32) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M090.r2895) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 32) Nonrational.InducedTerminalMatches.M090.r2895
    Nonrational.InducedTerminalMatches.M090.r2895_checked (by decide +kernel)
theorem record002_leaf_checked_33 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 33)
      (record002_certificates 33) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M090.r2896) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 33) Nonrational.InducedTerminalMatches.M090.r2896
    Nonrational.InducedTerminalMatches.M090.r2896_checked (by decide +kernel)
theorem record002_leaf_checked_34 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 34)
      (record002_certificates 34) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M090.r2897) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 34) Nonrational.InducedTerminalMatches.M090.r2897
    Nonrational.InducedTerminalMatches.M090.r2897_checked (by decide +kernel)
theorem record002_leaf_checked_35 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 35)
      (record002_certificates 35) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M090.r2898) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 35) Nonrational.InducedTerminalMatches.M090.r2898
    Nonrational.InducedTerminalMatches.M090.r2898_checked (by decide +kernel)
theorem record002_leaf_checked_36 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 36)
      (record002_certificates 36) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M090.r2899) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 36) Nonrational.InducedTerminalMatches.M090.r2899
    Nonrational.InducedTerminalMatches.M090.r2899_checked (by decide +kernel)
theorem record002_leaf_checked_37 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 37)
      (record002_certificates 37) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M090.r2900) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 37) Nonrational.InducedTerminalMatches.M090.r2900
    Nonrational.InducedTerminalMatches.M090.r2900_checked (by decide +kernel)
theorem record002_leaf_checked_38 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 38)
      (record002_certificates 38) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M090.r2901) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 38) Nonrational.InducedTerminalMatches.M090.r2901
    Nonrational.InducedTerminalMatches.M090.r2901_checked (by decide +kernel)
theorem record002_leaf_checked_39 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 39)
      (record002_certificates 39) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M090.r2902) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 39) Nonrational.InducedTerminalMatches.M090.r2902
    Nonrational.InducedTerminalMatches.M090.r2902_checked (by decide +kernel)
theorem record002_leaf_checked_40 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 40)
      (record002_certificates 40) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M090.r2903) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 40) Nonrational.InducedTerminalMatches.M090.r2903
    Nonrational.InducedTerminalMatches.M090.r2903_checked (by decide +kernel)
theorem record002_leaf_checked_41 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 41)
      (record002_certificates 41) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M090.r2904) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 41) Nonrational.InducedTerminalMatches.M090.r2904
    Nonrational.InducedTerminalMatches.M090.r2904_checked (by decide +kernel)
theorem record002_leaf_checked_42 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 42)
      (record002_certificates 42) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M090.r2905) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 42) Nonrational.InducedTerminalMatches.M090.r2905
    Nonrational.InducedTerminalMatches.M090.r2905_checked (by decide +kernel)
theorem record002_leaf_checked_43 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 43)
      (record002_certificates 43) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M090.r2906) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 43) Nonrational.InducedTerminalMatches.M090.r2906
    Nonrational.InducedTerminalMatches.M090.r2906_checked (by decide +kernel)
theorem record002_leaf_checked_44 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 44)
      (record002_certificates 44) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M090.r2907) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 44) Nonrational.InducedTerminalMatches.M090.r2907
    Nonrational.InducedTerminalMatches.M090.r2907_checked (by decide +kernel)
theorem record002_leaf_checked_45 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 45)
      (record002_certificates 45) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M090.r2908) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 45) Nonrational.InducedTerminalMatches.M090.r2908
    Nonrational.InducedTerminalMatches.M090.r2908_checked (by decide +kernel)
theorem record002_leaf_checked_46 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 46)
      (record002_certificates 46) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M090.r2909) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 46) Nonrational.InducedTerminalMatches.M090.r2909
    Nonrational.InducedTerminalMatches.M090.r2909_checked (by decide +kernel)
theorem record002_leaf_checked_47 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 47)
      (record002_certificates 47) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M090.r2910) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 47) Nonrational.InducedTerminalMatches.M090.r2910
    Nonrational.InducedTerminalMatches.M090.r2910_checked (by decide +kernel)
theorem record002_leaf_checked_48 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 48)
      (record002_certificates 48) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M090.r2911) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 48) Nonrational.InducedTerminalMatches.M090.r2911
    Nonrational.InducedTerminalMatches.M090.r2911_checked (by decide +kernel)
theorem record002_leaf_checked_49 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 49)
      (record002_certificates 49) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M091.r2912) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 49) Nonrational.InducedTerminalMatches.M091.r2912
    Nonrational.InducedTerminalMatches.M091.r2912_checked (by decide +kernel)
theorem record002_leaf_checked_50 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 50)
      (record002_certificates 50) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M091.r2913) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 50) Nonrational.InducedTerminalMatches.M091.r2913
    Nonrational.InducedTerminalMatches.M091.r2913_checked (by decide +kernel)
theorem record002_leaf_checked_51 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 51)
      (record002_certificates 51) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M091.r2914) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 51) Nonrational.InducedTerminalMatches.M091.r2914
    Nonrational.InducedTerminalMatches.M091.r2914_checked (by decide +kernel)
theorem record002_leaf_checked_52 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 52)
      (record002_certificates 52) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M091.r2915) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 52) Nonrational.InducedTerminalMatches.M091.r2915
    Nonrational.InducedTerminalMatches.M091.r2915_checked (by decide +kernel)
theorem record002_leaf_checked_53 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 53)
      (record002_certificates 53) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M091.r2916) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 53) Nonrational.InducedTerminalMatches.M091.r2916
    Nonrational.InducedTerminalMatches.M091.r2916_checked (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (Fin.cases record002_leaf_checked_14 (Fin.cases record002_leaf_checked_15 (Fin.cases record002_leaf_checked_16 (Fin.cases record002_leaf_checked_17 (Fin.cases record002_leaf_checked_18 (Fin.cases record002_leaf_checked_19 (Fin.cases record002_leaf_checked_20 (Fin.cases record002_leaf_checked_21 (Fin.cases record002_leaf_checked_22 (Fin.cases record002_leaf_checked_23 (Fin.cases record002_leaf_checked_24 (Fin.cases record002_leaf_checked_25 (Fin.cases record002_leaf_checked_26 (Fin.cases record002_leaf_checked_27 (Fin.cases record002_leaf_checked_28 (Fin.cases record002_leaf_checked_29 (Fin.cases record002_leaf_checked_30 (Fin.cases record002_leaf_checked_31 (Fin.cases record002_leaf_checked_32 (Fin.cases record002_leaf_checked_33 (Fin.cases record002_leaf_checked_34 (Fin.cases record002_leaf_checked_35 (Fin.cases record002_leaf_checked_36 (Fin.cases record002_leaf_checked_37 (Fin.cases record002_leaf_checked_38 (Fin.cases record002_leaf_checked_39 (Fin.cases record002_leaf_checked_40 (Fin.cases record002_leaf_checked_41 (Fin.cases record002_leaf_checked_42 (Fin.cases record002_leaf_checked_43 (Fin.cases record002_leaf_checked_44 (Fin.cases record002_leaf_checked_45 (Fin.cases record002_leaf_checked_46 (Fin.cases record002_leaf_checked_47 (Fin.cases record002_leaf_checked_48 (Fin.cases record002_leaf_checked_49 (Fin.cases record002_leaf_checked_50 (Fin.cases record002_leaf_checked_51 (Fin.cases record002_leaf_checked_52 (Fin.cases record002_leaf_checked_53 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record002_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093
