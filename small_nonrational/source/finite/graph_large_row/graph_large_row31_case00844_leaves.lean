module
prelude
public import GraphLargeRow31Case00844Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M083
public import InducedTerminalMatches.M084

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2673))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2674))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2675))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2676))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2677)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2678))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2679)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2680))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2681)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2682))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2683))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2684))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2685)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2686))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2687))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2688))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2689))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2690))))
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2691))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2692)))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2693))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2694)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2695))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2696)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2697))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2698))))
 (.branch 28
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2699))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2700)))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2701))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2702)))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M083.r2673) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M083.r2673
    Nonrational.InducedTerminalMatches.M083.r2673_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M083.r2674) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M083.r2674
    Nonrational.InducedTerminalMatches.M083.r2674_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M083.r2675) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M083.r2675
    Nonrational.InducedTerminalMatches.M083.r2675_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M083.r2676) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M083.r2676
    Nonrational.InducedTerminalMatches.M083.r2676_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M083.r2677) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M083.r2677
    Nonrational.InducedTerminalMatches.M083.r2677_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M083.r2678) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M083.r2678
    Nonrational.InducedTerminalMatches.M083.r2678_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M083.r2679) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M083.r2679
    Nonrational.InducedTerminalMatches.M083.r2679_checked (by decide +kernel)
theorem record000_leaf_checked_7 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
      (record000_certificates 7) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M083.r2680) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 7) Nonrational.InducedTerminalMatches.M083.r2680
    Nonrational.InducedTerminalMatches.M083.r2680_checked (by decide +kernel)
theorem record000_leaf_checked_8 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
      (record000_certificates 8) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M083.r2681) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 8) Nonrational.InducedTerminalMatches.M083.r2681
    Nonrational.InducedTerminalMatches.M083.r2681_checked (by decide +kernel)
theorem record000_leaf_checked_9 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
      (record000_certificates 9) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M083.r2682) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 9) Nonrational.InducedTerminalMatches.M083.r2682
    Nonrational.InducedTerminalMatches.M083.r2682_checked (by decide +kernel)
theorem record000_leaf_checked_10 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
      (record000_certificates 10) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M083.r2683) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 10) Nonrational.InducedTerminalMatches.M083.r2683
    Nonrational.InducedTerminalMatches.M083.r2683_checked (by decide +kernel)
theorem record000_leaf_checked_11 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
      (record000_certificates 11) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M083.r2684) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 11) Nonrational.InducedTerminalMatches.M083.r2684
    Nonrational.InducedTerminalMatches.M083.r2684_checked (by decide +kernel)
theorem record000_leaf_checked_12 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
      (record000_certificates 12) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M083.r2685) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 12) Nonrational.InducedTerminalMatches.M083.r2685
    Nonrational.InducedTerminalMatches.M083.r2685_checked (by decide +kernel)
theorem record000_leaf_checked_13 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
      (record000_certificates 13) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M083.r2686) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 13) Nonrational.InducedTerminalMatches.M083.r2686
    Nonrational.InducedTerminalMatches.M083.r2686_checked (by decide +kernel)
theorem record000_leaf_checked_14 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
      (record000_certificates 14) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M083.r2687) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 14) Nonrational.InducedTerminalMatches.M083.r2687
    Nonrational.InducedTerminalMatches.M083.r2687_checked (by decide +kernel)
theorem record000_leaf_checked_15 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
      (record000_certificates 15) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M084.r2688) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 15) Nonrational.InducedTerminalMatches.M084.r2688
    Nonrational.InducedTerminalMatches.M084.r2688_checked (by decide +kernel)
theorem record000_leaf_checked_16 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
      (record000_certificates 16) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M084.r2689) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 16) Nonrational.InducedTerminalMatches.M084.r2689
    Nonrational.InducedTerminalMatches.M084.r2689_checked (by decide +kernel)
theorem record000_leaf_checked_17 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
      (record000_certificates 17) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M084.r2690) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 17) Nonrational.InducedTerminalMatches.M084.r2690
    Nonrational.InducedTerminalMatches.M084.r2690_checked (by decide +kernel)
theorem record000_leaf_checked_18 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
      (record000_certificates 18) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M084.r2691) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 18) Nonrational.InducedTerminalMatches.M084.r2691
    Nonrational.InducedTerminalMatches.M084.r2691_checked (by decide +kernel)
theorem record000_leaf_checked_19 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
      (record000_certificates 19) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M084.r2692) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 19) Nonrational.InducedTerminalMatches.M084.r2692
    Nonrational.InducedTerminalMatches.M084.r2692_checked (by decide +kernel)
theorem record000_leaf_checked_20 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
      (record000_certificates 20) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M084.r2693) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 20) Nonrational.InducedTerminalMatches.M084.r2693
    Nonrational.InducedTerminalMatches.M084.r2693_checked (by decide +kernel)
theorem record000_leaf_checked_21 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
      (record000_certificates 21) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M084.r2694) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 21) Nonrational.InducedTerminalMatches.M084.r2694
    Nonrational.InducedTerminalMatches.M084.r2694_checked (by decide +kernel)
theorem record000_leaf_checked_22 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
      (record000_certificates 22) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M084.r2695) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 22) Nonrational.InducedTerminalMatches.M084.r2695
    Nonrational.InducedTerminalMatches.M084.r2695_checked (by decide +kernel)
theorem record000_leaf_checked_23 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
      (record000_certificates 23) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M084.r2696) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 23) Nonrational.InducedTerminalMatches.M084.r2696
    Nonrational.InducedTerminalMatches.M084.r2696_checked (by decide +kernel)
theorem record000_leaf_checked_24 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
      (record000_certificates 24) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M084.r2697) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 24) Nonrational.InducedTerminalMatches.M084.r2697
    Nonrational.InducedTerminalMatches.M084.r2697_checked (by decide +kernel)
theorem record000_leaf_checked_25 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
      (record000_certificates 25) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M084.r2698) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 25) Nonrational.InducedTerminalMatches.M084.r2698
    Nonrational.InducedTerminalMatches.M084.r2698_checked (by decide +kernel)
theorem record000_leaf_checked_26 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
      (record000_certificates 26) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M084.r2699) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 26) Nonrational.InducedTerminalMatches.M084.r2699
    Nonrational.InducedTerminalMatches.M084.r2699_checked (by decide +kernel)
theorem record000_leaf_checked_27 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
      (record000_certificates 27) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M084.r2700) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 27) Nonrational.InducedTerminalMatches.M084.r2700
    Nonrational.InducedTerminalMatches.M084.r2700_checked (by decide +kernel)
theorem record000_leaf_checked_28 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
      (record000_certificates 28) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M084.r2701) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 28) Nonrational.InducedTerminalMatches.M084.r2701
    Nonrational.InducedTerminalMatches.M084.r2701_checked (by decide +kernel)
theorem record000_leaf_checked_29 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
      (record000_certificates 29) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M084.r2702) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 29) Nonrational.InducedTerminalMatches.M084.r2702
    Nonrational.InducedTerminalMatches.M084.r2702_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

end Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
