module
prelude
public import GraphInputsRow24Part00142Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M024
public import InducedTerminalMatches.M025
public import InducedTerminalMatches.M026

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0786))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0787))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0788))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0789))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0790))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0791)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0792))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0793))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0794))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0795))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0796)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0797))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0798))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M024.r0799))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0800))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0801))))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0802))
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0803))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0804)))))
 (.branch 22
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0805))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0806))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0807))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0808))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0809)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0810))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0811)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0812))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0813))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0814))))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0815))
 (.branch 31
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0816))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0817)))))
 (.branch 35
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0818))
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0819))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0820))))
 (.branch 37
 (.branch 36
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0821))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0822)))
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0823))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0824))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0825))
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0826))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0827))))
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0828))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0829))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0830)))))
 (.branch 48
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M025.r0831))
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M026.r0832))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M026.r0833))))
 (.branch 50
 (.branch 49
 (.leaf (.matching Nonrational.InducedTerminalMatches.M026.r0834))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M026.r0835)))
 (.branch 51
 (.leaf (.matching Nonrational.InducedTerminalMatches.M026.r0836))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M026.r0837))))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M024.r0786) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M024.r0786
    Nonrational.InducedTerminalMatches.M024.r0786_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M024.r0787) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M024.r0787
    Nonrational.InducedTerminalMatches.M024.r0787_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M024.r0788) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M024.r0788
    Nonrational.InducedTerminalMatches.M024.r0788_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M024.r0789) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M024.r0789
    Nonrational.InducedTerminalMatches.M024.r0789_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M024.r0790) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M024.r0790
    Nonrational.InducedTerminalMatches.M024.r0790_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M024.r0791) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M024.r0791
    Nonrational.InducedTerminalMatches.M024.r0791_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M024.r0792) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M024.r0792
    Nonrational.InducedTerminalMatches.M024.r0792_checked (by decide +kernel)
theorem record000_leaf_checked_7 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
      (record000_certificates 7) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M024.r0793) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 7) Nonrational.InducedTerminalMatches.M024.r0793
    Nonrational.InducedTerminalMatches.M024.r0793_checked (by decide +kernel)
theorem record000_leaf_checked_8 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
      (record000_certificates 8) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M024.r0794) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 8) Nonrational.InducedTerminalMatches.M024.r0794
    Nonrational.InducedTerminalMatches.M024.r0794_checked (by decide +kernel)
theorem record000_leaf_checked_9 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
      (record000_certificates 9) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M024.r0795) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 9) Nonrational.InducedTerminalMatches.M024.r0795
    Nonrational.InducedTerminalMatches.M024.r0795_checked (by decide +kernel)
theorem record000_leaf_checked_10 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
      (record000_certificates 10) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M024.r0796) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 10) Nonrational.InducedTerminalMatches.M024.r0796
    Nonrational.InducedTerminalMatches.M024.r0796_checked (by decide +kernel)
theorem record000_leaf_checked_11 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
      (record000_certificates 11) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M024.r0797) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 11) Nonrational.InducedTerminalMatches.M024.r0797
    Nonrational.InducedTerminalMatches.M024.r0797_checked (by decide +kernel)
theorem record000_leaf_checked_12 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
      (record000_certificates 12) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M024.r0798) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 12) Nonrational.InducedTerminalMatches.M024.r0798
    Nonrational.InducedTerminalMatches.M024.r0798_checked (by decide +kernel)
theorem record000_leaf_checked_13 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
      (record000_certificates 13) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M024.r0799) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 13) Nonrational.InducedTerminalMatches.M024.r0799
    Nonrational.InducedTerminalMatches.M024.r0799_checked (by decide +kernel)
theorem record000_leaf_checked_14 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
      (record000_certificates 14) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M025.r0800) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 14) Nonrational.InducedTerminalMatches.M025.r0800
    Nonrational.InducedTerminalMatches.M025.r0800_checked (by decide +kernel)
theorem record000_leaf_checked_15 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
      (record000_certificates 15) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M025.r0801) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 15) Nonrational.InducedTerminalMatches.M025.r0801
    Nonrational.InducedTerminalMatches.M025.r0801_checked (by decide +kernel)
theorem record000_leaf_checked_16 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
      (record000_certificates 16) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M025.r0802) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 16) Nonrational.InducedTerminalMatches.M025.r0802
    Nonrational.InducedTerminalMatches.M025.r0802_checked (by decide +kernel)
theorem record000_leaf_checked_17 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
      (record000_certificates 17) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M025.r0803) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 17) Nonrational.InducedTerminalMatches.M025.r0803
    Nonrational.InducedTerminalMatches.M025.r0803_checked (by decide +kernel)
theorem record000_leaf_checked_18 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
      (record000_certificates 18) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M025.r0804) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 18) Nonrational.InducedTerminalMatches.M025.r0804
    Nonrational.InducedTerminalMatches.M025.r0804_checked (by decide +kernel)
theorem record000_leaf_checked_19 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
      (record000_certificates 19) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M025.r0805) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 19) Nonrational.InducedTerminalMatches.M025.r0805
    Nonrational.InducedTerminalMatches.M025.r0805_checked (by decide +kernel)
theorem record000_leaf_checked_20 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
      (record000_certificates 20) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M025.r0806) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 20) Nonrational.InducedTerminalMatches.M025.r0806
    Nonrational.InducedTerminalMatches.M025.r0806_checked (by decide +kernel)
theorem record000_leaf_checked_21 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
      (record000_certificates 21) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M025.r0807) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 21) Nonrational.InducedTerminalMatches.M025.r0807
    Nonrational.InducedTerminalMatches.M025.r0807_checked (by decide +kernel)
theorem record000_leaf_checked_22 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
      (record000_certificates 22) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M025.r0808) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 22) Nonrational.InducedTerminalMatches.M025.r0808
    Nonrational.InducedTerminalMatches.M025.r0808_checked (by decide +kernel)
theorem record000_leaf_checked_23 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
      (record000_certificates 23) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M025.r0809) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 23) Nonrational.InducedTerminalMatches.M025.r0809
    Nonrational.InducedTerminalMatches.M025.r0809_checked (by decide +kernel)
theorem record000_leaf_checked_24 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
      (record000_certificates 24) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M025.r0810) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 24) Nonrational.InducedTerminalMatches.M025.r0810
    Nonrational.InducedTerminalMatches.M025.r0810_checked (by decide +kernel)
theorem record000_leaf_checked_25 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
      (record000_certificates 25) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M025.r0811) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 25) Nonrational.InducedTerminalMatches.M025.r0811
    Nonrational.InducedTerminalMatches.M025.r0811_checked (by decide +kernel)
theorem record000_leaf_checked_26 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
      (record000_certificates 26) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M025.r0812) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 26) Nonrational.InducedTerminalMatches.M025.r0812
    Nonrational.InducedTerminalMatches.M025.r0812_checked (by decide +kernel)
theorem record000_leaf_checked_27 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
      (record000_certificates 27) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M025.r0813) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 27) Nonrational.InducedTerminalMatches.M025.r0813
    Nonrational.InducedTerminalMatches.M025.r0813_checked (by decide +kernel)
theorem record000_leaf_checked_28 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
      (record000_certificates 28) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M025.r0814) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 28) Nonrational.InducedTerminalMatches.M025.r0814
    Nonrational.InducedTerminalMatches.M025.r0814_checked (by decide +kernel)
theorem record000_leaf_checked_29 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
      (record000_certificates 29) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M025.r0815) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 29) Nonrational.InducedTerminalMatches.M025.r0815
    Nonrational.InducedTerminalMatches.M025.r0815_checked (by decide +kernel)
theorem record000_leaf_checked_30 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
      (record000_certificates 30) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M025.r0816) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 30) Nonrational.InducedTerminalMatches.M025.r0816
    Nonrational.InducedTerminalMatches.M025.r0816_checked (by decide +kernel)
theorem record000_leaf_checked_31 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
      (record000_certificates 31) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M025.r0817) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 31) Nonrational.InducedTerminalMatches.M025.r0817
    Nonrational.InducedTerminalMatches.M025.r0817_checked (by decide +kernel)
theorem record000_leaf_checked_32 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
      (record000_certificates 32) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M025.r0818) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 32) Nonrational.InducedTerminalMatches.M025.r0818
    Nonrational.InducedTerminalMatches.M025.r0818_checked (by decide +kernel)
theorem record000_leaf_checked_33 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
      (record000_certificates 33) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M025.r0819) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 33) Nonrational.InducedTerminalMatches.M025.r0819
    Nonrational.InducedTerminalMatches.M025.r0819_checked (by decide +kernel)
theorem record000_leaf_checked_34 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
      (record000_certificates 34) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M025.r0820) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 34) Nonrational.InducedTerminalMatches.M025.r0820
    Nonrational.InducedTerminalMatches.M025.r0820_checked (by decide +kernel)
theorem record000_leaf_checked_35 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
      (record000_certificates 35) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M025.r0821) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 35) Nonrational.InducedTerminalMatches.M025.r0821
    Nonrational.InducedTerminalMatches.M025.r0821_checked (by decide +kernel)
theorem record000_leaf_checked_36 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
      (record000_certificates 36) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M025.r0822) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 36) Nonrational.InducedTerminalMatches.M025.r0822
    Nonrational.InducedTerminalMatches.M025.r0822_checked (by decide +kernel)
theorem record000_leaf_checked_37 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
      (record000_certificates 37) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M025.r0823) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 37) Nonrational.InducedTerminalMatches.M025.r0823
    Nonrational.InducedTerminalMatches.M025.r0823_checked (by decide +kernel)
theorem record000_leaf_checked_38 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
      (record000_certificates 38) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M025.r0824) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 38) Nonrational.InducedTerminalMatches.M025.r0824
    Nonrational.InducedTerminalMatches.M025.r0824_checked (by decide +kernel)
theorem record000_leaf_checked_39 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
      (record000_certificates 39) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M025.r0825) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 39) Nonrational.InducedTerminalMatches.M025.r0825
    Nonrational.InducedTerminalMatches.M025.r0825_checked (by decide +kernel)
theorem record000_leaf_checked_40 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
      (record000_certificates 40) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M025.r0826) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 40) Nonrational.InducedTerminalMatches.M025.r0826
    Nonrational.InducedTerminalMatches.M025.r0826_checked (by decide +kernel)
theorem record000_leaf_checked_41 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
      (record000_certificates 41) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M025.r0827) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 41) Nonrational.InducedTerminalMatches.M025.r0827
    Nonrational.InducedTerminalMatches.M025.r0827_checked (by decide +kernel)
theorem record000_leaf_checked_42 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
      (record000_certificates 42) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M025.r0828) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 42) Nonrational.InducedTerminalMatches.M025.r0828
    Nonrational.InducedTerminalMatches.M025.r0828_checked (by decide +kernel)
theorem record000_leaf_checked_43 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
      (record000_certificates 43) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M025.r0829) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 43) Nonrational.InducedTerminalMatches.M025.r0829
    Nonrational.InducedTerminalMatches.M025.r0829_checked (by decide +kernel)
theorem record000_leaf_checked_44 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
      (record000_certificates 44) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M025.r0830) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 44) Nonrational.InducedTerminalMatches.M025.r0830
    Nonrational.InducedTerminalMatches.M025.r0830_checked (by decide +kernel)
theorem record000_leaf_checked_45 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
      (record000_certificates 45) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M025.r0831) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 45) Nonrational.InducedTerminalMatches.M025.r0831
    Nonrational.InducedTerminalMatches.M025.r0831_checked (by decide +kernel)
theorem record000_leaf_checked_46 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
      (record000_certificates 46) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M026.r0832) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 46) Nonrational.InducedTerminalMatches.M026.r0832
    Nonrational.InducedTerminalMatches.M026.r0832_checked (by decide +kernel)
theorem record000_leaf_checked_47 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
      (record000_certificates 47) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M026.r0833) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 47) Nonrational.InducedTerminalMatches.M026.r0833
    Nonrational.InducedTerminalMatches.M026.r0833_checked (by decide +kernel)
theorem record000_leaf_checked_48 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 48)
      (record000_certificates 48) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M026.r0834) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 48) Nonrational.InducedTerminalMatches.M026.r0834
    Nonrational.InducedTerminalMatches.M026.r0834_checked (by decide +kernel)
theorem record000_leaf_checked_49 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 49)
      (record000_certificates 49) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M026.r0835) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 49) Nonrational.InducedTerminalMatches.M026.r0835
    Nonrational.InducedTerminalMatches.M026.r0835_checked (by decide +kernel)
theorem record000_leaf_checked_50 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 50)
      (record000_certificates 50) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M026.r0836) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 50) Nonrational.InducedTerminalMatches.M026.r0836
    Nonrational.InducedTerminalMatches.M026.r0836_checked (by decide +kernel)
theorem record000_leaf_checked_51 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 51)
      (record000_certificates 51) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M026.r0837) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 51) Nonrational.InducedTerminalMatches.M026.r0837
    Nonrational.InducedTerminalMatches.M026.r0837_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (Fin.cases record000_leaf_checked_30 (Fin.cases record000_leaf_checked_31 (Fin.cases record000_leaf_checked_32 (Fin.cases record000_leaf_checked_33 (Fin.cases record000_leaf_checked_34 (Fin.cases record000_leaf_checked_35 (Fin.cases record000_leaf_checked_36 (Fin.cases record000_leaf_checked_37 (Fin.cases record000_leaf_checked_38 (Fin.cases record000_leaf_checked_39 (Fin.cases record000_leaf_checked_40 (Fin.cases record000_leaf_checked_41 (Fin.cases record000_leaf_checked_42 (Fin.cases record000_leaf_checked_43 (Fin.cases record000_leaf_checked_44 (Fin.cases record000_leaf_checked_45 (Fin.cases record000_leaf_checked_46 (Fin.cases record000_leaf_checked_47 (Fin.cases record000_leaf_checked_48 (Fin.cases record000_leaf_checked_49 (Fin.cases record000_leaf_checked_50 (Fin.cases record000_leaf_checked_51 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142
