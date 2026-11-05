module
prelude
public import GraphInputsRow31Part00001Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M073
public import InducedTerminalMatches.M074
public import InducedTerminalMatches.M075

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00001
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
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M073.r2367))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2368)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2369))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2370))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2371))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2372)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2373))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2374)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2375))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2376)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2377))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2378))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2379))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2380)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2381))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2382))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2383)))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2384))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2385)))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2386))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2387))))
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2388))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2389)))
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2390))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2391)))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2392))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2393)))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2394))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2395))))
 (.branch 31
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2396))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2397)))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2398))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M074.r2399))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2400))))))))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M073.r2367) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M073.r2367
    Nonrational.InducedTerminalMatches.M073.r2367_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M074.r2368) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M074.r2368
    Nonrational.InducedTerminalMatches.M074.r2368_checked (by decide +kernel)
theorem record001_leaf_checked_2 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
      (record001_certificates 2) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M074.r2369) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 2) Nonrational.InducedTerminalMatches.M074.r2369
    Nonrational.InducedTerminalMatches.M074.r2369_checked (by decide +kernel)
theorem record001_leaf_checked_3 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
      (record001_certificates 3) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M074.r2370) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 3) Nonrational.InducedTerminalMatches.M074.r2370
    Nonrational.InducedTerminalMatches.M074.r2370_checked (by decide +kernel)
theorem record001_leaf_checked_4 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
      (record001_certificates 4) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M074.r2371) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 4) Nonrational.InducedTerminalMatches.M074.r2371
    Nonrational.InducedTerminalMatches.M074.r2371_checked (by decide +kernel)
theorem record001_leaf_checked_5 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
      (record001_certificates 5) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M074.r2372) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 5) Nonrational.InducedTerminalMatches.M074.r2372
    Nonrational.InducedTerminalMatches.M074.r2372_checked (by decide +kernel)
theorem record001_leaf_checked_6 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
      (record001_certificates 6) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M074.r2373) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 6) Nonrational.InducedTerminalMatches.M074.r2373
    Nonrational.InducedTerminalMatches.M074.r2373_checked (by decide +kernel)
theorem record001_leaf_checked_7 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
      (record001_certificates 7) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M074.r2374) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 7) Nonrational.InducedTerminalMatches.M074.r2374
    Nonrational.InducedTerminalMatches.M074.r2374_checked (by decide +kernel)
theorem record001_leaf_checked_8 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
      (record001_certificates 8) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M074.r2375) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 8) Nonrational.InducedTerminalMatches.M074.r2375
    Nonrational.InducedTerminalMatches.M074.r2375_checked (by decide +kernel)
theorem record001_leaf_checked_9 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
      (record001_certificates 9) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M074.r2376) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 9) Nonrational.InducedTerminalMatches.M074.r2376
    Nonrational.InducedTerminalMatches.M074.r2376_checked (by decide +kernel)
theorem record001_leaf_checked_10 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
      (record001_certificates 10) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M074.r2377) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 10) Nonrational.InducedTerminalMatches.M074.r2377
    Nonrational.InducedTerminalMatches.M074.r2377_checked (by decide +kernel)
theorem record001_leaf_checked_11 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
      (record001_certificates 11) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M074.r2378) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 11) Nonrational.InducedTerminalMatches.M074.r2378
    Nonrational.InducedTerminalMatches.M074.r2378_checked (by decide +kernel)
theorem record001_leaf_checked_12 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 12)
      (record001_certificates 12) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M074.r2379) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 12) Nonrational.InducedTerminalMatches.M074.r2379
    Nonrational.InducedTerminalMatches.M074.r2379_checked (by decide +kernel)
theorem record001_leaf_checked_13 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 13)
      (record001_certificates 13) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M074.r2380) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 13) Nonrational.InducedTerminalMatches.M074.r2380
    Nonrational.InducedTerminalMatches.M074.r2380_checked (by decide +kernel)
theorem record001_leaf_checked_14 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 14)
      (record001_certificates 14) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M074.r2381) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 14) Nonrational.InducedTerminalMatches.M074.r2381
    Nonrational.InducedTerminalMatches.M074.r2381_checked (by decide +kernel)
theorem record001_leaf_checked_15 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 15)
      (record001_certificates 15) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M074.r2382) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 15) Nonrational.InducedTerminalMatches.M074.r2382
    Nonrational.InducedTerminalMatches.M074.r2382_checked (by decide +kernel)
theorem record001_leaf_checked_16 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 16)
      (record001_certificates 16) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M074.r2383) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 16) Nonrational.InducedTerminalMatches.M074.r2383
    Nonrational.InducedTerminalMatches.M074.r2383_checked (by decide +kernel)
theorem record001_leaf_checked_17 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 17)
      (record001_certificates 17) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M074.r2384) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 17) Nonrational.InducedTerminalMatches.M074.r2384
    Nonrational.InducedTerminalMatches.M074.r2384_checked (by decide +kernel)
theorem record001_leaf_checked_18 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 18)
      (record001_certificates 18) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M074.r2385) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 18) Nonrational.InducedTerminalMatches.M074.r2385
    Nonrational.InducedTerminalMatches.M074.r2385_checked (by decide +kernel)
theorem record001_leaf_checked_19 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 19)
      (record001_certificates 19) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M074.r2386) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 19) Nonrational.InducedTerminalMatches.M074.r2386
    Nonrational.InducedTerminalMatches.M074.r2386_checked (by decide +kernel)
theorem record001_leaf_checked_20 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 20)
      (record001_certificates 20) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M074.r2387) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 20) Nonrational.InducedTerminalMatches.M074.r2387
    Nonrational.InducedTerminalMatches.M074.r2387_checked (by decide +kernel)
theorem record001_leaf_checked_21 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 21)
      (record001_certificates 21) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M074.r2388) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 21) Nonrational.InducedTerminalMatches.M074.r2388
    Nonrational.InducedTerminalMatches.M074.r2388_checked (by decide +kernel)
theorem record001_leaf_checked_22 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 22)
      (record001_certificates 22) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M074.r2389) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 22) Nonrational.InducedTerminalMatches.M074.r2389
    Nonrational.InducedTerminalMatches.M074.r2389_checked (by decide +kernel)
theorem record001_leaf_checked_23 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 23)
      (record001_certificates 23) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M074.r2390) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 23) Nonrational.InducedTerminalMatches.M074.r2390
    Nonrational.InducedTerminalMatches.M074.r2390_checked (by decide +kernel)
theorem record001_leaf_checked_24 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 24)
      (record001_certificates 24) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M074.r2391) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 24) Nonrational.InducedTerminalMatches.M074.r2391
    Nonrational.InducedTerminalMatches.M074.r2391_checked (by decide +kernel)
theorem record001_leaf_checked_25 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 25)
      (record001_certificates 25) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M074.r2392) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 25) Nonrational.InducedTerminalMatches.M074.r2392
    Nonrational.InducedTerminalMatches.M074.r2392_checked (by decide +kernel)
theorem record001_leaf_checked_26 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 26)
      (record001_certificates 26) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M074.r2393) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 26) Nonrational.InducedTerminalMatches.M074.r2393
    Nonrational.InducedTerminalMatches.M074.r2393_checked (by decide +kernel)
theorem record001_leaf_checked_27 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 27)
      (record001_certificates 27) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M074.r2394) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 27) Nonrational.InducedTerminalMatches.M074.r2394
    Nonrational.InducedTerminalMatches.M074.r2394_checked (by decide +kernel)
theorem record001_leaf_checked_28 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 28)
      (record001_certificates 28) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M074.r2395) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 28) Nonrational.InducedTerminalMatches.M074.r2395
    Nonrational.InducedTerminalMatches.M074.r2395_checked (by decide +kernel)
theorem record001_leaf_checked_29 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 29)
      (record001_certificates 29) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M074.r2396) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 29) Nonrational.InducedTerminalMatches.M074.r2396
    Nonrational.InducedTerminalMatches.M074.r2396_checked (by decide +kernel)
theorem record001_leaf_checked_30 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 30)
      (record001_certificates 30) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M074.r2397) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 30) Nonrational.InducedTerminalMatches.M074.r2397
    Nonrational.InducedTerminalMatches.M074.r2397_checked (by decide +kernel)
theorem record001_leaf_checked_31 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 31)
      (record001_certificates 31) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M074.r2398) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 31) Nonrational.InducedTerminalMatches.M074.r2398
    Nonrational.InducedTerminalMatches.M074.r2398_checked (by decide +kernel)
theorem record001_leaf_checked_32 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 32)
      (record001_certificates 32) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M074.r2399) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 32) Nonrational.InducedTerminalMatches.M074.r2399
    Nonrational.InducedTerminalMatches.M074.r2399_checked (by decide +kernel)
theorem record001_leaf_checked_33 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 33)
      (record001_certificates 33) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M075.r2400) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 33) Nonrational.InducedTerminalMatches.M075.r2400
    Nonrational.InducedTerminalMatches.M075.r2400_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (Fin.cases record001_leaf_checked_15 (Fin.cases record001_leaf_checked_16 (Fin.cases record001_leaf_checked_17 (Fin.cases record001_leaf_checked_18 (Fin.cases record001_leaf_checked_19 (Fin.cases record001_leaf_checked_20 (Fin.cases record001_leaf_checked_21 (Fin.cases record001_leaf_checked_22 (Fin.cases record001_leaf_checked_23 (Fin.cases record001_leaf_checked_24 (Fin.cases record001_leaf_checked_25 (Fin.cases record001_leaf_checked_26 (Fin.cases record001_leaf_checked_27 (Fin.cases record001_leaf_checked_28 (Fin.cases record001_leaf_checked_29 (Fin.cases record001_leaf_checked_30 (Fin.cases record001_leaf_checked_31 (Fin.cases record001_leaf_checked_32 (Fin.cases record001_leaf_checked_33 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))
#print axioms record001_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00001
