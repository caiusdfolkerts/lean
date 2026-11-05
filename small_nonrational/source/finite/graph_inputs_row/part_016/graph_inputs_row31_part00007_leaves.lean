module
prelude
public import GraphInputsRow31Part00007Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M075
public import InducedTerminalMatches.M076

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2401))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2402))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2403))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2404))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2405))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2406)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2407))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2408))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2409))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2410))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2411))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2412))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2413))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2414))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2415))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2416))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2417))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2418)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2419))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2420))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2421))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2422))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2423))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2424)))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2425))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2426))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2427))))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2428))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2429))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2430)))))
 (.branch 33
 (.branch 31
 (.leaf (.matching Nonrational.InducedTerminalMatches.M075.r2431))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2432))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2433))))
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2434))
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2435))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2436))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2437))
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2438))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2439))))
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2440))
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2441))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2442)))))
 (.branch 45
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2443))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2444))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2445))))
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2446))
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2447))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2448))))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M075.r2401) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M075.r2401
    Nonrational.InducedTerminalMatches.M075.r2401_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M075.r2402) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M075.r2402
    Nonrational.InducedTerminalMatches.M075.r2402_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M075.r2403) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M075.r2403
    Nonrational.InducedTerminalMatches.M075.r2403_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M075.r2404) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M075.r2404
    Nonrational.InducedTerminalMatches.M075.r2404_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M075.r2405) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M075.r2405
    Nonrational.InducedTerminalMatches.M075.r2405_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M075.r2406) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M075.r2406
    Nonrational.InducedTerminalMatches.M075.r2406_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M075.r2407) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M075.r2407
    Nonrational.InducedTerminalMatches.M075.r2407_checked (by decide +kernel)
theorem record000_leaf_checked_7 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
      (record000_certificates 7) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M075.r2408) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 7) Nonrational.InducedTerminalMatches.M075.r2408
    Nonrational.InducedTerminalMatches.M075.r2408_checked (by decide +kernel)
theorem record000_leaf_checked_8 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
      (record000_certificates 8) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M075.r2409) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 8) Nonrational.InducedTerminalMatches.M075.r2409
    Nonrational.InducedTerminalMatches.M075.r2409_checked (by decide +kernel)
theorem record000_leaf_checked_9 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
      (record000_certificates 9) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M075.r2410) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 9) Nonrational.InducedTerminalMatches.M075.r2410
    Nonrational.InducedTerminalMatches.M075.r2410_checked (by decide +kernel)
theorem record000_leaf_checked_10 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
      (record000_certificates 10) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M075.r2411) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 10) Nonrational.InducedTerminalMatches.M075.r2411
    Nonrational.InducedTerminalMatches.M075.r2411_checked (by decide +kernel)
theorem record000_leaf_checked_11 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
      (record000_certificates 11) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M075.r2412) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 11) Nonrational.InducedTerminalMatches.M075.r2412
    Nonrational.InducedTerminalMatches.M075.r2412_checked (by decide +kernel)
theorem record000_leaf_checked_12 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
      (record000_certificates 12) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M075.r2413) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 12) Nonrational.InducedTerminalMatches.M075.r2413
    Nonrational.InducedTerminalMatches.M075.r2413_checked (by decide +kernel)
theorem record000_leaf_checked_13 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
      (record000_certificates 13) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M075.r2414) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 13) Nonrational.InducedTerminalMatches.M075.r2414
    Nonrational.InducedTerminalMatches.M075.r2414_checked (by decide +kernel)
theorem record000_leaf_checked_14 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
      (record000_certificates 14) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M075.r2415) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 14) Nonrational.InducedTerminalMatches.M075.r2415
    Nonrational.InducedTerminalMatches.M075.r2415_checked (by decide +kernel)
theorem record000_leaf_checked_15 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
      (record000_certificates 15) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M075.r2416) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 15) Nonrational.InducedTerminalMatches.M075.r2416
    Nonrational.InducedTerminalMatches.M075.r2416_checked (by decide +kernel)
theorem record000_leaf_checked_16 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
      (record000_certificates 16) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M075.r2417) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 16) Nonrational.InducedTerminalMatches.M075.r2417
    Nonrational.InducedTerminalMatches.M075.r2417_checked (by decide +kernel)
theorem record000_leaf_checked_17 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
      (record000_certificates 17) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M075.r2418) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 17) Nonrational.InducedTerminalMatches.M075.r2418
    Nonrational.InducedTerminalMatches.M075.r2418_checked (by decide +kernel)
theorem record000_leaf_checked_18 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
      (record000_certificates 18) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M075.r2419) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 18) Nonrational.InducedTerminalMatches.M075.r2419
    Nonrational.InducedTerminalMatches.M075.r2419_checked (by decide +kernel)
theorem record000_leaf_checked_19 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
      (record000_certificates 19) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M075.r2420) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 19) Nonrational.InducedTerminalMatches.M075.r2420
    Nonrational.InducedTerminalMatches.M075.r2420_checked (by decide +kernel)
theorem record000_leaf_checked_20 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
      (record000_certificates 20) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M075.r2421) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 20) Nonrational.InducedTerminalMatches.M075.r2421
    Nonrational.InducedTerminalMatches.M075.r2421_checked (by decide +kernel)
theorem record000_leaf_checked_21 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
      (record000_certificates 21) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M075.r2422) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 21) Nonrational.InducedTerminalMatches.M075.r2422
    Nonrational.InducedTerminalMatches.M075.r2422_checked (by decide +kernel)
theorem record000_leaf_checked_22 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
      (record000_certificates 22) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M075.r2423) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 22) Nonrational.InducedTerminalMatches.M075.r2423
    Nonrational.InducedTerminalMatches.M075.r2423_checked (by decide +kernel)
theorem record000_leaf_checked_23 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
      (record000_certificates 23) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M075.r2424) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 23) Nonrational.InducedTerminalMatches.M075.r2424
    Nonrational.InducedTerminalMatches.M075.r2424_checked (by decide +kernel)
theorem record000_leaf_checked_24 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
      (record000_certificates 24) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M075.r2425) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 24) Nonrational.InducedTerminalMatches.M075.r2425
    Nonrational.InducedTerminalMatches.M075.r2425_checked (by decide +kernel)
theorem record000_leaf_checked_25 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
      (record000_certificates 25) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M075.r2426) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 25) Nonrational.InducedTerminalMatches.M075.r2426
    Nonrational.InducedTerminalMatches.M075.r2426_checked (by decide +kernel)
theorem record000_leaf_checked_26 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
      (record000_certificates 26) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M075.r2427) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 26) Nonrational.InducedTerminalMatches.M075.r2427
    Nonrational.InducedTerminalMatches.M075.r2427_checked (by decide +kernel)
theorem record000_leaf_checked_27 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
      (record000_certificates 27) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M075.r2428) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 27) Nonrational.InducedTerminalMatches.M075.r2428
    Nonrational.InducedTerminalMatches.M075.r2428_checked (by decide +kernel)
theorem record000_leaf_checked_28 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
      (record000_certificates 28) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M075.r2429) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 28) Nonrational.InducedTerminalMatches.M075.r2429
    Nonrational.InducedTerminalMatches.M075.r2429_checked (by decide +kernel)
theorem record000_leaf_checked_29 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
      (record000_certificates 29) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M075.r2430) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 29) Nonrational.InducedTerminalMatches.M075.r2430
    Nonrational.InducedTerminalMatches.M075.r2430_checked (by decide +kernel)
theorem record000_leaf_checked_30 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
      (record000_certificates 30) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M075.r2431) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 30) Nonrational.InducedTerminalMatches.M075.r2431
    Nonrational.InducedTerminalMatches.M075.r2431_checked (by decide +kernel)
theorem record000_leaf_checked_31 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
      (record000_certificates 31) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M076.r2432) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 31) Nonrational.InducedTerminalMatches.M076.r2432
    Nonrational.InducedTerminalMatches.M076.r2432_checked (by decide +kernel)
theorem record000_leaf_checked_32 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
      (record000_certificates 32) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M076.r2433) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 32) Nonrational.InducedTerminalMatches.M076.r2433
    Nonrational.InducedTerminalMatches.M076.r2433_checked (by decide +kernel)
theorem record000_leaf_checked_33 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
      (record000_certificates 33) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M076.r2434) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 33) Nonrational.InducedTerminalMatches.M076.r2434
    Nonrational.InducedTerminalMatches.M076.r2434_checked (by decide +kernel)
theorem record000_leaf_checked_34 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
      (record000_certificates 34) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M076.r2435) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 34) Nonrational.InducedTerminalMatches.M076.r2435
    Nonrational.InducedTerminalMatches.M076.r2435_checked (by decide +kernel)
theorem record000_leaf_checked_35 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
      (record000_certificates 35) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M076.r2436) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 35) Nonrational.InducedTerminalMatches.M076.r2436
    Nonrational.InducedTerminalMatches.M076.r2436_checked (by decide +kernel)
theorem record000_leaf_checked_36 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
      (record000_certificates 36) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M076.r2437) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 36) Nonrational.InducedTerminalMatches.M076.r2437
    Nonrational.InducedTerminalMatches.M076.r2437_checked (by decide +kernel)
theorem record000_leaf_checked_37 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
      (record000_certificates 37) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M076.r2438) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 37) Nonrational.InducedTerminalMatches.M076.r2438
    Nonrational.InducedTerminalMatches.M076.r2438_checked (by decide +kernel)
theorem record000_leaf_checked_38 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
      (record000_certificates 38) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M076.r2439) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 38) Nonrational.InducedTerminalMatches.M076.r2439
    Nonrational.InducedTerminalMatches.M076.r2439_checked (by decide +kernel)
theorem record000_leaf_checked_39 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
      (record000_certificates 39) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M076.r2440) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 39) Nonrational.InducedTerminalMatches.M076.r2440
    Nonrational.InducedTerminalMatches.M076.r2440_checked (by decide +kernel)
theorem record000_leaf_checked_40 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
      (record000_certificates 40) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M076.r2441) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 40) Nonrational.InducedTerminalMatches.M076.r2441
    Nonrational.InducedTerminalMatches.M076.r2441_checked (by decide +kernel)
theorem record000_leaf_checked_41 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
      (record000_certificates 41) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M076.r2442) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 41) Nonrational.InducedTerminalMatches.M076.r2442
    Nonrational.InducedTerminalMatches.M076.r2442_checked (by decide +kernel)
theorem record000_leaf_checked_42 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
      (record000_certificates 42) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M076.r2443) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 42) Nonrational.InducedTerminalMatches.M076.r2443
    Nonrational.InducedTerminalMatches.M076.r2443_checked (by decide +kernel)
theorem record000_leaf_checked_43 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
      (record000_certificates 43) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M076.r2444) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 43) Nonrational.InducedTerminalMatches.M076.r2444
    Nonrational.InducedTerminalMatches.M076.r2444_checked (by decide +kernel)
theorem record000_leaf_checked_44 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
      (record000_certificates 44) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M076.r2445) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 44) Nonrational.InducedTerminalMatches.M076.r2445
    Nonrational.InducedTerminalMatches.M076.r2445_checked (by decide +kernel)
theorem record000_leaf_checked_45 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
      (record000_certificates 45) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M076.r2446) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 45) Nonrational.InducedTerminalMatches.M076.r2446
    Nonrational.InducedTerminalMatches.M076.r2446_checked (by decide +kernel)
theorem record000_leaf_checked_46 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
      (record000_certificates 46) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M076.r2447) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 46) Nonrational.InducedTerminalMatches.M076.r2447
    Nonrational.InducedTerminalMatches.M076.r2447_checked (by decide +kernel)
theorem record000_leaf_checked_47 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
      (record000_certificates 47) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M076.r2448) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 47) Nonrational.InducedTerminalMatches.M076.r2448
    Nonrational.InducedTerminalMatches.M076.r2448_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (Fin.cases record000_leaf_checked_30 (Fin.cases record000_leaf_checked_31 (Fin.cases record000_leaf_checked_32 (Fin.cases record000_leaf_checked_33 (Fin.cases record000_leaf_checked_34 (Fin.cases record000_leaf_checked_35 (Fin.cases record000_leaf_checked_36 (Fin.cases record000_leaf_checked_37 (Fin.cases record000_leaf_checked_38 (Fin.cases record000_leaf_checked_39 (Fin.cases record000_leaf_checked_40 (Fin.cases record000_leaf_checked_41 (Fin.cases record000_leaf_checked_42 (Fin.cases record000_leaf_checked_43 (Fin.cases record000_leaf_checked_44 (Fin.cases record000_leaf_checked_45 (Fin.cases record000_leaf_checked_46 (Fin.cases record000_leaf_checked_47 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007
