module
prelude
public meta import LowerSchemas.Leaves
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

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_5 000
cert_graph_certificates 000
cert_graph_leaf_checked_3 000
cert_graph_leaf_certificates_checked_7 000
#print axioms record000_leaf_certificates_checked

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
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
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 073 2367
cert_graph_leaf_checked_2 001 1 074 2368
cert_graph_leaf_checked_2 001 2 074 2369
cert_graph_leaf_checked_2 001 3 074 2370
cert_graph_leaf_checked_2 001 4 074 2371
cert_graph_leaf_checked_2 001 5 074 2372
cert_graph_leaf_checked_2 001 6 074 2373
cert_graph_leaf_checked_2 001 7 074 2374
cert_graph_leaf_checked_2 001 8 074 2375
cert_graph_leaf_checked_2 001 9 074 2376
cert_graph_leaf_checked_2 001 10 074 2377
cert_graph_leaf_checked_2 001 11 074 2378
cert_graph_leaf_checked_2 001 12 074 2379
cert_graph_leaf_checked_2 001 13 074 2380
cert_graph_leaf_checked_2 001 14 074 2381
cert_graph_leaf_checked_2 001 15 074 2382
cert_graph_leaf_checked_2 001 16 074 2383
cert_graph_leaf_checked_2 001 17 074 2384
cert_graph_leaf_checked_2 001 18 074 2385
cert_graph_leaf_checked_2 001 19 074 2386
cert_graph_leaf_checked_2 001 20 074 2387
cert_graph_leaf_checked_2 001 21 074 2388
cert_graph_leaf_checked_2 001 22 074 2389
cert_graph_leaf_checked_2 001 23 074 2390
cert_graph_leaf_checked_2 001 24 074 2391
cert_graph_leaf_checked_2 001 25 074 2392
cert_graph_leaf_checked_2 001 26 074 2393
cert_graph_leaf_checked_2 001 27 074 2394
cert_graph_leaf_checked_2 001 28 074 2395
cert_graph_leaf_checked_2 001 29 074 2396
cert_graph_leaf_checked_2 001 30 074 2397
cert_graph_leaf_checked_2 001 31 074 2398
cert_graph_leaf_checked_2 001 32 074 2399
cert_graph_leaf_checked_2 001 33 075 2400
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (Fin.cases record001_leaf_checked_15 (Fin.cases record001_leaf_checked_16 (Fin.cases record001_leaf_checked_17 (Fin.cases record001_leaf_checked_18 (Fin.cases record001_leaf_checked_19 (Fin.cases record001_leaf_checked_20 (Fin.cases record001_leaf_checked_21 (Fin.cases record001_leaf_checked_22 (Fin.cases record001_leaf_checked_23 (Fin.cases record001_leaf_checked_24 (Fin.cases record001_leaf_checked_25 (Fin.cases record001_leaf_checked_26 (Fin.cases record001_leaf_checked_27 (Fin.cases record001_leaf_checked_28 (Fin.cases record001_leaf_checked_29 (Fin.cases record001_leaf_checked_30 (Fin.cases record001_leaf_checked_31 (Fin.cases record001_leaf_checked_32 (Fin.cases record001_leaf_checked_33 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))
#print axioms record001_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00001
