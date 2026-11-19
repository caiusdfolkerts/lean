module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00022Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M077
public import InducedTerminalMatches.M078

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022
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
cert_graph_certificateTable_5 001
cert_graph_certificates 001
cert_graph_leaf_checked_3 001
cert_graph_leaf_certificates_checked_7 001
#print axioms record001_leaf_certificates_checked

cert_graph_rawLeaves 002
cert_graph_raw_exact 002
cert_graph_certificateTable_5 002
cert_graph_certificates 002
cert_graph_leaf_checked_3 002
cert_graph_leaf_certificates_checked_7 002
#print axioms record002_leaf_certificates_checked

cert_graph_rawLeaves 003
cert_graph_raw_exact 003
noncomputable def record003_certificateTable : Table Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2488))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2489)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2490))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2491))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2492))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2493)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2494))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2495))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2496))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2497))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2498)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2499))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2500))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2501))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2502)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2503))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2504))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2505)))))))
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 077 2488
cert_graph_leaf_checked_2 003 1 077 2489
cert_graph_leaf_checked_2 003 2 077 2490
cert_graph_leaf_checked_2 003 3 077 2491
cert_graph_leaf_checked_2 003 4 077 2492
cert_graph_leaf_checked_2 003 5 077 2493
cert_graph_leaf_checked_2 003 6 077 2494
cert_graph_leaf_checked_2 003 7 077 2495
cert_graph_leaf_checked_2 003 8 078 2496
cert_graph_leaf_checked_2 003 9 078 2497
cert_graph_leaf_checked_2 003 10 078 2498
cert_graph_leaf_checked_2 003 11 078 2499
cert_graph_leaf_checked_2 003 12 078 2500
cert_graph_leaf_checked_2 003 13 078 2501
cert_graph_leaf_checked_2 003 14 078 2502
cert_graph_leaf_checked_2 003 15 078 2503
cert_graph_leaf_checked_2 003 16 078 2504
cert_graph_leaf_checked_2 003 17 078 2505
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (Fin.cases record003_leaf_checked_9 (Fin.cases record003_leaf_checked_10 (Fin.cases record003_leaf_checked_11 (Fin.cases record003_leaf_checked_12 (Fin.cases record003_leaf_checked_13 (Fin.cases record003_leaf_checked_14 (Fin.cases record003_leaf_checked_15 (Fin.cases record003_leaf_checked_16 (Fin.cases record003_leaf_checked_17 (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record003_leaf_certificates_checked

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
cert_graph_certificateTable_5 004
cert_graph_certificates 004
cert_graph_leaf_checked_3 004
cert_graph_leaf_certificates_checked_7 004
#print axioms record004_leaf_certificates_checked

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable 005 078 2506
cert_graph_certificates 005
cert_graph_leaf_checked_2 005 0 078 2506
cert_graph_leaf_certificates_checked_7 005
#print axioms record005_leaf_certificates_checked

cert_graph_rawLeaves 006
cert_graph_raw_exact 006
cert_graph_certificateTable_5 006
cert_graph_certificates 006
cert_graph_leaf_checked_3 006
cert_graph_leaf_certificates_checked_7 006
#print axioms record006_leaf_certificates_checked

cert_graph_rawLeaves 007
cert_graph_raw_exact 007
cert_graph_certificateTable_5 007
cert_graph_certificates 007
cert_graph_leaf_checked_3 007
cert_graph_leaf_certificates_checked_7 007
#print axioms record007_leaf_certificates_checked

cert_graph_rawLeaves 008
cert_graph_raw_exact 008
cert_graph_certificateTable_5 008
cert_graph_certificates 008
cert_graph_leaf_checked_3 008
cert_graph_leaf_certificates_checked_7 008
#print axioms record008_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022
