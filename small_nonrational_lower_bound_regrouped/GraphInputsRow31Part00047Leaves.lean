module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00047Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M080
public import InducedTerminalMatches.M081

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_2 000 080 080 080 080 2584 2585 2586 2587 2588 2589
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 080 2584
cert_graph_leaf_checked_2 000 1 080 2585
cert_graph_leaf_checked_2 000 2 080 2586
cert_graph_leaf_checked_2 000 3 080 2587
cert_graph_leaf_checked_2 000 4 080 2588
cert_graph_leaf_checked_2 000 5 080 2589
cert_graph_leaf_certificates_checked_6 000
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
noncomputable def record002_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2590))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M080.r2591))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2592))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2593))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2594)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2595))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2596)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2597))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2598))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2599))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2600))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2601)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2602))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2603))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 080 2590
cert_graph_leaf_checked_2 002 1 080 2591
cert_graph_leaf_checked_2 002 2 081 2592
cert_graph_leaf_checked_2 002 3 081 2593
cert_graph_leaf_checked_2 002 4 081 2594
cert_graph_leaf_checked_2 002 5 081 2595
cert_graph_leaf_checked_2 002 6 081 2596
cert_graph_leaf_checked_2 002 7 081 2597
cert_graph_leaf_checked_2 002 8 081 2598
cert_graph_leaf_checked_2 002 9 081 2599
cert_graph_leaf_checked_2 002 10 081 2600
cert_graph_leaf_checked_2 002 11 081 2601
cert_graph_leaf_checked_2 002 12 081 2602
cert_graph_leaf_checked_2 002 13 081 2603
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))
#print axioms record002_leaf_certificates_checked

cert_graph_rawLeaves 003
cert_graph_raw_exact 003
cert_graph_certificateTable_5 003
cert_graph_certificates 003
cert_graph_leaf_checked_3 003
cert_graph_leaf_certificates_checked_7 003
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
cert_graph_certificateTable_10 005 081 081 2604 2605 2606
cert_graph_certificates 005
cert_graph_leaf_checked_2 005 0 081 2604
cert_graph_leaf_checked_2 005 1 081 2605
cert_graph_leaf_checked_2 005 2 081 2606
cert_graph_leaf_certificates_checked_5 005
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

cert_graph_rawLeaves 009
cert_graph_raw_exact 009
cert_graph_certificateTable_5 009
cert_graph_certificates 009
cert_graph_leaf_checked_3 009
cert_graph_leaf_certificates_checked_7 009
#print axioms record009_leaf_certificates_checked

cert_graph_rawLeaves 010
cert_graph_raw_exact 010
cert_graph_certificateTable_5 010
cert_graph_certificates 010
cert_graph_leaf_checked_3 010
cert_graph_leaf_certificates_checked_7 010
#print axioms record010_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047
