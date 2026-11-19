module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00008Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M076
public import InducedTerminalMatches.M077

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_5 000
cert_graph_certificates 000
cert_graph_leaf_checked_3 000
cert_graph_leaf_certificates_checked_7 000

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
noncomputable def record001_certificateTable : Table Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2449))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2450)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2451))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2452))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2453))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2454)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2455))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2456))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2457))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2458))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2459)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2460))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2461))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2462))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M076.r2463)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2464))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2465))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M077.r2466)))))))
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 076 2449
cert_graph_leaf_checked_2 001 1 076 2450
cert_graph_leaf_checked_2 001 2 076 2451
cert_graph_leaf_checked_2 001 3 076 2452
cert_graph_leaf_checked_2 001 4 076 2453
cert_graph_leaf_checked_2 001 5 076 2454
cert_graph_leaf_checked_2 001 6 076 2455
cert_graph_leaf_checked_2 001 7 076 2456
cert_graph_leaf_checked_2 001 8 076 2457
cert_graph_leaf_checked_2 001 9 076 2458
cert_graph_leaf_checked_2 001 10 076 2459
cert_graph_leaf_checked_2 001 11 076 2460
cert_graph_leaf_checked_2 001 12 076 2461
cert_graph_leaf_checked_2 001 13 076 2462
cert_graph_leaf_checked_2 001 14 076 2463
cert_graph_leaf_checked_2 001 15 077 2464
cert_graph_leaf_checked_2 001 16 077 2465
cert_graph_leaf_checked_2 001 17 077 2466
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (Fin.cases record001_leaf_checked_15 (Fin.cases record001_leaf_checked_16 (Fin.cases record001_leaf_checked_17 (fun j => Fin.elim0 j)))))))))))))))))))

cert_graph_rawLeaves 002
cert_graph_raw_exact 002
cert_graph_certificateTable_5 002
cert_graph_certificates 002
cert_graph_leaf_checked_3 002
cert_graph_leaf_certificates_checked_7 002

cert_graph_rawLeaves 003
cert_graph_raw_exact 003
cert_graph_certificateTable_5 003
cert_graph_certificates 003
cert_graph_leaf_checked_3 003
cert_graph_leaf_certificates_checked_7 003

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
cert_graph_certificateTable_5 004
cert_graph_certificates 004
cert_graph_leaf_checked_3 004
cert_graph_leaf_certificates_checked_7 004

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable_5 005
cert_graph_certificates 005
cert_graph_leaf_checked_3 005
cert_graph_leaf_certificates_checked_7 005

cert_graph_rawLeaves 006
cert_graph_raw_exact 006
cert_graph_certificateTable_5 006
cert_graph_certificates 006
cert_graph_leaf_checked_3 006
cert_graph_leaf_certificates_checked_7 006

cert_graph_rawLeaves 007
cert_graph_raw_exact 007
cert_graph_certificateTable_5 007
cert_graph_certificates 007
cert_graph_leaf_checked_3 007
cert_graph_leaf_certificates_checked_7 007

cert_graph_rawLeaves 008
cert_graph_raw_exact 008
cert_graph_certificateTable_5 008
cert_graph_certificates 008
cert_graph_leaf_checked_3 008
cert_graph_leaf_certificates_checked_7 008

cert_graph_rawLeaves 009
cert_graph_raw_exact 009
cert_graph_certificateTable_5 009
cert_graph_certificates 009
cert_graph_leaf_checked_3 009
cert_graph_leaf_certificates_checked_7 009

cert_graph_rawLeaves 010
cert_graph_raw_exact 010
cert_graph_certificateTable_5 010
cert_graph_certificates 010
cert_graph_leaf_checked_3 010
cert_graph_leaf_certificates_checked_7 010
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008
