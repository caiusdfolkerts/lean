module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00049Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M081

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049
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
cert_graph_certificateTable_5 001
cert_graph_certificates 001
cert_graph_leaf_checked_3 001
cert_graph_leaf_certificates_checked_7 001

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
noncomputable def record004_certificateTable : Table Certificate :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2611))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2612)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2613))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2614))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2615)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2616))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2617))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2618))))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2619))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2620))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M081.r2621))))))
cert_graph_certificates 004
cert_graph_leaf_checked_2 004 0 081 2611
cert_graph_leaf_checked_2 004 1 081 2612
cert_graph_leaf_checked_2 004 2 081 2613
cert_graph_leaf_checked_2 004 3 081 2614
cert_graph_leaf_checked_2 004 4 081 2615
cert_graph_leaf_checked_2 004 5 081 2616
cert_graph_leaf_checked_2 004 6 081 2617
cert_graph_leaf_checked_2 004 7 081 2618
cert_graph_leaf_checked_2 004 8 081 2619
cert_graph_leaf_checked_2 004 9 081 2620
cert_graph_leaf_checked_2 004 10 081 2621
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (Fin.cases record004_leaf_checked_1 (Fin.cases record004_leaf_checked_2 (Fin.cases record004_leaf_checked_3 (Fin.cases record004_leaf_checked_4 (Fin.cases record004_leaf_checked_5 (Fin.cases record004_leaf_checked_6 (Fin.cases record004_leaf_checked_7 (Fin.cases record004_leaf_checked_8 (Fin.cases record004_leaf_checked_9 (Fin.cases record004_leaf_checked_10 (fun j => Fin.elim0 j))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049
