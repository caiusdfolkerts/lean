module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00065Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M082

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065
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
noncomputable def record002_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2633))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2634))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2635))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2636))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2637)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2638))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2639)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2640))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2641))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2642))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2643))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2644)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2645))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M082.r2646))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 082 2633
cert_graph_leaf_checked_2 002 1 082 2634
cert_graph_leaf_checked_2 002 2 082 2635
cert_graph_leaf_checked_2 002 3 082 2636
cert_graph_leaf_checked_2 002 4 082 2637
cert_graph_leaf_checked_2 002 5 082 2638
cert_graph_leaf_checked_2 002 6 082 2639
cert_graph_leaf_checked_2 002 7 082 2640
cert_graph_leaf_checked_2 002 8 082 2641
cert_graph_leaf_checked_2 002 9 082 2642
cert_graph_leaf_checked_2 002 10 082 2643
cert_graph_leaf_checked_2 002 11 082 2644
cert_graph_leaf_checked_2 002 12 082 2645
cert_graph_leaf_checked_2 002 13 082 2646
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00065
