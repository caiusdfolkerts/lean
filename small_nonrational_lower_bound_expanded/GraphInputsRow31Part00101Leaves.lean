module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00101Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M092

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101
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
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2958))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2959))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2960))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2961))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2962))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2963)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2964))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2965))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2966))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2967))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2968))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M092.r2969))))))
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 092 2958
cert_graph_leaf_checked_2 001 1 092 2959
cert_graph_leaf_checked_2 001 2 092 2960
cert_graph_leaf_checked_2 001 3 092 2961
cert_graph_leaf_checked_2 001 4 092 2962
cert_graph_leaf_checked_2 001 5 092 2963
cert_graph_leaf_checked_2 001 6 092 2964
cert_graph_leaf_checked_2 001 7 092 2965
cert_graph_leaf_checked_2 001 8 092 2966
cert_graph_leaf_checked_2 001 9 092 2967
cert_graph_leaf_checked_2 001 10 092 2968
cert_graph_leaf_checked_2 001 11 092 2969
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (fun j => Fin.elim0 j)))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00101
