module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00094Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M091

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094
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
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2917))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2918))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2919))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2920))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2921)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2922))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2923)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2924))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2925)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2926))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2927))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2928))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2929)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2930))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M091.r2931))))))
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 091 2917
cert_graph_leaf_checked_2 001 1 091 2918
cert_graph_leaf_checked_2 001 2 091 2919
cert_graph_leaf_checked_2 001 3 091 2920
cert_graph_leaf_checked_2 001 4 091 2921
cert_graph_leaf_checked_2 001 5 091 2922
cert_graph_leaf_checked_2 001 6 091 2923
cert_graph_leaf_checked_2 001 7 091 2924
cert_graph_leaf_checked_2 001 8 091 2925
cert_graph_leaf_checked_2 001 9 091 2926
cert_graph_leaf_checked_2 001 10 091 2927
cert_graph_leaf_checked_2 001 11 091 2928
cert_graph_leaf_checked_2 001 12 091 2929
cert_graph_leaf_checked_2 001 13 091 2930
cert_graph_leaf_checked_2 001 14 091 2931
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (fun j => Fin.elim0 j))))))))))))))))

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

cert_graph_rawLeaves 011
cert_graph_raw_exact 011
cert_graph_certificateTable_5 011
cert_graph_certificates 011
cert_graph_leaf_checked_3 011
cert_graph_leaf_certificates_checked_7 011

cert_graph_rawLeaves 012
cert_graph_raw_exact 012
cert_graph_certificateTable_5 012
cert_graph_certificates 012
cert_graph_leaf_checked_3 012
cert_graph_leaf_certificates_checked_7 012

cert_graph_rawLeaves 013
cert_graph_raw_exact 013
cert_graph_certificateTable_5 013
cert_graph_certificates 013
cert_graph_leaf_checked_3 013
cert_graph_leaf_certificates_checked_7 013

cert_graph_rawLeaves 014
cert_graph_raw_exact 014
cert_graph_certificateTable_3 014 091 091 2932 2933
cert_graph_certificates 014
cert_graph_leaf_checked_2 014 0 091 2932
cert_graph_leaf_checked_2 014 1 091 2933
cert_graph_leaf_certificates_checked_9 014
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094
