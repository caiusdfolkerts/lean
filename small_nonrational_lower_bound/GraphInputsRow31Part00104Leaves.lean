module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00104Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M093

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
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
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2977))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2978)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2979))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2980))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2981))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2982)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2983))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2984)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2985))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2986)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2987))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2988))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2989))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2990)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2991))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2992))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M093.r2993)))))))
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 093 2977
cert_graph_leaf_checked_2 003 1 093 2978
cert_graph_leaf_checked_2 003 2 093 2979
cert_graph_leaf_checked_2 003 3 093 2980
cert_graph_leaf_checked_2 003 4 093 2981
cert_graph_leaf_checked_2 003 5 093 2982
cert_graph_leaf_checked_2 003 6 093 2983
cert_graph_leaf_checked_2 003 7 093 2984
cert_graph_leaf_checked_2 003 8 093 2985
cert_graph_leaf_checked_2 003 9 093 2986
cert_graph_leaf_checked_2 003 10 093 2987
cert_graph_leaf_checked_2 003 11 093 2988
cert_graph_leaf_checked_2 003 12 093 2989
cert_graph_leaf_checked_2 003 13 093 2990
cert_graph_leaf_checked_2 003 14 093 2991
cert_graph_leaf_checked_2 003 15 093 2992
cert_graph_leaf_checked_2 003 16 093 2993
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (Fin.cases record003_leaf_checked_9 (Fin.cases record003_leaf_checked_10 (Fin.cases record003_leaf_checked_11 (Fin.cases record003_leaf_checked_12 (Fin.cases record003_leaf_checked_13 (Fin.cases record003_leaf_checked_14 (Fin.cases record003_leaf_checked_15 (Fin.cases record003_leaf_checked_16 (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record003_leaf_certificates_checked

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
cert_graph_certificateTable_2 004 093 093 093 093 2994 2995 2996 2997 2998 2999
cert_graph_certificates 004
cert_graph_leaf_checked_2 004 0 093 2994
cert_graph_leaf_checked_2 004 1 093 2995
cert_graph_leaf_checked_2 004 2 093 2996
cert_graph_leaf_checked_2 004 3 093 2997
cert_graph_leaf_checked_2 004 4 093 2998
cert_graph_leaf_checked_2 004 5 093 2999
cert_graph_leaf_certificates_checked_6 004
#print axioms record004_leaf_certificates_checked

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable_8 005 093 093 093 3000 3001 3002 3003
cert_graph_certificates 005
cert_graph_leaf_checked_2 005 0 093 3000
cert_graph_leaf_checked_2 005 1 093 3001
cert_graph_leaf_checked_2 005 2 093 3002
cert_graph_leaf_checked_2 005 3 093 3003
cert_graph_leaf_certificates_checked_4 005
#print axioms record005_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
