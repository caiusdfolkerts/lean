module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00124Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M096
public import InducedTerminalMatches.M097

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124
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
cert_graph_certificateTable_7 001 096 3077 3078 3079 3080 3081
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 096 3077
cert_graph_leaf_checked_2 001 1 096 3078
cert_graph_leaf_checked_2 001 2 096 3079
cert_graph_leaf_checked_2 001 3 096 3080
cert_graph_leaf_checked_2 001 4 096 3081
cert_graph_leaf_certificates_checked_3 001

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
noncomputable def record007_certificateTable : Table Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3082))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3083))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3084))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3085))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3086))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3087)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3088))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3089))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3090))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3091))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3092))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3093))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3094))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3095))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3096))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3097))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3098))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3099)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3100))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3101))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3102))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M096.r3103))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M097.r3104))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M097.r3105)))))))
cert_graph_certificates 007
cert_graph_leaf_checked_2 007 0 096 3082
cert_graph_leaf_checked_2 007 1 096 3083
cert_graph_leaf_checked_2 007 2 096 3084
cert_graph_leaf_checked_2 007 3 096 3085
cert_graph_leaf_checked_2 007 4 096 3086
cert_graph_leaf_checked_2 007 5 096 3087
cert_graph_leaf_checked_2 007 6 096 3088
cert_graph_leaf_checked_2 007 7 096 3089
cert_graph_leaf_checked_2 007 8 096 3090
cert_graph_leaf_checked_2 007 9 096 3091
cert_graph_leaf_checked_2 007 10 096 3092
cert_graph_leaf_checked_2 007 11 096 3093
cert_graph_leaf_checked_2 007 12 096 3094
cert_graph_leaf_checked_2 007 13 096 3095
cert_graph_leaf_checked_2 007 14 096 3096
cert_graph_leaf_checked_2 007 15 096 3097
cert_graph_leaf_checked_2 007 16 096 3098
cert_graph_leaf_checked_2 007 17 096 3099
cert_graph_leaf_checked_2 007 18 096 3100
cert_graph_leaf_checked_2 007 19 096 3101
cert_graph_leaf_checked_2 007 20 096 3102
cert_graph_leaf_checked_2 007 21 096 3103
cert_graph_leaf_checked_2 007 22 097 3104
cert_graph_leaf_checked_2 007 23 097 3105
theorem record007_leaf_certificates_checked : ∀ j : Fin record007.l,
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves j)
      (record007_certificates j) = true :=
  (Fin.cases record007_leaf_checked_0 (Fin.cases record007_leaf_checked_1 (Fin.cases record007_leaf_checked_2 (Fin.cases record007_leaf_checked_3 (Fin.cases record007_leaf_checked_4 (Fin.cases record007_leaf_checked_5 (Fin.cases record007_leaf_checked_6 (Fin.cases record007_leaf_checked_7 (Fin.cases record007_leaf_checked_8 (Fin.cases record007_leaf_checked_9 (Fin.cases record007_leaf_checked_10 (Fin.cases record007_leaf_checked_11 (Fin.cases record007_leaf_checked_12 (Fin.cases record007_leaf_checked_13 (Fin.cases record007_leaf_checked_14 (Fin.cases record007_leaf_checked_15 (Fin.cases record007_leaf_checked_16 (Fin.cases record007_leaf_checked_17 (Fin.cases record007_leaf_checked_18 (Fin.cases record007_leaf_checked_19 (Fin.cases record007_leaf_checked_20 (Fin.cases record007_leaf_checked_21 (Fin.cases record007_leaf_checked_22 (Fin.cases record007_leaf_checked_23 (fun j => Fin.elim0 j)))))))))))))))))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124
