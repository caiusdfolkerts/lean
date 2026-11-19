module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00074Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M085
public import InducedTerminalMatches.M086

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074
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
cert_graph_certificateTable 003 085 2738
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 085 2738
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
noncomputable def record009_certificateTable : Table Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2739))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2740)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2741))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2742))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2743))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2744)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2745))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2746)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2747))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2748)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2749))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2750))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2751))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2752)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2753))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M086.r2754))))))
cert_graph_certificates 009
cert_graph_leaf_checked_2 009 0 085 2739
cert_graph_leaf_checked_2 009 1 085 2740
cert_graph_leaf_checked_2 009 2 085 2741
cert_graph_leaf_checked_2 009 3 085 2742
cert_graph_leaf_checked_2 009 4 085 2743
cert_graph_leaf_checked_2 009 5 085 2744
cert_graph_leaf_checked_2 009 6 085 2745
cert_graph_leaf_checked_2 009 7 085 2746
cert_graph_leaf_checked_2 009 8 085 2747
cert_graph_leaf_checked_2 009 9 085 2748
cert_graph_leaf_checked_2 009 10 085 2749
cert_graph_leaf_checked_2 009 11 085 2750
cert_graph_leaf_checked_2 009 12 085 2751
cert_graph_leaf_checked_2 009 13 086 2752
cert_graph_leaf_checked_2 009 14 086 2753
cert_graph_leaf_checked_2 009 15 086 2754
theorem record009_leaf_certificates_checked : ∀ j : Fin record009.l,
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves j)
      (record009_certificates j) = true :=
  (Fin.cases record009_leaf_checked_0 (Fin.cases record009_leaf_checked_1 (Fin.cases record009_leaf_checked_2 (Fin.cases record009_leaf_checked_3 (Fin.cases record009_leaf_checked_4 (Fin.cases record009_leaf_checked_5 (Fin.cases record009_leaf_checked_6 (Fin.cases record009_leaf_checked_7 (Fin.cases record009_leaf_checked_8 (Fin.cases record009_leaf_checked_9 (Fin.cases record009_leaf_checked_10 (Fin.cases record009_leaf_checked_11 (Fin.cases record009_leaf_checked_12 (Fin.cases record009_leaf_checked_13 (Fin.cases record009_leaf_checked_14 (Fin.cases record009_leaf_checked_15 (fun j => Fin.elim0 j)))))))))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074
