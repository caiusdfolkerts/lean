module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00090Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M088
public import InducedTerminalMatches.M089

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090
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
cert_graph_certificateTable_3 003 088 088 2834 2835
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 088 2834
cert_graph_leaf_checked_2 003 1 088 2835
cert_graph_leaf_certificates_checked_9 003

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
noncomputable def record004_certificateTable : Table Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2836))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2837))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2838))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2839))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2840))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2841)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2842))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2843))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2844))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2845))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2846))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M088.r2847))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2848))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2849))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2850))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2851))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2852))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2853)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2854))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2855))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2856))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2857))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2858))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M089.r2859)))))))
cert_graph_certificates 004
cert_graph_leaf_checked_2 004 0 088 2836
cert_graph_leaf_checked_2 004 1 088 2837
cert_graph_leaf_checked_2 004 2 088 2838
cert_graph_leaf_checked_2 004 3 088 2839
cert_graph_leaf_checked_2 004 4 088 2840
cert_graph_leaf_checked_2 004 5 088 2841
cert_graph_leaf_checked_2 004 6 088 2842
cert_graph_leaf_checked_2 004 7 088 2843
cert_graph_leaf_checked_2 004 8 088 2844
cert_graph_leaf_checked_2 004 9 088 2845
cert_graph_leaf_checked_2 004 10 088 2846
cert_graph_leaf_checked_2 004 11 088 2847
cert_graph_leaf_checked_2 004 12 089 2848
cert_graph_leaf_checked_2 004 13 089 2849
cert_graph_leaf_checked_2 004 14 089 2850
cert_graph_leaf_checked_2 004 15 089 2851
cert_graph_leaf_checked_2 004 16 089 2852
cert_graph_leaf_checked_2 004 17 089 2853
cert_graph_leaf_checked_2 004 18 089 2854
cert_graph_leaf_checked_2 004 19 089 2855
cert_graph_leaf_checked_2 004 20 089 2856
cert_graph_leaf_checked_2 004 21 089 2857
cert_graph_leaf_checked_2 004 22 089 2858
cert_graph_leaf_checked_2 004 23 089 2859
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (Fin.cases record004_leaf_checked_1 (Fin.cases record004_leaf_checked_2 (Fin.cases record004_leaf_checked_3 (Fin.cases record004_leaf_checked_4 (Fin.cases record004_leaf_checked_5 (Fin.cases record004_leaf_checked_6 (Fin.cases record004_leaf_checked_7 (Fin.cases record004_leaf_checked_8 (Fin.cases record004_leaf_checked_9 (Fin.cases record004_leaf_checked_10 (Fin.cases record004_leaf_checked_11 (Fin.cases record004_leaf_checked_12 (Fin.cases record004_leaf_checked_13 (Fin.cases record004_leaf_checked_14 (Fin.cases record004_leaf_checked_15 (Fin.cases record004_leaf_checked_16 (Fin.cases record004_leaf_checked_17 (Fin.cases record004_leaf_checked_18 (Fin.cases record004_leaf_checked_19 (Fin.cases record004_leaf_checked_20 (Fin.cases record004_leaf_checked_21 (Fin.cases record004_leaf_checked_22 (Fin.cases record004_leaf_checked_23 (fun j => Fin.elim0 j)))))))))))))))))))))))))

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable_10 005 089 089 2860 2861 2862
cert_graph_certificates 005
cert_graph_leaf_checked_2 005 0 089 2860
cert_graph_leaf_checked_2 005 1 089 2861
cert_graph_leaf_checked_2 005 2 089 2862
cert_graph_leaf_certificates_checked_5 005
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090
