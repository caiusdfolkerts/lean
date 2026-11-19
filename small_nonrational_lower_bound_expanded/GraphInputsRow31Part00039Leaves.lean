module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00039Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M079

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00039
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
noncomputable def record003_certificateTable : Table Certificate :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2530))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2531)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2532))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2533))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2534)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2535))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2536))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2537))))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2538))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2539))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2540))))))
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 079 2530
cert_graph_leaf_checked_2 003 1 079 2531
cert_graph_leaf_checked_2 003 2 079 2532
cert_graph_leaf_checked_2 003 3 079 2533
cert_graph_leaf_checked_2 003 4 079 2534
cert_graph_leaf_checked_2 003 5 079 2535
cert_graph_leaf_checked_2 003 6 079 2536
cert_graph_leaf_checked_2 003 7 079 2537
cert_graph_leaf_checked_2 003 8 079 2538
cert_graph_leaf_checked_2 003 9 079 2539
cert_graph_leaf_checked_2 003 10 079 2540
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (Fin.cases record003_leaf_checked_9 (Fin.cases record003_leaf_checked_10 (fun j => Fin.elim0 j))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00039
