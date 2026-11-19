module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow24Part00069Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M017

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0556))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0557))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0558))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0559))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0560))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0561)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0562))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0563))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0564))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0565))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0566))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M017.r0567))))))
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 017 0556
cert_graph_leaf_checked_2 000 1 017 0557
cert_graph_leaf_checked_2 000 2 017 0558
cert_graph_leaf_checked_2 000 3 017 0559
cert_graph_leaf_checked_2 000 4 017 0560
cert_graph_leaf_checked_2 000 5 017 0561
cert_graph_leaf_checked_2 000 6 017 0562
cert_graph_leaf_checked_2 000 7 017 0563
cert_graph_leaf_checked_2 000 8 017 0564
cert_graph_leaf_checked_2 000 9 017 0565
cert_graph_leaf_checked_2 000 10 017 0566
cert_graph_leaf_checked_2 000 11 017 0567
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (fun j => Fin.elim0 j)))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069
