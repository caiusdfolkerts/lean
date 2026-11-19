module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow24Part00100Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M020

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00100
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
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0658))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0659))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0660))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0661))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0662)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0663))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0664)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0665))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0666))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0667))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0668))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0669)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0670))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M020.r0671))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 020 0658
cert_graph_leaf_checked_2 002 1 020 0659
cert_graph_leaf_checked_2 002 2 020 0660
cert_graph_leaf_checked_2 002 3 020 0661
cert_graph_leaf_checked_2 002 4 020 0662
cert_graph_leaf_checked_2 002 5 020 0663
cert_graph_leaf_checked_2 002 6 020 0664
cert_graph_leaf_checked_2 002 7 020 0665
cert_graph_leaf_checked_2 002 8 020 0666
cert_graph_leaf_checked_2 002 9 020 0667
cert_graph_leaf_checked_2 002 10 020 0668
cert_graph_leaf_checked_2 002 11 020 0669
cert_graph_leaf_checked_2 002 12 020 0670
cert_graph_leaf_checked_2 002 13 020 0671
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00100
