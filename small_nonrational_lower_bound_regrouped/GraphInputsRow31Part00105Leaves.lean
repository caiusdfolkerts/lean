module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00105Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M093
public import InducedTerminalMatches.M094

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_2 000 093 093 093 094 3004 3005 3006 3007 3008 3009
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 093 3004
cert_graph_leaf_checked_2 000 1 093 3005
cert_graph_leaf_checked_2 000 2 093 3006
cert_graph_leaf_checked_2 000 3 093 3007
cert_graph_leaf_checked_2 000 4 094 3008
cert_graph_leaf_checked_2 000 5 094 3009
cert_graph_leaf_certificates_checked_6 000
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
(.leaf (.vertexLink 0))
cert_graph_certificates 003
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  decide +kernel
cert_graph_leaf_certificates_checked_7 003
#print axioms record003_leaf_certificates_checked

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
cert_graph_certificateTable_5 004
cert_graph_certificates 004
cert_graph_leaf_checked_3 004
cert_graph_leaf_certificates_checked_7 004
#print axioms record004_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105
