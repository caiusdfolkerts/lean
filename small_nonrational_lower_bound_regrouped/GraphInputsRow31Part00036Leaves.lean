module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00036Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M078
public import InducedTerminalMatches.M079

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_9 000 078 078 078 2521 2522 2523 2524 2525 2526 2527
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 078 2521
cert_graph_leaf_checked_2 000 1 078 2522
cert_graph_leaf_checked_2 000 2 078 2523
cert_graph_leaf_checked_2 000 3 078 2524
cert_graph_leaf_checked_2 000 4 078 2525
cert_graph_leaf_checked_2 000 5 078 2526
cert_graph_leaf_checked_2 000 6 078 2527
cert_graph_leaf_certificates_checked_2 000
#print axioms record000_leaf_certificates_checked

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
noncomputable def record001_certificateTable : Table Certificate :=
(.leaf (.vertexLink 0))
cert_graph_certificates 001
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  decide +kernel
cert_graph_leaf_certificates_checked_7 001
#print axioms record001_leaf_certificates_checked

cert_graph_rawLeaves 002
cert_graph_raw_exact 002
cert_graph_certificateTable 002 079 2528
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 079 2528
cert_graph_leaf_certificates_checked_7 002
#print axioms record002_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036
