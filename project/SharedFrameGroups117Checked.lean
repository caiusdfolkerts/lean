module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups117Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1111
cert_group_pairs 1111 00000 0 128 128
cert_group_pairs 1111 00128 128 256 128
cert_group_pairs 1111 00256 256 384 128
cert_group_pairs 1111 00384 384 512 128
cert_group_pairs 1111 00512 512 640 128
cert_group_pairs 1111 00640 640 698 58
theorem group1111_facts : group1111.Facts FacetUniverses.FullSix0.cells :=
  group1111.facts_of_checks _ group1111_header (interval_append _ 0 384 698 (interval_append _ 0 128 384 group1111_pairs_00000 (interval_append _ 128 256 384 group1111_pairs_00128 group1111_pairs_00256)) (interval_append _ 384 512 698 group1111_pairs_00384 (interval_append _ 512 640 698 group1111_pairs_00512 group1111_pairs_00640)))
#print axioms group1111_facts
cert_group_header 1112
cert_group_pairs 1112 00000 0 128 128
cert_group_pairs 1112 00128 128 256 128
cert_group_pairs 1112 00256 256 384 128
cert_group_pairs 1112 00384 384 512 128
cert_group_pairs 1112 00512 512 640 128
cert_group_pairs 1112 00640 640 768 128
cert_group_pairs 1112 00768 768 896 128
cert_group_pairs 1112 00896 896 1024 128
cert_group_pairs 1112 01024 1024 1079 55
theorem group1112_facts : group1112.Facts FacetUniverses.FullSix0.cells :=
  group1112.facts_of_checks _ group1112_header (interval_append _ 0 512 1079 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1112_pairs_00000 group1112_pairs_00128) (interval_append _ 256 384 512 group1112_pairs_00256 group1112_pairs_00384)) (interval_append _ 512 768 1079 (interval_append _ 512 640 768 group1112_pairs_00512 group1112_pairs_00640) (interval_append _ 768 896 1079 group1112_pairs_00768 (interval_append _ 896 1024 1079 group1112_pairs_00896 group1112_pairs_01024))))
#print axioms group1112_facts
cert_group_header 1113
cert_group_pairs 1113 00000 0 128 128
cert_group_pairs 1113 00128 128 256 128
cert_group_pairs 1113 00256 256 384 128
cert_group_pairs 1113 00384 384 512 128
cert_group_pairs 1113 00512 512 640 128
cert_group_pairs 1113 00640 640 768 128
cert_group_pairs 1113 00768 768 896 128
cert_group_pairs 1113 00896 896 1024 128
cert_group_pairs 1113 01024 1024 1152 128
cert_group_pairs 1113 01152 1152 1258 106
cert_group_facts_3 1113 1258
#print axioms group1113_facts
end Papers.RationalityTen.SharedFrameCatalogue
