module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups111Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1095
cert_group_pairs 1095 00000 0 128 128
cert_group_pairs 1095 00128 128 238 110
cert_group_facts 1095 238
cert_group_header 1096
cert_group_pairs 1096 00000 0 128 128
cert_group_pairs 1096 00128 128 256 128
cert_group_pairs 1096 00256 256 265 9
cert_group_facts_2 1096 265
cert_group_header 1097
cert_group_pairs 1097 00000 0 128 128
cert_group_pairs 1097 00128 128 256 128
cert_group_pairs 1097 00256 256 322 66
cert_group_facts_2 1097 322
cert_group_header 1098
cert_group_pairs 1098 00000 0 128 128
cert_group_pairs 1098 00128 128 256 128
cert_group_pairs 1098 00256 256 384 128
cert_group_pairs 1098 00384 384 512 128
cert_group_pairs 1098 00512 512 640 128
cert_group_pairs 1098 00640 640 768 128
cert_group_pairs 1098 00768 768 896 128
cert_group_pairs 1098 00896 896 1024 128
cert_group_pairs 1098 01024 1024 1152 128
cert_group_pairs 1098 01152 1152 1280 128
cert_group_pairs 1098 01280 1280 1408 128
cert_group_pairs 1098 01408 1408 1536 128
cert_group_pairs 1098 01536 1536 1664 128
cert_group_pairs 1098 01664 1664 1792 128
cert_group_pairs 1098 01792 1792 1793 1
theorem group1098_facts : group1098.Facts FacetUniverses.FullSix0.cells :=
  group1098.facts_of_checks _ group1098_header (interval_append _ 0 896 1793 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group1098_pairs_00000 (interval_append _ 128 256 384 group1098_pairs_00128 group1098_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group1098_pairs_00384 group1098_pairs_00512) (interval_append _ 640 768 896 group1098_pairs_00640 group1098_pairs_00768))) (interval_append _ 896 1408 1793 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group1098_pairs_00896 group1098_pairs_01024) (interval_append _ 1152 1280 1408 group1098_pairs_01152 group1098_pairs_01280)) (interval_append _ 1408 1664 1793 (interval_append _ 1408 1536 1664 group1098_pairs_01408 group1098_pairs_01536) (interval_append _ 1664 1792 1793 group1098_pairs_01664 group1098_pairs_01792))))
end Papers.RationalityTen.SharedFrameCatalogue
