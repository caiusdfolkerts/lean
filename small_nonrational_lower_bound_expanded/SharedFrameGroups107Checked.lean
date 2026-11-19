module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups107Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1079
cert_group_pairs 1079 00000 0 128 128
cert_group_pairs 1079 00128 128 256 128
cert_group_pairs 1079 00256 256 384 128
cert_group_pairs 1079 00384 384 512 128
cert_group_pairs 1079 00512 512 640 128
cert_group_pairs 1079 00640 640 768 128
cert_group_pairs 1079 00768 768 896 128
cert_group_pairs 1079 00896 896 1024 128
cert_group_pairs 1079 01024 1024 1152 128
cert_group_pairs 1079 01152 1152 1280 128
cert_group_pairs 1079 01280 1280 1408 128
cert_group_pairs 1079 01408 1408 1536 128
cert_group_pairs 1079 01536 1536 1664 128
cert_group_pairs 1079 01664 1664 1723 59
theorem group1079_facts : group1079.Facts FacetUniverses.FullSix0.cells :=
  group1079.facts_of_checks _ group1079_header (interval_append _ 0 896 1723 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group1079_pairs_00000 (interval_append _ 128 256 384 group1079_pairs_00128 group1079_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group1079_pairs_00384 group1079_pairs_00512) (interval_append _ 640 768 896 group1079_pairs_00640 group1079_pairs_00768))) (interval_append _ 896 1280 1723 (interval_append _ 896 1024 1280 group1079_pairs_00896 (interval_append _ 1024 1152 1280 group1079_pairs_01024 group1079_pairs_01152)) (interval_append _ 1280 1536 1723 (interval_append _ 1280 1408 1536 group1079_pairs_01280 group1079_pairs_01408) (interval_append _ 1536 1664 1723 group1079_pairs_01536 group1079_pairs_01664))))
end Papers.RationalityTen.SharedFrameCatalogue
