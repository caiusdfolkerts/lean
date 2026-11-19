module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups098Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1039
cert_group_pairs 1039 00000 0 128 128
cert_group_pairs 1039 00128 128 256 128
cert_group_pairs 1039 00256 256 384 128
cert_group_pairs 1039 00384 384 512 128
cert_group_pairs 1039 00512 512 640 128
cert_group_pairs 1039 00640 640 768 128
cert_group_pairs 1039 00768 768 896 128
cert_group_pairs 1039 00896 896 1024 128
cert_group_pairs 1039 01024 1024 1152 128
cert_group_pairs 1039 01152 1152 1280 128
cert_group_pairs 1039 01280 1280 1408 128
cert_group_pairs 1039 01408 1408 1536 128
cert_group_pairs 1039 01536 1536 1658 122
theorem group1039_facts : group1039.Facts FacetUniverses.FullSix0.cells :=
  group1039.facts_of_checks _ group1039_header (interval_append _ 0 768 1658 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group1039_pairs_00000 (interval_append _ 128 256 384 group1039_pairs_00128 group1039_pairs_00256)) (interval_append _ 384 512 768 group1039_pairs_00384 (interval_append _ 512 640 768 group1039_pairs_00512 group1039_pairs_00640))) (interval_append _ 768 1152 1658 (interval_append _ 768 896 1152 group1039_pairs_00768 (interval_append _ 896 1024 1152 group1039_pairs_00896 group1039_pairs_01024)) (interval_append _ 1152 1408 1658 (interval_append _ 1152 1280 1408 group1039_pairs_01152 group1039_pairs_01280) (interval_append _ 1408 1536 1658 group1039_pairs_01408 group1039_pairs_01536))))
cert_group_header 1040
cert_group_pairs 1040 00000 0 128 128
cert_group_pairs 1040 00128 128 256 128
cert_group_pairs 1040 00256 256 384 128
cert_group_pairs 1040 00384 384 512 128
cert_group_pairs 1040 00512 512 640 128
cert_group_pairs 1040 00640 640 768 128
cert_group_pairs 1040 00768 768 896 128
cert_group_pairs 1040 00896 896 1024 128
cert_group_pairs 1040 01024 1024 1152 128
cert_group_pairs 1040 01152 1152 1160 8
cert_group_facts_3 1040 1160
end Papers.RationalityTen.SharedFrameCatalogue
