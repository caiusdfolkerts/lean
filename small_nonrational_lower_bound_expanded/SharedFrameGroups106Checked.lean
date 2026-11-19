module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups106Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1075
cert_group_pairs 1075 00000 0 128 128
cert_group_pairs 1075 00128 128 256 128
cert_group_pairs 1075 00256 256 384 128
cert_group_pairs 1075 00384 384 512 128
cert_group_pairs 1075 00512 512 640 128
cert_group_pairs 1075 00640 640 768 128
cert_group_pairs 1075 00768 768 896 128
cert_group_pairs 1075 00896 896 1024 128
cert_group_pairs 1075 01024 1024 1152 128
cert_group_pairs 1075 01152 1152 1280 128
cert_group_pairs 1075 01280 1280 1408 128
cert_group_pairs 1075 01408 1408 1536 128
cert_group_pairs 1075 01536 1536 1664 128
cert_group_pairs 1075 01664 1664 1792 128
cert_group_pairs 1075 01792 1792 1920 128
cert_group_pairs 1075 01920 1920 2048 128
cert_group_pairs 1075 02048 2048 2176 128
cert_group_pairs 1075 02176 2176 2304 128
cert_group_pairs 1075 02304 2304 2432 128
cert_group_pairs 1075 02432 2432 2560 128
cert_group_pairs 1075 02560 2560 2688 128
cert_group_pairs 1075 02688 2688 2813 125
theorem group1075_facts : group1075.Facts FacetUniverses.FullSix0.cells :=
  group1075.facts_of_checks _ group1075_header (interval_append _ 0 1408 2813 (interval_append _ 0 640 1408 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1075_pairs_00000 group1075_pairs_00128) (interval_append _ 256 384 640 group1075_pairs_00256 (interval_append _ 384 512 640 group1075_pairs_00384 group1075_pairs_00512))) (interval_append _ 640 1024 1408 (interval_append _ 640 768 1024 group1075_pairs_00640 (interval_append _ 768 896 1024 group1075_pairs_00768 group1075_pairs_00896)) (interval_append _ 1024 1152 1408 group1075_pairs_01024 (interval_append _ 1152 1280 1408 group1075_pairs_01152 group1075_pairs_01280)))) (interval_append _ 1408 2048 2813 (interval_append _ 1408 1664 2048 (interval_append _ 1408 1536 1664 group1075_pairs_01408 group1075_pairs_01536) (interval_append _ 1664 1792 2048 group1075_pairs_01664 (interval_append _ 1792 1920 2048 group1075_pairs_01792 group1075_pairs_01920))) (interval_append _ 2048 2432 2813 (interval_append _ 2048 2176 2432 group1075_pairs_02048 (interval_append _ 2176 2304 2432 group1075_pairs_02176 group1075_pairs_02304)) (interval_append _ 2432 2560 2813 group1075_pairs_02432 (interval_append _ 2560 2688 2813 group1075_pairs_02560 group1075_pairs_02688)))))
cert_group_header 1076
cert_group_pairs 1076 00000 0 102 102
cert_group_facts_6 1076
cert_group_header 1077
cert_group_pairs 1077 00000 0 128 128
cert_group_pairs 1077 00128 128 256 128
cert_group_pairs 1077 00256 256 269 13
cert_group_facts_2 1077 269
cert_group_header 1078
cert_group_pairs 1078 00000 0 128 128
cert_group_pairs 1078 00128 128 256 128
cert_group_pairs 1078 00256 256 335 79
cert_group_facts_2 1078 335
end Papers.RationalityTen.SharedFrameCatalogue
