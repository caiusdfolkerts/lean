module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups115Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1109
cert_group_pairs 1109 00000 0 128 128
cert_group_pairs 1109 00128 128 256 128
cert_group_pairs 1109 00256 256 384 128
cert_group_pairs 1109 00384 384 512 128
cert_group_pairs 1109 00512 512 640 128
cert_group_pairs 1109 00640 640 768 128
cert_group_pairs 1109 00768 768 896 128
cert_group_pairs 1109 00896 896 1024 128
cert_group_pairs 1109 01024 1024 1152 128
cert_group_pairs 1109 01152 1152 1280 128
cert_group_pairs 1109 01280 1280 1408 128
cert_group_pairs 1109 01408 1408 1536 128
cert_group_pairs 1109 01536 1536 1664 128
cert_group_pairs 1109 01664 1664 1792 128
cert_group_pairs 1109 01792 1792 1920 128
cert_group_pairs 1109 01920 1920 2048 128
cert_group_pairs 1109 02048 2048 2176 128
cert_group_pairs 1109 02176 2176 2304 128
cert_group_pairs 1109 02304 2304 2432 128
cert_group_pairs 1109 02432 2432 2450 18
theorem group1109_facts : group1109.Facts FacetUniverses.FullSix0.cells :=
  group1109.facts_of_checks _ group1109_header (interval_append _ 0 1280 2450 (interval_append _ 0 640 1280 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1109_pairs_00000 group1109_pairs_00128) (interval_append _ 256 384 640 group1109_pairs_00256 (interval_append _ 384 512 640 group1109_pairs_00384 group1109_pairs_00512))) (interval_append _ 640 896 1280 (interval_append _ 640 768 896 group1109_pairs_00640 group1109_pairs_00768) (interval_append _ 896 1024 1280 group1109_pairs_00896 (interval_append _ 1024 1152 1280 group1109_pairs_01024 group1109_pairs_01152)))) (interval_append _ 1280 1920 2450 (interval_append _ 1280 1536 1920 (interval_append _ 1280 1408 1536 group1109_pairs_01280 group1109_pairs_01408) (interval_append _ 1536 1664 1920 group1109_pairs_01536 (interval_append _ 1664 1792 1920 group1109_pairs_01664 group1109_pairs_01792))) (interval_append _ 1920 2176 2450 (interval_append _ 1920 2048 2176 group1109_pairs_01920 group1109_pairs_02048) (interval_append _ 2176 2304 2450 group1109_pairs_02176 (interval_append _ 2304 2432 2450 group1109_pairs_02304 group1109_pairs_02432)))))
end Papers.RationalityTen.SharedFrameCatalogue
