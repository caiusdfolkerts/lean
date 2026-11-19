module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups100Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1046
cert_group_pairs 1046 00000 0 128 128
cert_group_pairs 1046 00128 128 256 128
cert_group_pairs 1046 00256 256 384 128
cert_group_pairs 1046 00384 384 512 128
cert_group_pairs 1046 00512 512 640 128
cert_group_pairs 1046 00640 640 768 128
cert_group_pairs 1046 00768 768 896 128
cert_group_pairs 1046 00896 896 1024 128
cert_group_pairs 1046 01024 1024 1152 128
cert_group_pairs 1046 01152 1152 1280 128
cert_group_pairs 1046 01280 1280 1408 128
cert_group_pairs 1046 01408 1408 1536 128
cert_group_pairs 1046 01536 1536 1664 128
cert_group_pairs 1046 01664 1664 1792 128
cert_group_pairs 1046 01792 1792 1920 128
cert_group_pairs 1046 01920 1920 2048 128
cert_group_pairs 1046 02048 2048 2176 128
cert_group_pairs 1046 02176 2176 2275 99
theorem group1046_facts : group1046.Facts FacetUniverses.FullSix0.cells :=
  group1046.facts_of_checks _ group1046_header (interval_append _ 0 1152 2275 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1046_pairs_00000 group1046_pairs_00128) (interval_append _ 256 384 512 group1046_pairs_00256 group1046_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group1046_pairs_00512 group1046_pairs_00640) (interval_append _ 768 896 1152 group1046_pairs_00768 (interval_append _ 896 1024 1152 group1046_pairs_00896 group1046_pairs_01024)))) (interval_append _ 1152 1664 2275 (interval_append _ 1152 1408 1664 (interval_append _ 1152 1280 1408 group1046_pairs_01152 group1046_pairs_01280) (interval_append _ 1408 1536 1664 group1046_pairs_01408 group1046_pairs_01536)) (interval_append _ 1664 1920 2275 (interval_append _ 1664 1792 1920 group1046_pairs_01664 group1046_pairs_01792) (interval_append _ 1920 2048 2275 group1046_pairs_01920 (interval_append _ 2048 2176 2275 group1046_pairs_02048 group1046_pairs_02176)))))
cert_group_header 1047
cert_group_pairs 1047 00000 0 128 128
cert_group_pairs 1047 00128 128 256 128
cert_group_pairs 1047 00256 256 364 108
cert_group_facts_2 1047 364
cert_group_header 1048
cert_group_pairs 1048 00000 0 128 128
cert_group_pairs 1048 00128 128 256 128
cert_group_pairs 1048 00256 256 273 17
cert_group_facts_2 1048 273
cert_group_header 1049
cert_group_pairs 1049 00000 0 128 128
cert_group_pairs 1049 00128 128 256 128
cert_group_pairs 1049 00256 256 384 128
cert_group_pairs 1049 00384 384 403 19
cert_group_facts_4 1049 403
end Papers.RationalityTen.SharedFrameCatalogue
