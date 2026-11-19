module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups091Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1001
cert_group_pairs 1001 00000 0 128 128
cert_group_pairs 1001 00128 128 256 128
cert_group_pairs 1001 00256 256 384 128
cert_group_pairs 1001 00384 384 512 128
cert_group_pairs 1001 00512 512 640 128
cert_group_pairs 1001 00640 640 768 128
cert_group_pairs 1001 00768 768 896 128
cert_group_pairs 1001 00896 896 1024 128
cert_group_pairs 1001 01024 1024 1152 128
cert_group_pairs 1001 01152 1152 1280 128
cert_group_pairs 1001 01280 1280 1408 128
cert_group_pairs 1001 01408 1408 1536 128
cert_group_pairs 1001 01536 1536 1664 128
cert_group_pairs 1001 01664 1664 1792 128
cert_group_pairs 1001 01792 1792 1920 128
cert_group_pairs 1001 01920 1920 2048 128
cert_group_pairs 1001 02048 2048 2176 128
cert_group_pairs 1001 02176 2176 2304 128
cert_group_pairs 1001 02304 2304 2432 128
cert_group_pairs 1001 02432 2432 2560 128
cert_group_pairs 1001 02560 2560 2688 128
cert_group_pairs 1001 02688 2688 2758 70
theorem group1001_facts : group1001.Facts FacetUniverses.FullSix0.cells :=
  group1001.facts_of_checks _ group1001_header (interval_append _ 0 1408 2758 (interval_append _ 0 640 1408 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1001_pairs_00000 group1001_pairs_00128) (interval_append _ 256 384 640 group1001_pairs_00256 (interval_append _ 384 512 640 group1001_pairs_00384 group1001_pairs_00512))) (interval_append _ 640 1024 1408 (interval_append _ 640 768 1024 group1001_pairs_00640 (interval_append _ 768 896 1024 group1001_pairs_00768 group1001_pairs_00896)) (interval_append _ 1024 1152 1408 group1001_pairs_01024 (interval_append _ 1152 1280 1408 group1001_pairs_01152 group1001_pairs_01280)))) (interval_append _ 1408 2048 2758 (interval_append _ 1408 1664 2048 (interval_append _ 1408 1536 1664 group1001_pairs_01408 group1001_pairs_01536) (interval_append _ 1664 1792 2048 group1001_pairs_01664 (interval_append _ 1792 1920 2048 group1001_pairs_01792 group1001_pairs_01920))) (interval_append _ 2048 2432 2758 (interval_append _ 2048 2176 2432 group1001_pairs_02048 (interval_append _ 2176 2304 2432 group1001_pairs_02176 group1001_pairs_02304)) (interval_append _ 2432 2560 2758 group1001_pairs_02432 (interval_append _ 2560 2688 2758 group1001_pairs_02560 group1001_pairs_02688)))))
cert_group_header 1002
cert_group_pairs 1002 00000 0 128 128
cert_group_pairs 1002 00128 128 214 86
cert_group_facts 1002 214
cert_group_header 1003
cert_group_pairs 1003 00000 0 128 128
cert_group_pairs 1003 00128 128 256 128
cert_group_pairs 1003 00256 256 384 128
cert_group_pairs 1003 00384 384 421 37
cert_group_facts_4 1003 421
cert_group_header 1004
cert_group_pairs 1004 00000 0 128 128
cert_group_pairs 1004 00128 128 256 128
cert_group_pairs 1004 00256 256 367 111
cert_group_facts_2 1004 367
end Papers.RationalityTen.SharedFrameCatalogue
