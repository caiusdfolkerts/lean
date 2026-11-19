module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups094Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1007
cert_group_pairs 1007 00000 0 128 128
cert_group_pairs 1007 00128 128 256 128
cert_group_pairs 1007 00256 256 384 128
cert_group_pairs 1007 00384 384 512 128
cert_group_pairs 1007 00512 512 640 128
cert_group_pairs 1007 00640 640 768 128
cert_group_pairs 1007 00768 768 896 128
cert_group_pairs 1007 00896 896 1024 128
cert_group_pairs 1007 01024 1024 1152 128
cert_group_pairs 1007 01152 1152 1280 128
cert_group_pairs 1007 01280 1280 1408 128
cert_group_pairs 1007 01408 1408 1536 128
cert_group_pairs 1007 01536 1536 1664 128
cert_group_pairs 1007 01664 1664 1792 128
cert_group_pairs 1007 01792 1792 1920 128
cert_group_pairs 1007 01920 1920 2048 128
cert_group_pairs 1007 02048 2048 2176 128
cert_group_pairs 1007 02176 2176 2304 128
cert_group_pairs 1007 02304 2304 2432 128
cert_group_pairs 1007 02432 2432 2560 128
cert_group_pairs 1007 02560 2560 2688 128
cert_group_pairs 1007 02688 2688 2816 128
cert_group_pairs 1007 02816 2816 2944 128
cert_group_pairs 1007 02944 2944 3072 128
cert_group_pairs 1007 03072 3072 3200 128
cert_group_pairs 1007 03200 3200 3328 128
cert_group_pairs 1007 03328 3328 3456 128
cert_group_pairs 1007 03456 3456 3584 128
cert_group_pairs 1007 03584 3584 3712 128
cert_group_pairs 1007 03712 3712 3840 128
cert_group_pairs 1007 03840 3840 3968 128
cert_group_pairs 1007 03968 3968 4096 128
cert_group_pairs 1007 04096 4096 4224 128
cert_group_pairs 1007 04224 4224 4352 128
cert_group_pairs 1007 04352 4352 4480 128
cert_group_pairs 1007 04480 4480 4534 54
theorem group1007_facts : group1007.Facts FacetUniverses.FullSix0.cells :=
  group1007.facts_of_checks _ group1007_header (interval_append _ 0 2304 4534 (interval_append _ 0 1152 2304 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1007_pairs_00000 group1007_pairs_00128) (interval_append _ 256 384 512 group1007_pairs_00256 group1007_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group1007_pairs_00512 group1007_pairs_00640) (interval_append _ 768 896 1152 group1007_pairs_00768 (interval_append _ 896 1024 1152 group1007_pairs_00896 group1007_pairs_01024)))) (interval_append _ 1152 1664 2304 (interval_append _ 1152 1408 1664 (interval_append _ 1152 1280 1408 group1007_pairs_01152 group1007_pairs_01280) (interval_append _ 1408 1536 1664 group1007_pairs_01408 group1007_pairs_01536)) (interval_append _ 1664 1920 2304 (interval_append _ 1664 1792 1920 group1007_pairs_01664 group1007_pairs_01792) (interval_append _ 1920 2048 2304 group1007_pairs_01920 (interval_append _ 2048 2176 2304 group1007_pairs_02048 group1007_pairs_02176))))) (interval_append _ 2304 3456 4534 (interval_append _ 2304 2816 3456 (interval_append _ 2304 2560 2816 (interval_append _ 2304 2432 2560 group1007_pairs_02304 group1007_pairs_02432) (interval_append _ 2560 2688 2816 group1007_pairs_02560 group1007_pairs_02688)) (interval_append _ 2816 3072 3456 (interval_append _ 2816 2944 3072 group1007_pairs_02816 group1007_pairs_02944) (interval_append _ 3072 3200 3456 group1007_pairs_03072 (interval_append _ 3200 3328 3456 group1007_pairs_03200 group1007_pairs_03328)))) (interval_append _ 3456 3968 4534 (interval_append _ 3456 3712 3968 (interval_append _ 3456 3584 3712 group1007_pairs_03456 group1007_pairs_03584) (interval_append _ 3712 3840 3968 group1007_pairs_03712 group1007_pairs_03840)) (interval_append _ 3968 4224 4534 (interval_append _ 3968 4096 4224 group1007_pairs_03968 group1007_pairs_04096) (interval_append _ 4224 4352 4534 group1007_pairs_04224 (interval_append _ 4352 4480 4534 group1007_pairs_04352 group1007_pairs_04480))))))
#print axioms group1007_facts
end Papers.RationalityTen.SharedFrameCatalogue
