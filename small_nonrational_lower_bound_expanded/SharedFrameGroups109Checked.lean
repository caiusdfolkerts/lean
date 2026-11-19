module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups109Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1081
cert_group_pairs 1081 00000 0 128 128
cert_group_pairs 1081 00128 128 256 128
cert_group_pairs 1081 00256 256 384 128
cert_group_pairs 1081 00384 384 512 128
cert_group_pairs 1081 00512 512 640 128
cert_group_pairs 1081 00640 640 768 128
cert_group_pairs 1081 00768 768 896 128
cert_group_pairs 1081 00896 896 1024 128
cert_group_pairs 1081 01024 1024 1152 128
cert_group_pairs 1081 01152 1152 1280 128
cert_group_pairs 1081 01280 1280 1408 128
cert_group_pairs 1081 01408 1408 1536 128
cert_group_pairs 1081 01536 1536 1664 128
cert_group_pairs 1081 01664 1664 1792 128
cert_group_pairs 1081 01792 1792 1920 128
cert_group_pairs 1081 01920 1920 2048 128
cert_group_pairs 1081 02048 2048 2176 128
cert_group_pairs 1081 02176 2176 2304 128
cert_group_pairs 1081 02304 2304 2432 128
cert_group_pairs 1081 02432 2432 2560 128
cert_group_pairs 1081 02560 2560 2688 128
cert_group_pairs 1081 02688 2688 2816 128
cert_group_pairs 1081 02816 2816 2944 128
cert_group_pairs 1081 02944 2944 3072 128
cert_group_pairs 1081 03072 3072 3200 128
cert_group_pairs 1081 03200 3200 3328 128
cert_group_pairs 1081 03328 3328 3456 128
cert_group_pairs 1081 03456 3456 3584 128
cert_group_pairs 1081 03584 3584 3712 128
cert_group_pairs 1081 03712 3712 3840 128
cert_group_pairs 1081 03840 3840 3968 128
cert_group_pairs 1081 03968 3968 4096 128
cert_group_pairs 1081 04096 4096 4224 128
cert_group_pairs 1081 04224 4224 4352 128
cert_group_pairs 1081 04352 4352 4480 128
cert_group_pairs 1081 04480 4480 4608 128
cert_group_pairs 1081 04608 4608 4736 128
cert_group_pairs 1081 04736 4736 4864 128
cert_group_pairs 1081 04864 4864 4992 128
cert_group_pairs 1081 04992 4992 5120 128
cert_group_pairs 1081 05120 5120 5232 112
theorem group1081_facts : group1081.Facts FacetUniverses.FullSix0.cells :=
  group1081.facts_of_checks _ group1081_header (interval_append _ 0 2560 5232 (interval_append _ 0 1280 2560 (interval_append _ 0 640 1280 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1081_pairs_00000 group1081_pairs_00128) (interval_append _ 256 384 640 group1081_pairs_00256 (interval_append _ 384 512 640 group1081_pairs_00384 group1081_pairs_00512))) (interval_append _ 640 896 1280 (interval_append _ 640 768 896 group1081_pairs_00640 group1081_pairs_00768) (interval_append _ 896 1024 1280 group1081_pairs_00896 (interval_append _ 1024 1152 1280 group1081_pairs_01024 group1081_pairs_01152)))) (interval_append _ 1280 1920 2560 (interval_append _ 1280 1536 1920 (interval_append _ 1280 1408 1536 group1081_pairs_01280 group1081_pairs_01408) (interval_append _ 1536 1664 1920 group1081_pairs_01536 (interval_append _ 1664 1792 1920 group1081_pairs_01664 group1081_pairs_01792))) (interval_append _ 1920 2176 2560 (interval_append _ 1920 2048 2176 group1081_pairs_01920 group1081_pairs_02048) (interval_append _ 2176 2304 2560 group1081_pairs_02176 (interval_append _ 2304 2432 2560 group1081_pairs_02304 group1081_pairs_02432))))) (interval_append _ 2560 3840 5232 (interval_append _ 2560 3200 3840 (interval_append _ 2560 2816 3200 (interval_append _ 2560 2688 2816 group1081_pairs_02560 group1081_pairs_02688) (interval_append _ 2816 2944 3200 group1081_pairs_02816 (interval_append _ 2944 3072 3200 group1081_pairs_02944 group1081_pairs_03072))) (interval_append _ 3200 3456 3840 (interval_append _ 3200 3328 3456 group1081_pairs_03200 group1081_pairs_03328) (interval_append _ 3456 3584 3840 group1081_pairs_03456 (interval_append _ 3584 3712 3840 group1081_pairs_03584 group1081_pairs_03712)))) (interval_append _ 3840 4480 5232 (interval_append _ 3840 4096 4480 (interval_append _ 3840 3968 4096 group1081_pairs_03840 group1081_pairs_03968) (interval_append _ 4096 4224 4480 group1081_pairs_04096 (interval_append _ 4224 4352 4480 group1081_pairs_04224 group1081_pairs_04352))) (interval_append _ 4480 4864 5232 (interval_append _ 4480 4608 4864 group1081_pairs_04480 (interval_append _ 4608 4736 4864 group1081_pairs_04608 group1081_pairs_04736)) (interval_append _ 4864 4992 5232 group1081_pairs_04864 (interval_append _ 4992 5120 5232 group1081_pairs_04992 group1081_pairs_05120))))))
end Papers.RationalityTen.SharedFrameCatalogue
