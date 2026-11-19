module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups103Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1052
cert_group_pairs 1052 00000 0 128 128
cert_group_pairs 1052 00128 128 256 128
cert_group_pairs 1052 00256 256 384 128
cert_group_pairs 1052 00384 384 512 128
cert_group_pairs 1052 00512 512 640 128
cert_group_pairs 1052 00640 640 768 128
cert_group_pairs 1052 00768 768 896 128
cert_group_pairs 1052 00896 896 1024 128
cert_group_pairs 1052 01024 1024 1152 128
cert_group_pairs 1052 01152 1152 1280 128
cert_group_pairs 1052 01280 1280 1408 128
cert_group_pairs 1052 01408 1408 1536 128
cert_group_pairs 1052 01536 1536 1664 128
cert_group_pairs 1052 01664 1664 1792 128
cert_group_pairs 1052 01792 1792 1920 128
cert_group_pairs 1052 01920 1920 2048 128
cert_group_pairs 1052 02048 2048 2176 128
cert_group_pairs 1052 02176 2176 2304 128
cert_group_pairs 1052 02304 2304 2432 128
cert_group_pairs 1052 02432 2432 2560 128
cert_group_pairs 1052 02560 2560 2688 128
cert_group_pairs 1052 02688 2688 2816 128
cert_group_pairs 1052 02816 2816 2944 128
cert_group_pairs 1052 02944 2944 3072 128
cert_group_pairs 1052 03072 3072 3200 128
cert_group_pairs 1052 03200 3200 3328 128
cert_group_pairs 1052 03328 3328 3456 128
cert_group_pairs 1052 03456 3456 3584 128
cert_group_pairs 1052 03584 3584 3712 128
cert_group_pairs 1052 03712 3712 3840 128
cert_group_pairs 1052 03840 3840 3968 128
cert_group_pairs 1052 03968 3968 4096 128
cert_group_pairs 1052 04096 4096 4224 128
cert_group_pairs 1052 04224 4224 4352 128
cert_group_pairs 1052 04352 4352 4480 128
cert_group_pairs 1052 04480 4480 4608 128
cert_group_pairs 1052 04608 4608 4736 128
cert_group_pairs 1052 04736 4736 4864 128
cert_group_pairs 1052 04864 4864 4902 38
theorem group1052_facts : group1052.Facts FacetUniverses.FullSix0.cells :=
  group1052.facts_of_checks _ group1052_header (interval_append _ 0 2432 4902 (interval_append _ 0 1152 2432 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1052_pairs_00000 group1052_pairs_00128) (interval_append _ 256 384 512 group1052_pairs_00256 group1052_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group1052_pairs_00512 group1052_pairs_00640) (interval_append _ 768 896 1152 group1052_pairs_00768 (interval_append _ 896 1024 1152 group1052_pairs_00896 group1052_pairs_01024)))) (interval_append _ 1152 1792 2432 (interval_append _ 1152 1408 1792 (interval_append _ 1152 1280 1408 group1052_pairs_01152 group1052_pairs_01280) (interval_append _ 1408 1536 1792 group1052_pairs_01408 (interval_append _ 1536 1664 1792 group1052_pairs_01536 group1052_pairs_01664))) (interval_append _ 1792 2048 2432 (interval_append _ 1792 1920 2048 group1052_pairs_01792 group1052_pairs_01920) (interval_append _ 2048 2176 2432 group1052_pairs_02048 (interval_append _ 2176 2304 2432 group1052_pairs_02176 group1052_pairs_02304))))) (interval_append _ 2432 3712 4902 (interval_append _ 2432 3072 3712 (interval_append _ 2432 2688 3072 (interval_append _ 2432 2560 2688 group1052_pairs_02432 group1052_pairs_02560) (interval_append _ 2688 2816 3072 group1052_pairs_02688 (interval_append _ 2816 2944 3072 group1052_pairs_02816 group1052_pairs_02944))) (interval_append _ 3072 3328 3712 (interval_append _ 3072 3200 3328 group1052_pairs_03072 group1052_pairs_03200) (interval_append _ 3328 3456 3712 group1052_pairs_03328 (interval_append _ 3456 3584 3712 group1052_pairs_03456 group1052_pairs_03584)))) (interval_append _ 3712 4352 4902 (interval_append _ 3712 3968 4352 (interval_append _ 3712 3840 3968 group1052_pairs_03712 group1052_pairs_03840) (interval_append _ 3968 4096 4352 group1052_pairs_03968 (interval_append _ 4096 4224 4352 group1052_pairs_04096 group1052_pairs_04224))) (interval_append _ 4352 4608 4902 (interval_append _ 4352 4480 4608 group1052_pairs_04352 group1052_pairs_04480) (interval_append _ 4608 4736 4902 group1052_pairs_04608 (interval_append _ 4736 4864 4902 group1052_pairs_04736 group1052_pairs_04864))))))
#print axioms group1052_facts
end Papers.RationalityTen.SharedFrameCatalogue
