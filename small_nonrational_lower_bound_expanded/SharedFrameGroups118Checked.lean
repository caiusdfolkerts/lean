module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups118Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1114
cert_group_pairs 1114 00000 0 128 128
cert_group_pairs 1114 00128 128 256 128
cert_group_pairs 1114 00256 256 384 128
cert_group_pairs 1114 00384 384 512 128
cert_group_pairs 1114 00512 512 640 128
cert_group_pairs 1114 00640 640 768 128
cert_group_pairs 1114 00768 768 896 128
cert_group_pairs 1114 00896 896 1024 128
cert_group_pairs 1114 01024 1024 1152 128
cert_group_pairs 1114 01152 1152 1280 128
cert_group_pairs 1114 01280 1280 1408 128
cert_group_pairs 1114 01408 1408 1536 128
cert_group_pairs 1114 01536 1536 1664 128
cert_group_pairs 1114 01664 1664 1792 128
cert_group_pairs 1114 01792 1792 1920 128
cert_group_pairs 1114 01920 1920 2048 128
cert_group_pairs 1114 02048 2048 2176 128
cert_group_pairs 1114 02176 2176 2304 128
cert_group_pairs 1114 02304 2304 2432 128
cert_group_pairs 1114 02432 2432 2560 128
cert_group_pairs 1114 02560 2560 2688 128
cert_group_pairs 1114 02688 2688 2816 128
cert_group_pairs 1114 02816 2816 2944 128
cert_group_pairs 1114 02944 2944 3072 128
cert_group_pairs 1114 03072 3072 3200 128
cert_group_pairs 1114 03200 3200 3328 128
cert_group_pairs 1114 03328 3328 3456 128
cert_group_pairs 1114 03456 3456 3584 128
cert_group_pairs 1114 03584 3584 3712 128
cert_group_pairs 1114 03712 3712 3840 128
cert_group_pairs 1114 03840 3840 3968 128
cert_group_pairs 1114 03968 3968 4096 128
cert_group_pairs 1114 04096 4096 4224 128
cert_group_pairs 1114 04224 4224 4352 128
cert_group_pairs 1114 04352 4352 4480 128
cert_group_pairs 1114 04480 4480 4608 128
cert_group_pairs 1114 04608 4608 4736 128
cert_group_pairs 1114 04736 4736 4864 128
cert_group_pairs 1114 04864 4864 4992 128
cert_group_pairs 1114 04992 4992 5120 128
cert_group_pairs 1114 05120 5120 5248 128
cert_group_pairs 1114 05248 5248 5376 128
cert_group_pairs 1114 05376 5376 5504 128
cert_group_pairs 1114 05504 5504 5632 128
cert_group_pairs 1114 05632 5632 5760 128
cert_group_pairs 1114 05760 5760 5888 128
cert_group_pairs 1114 05888 5888 5945 57
theorem group1114_facts : group1114.Facts FacetUniverses.FullSix0.cells :=
  group1114.facts_of_checks _ group1114_header (interval_append _ 0 2944 5945 (interval_append _ 0 1408 2944 (interval_append _ 0 640 1408 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1114_pairs_00000 group1114_pairs_00128) (interval_append _ 256 384 640 group1114_pairs_00256 (interval_append _ 384 512 640 group1114_pairs_00384 group1114_pairs_00512))) (interval_append _ 640 1024 1408 (interval_append _ 640 768 1024 group1114_pairs_00640 (interval_append _ 768 896 1024 group1114_pairs_00768 group1114_pairs_00896)) (interval_append _ 1024 1152 1408 group1114_pairs_01024 (interval_append _ 1152 1280 1408 group1114_pairs_01152 group1114_pairs_01280)))) (interval_append _ 1408 2176 2944 (interval_append _ 1408 1792 2176 (interval_append _ 1408 1536 1792 group1114_pairs_01408 (interval_append _ 1536 1664 1792 group1114_pairs_01536 group1114_pairs_01664)) (interval_append _ 1792 1920 2176 group1114_pairs_01792 (interval_append _ 1920 2048 2176 group1114_pairs_01920 group1114_pairs_02048))) (interval_append _ 2176 2560 2944 (interval_append _ 2176 2304 2560 group1114_pairs_02176 (interval_append _ 2304 2432 2560 group1114_pairs_02304 group1114_pairs_02432)) (interval_append _ 2560 2688 2944 group1114_pairs_02560 (interval_append _ 2688 2816 2944 group1114_pairs_02688 group1114_pairs_02816))))) (interval_append _ 2944 4480 5945 (interval_append _ 2944 3712 4480 (interval_append _ 2944 3328 3712 (interval_append _ 2944 3072 3328 group1114_pairs_02944 (interval_append _ 3072 3200 3328 group1114_pairs_03072 group1114_pairs_03200)) (interval_append _ 3328 3456 3712 group1114_pairs_03328 (interval_append _ 3456 3584 3712 group1114_pairs_03456 group1114_pairs_03584))) (interval_append _ 3712 4096 4480 (interval_append _ 3712 3840 4096 group1114_pairs_03712 (interval_append _ 3840 3968 4096 group1114_pairs_03840 group1114_pairs_03968)) (interval_append _ 4096 4224 4480 group1114_pairs_04096 (interval_append _ 4224 4352 4480 group1114_pairs_04224 group1114_pairs_04352)))) (interval_append _ 4480 5248 5945 (interval_append _ 4480 4864 5248 (interval_append _ 4480 4608 4864 group1114_pairs_04480 (interval_append _ 4608 4736 4864 group1114_pairs_04608 group1114_pairs_04736)) (interval_append _ 4864 4992 5248 group1114_pairs_04864 (interval_append _ 4992 5120 5248 group1114_pairs_04992 group1114_pairs_05120))) (interval_append _ 5248 5632 5945 (interval_append _ 5248 5376 5632 group1114_pairs_05248 (interval_append _ 5376 5504 5632 group1114_pairs_05376 group1114_pairs_05504)) (interval_append _ 5632 5760 5945 group1114_pairs_05632 (interval_append _ 5760 5888 5945 group1114_pairs_05760 group1114_pairs_05888))))))
end Papers.RationalityTen.SharedFrameCatalogue
