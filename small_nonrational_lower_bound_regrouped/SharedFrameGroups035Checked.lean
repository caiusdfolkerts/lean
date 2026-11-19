module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups035Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0538
cert_group_pairs 0538 00000 0 128 128
cert_group_pairs 0538 00128 128 256 128
cert_group_pairs 0538 00256 256 384 128
cert_group_pairs 0538 00384 384 512 128
cert_group_pairs 0538 00512 512 640 128
cert_group_pairs 0538 00640 640 768 128
cert_group_pairs 0538 00768 768 896 128
cert_group_pairs 0538 00896 896 1024 128
cert_group_pairs 0538 01024 1024 1152 128
cert_group_pairs 0538 01152 1152 1280 128
cert_group_pairs 0538 01280 1280 1408 128
cert_group_pairs 0538 01408 1408 1536 128
cert_group_pairs 0538 01536 1536 1664 128
cert_group_pairs 0538 01664 1664 1792 128
cert_group_pairs 0538 01792 1792 1920 128
cert_group_pairs 0538 01920 1920 2048 128
cert_group_pairs 0538 02048 2048 2176 128
cert_group_pairs 0538 02176 2176 2304 128
cert_group_pairs 0538 02304 2304 2432 128
cert_group_pairs 0538 02432 2432 2560 128
cert_group_pairs 0538 02560 2560 2688 128
cert_group_pairs 0538 02688 2688 2816 128
cert_group_pairs 0538 02816 2816 2863 47
theorem group0538_facts : group0538.Facts FacetUniverses.FullSix0.cells :=
  group0538.facts_of_checks _ group0538_header (interval_append _ 0 1408 2863 (interval_append _ 0 640 1408 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0538_pairs_00000 group0538_pairs_00128) (interval_append _ 256 384 640 group0538_pairs_00256 (interval_append _ 384 512 640 group0538_pairs_00384 group0538_pairs_00512))) (interval_append _ 640 1024 1408 (interval_append _ 640 768 1024 group0538_pairs_00640 (interval_append _ 768 896 1024 group0538_pairs_00768 group0538_pairs_00896)) (interval_append _ 1024 1152 1408 group0538_pairs_01024 (interval_append _ 1152 1280 1408 group0538_pairs_01152 group0538_pairs_01280)))) (interval_append _ 1408 2176 2863 (interval_append _ 1408 1792 2176 (interval_append _ 1408 1536 1792 group0538_pairs_01408 (interval_append _ 1536 1664 1792 group0538_pairs_01536 group0538_pairs_01664)) (interval_append _ 1792 1920 2176 group0538_pairs_01792 (interval_append _ 1920 2048 2176 group0538_pairs_01920 group0538_pairs_02048))) (interval_append _ 2176 2560 2863 (interval_append _ 2176 2304 2560 group0538_pairs_02176 (interval_append _ 2304 2432 2560 group0538_pairs_02304 group0538_pairs_02432)) (interval_append _ 2560 2688 2863 group0538_pairs_02560 (interval_append _ 2688 2816 2863 group0538_pairs_02688 group0538_pairs_02816)))))
#print axioms group0538_facts
end Papers.RationalityTen.SharedFrameCatalogue
