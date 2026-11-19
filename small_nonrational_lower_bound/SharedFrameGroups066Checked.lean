module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups066Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0810
cert_group_pairs 0810 00000 0 128 128
cert_group_pairs 0810 00128 128 256 128
cert_group_pairs 0810 00256 256 306 50
cert_group_facts_2 0810 306
#print axioms group0810_facts
cert_group_header 0811
cert_group_pairs 0811 00000 0 128 128
cert_group_pairs 0811 00128 128 256 128
cert_group_pairs 0811 00256 256 303 47
cert_group_facts_2 0811 303
#print axioms group0811_facts
cert_group_header 0812
cert_group_pairs 0812 00000 0 128 128
cert_group_pairs 0812 00128 128 256 128
cert_group_pairs 0812 00256 256 384 128
cert_group_pairs 0812 00384 384 512 128
cert_group_pairs 0812 00512 512 640 128
cert_group_pairs 0812 00640 640 768 128
cert_group_pairs 0812 00768 768 896 128
cert_group_pairs 0812 00896 896 1024 128
cert_group_pairs 0812 01024 1024 1152 128
cert_group_pairs 0812 01152 1152 1280 128
cert_group_pairs 0812 01280 1280 1408 128
cert_group_pairs 0812 01408 1408 1536 128
cert_group_pairs 0812 01536 1536 1664 128
cert_group_pairs 0812 01664 1664 1792 128
cert_group_pairs 0812 01792 1792 1905 113
theorem group0812_facts : group0812.Facts FacetUniverses.FullSix0.cells :=
  group0812.facts_of_checks _ group0812_header (interval_append _ 0 896 1905 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0812_pairs_00000 (interval_append _ 128 256 384 group0812_pairs_00128 group0812_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0812_pairs_00384 group0812_pairs_00512) (interval_append _ 640 768 896 group0812_pairs_00640 group0812_pairs_00768))) (interval_append _ 896 1408 1905 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group0812_pairs_00896 group0812_pairs_01024) (interval_append _ 1152 1280 1408 group0812_pairs_01152 group0812_pairs_01280)) (interval_append _ 1408 1664 1905 (interval_append _ 1408 1536 1664 group0812_pairs_01408 group0812_pairs_01536) (interval_append _ 1664 1792 1905 group0812_pairs_01664 group0812_pairs_01792))))
#print axioms group0812_facts
cert_group_header 0813
cert_group_pairs 0813 00000 0 128 128
cert_group_pairs 0813 00128 128 256 128
cert_group_pairs 0813 00256 256 384 128
cert_group_pairs 0813 00384 384 512 128
cert_group_pairs 0813 00512 512 640 128
cert_group_pairs 0813 00640 640 768 128
cert_group_pairs 0813 00768 768 896 128
cert_group_pairs 0813 00896 896 1024 128
cert_group_pairs 0813 01024 1024 1152 128
cert_group_pairs 0813 01152 1152 1167 15
cert_group_facts_3 0813 1167
#print axioms group0813_facts
end Papers.RationalityTen.SharedFrameCatalogue
