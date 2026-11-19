module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups070Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0833
cert_group_pairs 0833 00000 0 128 128
cert_group_pairs 0833 00128 128 199 71
cert_group_facts 0833 199
#print axioms group0833_facts
cert_group_header 0834
cert_group_pairs 0834 00000 0 128 128
cert_group_pairs 0834 00128 128 136 8
cert_group_facts 0834 136
#print axioms group0834_facts
cert_group_header 0835
cert_group_pairs 0835 00000 0 128 128
cert_group_pairs 0835 00128 128 199 71
cert_group_facts 0835 199
#print axioms group0835_facts
cert_group_header 0836
cert_group_pairs 0836 00000 0 96 96
cert_group_facts_6 0836
#print axioms group0836_facts
cert_group_header 0837
cert_group_pairs 0837 00000 0 128 128
cert_group_pairs 0837 00128 128 132 4
cert_group_facts 0837 132
#print axioms group0837_facts
cert_group_header 0838
cert_group_pairs 0838 00000 0 122 122
cert_group_facts_6 0838
#print axioms group0838_facts
cert_group_header 0839
cert_group_pairs 0839 00000 0 128 128
cert_group_pairs 0839 00128 128 132 4
cert_group_facts 0839 132
#print axioms group0839_facts
cert_group_header 0840
cert_group_pairs 0840 00000 0 128 128
cert_group_pairs 0840 00128 128 256 128
cert_group_pairs 0840 00256 256 384 128
cert_group_pairs 0840 00384 384 512 128
cert_group_pairs 0840 00512 512 640 128
cert_group_pairs 0840 00640 640 768 128
cert_group_pairs 0840 00768 768 896 128
cert_group_pairs 0840 00896 896 1024 128
cert_group_pairs 0840 01024 1024 1152 128
cert_group_pairs 0840 01152 1152 1223 71
cert_group_facts_3 0840 1223
#print axioms group0840_facts
cert_group_header 0841
cert_group_pairs 0841 00000 0 128 128
cert_group_pairs 0841 00128 128 256 128
cert_group_pairs 0841 00256 256 384 128
cert_group_pairs 0841 00384 384 512 128
cert_group_pairs 0841 00512 512 640 128
cert_group_pairs 0841 00640 640 768 128
cert_group_pairs 0841 00768 768 896 128
cert_group_pairs 0841 00896 896 1024 128
cert_group_pairs 0841 01024 1024 1152 128
cert_group_pairs 0841 01152 1152 1280 128
cert_group_pairs 0841 01280 1280 1408 128
cert_group_pairs 0841 01408 1408 1536 128
cert_group_pairs 0841 01536 1536 1564 28
theorem group0841_facts : group0841.Facts FacetUniverses.FullSix0.cells :=
  group0841.facts_of_checks _ group0841_header (interval_append _ 0 768 1564 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0841_pairs_00000 (interval_append _ 128 256 384 group0841_pairs_00128 group0841_pairs_00256)) (interval_append _ 384 512 768 group0841_pairs_00384 (interval_append _ 512 640 768 group0841_pairs_00512 group0841_pairs_00640))) (interval_append _ 768 1152 1564 (interval_append _ 768 896 1152 group0841_pairs_00768 (interval_append _ 896 1024 1152 group0841_pairs_00896 group0841_pairs_01024)) (interval_append _ 1152 1408 1564 (interval_append _ 1152 1280 1408 group0841_pairs_01152 group0841_pairs_01280) (interval_append _ 1408 1536 1564 group0841_pairs_01408 group0841_pairs_01536))))
#print axioms group0841_facts
cert_group_header 0842
cert_group_pairs 0842 00000 0 128 128
cert_group_pairs 0842 00128 128 135 7
cert_group_facts 0842 135
#print axioms group0842_facts
end Papers.RationalityTen.SharedFrameCatalogue
