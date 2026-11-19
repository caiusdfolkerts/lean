module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups069Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0825
cert_group_pairs 0825 00000 0 128 128
cert_group_pairs 0825 00128 128 256 128
cert_group_pairs 0825 00256 256 384 128
cert_group_pairs 0825 00384 384 512 128
cert_group_pairs 0825 00512 512 640 128
cert_group_pairs 0825 00640 640 768 128
cert_group_pairs 0825 00768 768 896 128
cert_group_pairs 0825 00896 896 1024 128
cert_group_pairs 0825 01024 1024 1062 38
theorem group0825_facts : group0825.Facts FacetUniverses.FullSix0.cells :=
  group0825.facts_of_checks _ group0825_header (interval_append _ 0 512 1062 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0825_pairs_00000 group0825_pairs_00128) (interval_append _ 256 384 512 group0825_pairs_00256 group0825_pairs_00384)) (interval_append _ 512 768 1062 (interval_append _ 512 640 768 group0825_pairs_00512 group0825_pairs_00640) (interval_append _ 768 896 1062 group0825_pairs_00768 (interval_append _ 896 1024 1062 group0825_pairs_00896 group0825_pairs_01024))))
#print axioms group0825_facts
cert_group_header 0826
cert_group_pairs 0826 00000 0 128 128
cert_group_pairs 0826 00128 128 256 128
cert_group_pairs 0826 00256 256 384 128
cert_group_pairs 0826 00384 384 512 128
cert_group_pairs 0826 00512 512 640 128
cert_group_pairs 0826 00640 640 768 128
cert_group_pairs 0826 00768 768 896 128
cert_group_pairs 0826 00896 896 1024 128
cert_group_pairs 0826 01024 1024 1152 128
cert_group_pairs 0826 01152 1152 1280 128
cert_group_pairs 0826 01280 1280 1408 128
cert_group_pairs 0826 01408 1408 1536 128
cert_group_pairs 0826 01536 1536 1664 128
cert_group_pairs 0826 01664 1664 1787 123
theorem group0826_facts : group0826.Facts FacetUniverses.FullSix0.cells :=
  group0826.facts_of_checks _ group0826_header (interval_append _ 0 896 1787 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0826_pairs_00000 (interval_append _ 128 256 384 group0826_pairs_00128 group0826_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0826_pairs_00384 group0826_pairs_00512) (interval_append _ 640 768 896 group0826_pairs_00640 group0826_pairs_00768))) (interval_append _ 896 1280 1787 (interval_append _ 896 1024 1280 group0826_pairs_00896 (interval_append _ 1024 1152 1280 group0826_pairs_01024 group0826_pairs_01152)) (interval_append _ 1280 1536 1787 (interval_append _ 1280 1408 1536 group0826_pairs_01280 group0826_pairs_01408) (interval_append _ 1536 1664 1787 group0826_pairs_01536 group0826_pairs_01664))))
#print axioms group0826_facts
cert_group_header 0827
cert_group_pairs 0827 00000 0 99 99
cert_group_facts_6 0827
#print axioms group0827_facts
cert_group_header 0828
cert_group_pairs 0828 00000 0 128 128
cert_group_pairs 0828 00128 128 256 128
cert_group_pairs 0828 00256 256 268 12
cert_group_facts_2 0828 268
#print axioms group0828_facts
cert_group_header 0829
cert_group_pairs 0829 00000 0 107 107
cert_group_facts_6 0829
#print axioms group0829_facts
cert_group_header 0830
cert_group_pairs 0830 00000 0 107 107
cert_group_facts_6 0830
#print axioms group0830_facts
cert_group_header 0831
cert_group_pairs 0831 00000 0 128 128
cert_group_pairs 0831 00128 128 169 41
cert_group_facts 0831 169
#print axioms group0831_facts
cert_group_header 0832
cert_group_pairs 0832 00000 0 128 128
cert_group_pairs 0832 00128 128 256 128
cert_group_pairs 0832 00256 256 384 128
cert_group_pairs 0832 00384 384 493 109
cert_group_facts_4 0832 493
#print axioms group0832_facts
end Papers.RationalityTen.SharedFrameCatalogue
