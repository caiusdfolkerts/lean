module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups051Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0643
cert_group_pairs 0643 00000 0 128 128
cert_group_pairs 0643 00128 128 256 128
cert_group_pairs 0643 00256 256 326 70
cert_group_facts_2 0643 326
#print axioms group0643_facts
cert_group_header 0644
cert_group_pairs 0644 00000 0 128 128
cert_group_pairs 0644 00128 128 256 128
cert_group_pairs 0644 00256 256 384 128
cert_group_pairs 0644 00384 384 512 128
cert_group_pairs 0644 00512 512 640 128
cert_group_pairs 0644 00640 640 768 128
cert_group_pairs 0644 00768 768 896 128
cert_group_pairs 0644 00896 896 1024 128
cert_group_pairs 0644 01024 1024 1152 128
cert_group_pairs 0644 01152 1152 1280 128
cert_group_pairs 0644 01280 1280 1408 128
cert_group_pairs 0644 01408 1408 1536 128
cert_group_pairs 0644 01536 1536 1543 7
theorem group0644_facts : group0644.Facts FacetUniverses.FullSix0.cells :=
  group0644.facts_of_checks _ group0644_header (interval_append _ 0 768 1543 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0644_pairs_00000 (interval_append _ 128 256 384 group0644_pairs_00128 group0644_pairs_00256)) (interval_append _ 384 512 768 group0644_pairs_00384 (interval_append _ 512 640 768 group0644_pairs_00512 group0644_pairs_00640))) (interval_append _ 768 1152 1543 (interval_append _ 768 896 1152 group0644_pairs_00768 (interval_append _ 896 1024 1152 group0644_pairs_00896 group0644_pairs_01024)) (interval_append _ 1152 1408 1543 (interval_append _ 1152 1280 1408 group0644_pairs_01152 group0644_pairs_01280) (interval_append _ 1408 1536 1543 group0644_pairs_01408 group0644_pairs_01536))))
#print axioms group0644_facts
cert_group_header 0645
cert_group_pairs 0645 00000 0 128 128
cert_group_pairs 0645 00128 128 256 128
cert_group_pairs 0645 00256 256 384 128
cert_group_pairs 0645 00384 384 512 128
cert_group_pairs 0645 00512 512 640 128
cert_group_pairs 0645 00640 640 768 128
cert_group_pairs 0645 00768 768 896 128
cert_group_pairs 0645 00896 896 1024 128
cert_group_pairs 0645 01024 1024 1152 128
cert_group_pairs 0645 01152 1152 1280 128
cert_group_pairs 0645 01280 1280 1340 60
theorem group0645_facts : group0645.Facts FacetUniverses.FullSix0.cells :=
  group0645.facts_of_checks _ group0645_header (interval_append _ 0 640 1340 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0645_pairs_00000 group0645_pairs_00128) (interval_append _ 256 384 640 group0645_pairs_00256 (interval_append _ 384 512 640 group0645_pairs_00384 group0645_pairs_00512))) (interval_append _ 640 1024 1340 (interval_append _ 640 768 1024 group0645_pairs_00640 (interval_append _ 768 896 1024 group0645_pairs_00768 group0645_pairs_00896)) (interval_append _ 1024 1152 1340 group0645_pairs_01024 (interval_append _ 1152 1280 1340 group0645_pairs_01152 group0645_pairs_01280))))
#print axioms group0645_facts
end Papers.RationalityTen.SharedFrameCatalogue
