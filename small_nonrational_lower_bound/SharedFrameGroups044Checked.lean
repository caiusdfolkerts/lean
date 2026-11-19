module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups044Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0590
cert_group_pairs 0590 00000 0 128 128
cert_group_pairs 0590 00128 128 256 128
cert_group_pairs 0590 00256 256 384 128
cert_group_pairs 0590 00384 384 512 128
cert_group_pairs 0590 00512 512 640 128
cert_group_pairs 0590 00640 640 768 128
cert_group_pairs 0590 00768 768 896 128
cert_group_pairs 0590 00896 896 1024 128
cert_group_pairs 0590 01024 1024 1152 128
cert_group_pairs 0590 01152 1152 1280 128
cert_group_pairs 0590 01280 1280 1290 10
theorem group0590_facts : group0590.Facts FacetUniverses.FullSix0.cells :=
  group0590.facts_of_checks _ group0590_header (interval_append _ 0 640 1290 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0590_pairs_00000 group0590_pairs_00128) (interval_append _ 256 384 640 group0590_pairs_00256 (interval_append _ 384 512 640 group0590_pairs_00384 group0590_pairs_00512))) (interval_append _ 640 1024 1290 (interval_append _ 640 768 1024 group0590_pairs_00640 (interval_append _ 768 896 1024 group0590_pairs_00768 group0590_pairs_00896)) (interval_append _ 1024 1152 1290 group0590_pairs_01024 (interval_append _ 1152 1280 1290 group0590_pairs_01152 group0590_pairs_01280))))
#print axioms group0590_facts
cert_group_header 0591
cert_group_pairs 0591 00000 0 128 128
cert_group_pairs 0591 00128 128 256 128
cert_group_pairs 0591 00256 256 384 128
cert_group_pairs 0591 00384 384 512 128
cert_group_pairs 0591 00512 512 640 128
cert_group_pairs 0591 00640 640 768 128
cert_group_pairs 0591 00768 768 896 128
cert_group_pairs 0591 00896 896 1024 128
cert_group_pairs 0591 01024 1024 1152 128
cert_group_pairs 0591 01152 1152 1280 128
cert_group_pairs 0591 01280 1280 1408 128
cert_group_pairs 0591 01408 1408 1439 31
theorem group0591_facts : group0591.Facts FacetUniverses.FullSix0.cells :=
  group0591.facts_of_checks _ group0591_header (interval_append _ 0 768 1439 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0591_pairs_00000 (interval_append _ 128 256 384 group0591_pairs_00128 group0591_pairs_00256)) (interval_append _ 384 512 768 group0591_pairs_00384 (interval_append _ 512 640 768 group0591_pairs_00512 group0591_pairs_00640))) (interval_append _ 768 1152 1439 (interval_append _ 768 896 1152 group0591_pairs_00768 (interval_append _ 896 1024 1152 group0591_pairs_00896 group0591_pairs_01024)) (interval_append _ 1152 1280 1439 group0591_pairs_01152 (interval_append _ 1280 1408 1439 group0591_pairs_01280 group0591_pairs_01408))))
#print axioms group0591_facts
cert_group_header 0592
cert_group_pairs 0592 00000 0 128 128
cert_group_pairs 0592 00128 128 247 119
cert_group_facts 0592 247
#print axioms group0592_facts
cert_group_header 0593
cert_group_pairs 0593 00000 0 119 119
cert_group_facts_6 0593
#print axioms group0593_facts
cert_group_header 0594
cert_group_pairs 0594 00000 0 128 128
cert_group_pairs 0594 00128 128 158 30
cert_group_facts 0594 158
#print axioms group0594_facts
cert_group_header 0595
cert_group_pairs 0595 00000 0 119 119
cert_group_facts_6 0595
#print axioms group0595_facts
cert_group_header 0596
cert_group_pairs 0596 00000 0 128 128
cert_group_pairs 0596 00128 128 256 128
cert_group_pairs 0596 00256 256 289 33
cert_group_facts_2 0596 289
#print axioms group0596_facts
cert_group_header 0597
cert_group_pairs 0597 00000 0 128 128
cert_group_pairs 0597 00128 128 132 4
cert_group_facts 0597 132
#print axioms group0597_facts
cert_group_header 0598
cert_group_pairs 0598 00000 0 128 128
cert_group_pairs 0598 00128 128 142 14
cert_group_facts 0598 142
#print axioms group0598_facts
end Papers.RationalityTen.SharedFrameCatalogue
