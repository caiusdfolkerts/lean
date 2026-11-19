module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups043Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0580
cert_group_pairs 0580 00000 0 128 128
cert_group_pairs 0580 00128 128 230 102
cert_group_facts 0580 230
#print axioms group0580_facts
cert_group_header 0581
cert_group_pairs 0581 00000 0 128 128
cert_group_pairs 0581 00128 128 150 22
cert_group_facts 0581 150
#print axioms group0581_facts
cert_group_header 0582
cert_group_pairs 0582 00000 0 126 126
cert_group_facts_6 0582
#print axioms group0582_facts
cert_group_header 0583
cert_group_pairs 0583 00000 0 80 80
cert_group_facts_6 0583
#print axioms group0583_facts
cert_group_header 0584
cert_group_pairs 0584 00000 0 92 92
cert_group_facts_6 0584
#print axioms group0584_facts
cert_group_header 0585
cert_group_pairs 0585 00000 0 128 128
cert_group_pairs 0585 00128 128 210 82
cert_group_facts 0585 210
#print axioms group0585_facts
cert_group_header 0586
cert_group_pairs 0586 00000 0 128 128
cert_group_pairs 0586 00128 128 190 62
cert_group_facts 0586 190
#print axioms group0586_facts
cert_group_header 0587
cert_group_pairs 0587 00000 0 128 128
cert_group_pairs 0587 00128 128 190 62
cert_group_facts 0587 190
#print axioms group0587_facts
cert_group_header 0588
cert_group_pairs 0588 00000 0 128 128
cert_group_pairs 0588 00128 128 256 128
cert_group_pairs 0588 00256 256 261 5
cert_group_facts_2 0588 261
#print axioms group0588_facts
cert_group_header 0589
cert_group_pairs 0589 00000 0 128 128
cert_group_pairs 0589 00128 128 256 128
cert_group_pairs 0589 00256 256 384 128
cert_group_pairs 0589 00384 384 512 128
cert_group_pairs 0589 00512 512 640 128
cert_group_pairs 0589 00640 640 768 128
cert_group_pairs 0589 00768 768 896 128
cert_group_pairs 0589 00896 896 1024 128
cert_group_pairs 0589 01024 1024 1152 128
cert_group_pairs 0589 01152 1152 1280 128
cert_group_pairs 0589 01280 1280 1408 128
cert_group_pairs 0589 01408 1408 1440 32
theorem group0589_facts : group0589.Facts FacetUniverses.FullSix0.cells :=
  group0589.facts_of_checks _ group0589_header (interval_append _ 0 768 1440 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0589_pairs_00000 (interval_append _ 128 256 384 group0589_pairs_00128 group0589_pairs_00256)) (interval_append _ 384 512 768 group0589_pairs_00384 (interval_append _ 512 640 768 group0589_pairs_00512 group0589_pairs_00640))) (interval_append _ 768 1152 1440 (interval_append _ 768 896 1152 group0589_pairs_00768 (interval_append _ 896 1024 1152 group0589_pairs_00896 group0589_pairs_01024)) (interval_append _ 1152 1280 1440 group0589_pairs_01152 (interval_append _ 1280 1408 1440 group0589_pairs_01280 group0589_pairs_01408))))
#print axioms group0589_facts
end Papers.RationalityTen.SharedFrameCatalogue
