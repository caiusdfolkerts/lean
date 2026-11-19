module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups025Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0382
cert_group_pairs 0382 00000 0 128 128
cert_group_pairs 0382 00128 128 256 128
cert_group_pairs 0382 00256 256 384 128
cert_group_pairs 0382 00384 384 512 128
cert_group_pairs 0382 00512 512 640 128
cert_group_pairs 0382 00640 640 768 128
cert_group_pairs 0382 00768 768 896 128
cert_group_pairs 0382 00896 896 981 85
theorem group0382_facts : group0382.Facts FacetUniverses.FullSix0.cells :=
  group0382.facts_of_checks _ group0382_header (interval_append _ 0 512 981 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0382_pairs_00000 group0382_pairs_00128) (interval_append _ 256 384 512 group0382_pairs_00256 group0382_pairs_00384)) (interval_append _ 512 768 981 (interval_append _ 512 640 768 group0382_pairs_00512 group0382_pairs_00640) (interval_append _ 768 896 981 group0382_pairs_00768 group0382_pairs_00896)))
#print axioms group0382_facts
cert_group_header 0383
cert_group_pairs 0383 00000 0 75 75
cert_group_facts_6 0383
#print axioms group0383_facts
cert_group_header 0384
cert_group_pairs 0384 00000 0 125 125
cert_group_facts_6 0384
#print axioms group0384_facts
cert_group_header 0385
cert_group_pairs 0385 00000 0 75 75
cert_group_facts_6 0385
#print axioms group0385_facts
cert_group_header 0386
cert_group_pairs 0386 00000 0 125 125
cert_group_facts_6 0386
#print axioms group0386_facts
cert_group_header 0387
cert_group_pairs 0387 00000 0 128 128
cert_group_pairs 0387 00128 128 155 27
cert_group_facts 0387 155
#print axioms group0387_facts
cert_group_header 0388
cert_group_pairs 0388 00000 0 128 128
cert_group_pairs 0388 00128 128 155 27
cert_group_facts 0388 155
#print axioms group0388_facts
cert_group_header 0389
cert_group_pairs 0389 00000 0 128 128
cert_group_pairs 0389 00128 128 153 25
cert_group_facts 0389 153
#print axioms group0389_facts
cert_group_header 0390
cert_group_pairs 0390 00000 0 128 128
cert_group_pairs 0390 00128 128 201 73
cert_group_facts 0390 201
#print axioms group0390_facts
cert_group_header 0391
cert_group_pairs 0391 00000 0 128 128
cert_group_pairs 0391 00128 128 153 25
cert_group_facts 0391 153
#print axioms group0391_facts
cert_group_header 0392
cert_group_pairs 0392 00000 0 119 119
cert_group_facts_6 0392
#print axioms group0392_facts
cert_group_header 0393
cert_group_pairs 0393 00000 0 119 119
cert_group_facts_6 0393
#print axioms group0393_facts
cert_group_header 0394
cert_group_pairs 0394 00000 0 128 128
cert_group_pairs 0394 00128 128 146 18
cert_group_facts 0394 146
#print axioms group0394_facts
cert_group_header 0395
cert_group_pairs 0395 00000 0 117 117
cert_group_facts_6 0395
#print axioms group0395_facts
cert_group_header 0396
cert_group_pairs 0396 00000 0 128 128
cert_group_pairs 0396 00128 128 147 19
cert_group_facts 0396 147
#print axioms group0396_facts
cert_group_header 0397
cert_group_pairs 0397 00000 0 128 128
cert_group_pairs 0397 00128 128 147 19
cert_group_facts 0397 147
#print axioms group0397_facts
end Papers.RationalityTen.SharedFrameCatalogue
