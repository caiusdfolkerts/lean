module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups033Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0510
cert_group_pairs 0510 00000 0 125 125
cert_group_facts_6 0510
#print axioms group0510_facts
cert_group_header 0511
cert_group_pairs 0511 00000 0 128 128
cert_group_pairs 0511 00128 128 130 2
cert_group_facts 0511 130
#print axioms group0511_facts
cert_group_header 0512
cert_group_pairs 0512 00000 0 128 128
cert_group_pairs 0512 00128 128 130 2
cert_group_facts 0512 130
#print axioms group0512_facts
cert_group_header 0513
cert_group_pairs 0513 00000 0 128 128
cert_group_pairs 0513 00128 128 155 27
cert_group_facts 0513 155
#print axioms group0513_facts
cert_group_header 0514
cert_group_pairs 0514 00000 0 87 87
cert_group_facts_6 0514
#print axioms group0514_facts
cert_group_header 0515
cert_group_pairs 0515 00000 0 128 128
cert_group_pairs 0515 00128 128 153 25
cert_group_facts 0515 153
#print axioms group0515_facts
cert_group_header 0516
cert_group_pairs 0516 00000 0 92 92
cert_group_facts_6 0516
#print axioms group0516_facts
cert_group_header 0517
cert_group_pairs 0517 00000 0 87 87
cert_group_facts_6 0517
#print axioms group0517_facts
cert_group_header 0518
cert_group_pairs 0518 00000 0 128 128
cert_group_pairs 0518 00128 128 153 25
cert_group_facts 0518 153
#print axioms group0518_facts
cert_group_header 0519
cert_group_pairs 0519 00000 0 128 128
cert_group_pairs 0519 00128 128 256 128
cert_group_pairs 0519 00256 256 384 128
cert_group_pairs 0519 00384 384 512 128
cert_group_pairs 0519 00512 512 564 52
cert_group_facts_5 0519 564
#print axioms group0519_facts
cert_group_header 0520
cert_group_pairs 0520 00000 0 128 128
cert_group_pairs 0520 00128 128 256 128
cert_group_pairs 0520 00256 256 384 128
cert_group_pairs 0520 00384 384 465 81
cert_group_facts_4 0520 465
#print axioms group0520_facts
cert_group_header 0521
cert_group_pairs 0521 00000 0 128 128
cert_group_pairs 0521 00128 128 256 128
cert_group_pairs 0521 00256 256 384 128
cert_group_facts_2 0521 384
#print axioms group0521_facts
cert_group_header 0522
cert_group_pairs 0522 00000 0 128 128
cert_group_pairs 0522 00128 128 256 128
cert_group_pairs 0522 00256 256 258 2
cert_group_facts_2 0522 258
#print axioms group0522_facts
cert_group_header 0523
cert_group_pairs 0523 00000 0 128 128
cert_group_pairs 0523 00128 128 239 111
cert_group_facts 0523 239
#print axioms group0523_facts
cert_group_header 0524
cert_group_pairs 0524 00000 0 128 128
cert_group_pairs 0524 00128 128 256 128
cert_group_pairs 0524 00256 256 361 105
cert_group_facts_2 0524 361
#print axioms group0524_facts
cert_group_header 0525
cert_group_pairs 0525 00000 0 128 128
cert_group_pairs 0525 00128 128 256 128
cert_group_pairs 0525 00256 256 384 128
cert_group_pairs 0525 00384 384 512 128
cert_group_pairs 0525 00512 512 640 128
cert_group_pairs 0525 00640 640 682 42
theorem group0525_facts : group0525.Facts FacetUniverses.FullSix0.cells :=
  group0525.facts_of_checks _ group0525_header (interval_append _ 0 384 682 (interval_append _ 0 128 384 group0525_pairs_00000 (interval_append _ 128 256 384 group0525_pairs_00128 group0525_pairs_00256)) (interval_append _ 384 512 682 group0525_pairs_00384 (interval_append _ 512 640 682 group0525_pairs_00512 group0525_pairs_00640)))
#print axioms group0525_facts
end Papers.RationalityTen.SharedFrameCatalogue
