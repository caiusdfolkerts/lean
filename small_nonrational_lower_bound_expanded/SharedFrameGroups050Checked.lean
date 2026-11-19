module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups050Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0634
cert_group_pairs 0634 00000 0 128 128
cert_group_pairs 0634 00128 128 256 128
cert_group_pairs 0634 00256 256 384 128
cert_group_pairs 0634 00384 384 512 128
cert_group_pairs 0634 00512 512 640 128
cert_group_pairs 0634 00640 640 768 128
cert_group_pairs 0634 00768 768 896 128
cert_group_pairs 0634 00896 896 1024 128
cert_group_pairs 0634 01024 1024 1152 128
cert_group_pairs 0634 01152 1152 1280 128
cert_group_pairs 0634 01280 1280 1408 128
cert_group_pairs 0634 01408 1408 1536 128
cert_group_pairs 0634 01536 1536 1664 128
cert_group_pairs 0634 01664 1664 1792 128
cert_group_pairs 0634 01792 1792 1920 128
cert_group_pairs 0634 01920 1920 2003 83
theorem group0634_facts : group0634.Facts FacetUniverses.FullSix0.cells :=
  group0634.facts_of_checks _ group0634_header (interval_append _ 0 1024 2003 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0634_pairs_00000 group0634_pairs_00128) (interval_append _ 256 384 512 group0634_pairs_00256 group0634_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group0634_pairs_00512 group0634_pairs_00640) (interval_append _ 768 896 1024 group0634_pairs_00768 group0634_pairs_00896))) (interval_append _ 1024 1536 2003 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group0634_pairs_01024 group0634_pairs_01152) (interval_append _ 1280 1408 1536 group0634_pairs_01280 group0634_pairs_01408)) (interval_append _ 1536 1792 2003 (interval_append _ 1536 1664 1792 group0634_pairs_01536 group0634_pairs_01664) (interval_append _ 1792 1920 2003 group0634_pairs_01792 group0634_pairs_01920))))
cert_group_header 0635
cert_group_pairs 0635 00000 0 128 128
cert_group_pairs 0635 00128 128 256 128
cert_group_pairs 0635 00256 256 370 114
cert_group_facts_2 0635 370
cert_group_header 0636
cert_group_pairs 0636 00000 0 122 122
cert_group_facts_6 0636
cert_group_header 0637
cert_group_pairs 0637 00000 0 128 128
cert_group_pairs 0637 00128 128 164 36
cert_group_facts 0637 164
cert_group_header 0638
cert_group_pairs 0638 00000 0 104 104
cert_group_facts_6 0638
cert_group_header 0639
cert_group_pairs 0639 00000 0 128 128
cert_group_pairs 0639 00128 128 256 128
cert_group_pairs 0639 00256 256 384 128
cert_group_pairs 0639 00384 384 452 68
cert_group_facts_4 0639 452
cert_group_header 0640
cert_group_pairs 0640 00000 0 128 128
cert_group_pairs 0640 00128 128 202 74
cert_group_facts 0640 202
cert_group_header 0641
cert_group_pairs 0641 00000 0 128 128
cert_group_pairs 0641 00128 128 194 66
cert_group_facts 0641 194
cert_group_header 0642
cert_group_pairs 0642 00000 0 128 128
cert_group_pairs 0642 00128 128 256 128
cert_group_pairs 0642 00256 256 286 30
cert_group_facts_2 0642 286
end Papers.RationalityTen.SharedFrameCatalogue
