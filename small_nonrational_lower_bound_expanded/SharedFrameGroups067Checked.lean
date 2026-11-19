module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups067Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0814
cert_group_pairs 0814 00000 0 128 128
cert_group_pairs 0814 00128 128 256 128
cert_group_pairs 0814 00256 256 384 128
cert_group_pairs 0814 00384 384 512 128
cert_group_pairs 0814 00512 512 640 128
cert_group_pairs 0814 00640 640 768 128
cert_group_pairs 0814 00768 768 896 128
cert_group_pairs 0814 00896 896 1024 128
cert_group_pairs 0814 01024 1024 1152 128
cert_group_pairs 0814 01152 1152 1280 128
cert_group_pairs 0814 01280 1280 1408 128
cert_group_pairs 0814 01408 1408 1536 128
cert_group_pairs 0814 01536 1536 1606 70
theorem group0814_facts : group0814.Facts FacetUniverses.FullSix0.cells :=
  group0814.facts_of_checks _ group0814_header (interval_append _ 0 768 1606 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0814_pairs_00000 (interval_append _ 128 256 384 group0814_pairs_00128 group0814_pairs_00256)) (interval_append _ 384 512 768 group0814_pairs_00384 (interval_append _ 512 640 768 group0814_pairs_00512 group0814_pairs_00640))) (interval_append _ 768 1152 1606 (interval_append _ 768 896 1152 group0814_pairs_00768 (interval_append _ 896 1024 1152 group0814_pairs_00896 group0814_pairs_01024)) (interval_append _ 1152 1408 1606 (interval_append _ 1152 1280 1408 group0814_pairs_01152 group0814_pairs_01280) (interval_append _ 1408 1536 1606 group0814_pairs_01408 group0814_pairs_01536))))
cert_group_header 0815
cert_group_pairs 0815 00000 0 128 128
cert_group_pairs 0815 00128 128 132 4
cert_group_facts 0815 132
cert_group_header 0816
cert_group_pairs 0816 00000 0 128 128
cert_group_pairs 0816 00128 128 243 115
cert_group_facts 0816 243
cert_group_header 0817
cert_group_pairs 0817 00000 0 128 128
cert_group_pairs 0817 00128 128 132 4
cert_group_facts 0817 132
cert_group_header 0818
cert_group_pairs 0818 00000 0 128 128
cert_group_pairs 0818 00128 128 132 4
cert_group_facts 0818 132
cert_group_header 0819
cert_group_pairs 0819 00000 0 128 128
cert_group_pairs 0819 00128 128 256 128
cert_group_pairs 0819 00256 256 384 128
cert_group_pairs 0819 00384 384 512 128
cert_group_pairs 0819 00512 512 640 128
cert_group_pairs 0819 00640 640 768 128
cert_group_pairs 0819 00768 768 896 128
cert_group_pairs 0819 00896 896 1024 128
cert_group_pairs 0819 01024 1024 1152 128
cert_group_pairs 0819 01152 1152 1280 128
cert_group_pairs 0819 01280 1280 1408 128
cert_group_pairs 0819 01408 1408 1456 48
theorem group0819_facts : group0819.Facts FacetUniverses.FullSix0.cells :=
  group0819.facts_of_checks _ group0819_header (interval_append _ 0 768 1456 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0819_pairs_00000 (interval_append _ 128 256 384 group0819_pairs_00128 group0819_pairs_00256)) (interval_append _ 384 512 768 group0819_pairs_00384 (interval_append _ 512 640 768 group0819_pairs_00512 group0819_pairs_00640))) (interval_append _ 768 1152 1456 (interval_append _ 768 896 1152 group0819_pairs_00768 (interval_append _ 896 1024 1152 group0819_pairs_00896 group0819_pairs_01024)) (interval_append _ 1152 1280 1456 group0819_pairs_01152 (interval_append _ 1280 1408 1456 group0819_pairs_01280 group0819_pairs_01408))))
end Papers.RationalityTen.SharedFrameCatalogue
