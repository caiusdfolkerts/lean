module
prelude
public import SharedFrameGroups107Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem group1079_header : group1079.headerCheck = true := by
  decide +kernel
theorem group1079_pairs_00000 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1079_pairs_00128 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group1079_pairs_00256 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group1079_pairs_00384 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group1079_pairs_00512 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group1079_pairs_00640 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group1079_pairs_00768 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group1079_pairs_00896 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group1079_pairs_01024 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group1079_pairs_01152 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group1079_pairs_01280 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 1280 1408 :=
  interval_of_check _ 1280 128 (by decide +kernel)
theorem group1079_pairs_01408 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 1408 1536 :=
  interval_of_check _ 1408 128 (by decide +kernel)
theorem group1079_pairs_01536 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 1536 1664 :=
  interval_of_check _ 1536 128 (by decide +kernel)
theorem group1079_pairs_01664 :
    Interval (group1079.pairTest FacetUniverses.FullSix0.cells) 1664 1723 :=
  interval_of_check _ 1664 59 (by decide +kernel)
theorem group1079_facts : group1079.Facts FacetUniverses.FullSix0.cells :=
  group1079.facts_of_checks _ group1079_header (interval_append _ 0 896 1723 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group1079_pairs_00000 (interval_append _ 128 256 384 group1079_pairs_00128 group1079_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group1079_pairs_00384 group1079_pairs_00512) (interval_append _ 640 768 896 group1079_pairs_00640 group1079_pairs_00768))) (interval_append _ 896 1280 1723 (interval_append _ 896 1024 1280 group1079_pairs_00896 (interval_append _ 1024 1152 1280 group1079_pairs_01024 group1079_pairs_01152)) (interval_append _ 1280 1536 1723 (interval_append _ 1280 1408 1536 group1079_pairs_01280 group1079_pairs_01408) (interval_append _ 1536 1664 1723 group1079_pairs_01536 group1079_pairs_01664))))
#print axioms group1079_facts
end Papers.RationalityTen.SharedFrameCatalogue
