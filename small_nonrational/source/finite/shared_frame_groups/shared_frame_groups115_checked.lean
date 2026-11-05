module
prelude
public import SharedFrameGroups115Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem group1109_header : group1109.headerCheck = true := by
  decide +kernel
theorem group1109_pairs_00000 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1109_pairs_00128 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group1109_pairs_00256 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group1109_pairs_00384 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group1109_pairs_00512 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group1109_pairs_00640 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group1109_pairs_00768 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group1109_pairs_00896 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group1109_pairs_01024 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group1109_pairs_01152 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group1109_pairs_01280 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1280 1408 :=
  interval_of_check _ 1280 128 (by decide +kernel)
theorem group1109_pairs_01408 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1408 1536 :=
  interval_of_check _ 1408 128 (by decide +kernel)
theorem group1109_pairs_01536 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1536 1664 :=
  interval_of_check _ 1536 128 (by decide +kernel)
theorem group1109_pairs_01664 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1664 1792 :=
  interval_of_check _ 1664 128 (by decide +kernel)
theorem group1109_pairs_01792 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1792 1920 :=
  interval_of_check _ 1792 128 (by decide +kernel)
theorem group1109_pairs_01920 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 1920 2048 :=
  interval_of_check _ 1920 128 (by decide +kernel)
theorem group1109_pairs_02048 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 2048 2176 :=
  interval_of_check _ 2048 128 (by decide +kernel)
theorem group1109_pairs_02176 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 2176 2304 :=
  interval_of_check _ 2176 128 (by decide +kernel)
theorem group1109_pairs_02304 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 2304 2432 :=
  interval_of_check _ 2304 128 (by decide +kernel)
theorem group1109_pairs_02432 :
    Interval (group1109.pairTest FacetUniverses.FullSix0.cells) 2432 2450 :=
  interval_of_check _ 2432 18 (by decide +kernel)
theorem group1109_facts : group1109.Facts FacetUniverses.FullSix0.cells :=
  group1109.facts_of_checks _ group1109_header (interval_append _ 0 1280 2450 (interval_append _ 0 640 1280 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1109_pairs_00000 group1109_pairs_00128) (interval_append _ 256 384 640 group1109_pairs_00256 (interval_append _ 384 512 640 group1109_pairs_00384 group1109_pairs_00512))) (interval_append _ 640 896 1280 (interval_append _ 640 768 896 group1109_pairs_00640 group1109_pairs_00768) (interval_append _ 896 1024 1280 group1109_pairs_00896 (interval_append _ 1024 1152 1280 group1109_pairs_01024 group1109_pairs_01152)))) (interval_append _ 1280 1920 2450 (interval_append _ 1280 1536 1920 (interval_append _ 1280 1408 1536 group1109_pairs_01280 group1109_pairs_01408) (interval_append _ 1536 1664 1920 group1109_pairs_01536 (interval_append _ 1664 1792 1920 group1109_pairs_01664 group1109_pairs_01792))) (interval_append _ 1920 2176 2450 (interval_append _ 1920 2048 2176 group1109_pairs_01920 group1109_pairs_02048) (interval_append _ 2176 2304 2450 group1109_pairs_02176 (interval_append _ 2304 2432 2450 group1109_pairs_02304 group1109_pairs_02432)))))
#print axioms group1109_facts
end Papers.RationalityTen.SharedFrameCatalogue
