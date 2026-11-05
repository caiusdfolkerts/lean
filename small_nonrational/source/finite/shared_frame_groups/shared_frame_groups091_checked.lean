module
prelude
public import SharedFrameGroups091Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem group1001_header : group1001.headerCheck = true := by
  decide +kernel
theorem group1001_pairs_00000 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1001_pairs_00128 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group1001_pairs_00256 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group1001_pairs_00384 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group1001_pairs_00512 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group1001_pairs_00640 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group1001_pairs_00768 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group1001_pairs_00896 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group1001_pairs_01024 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group1001_pairs_01152 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group1001_pairs_01280 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1280 1408 :=
  interval_of_check _ 1280 128 (by decide +kernel)
theorem group1001_pairs_01408 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1408 1536 :=
  interval_of_check _ 1408 128 (by decide +kernel)
theorem group1001_pairs_01536 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1536 1664 :=
  interval_of_check _ 1536 128 (by decide +kernel)
theorem group1001_pairs_01664 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1664 1792 :=
  interval_of_check _ 1664 128 (by decide +kernel)
theorem group1001_pairs_01792 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1792 1920 :=
  interval_of_check _ 1792 128 (by decide +kernel)
theorem group1001_pairs_01920 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 1920 2048 :=
  interval_of_check _ 1920 128 (by decide +kernel)
theorem group1001_pairs_02048 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 2048 2176 :=
  interval_of_check _ 2048 128 (by decide +kernel)
theorem group1001_pairs_02176 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 2176 2304 :=
  interval_of_check _ 2176 128 (by decide +kernel)
theorem group1001_pairs_02304 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 2304 2432 :=
  interval_of_check _ 2304 128 (by decide +kernel)
theorem group1001_pairs_02432 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 2432 2560 :=
  interval_of_check _ 2432 128 (by decide +kernel)
theorem group1001_pairs_02560 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 2560 2688 :=
  interval_of_check _ 2560 128 (by decide +kernel)
theorem group1001_pairs_02688 :
    Interval (group1001.pairTest FacetUniverses.FullSix0.cells) 2688 2758 :=
  interval_of_check _ 2688 70 (by decide +kernel)
theorem group1001_facts : group1001.Facts FacetUniverses.FullSix0.cells :=
  group1001.facts_of_checks _ group1001_header (interval_append _ 0 1408 2758 (interval_append _ 0 640 1408 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1001_pairs_00000 group1001_pairs_00128) (interval_append _ 256 384 640 group1001_pairs_00256 (interval_append _ 384 512 640 group1001_pairs_00384 group1001_pairs_00512))) (interval_append _ 640 1024 1408 (interval_append _ 640 768 1024 group1001_pairs_00640 (interval_append _ 768 896 1024 group1001_pairs_00768 group1001_pairs_00896)) (interval_append _ 1024 1152 1408 group1001_pairs_01024 (interval_append _ 1152 1280 1408 group1001_pairs_01152 group1001_pairs_01280)))) (interval_append _ 1408 2048 2758 (interval_append _ 1408 1664 2048 (interval_append _ 1408 1536 1664 group1001_pairs_01408 group1001_pairs_01536) (interval_append _ 1664 1792 2048 group1001_pairs_01664 (interval_append _ 1792 1920 2048 group1001_pairs_01792 group1001_pairs_01920))) (interval_append _ 2048 2432 2758 (interval_append _ 2048 2176 2432 group1001_pairs_02048 (interval_append _ 2176 2304 2432 group1001_pairs_02176 group1001_pairs_02304)) (interval_append _ 2432 2560 2758 group1001_pairs_02432 (interval_append _ 2560 2688 2758 group1001_pairs_02560 group1001_pairs_02688)))))
#print axioms group1001_facts
theorem group1002_header : group1002.headerCheck = true := by
  decide +kernel
theorem group1002_pairs_00000 :
    Interval (group1002.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1002_pairs_00128 :
    Interval (group1002.pairTest FacetUniverses.FullSix0.cells) 128 214 :=
  interval_of_check _ 128 86 (by decide +kernel)
theorem group1002_facts : group1002.Facts FacetUniverses.FullSix0.cells :=
  group1002.facts_of_checks _ group1002_header (interval_append _ 0 128 214 group1002_pairs_00000 group1002_pairs_00128)
#print axioms group1002_facts
theorem group1003_header : group1003.headerCheck = true := by
  decide +kernel
theorem group1003_pairs_00000 :
    Interval (group1003.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1003_pairs_00128 :
    Interval (group1003.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group1003_pairs_00256 :
    Interval (group1003.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group1003_pairs_00384 :
    Interval (group1003.pairTest FacetUniverses.FullSix0.cells) 384 421 :=
  interval_of_check _ 384 37 (by decide +kernel)
theorem group1003_facts : group1003.Facts FacetUniverses.FullSix0.cells :=
  group1003.facts_of_checks _ group1003_header (interval_append _ 0 256 421 (interval_append _ 0 128 256 group1003_pairs_00000 group1003_pairs_00128) (interval_append _ 256 384 421 group1003_pairs_00256 group1003_pairs_00384))
#print axioms group1003_facts
theorem group1004_header : group1004.headerCheck = true := by
  decide +kernel
theorem group1004_pairs_00000 :
    Interval (group1004.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1004_pairs_00128 :
    Interval (group1004.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group1004_pairs_00256 :
    Interval (group1004.pairTest FacetUniverses.FullSix0.cells) 256 367 :=
  interval_of_check _ 256 111 (by decide +kernel)
theorem group1004_facts : group1004.Facts FacetUniverses.FullSix0.cells :=
  group1004.facts_of_checks _ group1004_header (interval_append _ 0 128 367 group1004_pairs_00000 (interval_append _ 128 256 367 group1004_pairs_00128 group1004_pairs_00256))
#print axioms group1004_facts
end Papers.RationalityTen.SharedFrameCatalogue
