module
prelude
public import SharedSmallCellPoolCheck000
public import SharedSmallCellPoolCheck001
public import SharedSmallCellPoolCheck002
public import SharedSmallCellPoolCheck003
public import SharedSmallCellPoolCheck004
public import SharedSmallCellPoolCheck005
public import SharedSmallCellPoolCheck006
public import SharedSmallCellPoolCheck007
public import SharedSmallCellPoolCheck008
public import SharedSmallCellPoolCheck009
public import SharedSmallCellPoolCheck010
public import SharedSmallCellPoolCheck011
public import SharedSmallCellPoolCheck012
public import SharedSmallCellPoolCheck013
public import SharedSmallCellPoolCheck014
public import SharedSmallCellPoolCheck015
public import SharedSmallCellPoolCheck016
public import SharedSmallCellPoolCheck017
public import SharedSmallCellPoolCheck018
public import SharedSmallCellPoolCheck019
public import SharedSmallCellPoolCheck020
public import SharedSmallCellPoolCheck021
public import SharedSmallCellPoolCheck022
public import SharedSmallCellPoolCheck023
public import SharedSmallCellPoolCheck024
public import SharedSmallCellPoolCheck025
public import SharedSmallCellPoolCheck026
public import SharedSmallCellPoolCheck027
public import SharedSmallCellPoolCheck028
public import SharedSmallCellPoolCheck029
public import SharedSmallCellPoolCheck030
public import SharedSmallCellPoolCheck031
public import SharedSmallCellPoolCheck032
public import SharedSmallCellPoolCheck033
public import SharedSmallCellPoolCheck034
public import SharedSmallCellPoolCheck035
public import SharedSmallCellPoolCheck036
public import SharedSmallCellPoolCheck037
public import SharedSmallCellPoolCheck038
public import SharedSmallCellPoolCheck039
public import SharedSmallCellPoolCheck040
public import SharedSmallCellPoolCheck041
public import SharedSmallCellPoolCheck042
public import SharedSmallCellPoolCheck043
public import SharedSmallCellPoolCheck044
public import SharedSmallCellPoolCheck045
public import SharedSmallCellPoolCheck046
public import SharedSmallCellPoolCheck047
public import SharedSmallCellPoolCheck048
public import SharedSmallCellPoolCheck049
public import SharedSmallCellPoolCheck050

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem checked : Interval test 0 count :=
  (FiniteChecks.interval_append test 0 3200 6510
  (FiniteChecks.interval_append test 0 1536 3200
  (FiniteChecks.interval_append test 0 768 1536
  (FiniteChecks.interval_append test 0 384 768
  (FiniteChecks.interval_append test 0 128 384
  Check000.checked
  (FiniteChecks.interval_append test 128 256 384
  Check001.checked
  Check002.checked))
  (FiniteChecks.interval_append test 384 512 768
  Check003.checked
  (FiniteChecks.interval_append test 512 640 768
  Check004.checked
  Check005.checked)))
  (FiniteChecks.interval_append test 768 1152 1536
  (FiniteChecks.interval_append test 768 896 1152
  Check006.checked
  (FiniteChecks.interval_append test 896 1024 1152
  Check007.checked
  Check008.checked))
  (FiniteChecks.interval_append test 1152 1280 1536
  Check009.checked
  (FiniteChecks.interval_append test 1280 1408 1536
  Check010.checked
  Check011.checked))))
  (FiniteChecks.interval_append test 1536 2304 3200
  (FiniteChecks.interval_append test 1536 1920 2304
  (FiniteChecks.interval_append test 1536 1664 1920
  Check012.checked
  (FiniteChecks.interval_append test 1664 1792 1920
  Check013.checked
  Check014.checked))
  (FiniteChecks.interval_append test 1920 2048 2304
  Check015.checked
  (FiniteChecks.interval_append test 2048 2176 2304
  Check016.checked
  Check017.checked)))
  (FiniteChecks.interval_append test 2304 2688 3200
  (FiniteChecks.interval_append test 2304 2432 2688
  Check018.checked
  (FiniteChecks.interval_append test 2432 2560 2688
  Check019.checked
  Check020.checked))
  (FiniteChecks.interval_append test 2688 2944 3200
  (FiniteChecks.interval_append test 2688 2816 2944
  Check021.checked
  Check022.checked)
  (FiniteChecks.interval_append test 2944 3072 3200
  Check023.checked
  Check024.checked)))))
  (FiniteChecks.interval_append test 3200 4864 6510
  (FiniteChecks.interval_append test 3200 3968 4864
  (FiniteChecks.interval_append test 3200 3584 3968
  (FiniteChecks.interval_append test 3200 3328 3584
  Check025.checked
  (FiniteChecks.interval_append test 3328 3456 3584
  Check026.checked
  Check027.checked))
  (FiniteChecks.interval_append test 3584 3712 3968
  Check028.checked
  (FiniteChecks.interval_append test 3712 3840 3968
  Check029.checked
  Check030.checked)))
  (FiniteChecks.interval_append test 3968 4352 4864
  (FiniteChecks.interval_append test 3968 4096 4352
  Check031.checked
  (FiniteChecks.interval_append test 4096 4224 4352
  Check032.checked
  Check033.checked))
  (FiniteChecks.interval_append test 4352 4608 4864
  (FiniteChecks.interval_append test 4352 4480 4608
  Check034.checked
  Check035.checked)
  (FiniteChecks.interval_append test 4608 4736 4864
  Check036.checked
  Check037.checked))))
  (FiniteChecks.interval_append test 4864 5632 6510
  (FiniteChecks.interval_append test 4864 5248 5632
  (FiniteChecks.interval_append test 4864 4992 5248
  Check038.checked
  (FiniteChecks.interval_append test 4992 5120 5248
  Check039.checked
  Check040.checked))
  (FiniteChecks.interval_append test 5248 5376 5632
  Check041.checked
  (FiniteChecks.interval_append test 5376 5504 5632
  Check042.checked
  Check043.checked)))
  (FiniteChecks.interval_append test 5632 6016 6510
  (FiniteChecks.interval_append test 5632 5760 6016
  Check044.checked
  (FiniteChecks.interval_append test 5760 5888 6016
  Check045.checked
  Check046.checked))
  (FiniteChecks.interval_append test 6016 6272 6510
  (FiniteChecks.interval_append test 6016 6144 6272
  Check047.checked
  Check048.checked)
  (FiniteChecks.interval_append test 6272 6400 6510
  Check049.checked
  Check050.checked))))))
theorem facts (c : Fin count) :
    (entry c).Facts (FacetUniverses.FullSmall.cells c) SharedSmallGraph.withinMask := by
  apply Entry.facts_of_check
  exact fin_of_interval (fun c : Fin count =>
    (entry c).check (FacetUniverses.FullSmall.cells c) SharedSmallGraph.withinMask) checked c
#print axioms facts
end Papers.RationalityTen.SharedSmallCellPool
