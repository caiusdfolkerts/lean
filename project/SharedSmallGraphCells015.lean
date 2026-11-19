module
prelude
public import SharedSmallGraphData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cells_015_b3840 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 3848 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 8 (by decide +kernel)

theorem cells_015_b3848 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3848 3856 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3848 8 (by decide +kernel)

theorem cells_015_b3856 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3856 3864 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3856 8 (by decide +kernel)

theorem cells_015_b3864 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3864 3872 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3864 8 (by decide +kernel)

theorem cells_015_b3872 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3872 3880 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3872 8 (by decide +kernel)

theorem cells_015_b3880 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3880 3888 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3880 8 (by decide +kernel)

theorem cells_015_b3888 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3888 3896 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3888 8 (by decide +kernel)

theorem cells_015_b3896 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3896 3904 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3896 8 (by decide +kernel)

theorem cells_015_b3904 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3904 3912 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3904 8 (by decide +kernel)

theorem cells_015_b3912 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3912 3920 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3912 8 (by decide +kernel)

theorem cells_015_b3920 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3920 3928 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3920 8 (by decide +kernel)

theorem cells_015_b3928 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3928 3936 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3928 8 (by decide +kernel)

theorem cells_015_b3936 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3936 3944 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3936 8 (by decide +kernel)

theorem cells_015_b3944 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3944 3952 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3944 8 (by decide +kernel)

theorem cells_015_b3952 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3952 3960 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3952 8 (by decide +kernel)

theorem cells_015_b3960 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3960 3968 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3960 8 (by decide +kernel)

theorem cells_015_b3968 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3968 3976 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3968 8 (by decide +kernel)

theorem cells_015_b3976 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3976 3984 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3976 8 (by decide +kernel)

theorem cells_015_b3984 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3984 3992 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3984 8 (by decide +kernel)

theorem cells_015_b3992 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3992 4000 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3992 8 (by decide +kernel)

theorem cells_015_b4000 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4000 4008 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4000 8 (by decide +kernel)

theorem cells_015_b4008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4008 4016 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4008 8 (by decide +kernel)

theorem cells_015_b4016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4016 4024 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4016 8 (by decide +kernel)

theorem cells_015_b4024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4024 4032 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4024 8 (by decide +kernel)

theorem cells_015_b4032 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4032 4040 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4032 8 (by decide +kernel)

theorem cells_015_b4040 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4040 4048 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4040 8 (by decide +kernel)

theorem cells_015_b4048 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4048 4056 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4048 8 (by decide +kernel)

theorem cells_015_b4056 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4056 4064 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4056 8 (by decide +kernel)

theorem cells_015_b4064 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4064 4072 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4064 8 (by decide +kernel)

theorem cells_015_b4072 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4072 4080 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4072 8 (by decide +kernel)

theorem cells_015_b4080 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4080 4088 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4080 8 (by decide +kernel)

theorem cells_015_b4088 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4088 4096 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4088 8 (by decide +kernel)

theorem cells_015 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 4096 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 3968 4096
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 3904 3968
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 3872 3904
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 3856 3872
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3840 3848 3856
 cells_015_b3840
 cells_015_b3848)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3856 3864 3872
 cells_015_b3856
 cells_015_b3864))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3872 3888 3904
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3872 3880 3888
 cells_015_b3872
 cells_015_b3880)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3888 3896 3904
 cells_015_b3888
 cells_015_b3896)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3904 3936 3968
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3904 3920 3936
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3904 3912 3920
 cells_015_b3904
 cells_015_b3912)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3920 3928 3936
 cells_015_b3920
 cells_015_b3928))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3936 3952 3968
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3936 3944 3952
 cells_015_b3936
 cells_015_b3944)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3952 3960 3968
 cells_015_b3952
 cells_015_b3960))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3968 4032 4096
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3968 4000 4032
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3968 3984 4000
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3968 3976 3984
 cells_015_b3968
 cells_015_b3976)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3984 3992 4000
 cells_015_b3984
 cells_015_b3992))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4000 4016 4032
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4000 4008 4016
 cells_015_b4000
 cells_015_b4008)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4016 4024 4032
 cells_015_b4016
 cells_015_b4024)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4032 4064 4096
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4032 4048 4064
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4032 4040 4048
 cells_015_b4032
 cells_015_b4040)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4048 4056 4064
 cells_015_b4048
 cells_015_b4056))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4064 4080 4096
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4064 4072 4080
 cells_015_b4064
 cells_015_b4072)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4080 4088 4096
 cells_015_b4080
 cells_015_b4088)))))
end Papers.RationalityTen.SharedSmallGraph
