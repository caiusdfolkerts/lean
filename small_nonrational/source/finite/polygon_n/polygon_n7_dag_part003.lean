module
prelude
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

theorem nodes_part003_00768 : FiniteChecks.Interval nodeTest 768 776 :=
  FiniteChecks.interval_of_check nodeTest 768 8 (by decide +kernel)

theorem nodes_part003_00776 : FiniteChecks.Interval nodeTest 776 784 :=
  FiniteChecks.interval_of_check nodeTest 776 8 (by decide +kernel)

theorem nodes_part003_00784 : FiniteChecks.Interval nodeTest 784 792 :=
  FiniteChecks.interval_of_check nodeTest 784 8 (by decide +kernel)

theorem nodes_part003_00792 : FiniteChecks.Interval nodeTest 792 800 :=
  FiniteChecks.interval_of_check nodeTest 792 8 (by decide +kernel)

theorem nodes_part003_00800 : FiniteChecks.Interval nodeTest 800 808 :=
  FiniteChecks.interval_of_check nodeTest 800 8 (by decide +kernel)

theorem nodes_part003_00808 : FiniteChecks.Interval nodeTest 808 816 :=
  FiniteChecks.interval_of_check nodeTest 808 8 (by decide +kernel)

theorem nodes_part003_00816 : FiniteChecks.Interval nodeTest 816 824 :=
  FiniteChecks.interval_of_check nodeTest 816 8 (by decide +kernel)

theorem nodes_part003_00824 : FiniteChecks.Interval nodeTest 824 832 :=
  FiniteChecks.interval_of_check nodeTest 824 8 (by decide +kernel)

theorem nodes_part003_00832 : FiniteChecks.Interval nodeTest 832 840 :=
  FiniteChecks.interval_of_check nodeTest 832 8 (by decide +kernel)

theorem nodes_part003_00840 : FiniteChecks.Interval nodeTest 840 848 :=
  FiniteChecks.interval_of_check nodeTest 840 8 (by decide +kernel)

theorem nodes_part003_00848 : FiniteChecks.Interval nodeTest 848 856 :=
  FiniteChecks.interval_of_check nodeTest 848 8 (by decide +kernel)

theorem nodes_part003_00856 : FiniteChecks.Interval nodeTest 856 864 :=
  FiniteChecks.interval_of_check nodeTest 856 8 (by decide +kernel)

theorem nodes_part003_00864 : FiniteChecks.Interval nodeTest 864 872 :=
  FiniteChecks.interval_of_check nodeTest 864 8 (by decide +kernel)

theorem nodes_part003_00872 : FiniteChecks.Interval nodeTest 872 880 :=
  FiniteChecks.interval_of_check nodeTest 872 8 (by decide +kernel)

theorem nodes_part003_00880 : FiniteChecks.Interval nodeTest 880 888 :=
  FiniteChecks.interval_of_check nodeTest 880 8 (by decide +kernel)

theorem nodes_part003_00888 : FiniteChecks.Interval nodeTest 888 896 :=
  FiniteChecks.interval_of_check nodeTest 888 8 (by decide +kernel)

theorem nodes_part003_00896 : FiniteChecks.Interval nodeTest 896 904 :=
  FiniteChecks.interval_of_check nodeTest 896 8 (by decide +kernel)

theorem nodes_part003_00904 : FiniteChecks.Interval nodeTest 904 912 :=
  FiniteChecks.interval_of_check nodeTest 904 8 (by decide +kernel)

theorem nodes_part003_00912 : FiniteChecks.Interval nodeTest 912 920 :=
  FiniteChecks.interval_of_check nodeTest 912 8 (by decide +kernel)

theorem nodes_part003_00920 : FiniteChecks.Interval nodeTest 920 928 :=
  FiniteChecks.interval_of_check nodeTest 920 8 (by decide +kernel)

theorem nodes_part003_00928 : FiniteChecks.Interval nodeTest 928 936 :=
  FiniteChecks.interval_of_check nodeTest 928 8 (by decide +kernel)

theorem nodes_part003_00936 : FiniteChecks.Interval nodeTest 936 944 :=
  FiniteChecks.interval_of_check nodeTest 936 8 (by decide +kernel)

theorem nodes_part003_00944 : FiniteChecks.Interval nodeTest 944 952 :=
  FiniteChecks.interval_of_check nodeTest 944 8 (by decide +kernel)

theorem nodes_part003_00952 : FiniteChecks.Interval nodeTest 952 960 :=
  FiniteChecks.interval_of_check nodeTest 952 8 (by decide +kernel)

theorem nodes_part003_00960 : FiniteChecks.Interval nodeTest 960 968 :=
  FiniteChecks.interval_of_check nodeTest 960 8 (by decide +kernel)

theorem nodes_part003_00968 : FiniteChecks.Interval nodeTest 968 976 :=
  FiniteChecks.interval_of_check nodeTest 968 8 (by decide +kernel)

theorem nodes_part003_00976 : FiniteChecks.Interval nodeTest 976 984 :=
  FiniteChecks.interval_of_check nodeTest 976 8 (by decide +kernel)

theorem nodes_part003_00984 : FiniteChecks.Interval nodeTest 984 992 :=
  FiniteChecks.interval_of_check nodeTest 984 8 (by decide +kernel)

theorem nodes_part003_00992 : FiniteChecks.Interval nodeTest 992 1000 :=
  FiniteChecks.interval_of_check nodeTest 992 8 (by decide +kernel)

theorem nodes_part003_01000 : FiniteChecks.Interval nodeTest 1000 1008 :=
  FiniteChecks.interval_of_check nodeTest 1000 8 (by decide +kernel)

theorem nodes_part003_01008 : FiniteChecks.Interval nodeTest 1008 1016 :=
  FiniteChecks.interval_of_check nodeTest 1008 8 (by decide +kernel)

theorem nodes_part003_01016 : FiniteChecks.Interval nodeTest 1016 1024 :=
  FiniteChecks.interval_of_check nodeTest 1016 8 (by decide +kernel)

theorem nodes_part003_join_00768_00784 : FiniteChecks.Interval nodeTest 768 784 :=
  FiniteChecks.interval_append nodeTest 768 776 784 nodes_part003_00768 nodes_part003_00776

theorem nodes_part003_join_00784_00800 : FiniteChecks.Interval nodeTest 784 800 :=
  FiniteChecks.interval_append nodeTest 784 792 800 nodes_part003_00784 nodes_part003_00792

theorem nodes_part003_join_00768_00800 : FiniteChecks.Interval nodeTest 768 800 :=
  FiniteChecks.interval_append nodeTest 768 784 800 nodes_part003_join_00768_00784 nodes_part003_join_00784_00800

theorem nodes_part003_join_00800_00816 : FiniteChecks.Interval nodeTest 800 816 :=
  FiniteChecks.interval_append nodeTest 800 808 816 nodes_part003_00800 nodes_part003_00808

theorem nodes_part003_join_00816_00832 : FiniteChecks.Interval nodeTest 816 832 :=
  FiniteChecks.interval_append nodeTest 816 824 832 nodes_part003_00816 nodes_part003_00824

theorem nodes_part003_join_00800_00832 : FiniteChecks.Interval nodeTest 800 832 :=
  FiniteChecks.interval_append nodeTest 800 816 832 nodes_part003_join_00800_00816 nodes_part003_join_00816_00832

theorem nodes_part003_join_00768_00832 : FiniteChecks.Interval nodeTest 768 832 :=
  FiniteChecks.interval_append nodeTest 768 800 832 nodes_part003_join_00768_00800 nodes_part003_join_00800_00832

theorem nodes_part003_join_00832_00848 : FiniteChecks.Interval nodeTest 832 848 :=
  FiniteChecks.interval_append nodeTest 832 840 848 nodes_part003_00832 nodes_part003_00840

theorem nodes_part003_join_00848_00864 : FiniteChecks.Interval nodeTest 848 864 :=
  FiniteChecks.interval_append nodeTest 848 856 864 nodes_part003_00848 nodes_part003_00856

theorem nodes_part003_join_00832_00864 : FiniteChecks.Interval nodeTest 832 864 :=
  FiniteChecks.interval_append nodeTest 832 848 864 nodes_part003_join_00832_00848 nodes_part003_join_00848_00864

theorem nodes_part003_join_00864_00880 : FiniteChecks.Interval nodeTest 864 880 :=
  FiniteChecks.interval_append nodeTest 864 872 880 nodes_part003_00864 nodes_part003_00872

theorem nodes_part003_join_00880_00896 : FiniteChecks.Interval nodeTest 880 896 :=
  FiniteChecks.interval_append nodeTest 880 888 896 nodes_part003_00880 nodes_part003_00888

theorem nodes_part003_join_00864_00896 : FiniteChecks.Interval nodeTest 864 896 :=
  FiniteChecks.interval_append nodeTest 864 880 896 nodes_part003_join_00864_00880 nodes_part003_join_00880_00896

theorem nodes_part003_join_00832_00896 : FiniteChecks.Interval nodeTest 832 896 :=
  FiniteChecks.interval_append nodeTest 832 864 896 nodes_part003_join_00832_00864 nodes_part003_join_00864_00896

theorem nodes_part003_join_00768_00896 : FiniteChecks.Interval nodeTest 768 896 :=
  FiniteChecks.interval_append nodeTest 768 832 896 nodes_part003_join_00768_00832 nodes_part003_join_00832_00896

theorem nodes_part003_join_00896_00912 : FiniteChecks.Interval nodeTest 896 912 :=
  FiniteChecks.interval_append nodeTest 896 904 912 nodes_part003_00896 nodes_part003_00904

theorem nodes_part003_join_00912_00928 : FiniteChecks.Interval nodeTest 912 928 :=
  FiniteChecks.interval_append nodeTest 912 920 928 nodes_part003_00912 nodes_part003_00920

theorem nodes_part003_join_00896_00928 : FiniteChecks.Interval nodeTest 896 928 :=
  FiniteChecks.interval_append nodeTest 896 912 928 nodes_part003_join_00896_00912 nodes_part003_join_00912_00928

theorem nodes_part003_join_00928_00944 : FiniteChecks.Interval nodeTest 928 944 :=
  FiniteChecks.interval_append nodeTest 928 936 944 nodes_part003_00928 nodes_part003_00936

theorem nodes_part003_join_00944_00960 : FiniteChecks.Interval nodeTest 944 960 :=
  FiniteChecks.interval_append nodeTest 944 952 960 nodes_part003_00944 nodes_part003_00952

theorem nodes_part003_join_00928_00960 : FiniteChecks.Interval nodeTest 928 960 :=
  FiniteChecks.interval_append nodeTest 928 944 960 nodes_part003_join_00928_00944 nodes_part003_join_00944_00960

theorem nodes_part003_join_00896_00960 : FiniteChecks.Interval nodeTest 896 960 :=
  FiniteChecks.interval_append nodeTest 896 928 960 nodes_part003_join_00896_00928 nodes_part003_join_00928_00960

theorem nodes_part003_join_00960_00976 : FiniteChecks.Interval nodeTest 960 976 :=
  FiniteChecks.interval_append nodeTest 960 968 976 nodes_part003_00960 nodes_part003_00968

theorem nodes_part003_join_00976_00992 : FiniteChecks.Interval nodeTest 976 992 :=
  FiniteChecks.interval_append nodeTest 976 984 992 nodes_part003_00976 nodes_part003_00984

theorem nodes_part003_join_00960_00992 : FiniteChecks.Interval nodeTest 960 992 :=
  FiniteChecks.interval_append nodeTest 960 976 992 nodes_part003_join_00960_00976 nodes_part003_join_00976_00992

theorem nodes_part003_join_00992_01008 : FiniteChecks.Interval nodeTest 992 1008 :=
  FiniteChecks.interval_append nodeTest 992 1000 1008 nodes_part003_00992 nodes_part003_01000

theorem nodes_part003_join_01008_01024 : FiniteChecks.Interval nodeTest 1008 1024 :=
  FiniteChecks.interval_append nodeTest 1008 1016 1024 nodes_part003_01008 nodes_part003_01016

theorem nodes_part003_join_00992_01024 : FiniteChecks.Interval nodeTest 992 1024 :=
  FiniteChecks.interval_append nodeTest 992 1008 1024 nodes_part003_join_00992_01008 nodes_part003_join_01008_01024

theorem nodes_part003_join_00960_01024 : FiniteChecks.Interval nodeTest 960 1024 :=
  FiniteChecks.interval_append nodeTest 960 992 1024 nodes_part003_join_00960_00992 nodes_part003_join_00992_01024

theorem nodes_part003_join_00896_01024 : FiniteChecks.Interval nodeTest 896 1024 :=
  FiniteChecks.interval_append nodeTest 896 960 1024 nodes_part003_join_00896_00960 nodes_part003_join_00960_01024

theorem nodes_part003_join_00768_01024 : FiniteChecks.Interval nodeTest 768 1024 :=
  FiniteChecks.interval_append nodeTest 768 896 1024 nodes_part003_join_00768_00896 nodes_part003_join_00896_01024

end Papers.RationalityTen.PolygonGrowth.N7
