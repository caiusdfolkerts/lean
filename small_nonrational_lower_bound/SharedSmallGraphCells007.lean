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
theorem cells_007_b1792 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 1800 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 8 (by decide +kernel)

theorem cells_007_b1800 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1800 1808 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1800 8 (by decide +kernel)

theorem cells_007_b1808 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1808 1816 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1808 8 (by decide +kernel)

theorem cells_007_b1816 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1816 1824 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1816 8 (by decide +kernel)

theorem cells_007_b1824 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1824 1832 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1824 8 (by decide +kernel)

theorem cells_007_b1832 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1832 1840 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1832 8 (by decide +kernel)

theorem cells_007_b1840 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1840 1848 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1840 8 (by decide +kernel)

theorem cells_007_b1848 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1848 1856 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1848 8 (by decide +kernel)

theorem cells_007_b1856 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1856 1864 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1856 8 (by decide +kernel)

theorem cells_007_b1864 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1864 1872 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1864 8 (by decide +kernel)

theorem cells_007_b1872 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1872 1880 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1872 8 (by decide +kernel)

theorem cells_007_b1880 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1880 1888 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1880 8 (by decide +kernel)

theorem cells_007_b1888 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1888 1896 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1888 8 (by decide +kernel)

theorem cells_007_b1896 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1896 1904 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1896 8 (by decide +kernel)

theorem cells_007_b1904 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1904 1912 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1904 8 (by decide +kernel)

theorem cells_007_b1912 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1912 1920 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1912 8 (by decide +kernel)

theorem cells_007_b1920 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1920 1928 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1920 8 (by decide +kernel)

theorem cells_007_b1928 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1928 1936 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1928 8 (by decide +kernel)

theorem cells_007_b1936 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1936 1944 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1936 8 (by decide +kernel)

theorem cells_007_b1944 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1944 1952 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1944 8 (by decide +kernel)

theorem cells_007_b1952 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1952 1960 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1952 8 (by decide +kernel)

theorem cells_007_b1960 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1960 1968 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1960 8 (by decide +kernel)

theorem cells_007_b1968 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1968 1976 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1968 8 (by decide +kernel)

theorem cells_007_b1976 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1976 1984 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1976 8 (by decide +kernel)

theorem cells_007_b1984 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1984 1992 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1984 8 (by decide +kernel)

theorem cells_007_b1992 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1992 2000 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1992 8 (by decide +kernel)

theorem cells_007_b2000 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2000 2008 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2000 8 (by decide +kernel)

theorem cells_007_b2008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2008 2016 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2008 8 (by decide +kernel)

theorem cells_007_b2016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2016 2024 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2016 8 (by decide +kernel)

theorem cells_007_b2024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2024 2032 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2024 8 (by decide +kernel)

theorem cells_007_b2032 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2032 2040 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2032 8 (by decide +kernel)

theorem cells_007_b2040 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2040 2048 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2040 8 (by decide +kernel)

theorem cells_007 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 2048 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 1920 2048
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 1856 1920
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 1824 1856
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 1808 1824
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 1800 1808
 cells_007_b1792
 cells_007_b1800)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1808 1816 1824
 cells_007_b1808
 cells_007_b1816))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1824 1840 1856
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1824 1832 1840
 cells_007_b1824
 cells_007_b1832)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1840 1848 1856
 cells_007_b1840
 cells_007_b1848)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1856 1888 1920
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1856 1872 1888
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1856 1864 1872
 cells_007_b1856
 cells_007_b1864)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1872 1880 1888
 cells_007_b1872
 cells_007_b1880))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1888 1904 1920
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1888 1896 1904
 cells_007_b1888
 cells_007_b1896)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1904 1912 1920
 cells_007_b1904
 cells_007_b1912))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1920 1984 2048
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1920 1952 1984
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1920 1936 1952
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1920 1928 1936
 cells_007_b1920
 cells_007_b1928)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1936 1944 1952
 cells_007_b1936
 cells_007_b1944))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1952 1968 1984
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1952 1960 1968
 cells_007_b1952
 cells_007_b1960)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1968 1976 1984
 cells_007_b1968
 cells_007_b1976)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1984 2016 2048
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1984 2000 2016
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1984 1992 2000
 cells_007_b1984
 cells_007_b1992)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2000 2008 2016
 cells_007_b2000
 cells_007_b2008))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2016 2032 2048
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2016 2024 2032
 cells_007_b2016
 cells_007_b2024)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2032 2040 2048
 cells_007_b2032
 cells_007_b2040)))))
end Papers.RationalityTen.SharedSmallGraph
