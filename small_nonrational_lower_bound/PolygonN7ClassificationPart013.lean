module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart012

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join_2 01728 01744 1728 1744 1736 01736
cert_terminal_data_join 01712 01744 1712 1744 1728 01728
cert_terminal_data_join_2 01744 01760 1744 1760 1752 01752
cert_terminal_data_join_2 01760 01776 1760 1776 1768 01768
cert_terminal_data_join 01744 01776 1744 1776 1760 01760
cert_terminal_data_join 01712 01776 1712 1776 1744 01744
cert_terminal_data_join 01656 01776 1656 1776 1712 01712
cert_terminal_data_join_2 01784 01800 1784 1800 1792 01792
cert_terminal_data_join_3 01776 01800 1776 1800 1784 01784
cert_terminal_data_join_2 01800 01816 1800 1816 1808 01808
cert_terminal_data_join_2 01816 01832 1816 1832 1824 01824
cert_terminal_data_join 01800 01832 1800 1832 1816 01816
cert_terminal_data_join 01776 01832 1776 1832 1800 01800
cert_terminal_data_join_2 01832 01848 1832 1848 1840 01840
cert_terminal_data_join_2 01848 01864 1848 1864 1856 01856
cert_terminal_data_join 01832 01864 1832 1864 1848 01848
cert_terminal_data_join_2 01864 01880 1864 1880 1872 01872
cert_terminal_data_join_2 01880 01896 1880 1896 1888 01888
cert_terminal_data_join 01864 01896 1864 1896 1880 01880
cert_terminal_data_join 01832 01896 1832 1896 1864 01864
cert_terminal_data_join 01776 01896 1776 1896 1832 01832
cert_terminal_data_join 01656 01896 1656 1896 1776 01776
cert_terminal_data_join 01416 01896 1416 1896 1656 01656
cert_terminal_data_join 00944 01896 944 1896 1416 01416
cert_terminal_data_join 00000 01896 0 1896 944 00944
cert_terminal_data_join_2 01904 01920 1904 1920 1912 01912
cert_terminal_data_join_3 01896 01920 1896 1920 1904 01904
cert_terminal_data_join_2 01920 01936 1920 1936 1928 01928
cert_terminal_data_join_2 01936 01952 1936 1952 1944 01944
cert_terminal_data_join 01920 01952 1920 1952 1936 01936
cert_terminal_data_join 01896 01952 1896 1952 1920 01920
cert_terminal_data_join_2 01960 01976 1960 1976 1968 01968
cert_terminal_data_join_3 01952 01976 1952 1976 1960 01960
cert_terminal_data_join_2 01976 01992 1976 1992 1984 01984
cert_terminal_data_join_2 01992 02008 1992 2008 2000 02000
cert_terminal_data_join 01976 02008 1976 2008 1992 01992
cert_terminal_data_join 01952 02008 1952 2008 1976 01976
cert_terminal_data_join 01896 02008 1896 2008 1952 01952
cert_terminal_data_join_2 02016 02032 2016 2032 2024 02024
cert_terminal_data_join_3 02008 02032 2008 2032 2016 02016
cert_terminal_data_join_2 02032 02048 2032 2048 2040 02040
cert_terminal_data_join_2 02048 02064 2048 2064 2056 02056
cert_terminal_data_join 02032 02064 2032 2064 2048 02048
cert_terminal_data_join 02008 02064 2008 2064 2032 02032
cert_terminal_data_join_2 02064 02080 2064 2080 2072 02072
cert_terminal_data_join_2 02080 02096 2080 2096 2088 02088
cert_terminal_data_join 02064 02096 2064 2096 2080 02080
cert_terminal_data_join_2 02096 02112 2096 2112 2104 02104
cert_terminal_data_join_2 02112 02128 2112 2128 2120 02120
cert_terminal_data_join 02096 02128 2096 2128 2112 02112
cert_terminal_data_join 02064 02128 2064 2128 2096 02096
cert_terminal_data_join 02008 02128 2008 2128 2064 02064
cert_terminal_data_join 01896 02128 1896 2128 2008 02008
cert_terminal_data_join_2 02136 02152 2136 2152 2144 02144
cert_terminal_data_join_3 02128 02152 2128 2152 2136 02136
cert_terminal_data_join_2 02152 02168 2152 2168 2160 02160
cert_terminal_data_join_2 02168 02184 2168 2184 2176 02176
cert_terminal_data_join 02152 02184 2152 2184 2168 02168
cert_terminal_data_join 02128 02184 2128 2184 2152 02152
cert_terminal_data_join_2 02184 02200 2184 2200 2192 02192
cert_terminal_data_join_2 02200 02216 2200 2216 2208 02208
cert_terminal_data_join 02184 02216 2184 2216 2200 02200
cert_terminal_data_join_2 02216 02232 2216 2232 2224 02224
theorem terminal_data_join_02232_02248 : FiniteChecks.Interval terminalTest 2232 2248 :=
  FiniteChecks.interval_append terminalTest 2232 2240 2248 terminal_data_02232 terminal_data_02240


end Papers.RationalityTen.ConcretePolygonClassification.N7
