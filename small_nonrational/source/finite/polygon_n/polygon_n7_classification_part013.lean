module

public import PolygonN7ClassificationPart012

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_01728_01744 : FiniteChecks.Interval terminalTest 1728 1744 :=
  FiniteChecks.interval_append terminalTest 1728 1736 1744 terminal_data_01728 terminal_data_01736

theorem terminal_data_join_01712_01744 : FiniteChecks.Interval terminalTest 1712 1744 :=
  FiniteChecks.interval_append terminalTest 1712 1728 1744 terminal_data_join_01712_01728 terminal_data_join_01728_01744

theorem terminal_data_join_01744_01760 : FiniteChecks.Interval terminalTest 1744 1760 :=
  FiniteChecks.interval_append terminalTest 1744 1752 1760 terminal_data_01744 terminal_data_01752

theorem terminal_data_join_01760_01776 : FiniteChecks.Interval terminalTest 1760 1776 :=
  FiniteChecks.interval_append terminalTest 1760 1768 1776 terminal_data_01760 terminal_data_01768

theorem terminal_data_join_01744_01776 : FiniteChecks.Interval terminalTest 1744 1776 :=
  FiniteChecks.interval_append terminalTest 1744 1760 1776 terminal_data_join_01744_01760 terminal_data_join_01760_01776

theorem terminal_data_join_01712_01776 : FiniteChecks.Interval terminalTest 1712 1776 :=
  FiniteChecks.interval_append terminalTest 1712 1744 1776 terminal_data_join_01712_01744 terminal_data_join_01744_01776

theorem terminal_data_join_01656_01776 : FiniteChecks.Interval terminalTest 1656 1776 :=
  FiniteChecks.interval_append terminalTest 1656 1712 1776 terminal_data_join_01656_01712 terminal_data_join_01712_01776

theorem terminal_data_join_01784_01800 : FiniteChecks.Interval terminalTest 1784 1800 :=
  FiniteChecks.interval_append terminalTest 1784 1792 1800 terminal_data_01784 terminal_data_01792

theorem terminal_data_join_01776_01800 : FiniteChecks.Interval terminalTest 1776 1800 :=
  FiniteChecks.interval_append terminalTest 1776 1784 1800 terminal_data_01776 terminal_data_join_01784_01800

theorem terminal_data_join_01800_01816 : FiniteChecks.Interval terminalTest 1800 1816 :=
  FiniteChecks.interval_append terminalTest 1800 1808 1816 terminal_data_01800 terminal_data_01808

theorem terminal_data_join_01816_01832 : FiniteChecks.Interval terminalTest 1816 1832 :=
  FiniteChecks.interval_append terminalTest 1816 1824 1832 terminal_data_01816 terminal_data_01824

theorem terminal_data_join_01800_01832 : FiniteChecks.Interval terminalTest 1800 1832 :=
  FiniteChecks.interval_append terminalTest 1800 1816 1832 terminal_data_join_01800_01816 terminal_data_join_01816_01832

theorem terminal_data_join_01776_01832 : FiniteChecks.Interval terminalTest 1776 1832 :=
  FiniteChecks.interval_append terminalTest 1776 1800 1832 terminal_data_join_01776_01800 terminal_data_join_01800_01832

theorem terminal_data_join_01832_01848 : FiniteChecks.Interval terminalTest 1832 1848 :=
  FiniteChecks.interval_append terminalTest 1832 1840 1848 terminal_data_01832 terminal_data_01840

theorem terminal_data_join_01848_01864 : FiniteChecks.Interval terminalTest 1848 1864 :=
  FiniteChecks.interval_append terminalTest 1848 1856 1864 terminal_data_01848 terminal_data_01856

theorem terminal_data_join_01832_01864 : FiniteChecks.Interval terminalTest 1832 1864 :=
  FiniteChecks.interval_append terminalTest 1832 1848 1864 terminal_data_join_01832_01848 terminal_data_join_01848_01864

theorem terminal_data_join_01864_01880 : FiniteChecks.Interval terminalTest 1864 1880 :=
  FiniteChecks.interval_append terminalTest 1864 1872 1880 terminal_data_01864 terminal_data_01872

theorem terminal_data_join_01880_01896 : FiniteChecks.Interval terminalTest 1880 1896 :=
  FiniteChecks.interval_append terminalTest 1880 1888 1896 terminal_data_01880 terminal_data_01888

theorem terminal_data_join_01864_01896 : FiniteChecks.Interval terminalTest 1864 1896 :=
  FiniteChecks.interval_append terminalTest 1864 1880 1896 terminal_data_join_01864_01880 terminal_data_join_01880_01896

theorem terminal_data_join_01832_01896 : FiniteChecks.Interval terminalTest 1832 1896 :=
  FiniteChecks.interval_append terminalTest 1832 1864 1896 terminal_data_join_01832_01864 terminal_data_join_01864_01896

theorem terminal_data_join_01776_01896 : FiniteChecks.Interval terminalTest 1776 1896 :=
  FiniteChecks.interval_append terminalTest 1776 1832 1896 terminal_data_join_01776_01832 terminal_data_join_01832_01896

theorem terminal_data_join_01656_01896 : FiniteChecks.Interval terminalTest 1656 1896 :=
  FiniteChecks.interval_append terminalTest 1656 1776 1896 terminal_data_join_01656_01776 terminal_data_join_01776_01896

theorem terminal_data_join_01416_01896 : FiniteChecks.Interval terminalTest 1416 1896 :=
  FiniteChecks.interval_append terminalTest 1416 1656 1896 terminal_data_join_01416_01656 terminal_data_join_01656_01896

theorem terminal_data_join_00944_01896 : FiniteChecks.Interval terminalTest 944 1896 :=
  FiniteChecks.interval_append terminalTest 944 1416 1896 terminal_data_join_00944_01416 terminal_data_join_01416_01896

theorem terminal_data_join_00000_01896 : FiniteChecks.Interval terminalTest 0 1896 :=
  FiniteChecks.interval_append terminalTest 0 944 1896 terminal_data_join_00000_00944 terminal_data_join_00944_01896

theorem terminal_data_join_01904_01920 : FiniteChecks.Interval terminalTest 1904 1920 :=
  FiniteChecks.interval_append terminalTest 1904 1912 1920 terminal_data_01904 terminal_data_01912

theorem terminal_data_join_01896_01920 : FiniteChecks.Interval terminalTest 1896 1920 :=
  FiniteChecks.interval_append terminalTest 1896 1904 1920 terminal_data_01896 terminal_data_join_01904_01920

theorem terminal_data_join_01920_01936 : FiniteChecks.Interval terminalTest 1920 1936 :=
  FiniteChecks.interval_append terminalTest 1920 1928 1936 terminal_data_01920 terminal_data_01928

theorem terminal_data_join_01936_01952 : FiniteChecks.Interval terminalTest 1936 1952 :=
  FiniteChecks.interval_append terminalTest 1936 1944 1952 terminal_data_01936 terminal_data_01944

theorem terminal_data_join_01920_01952 : FiniteChecks.Interval terminalTest 1920 1952 :=
  FiniteChecks.interval_append terminalTest 1920 1936 1952 terminal_data_join_01920_01936 terminal_data_join_01936_01952

theorem terminal_data_join_01896_01952 : FiniteChecks.Interval terminalTest 1896 1952 :=
  FiniteChecks.interval_append terminalTest 1896 1920 1952 terminal_data_join_01896_01920 terminal_data_join_01920_01952

theorem terminal_data_join_01960_01976 : FiniteChecks.Interval terminalTest 1960 1976 :=
  FiniteChecks.interval_append terminalTest 1960 1968 1976 terminal_data_01960 terminal_data_01968

theorem terminal_data_join_01952_01976 : FiniteChecks.Interval terminalTest 1952 1976 :=
  FiniteChecks.interval_append terminalTest 1952 1960 1976 terminal_data_01952 terminal_data_join_01960_01976

theorem terminal_data_join_01976_01992 : FiniteChecks.Interval terminalTest 1976 1992 :=
  FiniteChecks.interval_append terminalTest 1976 1984 1992 terminal_data_01976 terminal_data_01984

theorem terminal_data_join_01992_02008 : FiniteChecks.Interval terminalTest 1992 2008 :=
  FiniteChecks.interval_append terminalTest 1992 2000 2008 terminal_data_01992 terminal_data_02000

theorem terminal_data_join_01976_02008 : FiniteChecks.Interval terminalTest 1976 2008 :=
  FiniteChecks.interval_append terminalTest 1976 1992 2008 terminal_data_join_01976_01992 terminal_data_join_01992_02008

theorem terminal_data_join_01952_02008 : FiniteChecks.Interval terminalTest 1952 2008 :=
  FiniteChecks.interval_append terminalTest 1952 1976 2008 terminal_data_join_01952_01976 terminal_data_join_01976_02008

theorem terminal_data_join_01896_02008 : FiniteChecks.Interval terminalTest 1896 2008 :=
  FiniteChecks.interval_append terminalTest 1896 1952 2008 terminal_data_join_01896_01952 terminal_data_join_01952_02008

theorem terminal_data_join_02016_02032 : FiniteChecks.Interval terminalTest 2016 2032 :=
  FiniteChecks.interval_append terminalTest 2016 2024 2032 terminal_data_02016 terminal_data_02024

theorem terminal_data_join_02008_02032 : FiniteChecks.Interval terminalTest 2008 2032 :=
  FiniteChecks.interval_append terminalTest 2008 2016 2032 terminal_data_02008 terminal_data_join_02016_02032

theorem terminal_data_join_02032_02048 : FiniteChecks.Interval terminalTest 2032 2048 :=
  FiniteChecks.interval_append terminalTest 2032 2040 2048 terminal_data_02032 terminal_data_02040

theorem terminal_data_join_02048_02064 : FiniteChecks.Interval terminalTest 2048 2064 :=
  FiniteChecks.interval_append terminalTest 2048 2056 2064 terminal_data_02048 terminal_data_02056

theorem terminal_data_join_02032_02064 : FiniteChecks.Interval terminalTest 2032 2064 :=
  FiniteChecks.interval_append terminalTest 2032 2048 2064 terminal_data_join_02032_02048 terminal_data_join_02048_02064

theorem terminal_data_join_02008_02064 : FiniteChecks.Interval terminalTest 2008 2064 :=
  FiniteChecks.interval_append terminalTest 2008 2032 2064 terminal_data_join_02008_02032 terminal_data_join_02032_02064

theorem terminal_data_join_02064_02080 : FiniteChecks.Interval terminalTest 2064 2080 :=
  FiniteChecks.interval_append terminalTest 2064 2072 2080 terminal_data_02064 terminal_data_02072

theorem terminal_data_join_02080_02096 : FiniteChecks.Interval terminalTest 2080 2096 :=
  FiniteChecks.interval_append terminalTest 2080 2088 2096 terminal_data_02080 terminal_data_02088

theorem terminal_data_join_02064_02096 : FiniteChecks.Interval terminalTest 2064 2096 :=
  FiniteChecks.interval_append terminalTest 2064 2080 2096 terminal_data_join_02064_02080 terminal_data_join_02080_02096

theorem terminal_data_join_02096_02112 : FiniteChecks.Interval terminalTest 2096 2112 :=
  FiniteChecks.interval_append terminalTest 2096 2104 2112 terminal_data_02096 terminal_data_02104

theorem terminal_data_join_02112_02128 : FiniteChecks.Interval terminalTest 2112 2128 :=
  FiniteChecks.interval_append terminalTest 2112 2120 2128 terminal_data_02112 terminal_data_02120

theorem terminal_data_join_02096_02128 : FiniteChecks.Interval terminalTest 2096 2128 :=
  FiniteChecks.interval_append terminalTest 2096 2112 2128 terminal_data_join_02096_02112 terminal_data_join_02112_02128

theorem terminal_data_join_02064_02128 : FiniteChecks.Interval terminalTest 2064 2128 :=
  FiniteChecks.interval_append terminalTest 2064 2096 2128 terminal_data_join_02064_02096 terminal_data_join_02096_02128

theorem terminal_data_join_02008_02128 : FiniteChecks.Interval terminalTest 2008 2128 :=
  FiniteChecks.interval_append terminalTest 2008 2064 2128 terminal_data_join_02008_02064 terminal_data_join_02064_02128

theorem terminal_data_join_01896_02128 : FiniteChecks.Interval terminalTest 1896 2128 :=
  FiniteChecks.interval_append terminalTest 1896 2008 2128 terminal_data_join_01896_02008 terminal_data_join_02008_02128

theorem terminal_data_join_02136_02152 : FiniteChecks.Interval terminalTest 2136 2152 :=
  FiniteChecks.interval_append terminalTest 2136 2144 2152 terminal_data_02136 terminal_data_02144

theorem terminal_data_join_02128_02152 : FiniteChecks.Interval terminalTest 2128 2152 :=
  FiniteChecks.interval_append terminalTest 2128 2136 2152 terminal_data_02128 terminal_data_join_02136_02152

theorem terminal_data_join_02152_02168 : FiniteChecks.Interval terminalTest 2152 2168 :=
  FiniteChecks.interval_append terminalTest 2152 2160 2168 terminal_data_02152 terminal_data_02160

theorem terminal_data_join_02168_02184 : FiniteChecks.Interval terminalTest 2168 2184 :=
  FiniteChecks.interval_append terminalTest 2168 2176 2184 terminal_data_02168 terminal_data_02176

theorem terminal_data_join_02152_02184 : FiniteChecks.Interval terminalTest 2152 2184 :=
  FiniteChecks.interval_append terminalTest 2152 2168 2184 terminal_data_join_02152_02168 terminal_data_join_02168_02184

theorem terminal_data_join_02128_02184 : FiniteChecks.Interval terminalTest 2128 2184 :=
  FiniteChecks.interval_append terminalTest 2128 2152 2184 terminal_data_join_02128_02152 terminal_data_join_02152_02184

theorem terminal_data_join_02184_02200 : FiniteChecks.Interval terminalTest 2184 2200 :=
  FiniteChecks.interval_append terminalTest 2184 2192 2200 terminal_data_02184 terminal_data_02192

theorem terminal_data_join_02200_02216 : FiniteChecks.Interval terminalTest 2200 2216 :=
  FiniteChecks.interval_append terminalTest 2200 2208 2216 terminal_data_02200 terminal_data_02208

theorem terminal_data_join_02184_02216 : FiniteChecks.Interval terminalTest 2184 2216 :=
  FiniteChecks.interval_append terminalTest 2184 2200 2216 terminal_data_join_02184_02200 terminal_data_join_02200_02216

theorem terminal_data_join_02216_02232 : FiniteChecks.Interval terminalTest 2216 2232 :=
  FiniteChecks.interval_append terminalTest 2216 2224 2232 terminal_data_02216 terminal_data_02224

theorem terminal_data_join_02232_02248 : FiniteChecks.Interval terminalTest 2232 2248 :=
  FiniteChecks.interval_append terminalTest 2232 2240 2248 terminal_data_02232 terminal_data_02240


end Papers.RationalityTen.ConcretePolygonClassification.N7
