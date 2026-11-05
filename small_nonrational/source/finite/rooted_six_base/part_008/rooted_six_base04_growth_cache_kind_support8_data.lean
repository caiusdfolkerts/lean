module
prelude
public import RootedSixBase04GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport8_000 : List Nat := [1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895]
def kindSupport8_001 : List Nat := [1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927]
def kindSupport8_002 : List Nat := [1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959]
def kindSupport8_003 : List Nat := [1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991]
def kindSupport8_004 : List Nat := [1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023]
def kindSupport8_005 : List Nat := [2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055]
def kindSupport8_006 : List Nat := [2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087]
def kindSupport8_007 : List Nat := [2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119]
def kindSupport8_008 : List Nat := [2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151]
def kindSupport8_009 : List Nat := [2152,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183]
def kindSupport8_010 : List Nat := [2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199]
def kindSupport8_code : Nat := 0x89789689589489389289189088f88e88d88c88b88a88988888788688588488388288188087f87e87d87c87b87a87987887787687587487387287187086f86e86d86c86b86a86986886786686586486386286186085f85e85d85c85b85a85985885785685585485385285185084f84e84d84c84b84a84984884784684584484384284184083f83e83d83c83b83a83983883783683583483383283183082f82e82d82c82b82a82982882782682582482382282182081f81e81d81c81b81a81981881781681581481381281181080f80e80d80c80b80a8098088078068058048038028018007ff7fe7fd7fc7fb7fa7f97f87f77f67f57f47f37f27f17f07ef7ee7ed7ec7eb7ea7e97e87e77e67e57e47e37e27e17e07df7de7dd7dc7db7da7d97d87d77d67d57d47d37d27d17d07cf7ce7cd7cc7cb7ca7c97c87c77c67c57c47c37c27c17c07bf7be7bd7bc7bb7ba7b97b87b77b67b57b47b37b27b17b07af7ae7ad7ac7ab7aa7a97a87a77a67a57a47a37a27a17a079f79e79d79c79b79a79979879779679579479379279179078f78e78d78c78b78a78978878778678578478378278178077f77e77d77c77b77a77977877777677577477377277177076f76e76d76c76b76a76976876776676576476376276176075f75e75d75c75b75a75975875775675575475375275175074f74e74d74c74b74a749748
def kindSupport8_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport8_code
def kindSupport8_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport8_code
def kindSupport8_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport8_code
def kindSupport8_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport8_code
def kindSupport8_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport8_code
def kindSupport8_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport8_code
def kindSupport8_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport8_code
def kindSupport8_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport8_code
def kindSupport8_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport8_code
def kindSupport8_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport8_code
def kindSupport8_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport8_code
def kindSupport8_rest_011 : Nat := PackedRawNatGrowth.drop 4032 kindSupport8_code
def kindSupport8_suffix_011 : List Nat := []
def kindSupport8_suffix_010 : List Nat := kindSupport8_010 ++ kindSupport8_suffix_011
def kindSupport8_suffix_009 : List Nat := kindSupport8_009 ++ kindSupport8_suffix_010
def kindSupport8_suffix_008 : List Nat := kindSupport8_008 ++ kindSupport8_suffix_009
def kindSupport8_suffix_007 : List Nat := kindSupport8_007 ++ kindSupport8_suffix_008
def kindSupport8_suffix_006 : List Nat := kindSupport8_006 ++ kindSupport8_suffix_007
def kindSupport8_suffix_005 : List Nat := kindSupport8_005 ++ kindSupport8_suffix_006
def kindSupport8_suffix_004 : List Nat := kindSupport8_004 ++ kindSupport8_suffix_005
def kindSupport8_suffix_003 : List Nat := kindSupport8_003 ++ kindSupport8_suffix_004
def kindSupport8_suffix_002 : List Nat := kindSupport8_002 ++ kindSupport8_suffix_003
def kindSupport8_suffix_001 : List Nat := kindSupport8_001 ++ kindSupport8_suffix_002
def kindSupport8_suffix_000 : List Nat := kindSupport8_000 ++ kindSupport8_suffix_001
theorem kindSupport8_source : kindSupports 8 =
    (PackedRawNatGrowth.readList 12 336 kindSupport8_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
