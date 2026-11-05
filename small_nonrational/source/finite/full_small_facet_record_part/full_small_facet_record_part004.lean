module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_2048 : FiniteChecks.Interval recordTest 2048 2064 :=
      FiniteChecks.interval_of_check recordTest 2048 16 (by decide +kernel)
    
theorem records_2064 : FiniteChecks.Interval recordTest 2064 2080 :=
      FiniteChecks.interval_of_check recordTest 2064 16 (by decide +kernel)
    
theorem records_2080 : FiniteChecks.Interval recordTest 2080 2096 :=
      FiniteChecks.interval_of_check recordTest 2080 16 (by decide +kernel)
    
theorem records_2096 : FiniteChecks.Interval recordTest 2096 2112 :=
      FiniteChecks.interval_of_check recordTest 2096 16 (by decide +kernel)
    
theorem records_2112 : FiniteChecks.Interval recordTest 2112 2128 :=
      FiniteChecks.interval_of_check recordTest 2112 16 (by decide +kernel)
    
theorem records_2128 : FiniteChecks.Interval recordTest 2128 2144 :=
      FiniteChecks.interval_of_check recordTest 2128 16 (by decide +kernel)
    
theorem records_2144 : FiniteChecks.Interval recordTest 2144 2160 :=
      FiniteChecks.interval_of_check recordTest 2144 16 (by decide +kernel)
    
theorem records_2160 : FiniteChecks.Interval recordTest 2160 2176 :=
      FiniteChecks.interval_of_check recordTest 2160 16 (by decide +kernel)
    
theorem records_2176 : FiniteChecks.Interval recordTest 2176 2192 :=
      FiniteChecks.interval_of_check recordTest 2176 16 (by decide +kernel)
    
theorem records_2192 : FiniteChecks.Interval recordTest 2192 2208 :=
      FiniteChecks.interval_of_check recordTest 2192 16 (by decide +kernel)
    
theorem records_2208 : FiniteChecks.Interval recordTest 2208 2224 :=
      FiniteChecks.interval_of_check recordTest 2208 16 (by decide +kernel)
    
theorem records_2224 : FiniteChecks.Interval recordTest 2224 2240 :=
      FiniteChecks.interval_of_check recordTest 2224 16 (by decide +kernel)
    
theorem records_2240 : FiniteChecks.Interval recordTest 2240 2256 :=
      FiniteChecks.interval_of_check recordTest 2240 16 (by decide +kernel)
    
theorem records_2256 : FiniteChecks.Interval recordTest 2256 2272 :=
      FiniteChecks.interval_of_check recordTest 2256 16 (by decide +kernel)
    
theorem records_2272 : FiniteChecks.Interval recordTest 2272 2288 :=
      FiniteChecks.interval_of_check recordTest 2272 16 (by decide +kernel)
    
theorem records_2288 : FiniteChecks.Interval recordTest 2288 2304 :=
      FiniteChecks.interval_of_check recordTest 2288 16 (by decide +kernel)
    
theorem records_2304 : FiniteChecks.Interval recordTest 2304 2320 :=
      FiniteChecks.interval_of_check recordTest 2304 16 (by decide +kernel)
    
theorem records_2320 : FiniteChecks.Interval recordTest 2320 2336 :=
      FiniteChecks.interval_of_check recordTest 2320 16 (by decide +kernel)
    
theorem records_2336 : FiniteChecks.Interval recordTest 2336 2352 :=
      FiniteChecks.interval_of_check recordTest 2336 16 (by decide +kernel)
    
theorem records_2352 : FiniteChecks.Interval recordTest 2352 2368 :=
      FiniteChecks.interval_of_check recordTest 2352 16 (by decide +kernel)
    
theorem records_2368 : FiniteChecks.Interval recordTest 2368 2384 :=
      FiniteChecks.interval_of_check recordTest 2368 16 (by decide +kernel)
    
theorem records_2384 : FiniteChecks.Interval recordTest 2384 2400 :=
      FiniteChecks.interval_of_check recordTest 2384 16 (by decide +kernel)
    
theorem records_2400 : FiniteChecks.Interval recordTest 2400 2416 :=
      FiniteChecks.interval_of_check recordTest 2400 16 (by decide +kernel)
    
theorem records_2416 : FiniteChecks.Interval recordTest 2416 2432 :=
      FiniteChecks.interval_of_check recordTest 2416 16 (by decide +kernel)
    
theorem records_2432 : FiniteChecks.Interval recordTest 2432 2448 :=
      FiniteChecks.interval_of_check recordTest 2432 16 (by decide +kernel)
    
theorem records_2448 : FiniteChecks.Interval recordTest 2448 2464 :=
      FiniteChecks.interval_of_check recordTest 2448 16 (by decide +kernel)
    
theorem records_2464 : FiniteChecks.Interval recordTest 2464 2480 :=
      FiniteChecks.interval_of_check recordTest 2464 16 (by decide +kernel)
    
theorem records_2480 : FiniteChecks.Interval recordTest 2480 2496 :=
      FiniteChecks.interval_of_check recordTest 2480 16 (by decide +kernel)
    
theorem records_2496 : FiniteChecks.Interval recordTest 2496 2512 :=
      FiniteChecks.interval_of_check recordTest 2496 16 (by decide +kernel)
    
theorem records_2512 : FiniteChecks.Interval recordTest 2512 2528 :=
      FiniteChecks.interval_of_check recordTest 2512 16 (by decide +kernel)
    
theorem records_2528 : FiniteChecks.Interval recordTest 2528 2544 :=
      FiniteChecks.interval_of_check recordTest 2528 16 (by decide +kernel)
    
theorem records_2544 : FiniteChecks.Interval recordTest 2544 2560 :=
      FiniteChecks.interval_of_check recordTest 2544 16 (by decide +kernel)
    
theorem records_join_2048_2080 : FiniteChecks.Interval recordTest 2048 2080 :=
  FiniteChecks.interval_append recordTest 2048 2064 2080 records_2048 records_2064

theorem records_join_2080_2112 : FiniteChecks.Interval recordTest 2080 2112 :=
  FiniteChecks.interval_append recordTest 2080 2096 2112 records_2080 records_2096

theorem records_join_2048_2112 : FiniteChecks.Interval recordTest 2048 2112 :=
  FiniteChecks.interval_append recordTest 2048 2080 2112 records_join_2048_2080 records_join_2080_2112

theorem records_join_2112_2144 : FiniteChecks.Interval recordTest 2112 2144 :=
  FiniteChecks.interval_append recordTest 2112 2128 2144 records_2112 records_2128

theorem records_join_2144_2176 : FiniteChecks.Interval recordTest 2144 2176 :=
  FiniteChecks.interval_append recordTest 2144 2160 2176 records_2144 records_2160

theorem records_join_2112_2176 : FiniteChecks.Interval recordTest 2112 2176 :=
  FiniteChecks.interval_append recordTest 2112 2144 2176 records_join_2112_2144 records_join_2144_2176

theorem records_join_2048_2176 : FiniteChecks.Interval recordTest 2048 2176 :=
  FiniteChecks.interval_append recordTest 2048 2112 2176 records_join_2048_2112 records_join_2112_2176

theorem records_join_2176_2208 : FiniteChecks.Interval recordTest 2176 2208 :=
  FiniteChecks.interval_append recordTest 2176 2192 2208 records_2176 records_2192

theorem records_join_2208_2240 : FiniteChecks.Interval recordTest 2208 2240 :=
  FiniteChecks.interval_append recordTest 2208 2224 2240 records_2208 records_2224

theorem records_join_2176_2240 : FiniteChecks.Interval recordTest 2176 2240 :=
  FiniteChecks.interval_append recordTest 2176 2208 2240 records_join_2176_2208 records_join_2208_2240

theorem records_join_2240_2272 : FiniteChecks.Interval recordTest 2240 2272 :=
  FiniteChecks.interval_append recordTest 2240 2256 2272 records_2240 records_2256

theorem records_join_2272_2304 : FiniteChecks.Interval recordTest 2272 2304 :=
  FiniteChecks.interval_append recordTest 2272 2288 2304 records_2272 records_2288

theorem records_join_2240_2304 : FiniteChecks.Interval recordTest 2240 2304 :=
  FiniteChecks.interval_append recordTest 2240 2272 2304 records_join_2240_2272 records_join_2272_2304

theorem records_join_2176_2304 : FiniteChecks.Interval recordTest 2176 2304 :=
  FiniteChecks.interval_append recordTest 2176 2240 2304 records_join_2176_2240 records_join_2240_2304

theorem records_join_2048_2304 : FiniteChecks.Interval recordTest 2048 2304 :=
  FiniteChecks.interval_append recordTest 2048 2176 2304 records_join_2048_2176 records_join_2176_2304

theorem records_join_2304_2336 : FiniteChecks.Interval recordTest 2304 2336 :=
  FiniteChecks.interval_append recordTest 2304 2320 2336 records_2304 records_2320

theorem records_join_2336_2368 : FiniteChecks.Interval recordTest 2336 2368 :=
  FiniteChecks.interval_append recordTest 2336 2352 2368 records_2336 records_2352

theorem records_join_2304_2368 : FiniteChecks.Interval recordTest 2304 2368 :=
  FiniteChecks.interval_append recordTest 2304 2336 2368 records_join_2304_2336 records_join_2336_2368

theorem records_join_2368_2400 : FiniteChecks.Interval recordTest 2368 2400 :=
  FiniteChecks.interval_append recordTest 2368 2384 2400 records_2368 records_2384

theorem records_join_2400_2432 : FiniteChecks.Interval recordTest 2400 2432 :=
  FiniteChecks.interval_append recordTest 2400 2416 2432 records_2400 records_2416

theorem records_join_2368_2432 : FiniteChecks.Interval recordTest 2368 2432 :=
  FiniteChecks.interval_append recordTest 2368 2400 2432 records_join_2368_2400 records_join_2400_2432

theorem records_join_2304_2432 : FiniteChecks.Interval recordTest 2304 2432 :=
  FiniteChecks.interval_append recordTest 2304 2368 2432 records_join_2304_2368 records_join_2368_2432

theorem records_join_2432_2464 : FiniteChecks.Interval recordTest 2432 2464 :=
  FiniteChecks.interval_append recordTest 2432 2448 2464 records_2432 records_2448

theorem records_join_2464_2496 : FiniteChecks.Interval recordTest 2464 2496 :=
  FiniteChecks.interval_append recordTest 2464 2480 2496 records_2464 records_2480

theorem records_join_2432_2496 : FiniteChecks.Interval recordTest 2432 2496 :=
  FiniteChecks.interval_append recordTest 2432 2464 2496 records_join_2432_2464 records_join_2464_2496

theorem records_join_2496_2528 : FiniteChecks.Interval recordTest 2496 2528 :=
  FiniteChecks.interval_append recordTest 2496 2512 2528 records_2496 records_2512

theorem records_join_2528_2560 : FiniteChecks.Interval recordTest 2528 2560 :=
  FiniteChecks.interval_append recordTest 2528 2544 2560 records_2528 records_2544

theorem records_join_2496_2560 : FiniteChecks.Interval recordTest 2496 2560 :=
  FiniteChecks.interval_append recordTest 2496 2528 2560 records_join_2496_2528 records_join_2528_2560

theorem records_join_2432_2560 : FiniteChecks.Interval recordTest 2432 2560 :=
  FiniteChecks.interval_append recordTest 2432 2496 2560 records_join_2432_2496 records_join_2496_2560

theorem records_join_2304_2560 : FiniteChecks.Interval recordTest 2304 2560 :=
  FiniteChecks.interval_append recordTest 2304 2432 2560 records_join_2304_2432 records_join_2432_2560

theorem records_join_2048_2560 : FiniteChecks.Interval recordTest 2048 2560 :=
  FiniteChecks.interval_append recordTest 2048 2304 2560 records_join_2048_2304 records_join_2304_2560

theorem records_part_004 : FiniteChecks.Interval recordTest 2048 2560 := records_join_2048_2560
    end Papers.RationalityTen.FacetUniverses.FullSmall
    