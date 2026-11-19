module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_6144 : FiniteChecks.Interval recordTest 6144 6160 :=
      FiniteChecks.interval_of_check recordTest 6144 16 (by decide +kernel)
    
theorem records_6160 : FiniteChecks.Interval recordTest 6160 6176 :=
      FiniteChecks.interval_of_check recordTest 6160 16 (by decide +kernel)
    
theorem records_6176 : FiniteChecks.Interval recordTest 6176 6192 :=
      FiniteChecks.interval_of_check recordTest 6176 16 (by decide +kernel)
    
theorem records_6192 : FiniteChecks.Interval recordTest 6192 6208 :=
      FiniteChecks.interval_of_check recordTest 6192 16 (by decide +kernel)
    
theorem records_6208 : FiniteChecks.Interval recordTest 6208 6224 :=
      FiniteChecks.interval_of_check recordTest 6208 16 (by decide +kernel)
    
theorem records_6224 : FiniteChecks.Interval recordTest 6224 6240 :=
      FiniteChecks.interval_of_check recordTest 6224 16 (by decide +kernel)
    
theorem records_6240 : FiniteChecks.Interval recordTest 6240 6256 :=
      FiniteChecks.interval_of_check recordTest 6240 16 (by decide +kernel)
    
theorem records_6256 : FiniteChecks.Interval recordTest 6256 6272 :=
      FiniteChecks.interval_of_check recordTest 6256 16 (by decide +kernel)
    
theorem records_6272 : FiniteChecks.Interval recordTest 6272 6288 :=
      FiniteChecks.interval_of_check recordTest 6272 16 (by decide +kernel)
    
theorem records_6288 : FiniteChecks.Interval recordTest 6288 6304 :=
      FiniteChecks.interval_of_check recordTest 6288 16 (by decide +kernel)
    
theorem records_6304 : FiniteChecks.Interval recordTest 6304 6320 :=
      FiniteChecks.interval_of_check recordTest 6304 16 (by decide +kernel)
    
theorem records_6320 : FiniteChecks.Interval recordTest 6320 6336 :=
      FiniteChecks.interval_of_check recordTest 6320 16 (by decide +kernel)
    
theorem records_6336 : FiniteChecks.Interval recordTest 6336 6352 :=
      FiniteChecks.interval_of_check recordTest 6336 16 (by decide +kernel)
    
theorem records_6352 : FiniteChecks.Interval recordTest 6352 6368 :=
      FiniteChecks.interval_of_check recordTest 6352 16 (by decide +kernel)
    
theorem records_6368 : FiniteChecks.Interval recordTest 6368 6384 :=
      FiniteChecks.interval_of_check recordTest 6368 16 (by decide +kernel)
    
theorem records_6384 : FiniteChecks.Interval recordTest 6384 6400 :=
      FiniteChecks.interval_of_check recordTest 6384 16 (by decide +kernel)
    
theorem records_6400 : FiniteChecks.Interval recordTest 6400 6416 :=
      FiniteChecks.interval_of_check recordTest 6400 16 (by decide +kernel)
    
theorem records_6416 : FiniteChecks.Interval recordTest 6416 6432 :=
      FiniteChecks.interval_of_check recordTest 6416 16 (by decide +kernel)
    
theorem records_6432 : FiniteChecks.Interval recordTest 6432 6448 :=
      FiniteChecks.interval_of_check recordTest 6432 16 (by decide +kernel)
    
theorem records_6448 : FiniteChecks.Interval recordTest 6448 6464 :=
      FiniteChecks.interval_of_check recordTest 6448 16 (by decide +kernel)
    
theorem records_6464 : FiniteChecks.Interval recordTest 6464 6480 :=
      FiniteChecks.interval_of_check recordTest 6464 16 (by decide +kernel)
    
theorem records_6480 : FiniteChecks.Interval recordTest 6480 6496 :=
      FiniteChecks.interval_of_check recordTest 6480 16 (by decide +kernel)
    
theorem records_6496 : FiniteChecks.Interval recordTest 6496 6510 :=
      FiniteChecks.interval_of_check recordTest 6496 14 (by decide +kernel)
    
theorem records_join_6144_6176 : FiniteChecks.Interval recordTest 6144 6176 :=
  FiniteChecks.interval_append recordTest 6144 6160 6176 records_6144 records_6160

theorem records_join_6192_6224 : FiniteChecks.Interval recordTest 6192 6224 :=
  FiniteChecks.interval_append recordTest 6192 6208 6224 records_6192 records_6208

theorem records_join_6176_6224 : FiniteChecks.Interval recordTest 6176 6224 :=
  FiniteChecks.interval_append recordTest 6176 6192 6224 records_6176 records_join_6192_6224

theorem records_join_6144_6224 : FiniteChecks.Interval recordTest 6144 6224 :=
  FiniteChecks.interval_append recordTest 6144 6176 6224 records_join_6144_6176 records_join_6176_6224

theorem records_join_6240_6272 : FiniteChecks.Interval recordTest 6240 6272 :=
  FiniteChecks.interval_append recordTest 6240 6256 6272 records_6240 records_6256

theorem records_join_6224_6272 : FiniteChecks.Interval recordTest 6224 6272 :=
  FiniteChecks.interval_append recordTest 6224 6240 6272 records_6224 records_join_6240_6272

theorem records_join_6288_6320 : FiniteChecks.Interval recordTest 6288 6320 :=
  FiniteChecks.interval_append recordTest 6288 6304 6320 records_6288 records_6304

theorem records_join_6272_6320 : FiniteChecks.Interval recordTest 6272 6320 :=
  FiniteChecks.interval_append recordTest 6272 6288 6320 records_6272 records_join_6288_6320

theorem records_join_6224_6320 : FiniteChecks.Interval recordTest 6224 6320 :=
  FiniteChecks.interval_append recordTest 6224 6272 6320 records_join_6224_6272 records_join_6272_6320

theorem records_join_6144_6320 : FiniteChecks.Interval recordTest 6144 6320 :=
  FiniteChecks.interval_append recordTest 6144 6224 6320 records_join_6144_6224 records_join_6224_6320

theorem records_join_6336_6368 : FiniteChecks.Interval recordTest 6336 6368 :=
  FiniteChecks.interval_append recordTest 6336 6352 6368 records_6336 records_6352

theorem records_join_6320_6368 : FiniteChecks.Interval recordTest 6320 6368 :=
  FiniteChecks.interval_append recordTest 6320 6336 6368 records_6320 records_join_6336_6368

theorem records_join_6384_6416 : FiniteChecks.Interval recordTest 6384 6416 :=
  FiniteChecks.interval_append recordTest 6384 6400 6416 records_6384 records_6400

theorem records_join_6368_6416 : FiniteChecks.Interval recordTest 6368 6416 :=
  FiniteChecks.interval_append recordTest 6368 6384 6416 records_6368 records_join_6384_6416

theorem records_join_6320_6416 : FiniteChecks.Interval recordTest 6320 6416 :=
  FiniteChecks.interval_append recordTest 6320 6368 6416 records_join_6320_6368 records_join_6368_6416

theorem records_join_6432_6464 : FiniteChecks.Interval recordTest 6432 6464 :=
  FiniteChecks.interval_append recordTest 6432 6448 6464 records_6432 records_6448

theorem records_join_6416_6464 : FiniteChecks.Interval recordTest 6416 6464 :=
  FiniteChecks.interval_append recordTest 6416 6432 6464 records_6416 records_join_6432_6464

theorem records_join_6480_6510 : FiniteChecks.Interval recordTest 6480 6510 :=
  FiniteChecks.interval_append recordTest 6480 6496 6510 records_6480 records_6496

theorem records_join_6464_6510 : FiniteChecks.Interval recordTest 6464 6510 :=
  FiniteChecks.interval_append recordTest 6464 6480 6510 records_6464 records_join_6480_6510

theorem records_join_6416_6510 : FiniteChecks.Interval recordTest 6416 6510 :=
  FiniteChecks.interval_append recordTest 6416 6464 6510 records_join_6416_6464 records_join_6464_6510

theorem records_join_6320_6510 : FiniteChecks.Interval recordTest 6320 6510 :=
  FiniteChecks.interval_append recordTest 6320 6416 6510 records_join_6320_6416 records_join_6416_6510

theorem records_join_6144_6510 : FiniteChecks.Interval recordTest 6144 6510 :=
  FiniteChecks.interval_append recordTest 6144 6320 6510 records_join_6144_6320 records_join_6320_6510

theorem records_part_012 : FiniteChecks.Interval recordTest 6144 6510 := records_join_6144_6510
    end Papers.RationalityTen.FacetUniverses.FullSmall
    