module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_4096 : FiniteChecks.Interval recordTest 4096 4112 :=
      FiniteChecks.interval_of_check recordTest 4096 16 (by decide +kernel)
    
theorem records_4112 : FiniteChecks.Interval recordTest 4112 4128 :=
      FiniteChecks.interval_of_check recordTest 4112 16 (by decide +kernel)
    
theorem records_4128 : FiniteChecks.Interval recordTest 4128 4144 :=
      FiniteChecks.interval_of_check recordTest 4128 16 (by decide +kernel)
    
theorem records_4144 : FiniteChecks.Interval recordTest 4144 4160 :=
      FiniteChecks.interval_of_check recordTest 4144 16 (by decide +kernel)
    
theorem records_4160 : FiniteChecks.Interval recordTest 4160 4176 :=
      FiniteChecks.interval_of_check recordTest 4160 16 (by decide +kernel)
    
theorem records_4176 : FiniteChecks.Interval recordTest 4176 4192 :=
      FiniteChecks.interval_of_check recordTest 4176 16 (by decide +kernel)
    
theorem records_4192 : FiniteChecks.Interval recordTest 4192 4208 :=
      FiniteChecks.interval_of_check recordTest 4192 16 (by decide +kernel)
    
theorem records_4208 : FiniteChecks.Interval recordTest 4208 4224 :=
      FiniteChecks.interval_of_check recordTest 4208 16 (by decide +kernel)
    
theorem records_4224 : FiniteChecks.Interval recordTest 4224 4240 :=
      FiniteChecks.interval_of_check recordTest 4224 16 (by decide +kernel)
    
theorem records_4240 : FiniteChecks.Interval recordTest 4240 4256 :=
      FiniteChecks.interval_of_check recordTest 4240 16 (by decide +kernel)
    
theorem records_4256 : FiniteChecks.Interval recordTest 4256 4272 :=
      FiniteChecks.interval_of_check recordTest 4256 16 (by decide +kernel)
    
theorem records_4272 : FiniteChecks.Interval recordTest 4272 4288 :=
      FiniteChecks.interval_of_check recordTest 4272 16 (by decide +kernel)
    
theorem records_4288 : FiniteChecks.Interval recordTest 4288 4304 :=
      FiniteChecks.interval_of_check recordTest 4288 16 (by decide +kernel)
    
theorem records_4304 : FiniteChecks.Interval recordTest 4304 4320 :=
      FiniteChecks.interval_of_check recordTest 4304 16 (by decide +kernel)
    
theorem records_4320 : FiniteChecks.Interval recordTest 4320 4336 :=
      FiniteChecks.interval_of_check recordTest 4320 16 (by decide +kernel)
    
theorem records_4336 : FiniteChecks.Interval recordTest 4336 4352 :=
      FiniteChecks.interval_of_check recordTest 4336 16 (by decide +kernel)
    
theorem records_4352 : FiniteChecks.Interval recordTest 4352 4368 :=
      FiniteChecks.interval_of_check recordTest 4352 16 (by decide +kernel)
    
theorem records_4368 : FiniteChecks.Interval recordTest 4368 4384 :=
      FiniteChecks.interval_of_check recordTest 4368 16 (by decide +kernel)
    
theorem records_4384 : FiniteChecks.Interval recordTest 4384 4400 :=
      FiniteChecks.interval_of_check recordTest 4384 16 (by decide +kernel)
    
theorem records_4400 : FiniteChecks.Interval recordTest 4400 4416 :=
      FiniteChecks.interval_of_check recordTest 4400 16 (by decide +kernel)
    
theorem records_4416 : FiniteChecks.Interval recordTest 4416 4432 :=
      FiniteChecks.interval_of_check recordTest 4416 16 (by decide +kernel)
    
theorem records_4432 : FiniteChecks.Interval recordTest 4432 4448 :=
      FiniteChecks.interval_of_check recordTest 4432 16 (by decide +kernel)
    
theorem records_4448 : FiniteChecks.Interval recordTest 4448 4464 :=
      FiniteChecks.interval_of_check recordTest 4448 16 (by decide +kernel)
    
theorem records_4464 : FiniteChecks.Interval recordTest 4464 4480 :=
      FiniteChecks.interval_of_check recordTest 4464 16 (by decide +kernel)
    
theorem records_4480 : FiniteChecks.Interval recordTest 4480 4496 :=
      FiniteChecks.interval_of_check recordTest 4480 16 (by decide +kernel)
    
theorem records_4496 : FiniteChecks.Interval recordTest 4496 4512 :=
      FiniteChecks.interval_of_check recordTest 4496 16 (by decide +kernel)
    
theorem records_4512 : FiniteChecks.Interval recordTest 4512 4528 :=
      FiniteChecks.interval_of_check recordTest 4512 16 (by decide +kernel)
    
theorem records_4528 : FiniteChecks.Interval recordTest 4528 4544 :=
      FiniteChecks.interval_of_check recordTest 4528 16 (by decide +kernel)
    
theorem records_4544 : FiniteChecks.Interval recordTest 4544 4560 :=
      FiniteChecks.interval_of_check recordTest 4544 16 (by decide +kernel)
    
theorem records_4560 : FiniteChecks.Interval recordTest 4560 4576 :=
      FiniteChecks.interval_of_check recordTest 4560 16 (by decide +kernel)
    
theorem records_4576 : FiniteChecks.Interval recordTest 4576 4592 :=
      FiniteChecks.interval_of_check recordTest 4576 16 (by decide +kernel)
    
theorem records_4592 : FiniteChecks.Interval recordTest 4592 4608 :=
      FiniteChecks.interval_of_check recordTest 4592 16 (by decide +kernel)
    
theorem records_join_4096_4128 : FiniteChecks.Interval recordTest 4096 4128 :=
  FiniteChecks.interval_append recordTest 4096 4112 4128 records_4096 records_4112

theorem records_join_4128_4160 : FiniteChecks.Interval recordTest 4128 4160 :=
  FiniteChecks.interval_append recordTest 4128 4144 4160 records_4128 records_4144

theorem records_join_4096_4160 : FiniteChecks.Interval recordTest 4096 4160 :=
  FiniteChecks.interval_append recordTest 4096 4128 4160 records_join_4096_4128 records_join_4128_4160

theorem records_join_4160_4192 : FiniteChecks.Interval recordTest 4160 4192 :=
  FiniteChecks.interval_append recordTest 4160 4176 4192 records_4160 records_4176

theorem records_join_4192_4224 : FiniteChecks.Interval recordTest 4192 4224 :=
  FiniteChecks.interval_append recordTest 4192 4208 4224 records_4192 records_4208

theorem records_join_4160_4224 : FiniteChecks.Interval recordTest 4160 4224 :=
  FiniteChecks.interval_append recordTest 4160 4192 4224 records_join_4160_4192 records_join_4192_4224

theorem records_join_4096_4224 : FiniteChecks.Interval recordTest 4096 4224 :=
  FiniteChecks.interval_append recordTest 4096 4160 4224 records_join_4096_4160 records_join_4160_4224

theorem records_join_4224_4256 : FiniteChecks.Interval recordTest 4224 4256 :=
  FiniteChecks.interval_append recordTest 4224 4240 4256 records_4224 records_4240

theorem records_join_4256_4288 : FiniteChecks.Interval recordTest 4256 4288 :=
  FiniteChecks.interval_append recordTest 4256 4272 4288 records_4256 records_4272

theorem records_join_4224_4288 : FiniteChecks.Interval recordTest 4224 4288 :=
  FiniteChecks.interval_append recordTest 4224 4256 4288 records_join_4224_4256 records_join_4256_4288

theorem records_join_4288_4320 : FiniteChecks.Interval recordTest 4288 4320 :=
  FiniteChecks.interval_append recordTest 4288 4304 4320 records_4288 records_4304

theorem records_join_4320_4352 : FiniteChecks.Interval recordTest 4320 4352 :=
  FiniteChecks.interval_append recordTest 4320 4336 4352 records_4320 records_4336

theorem records_join_4288_4352 : FiniteChecks.Interval recordTest 4288 4352 :=
  FiniteChecks.interval_append recordTest 4288 4320 4352 records_join_4288_4320 records_join_4320_4352

theorem records_join_4224_4352 : FiniteChecks.Interval recordTest 4224 4352 :=
  FiniteChecks.interval_append recordTest 4224 4288 4352 records_join_4224_4288 records_join_4288_4352

theorem records_join_4096_4352 : FiniteChecks.Interval recordTest 4096 4352 :=
  FiniteChecks.interval_append recordTest 4096 4224 4352 records_join_4096_4224 records_join_4224_4352

theorem records_join_4352_4384 : FiniteChecks.Interval recordTest 4352 4384 :=
  FiniteChecks.interval_append recordTest 4352 4368 4384 records_4352 records_4368

theorem records_join_4384_4416 : FiniteChecks.Interval recordTest 4384 4416 :=
  FiniteChecks.interval_append recordTest 4384 4400 4416 records_4384 records_4400

theorem records_join_4352_4416 : FiniteChecks.Interval recordTest 4352 4416 :=
  FiniteChecks.interval_append recordTest 4352 4384 4416 records_join_4352_4384 records_join_4384_4416

theorem records_join_4416_4448 : FiniteChecks.Interval recordTest 4416 4448 :=
  FiniteChecks.interval_append recordTest 4416 4432 4448 records_4416 records_4432

theorem records_join_4448_4480 : FiniteChecks.Interval recordTest 4448 4480 :=
  FiniteChecks.interval_append recordTest 4448 4464 4480 records_4448 records_4464

theorem records_join_4416_4480 : FiniteChecks.Interval recordTest 4416 4480 :=
  FiniteChecks.interval_append recordTest 4416 4448 4480 records_join_4416_4448 records_join_4448_4480

theorem records_join_4352_4480 : FiniteChecks.Interval recordTest 4352 4480 :=
  FiniteChecks.interval_append recordTest 4352 4416 4480 records_join_4352_4416 records_join_4416_4480

theorem records_join_4480_4512 : FiniteChecks.Interval recordTest 4480 4512 :=
  FiniteChecks.interval_append recordTest 4480 4496 4512 records_4480 records_4496

theorem records_join_4512_4544 : FiniteChecks.Interval recordTest 4512 4544 :=
  FiniteChecks.interval_append recordTest 4512 4528 4544 records_4512 records_4528

theorem records_join_4480_4544 : FiniteChecks.Interval recordTest 4480 4544 :=
  FiniteChecks.interval_append recordTest 4480 4512 4544 records_join_4480_4512 records_join_4512_4544

theorem records_join_4544_4576 : FiniteChecks.Interval recordTest 4544 4576 :=
  FiniteChecks.interval_append recordTest 4544 4560 4576 records_4544 records_4560

theorem records_join_4576_4608 : FiniteChecks.Interval recordTest 4576 4608 :=
  FiniteChecks.interval_append recordTest 4576 4592 4608 records_4576 records_4592

theorem records_join_4544_4608 : FiniteChecks.Interval recordTest 4544 4608 :=
  FiniteChecks.interval_append recordTest 4544 4576 4608 records_join_4544_4576 records_join_4576_4608

theorem records_join_4480_4608 : FiniteChecks.Interval recordTest 4480 4608 :=
  FiniteChecks.interval_append recordTest 4480 4544 4608 records_join_4480_4544 records_join_4544_4608

theorem records_join_4352_4608 : FiniteChecks.Interval recordTest 4352 4608 :=
  FiniteChecks.interval_append recordTest 4352 4480 4608 records_join_4352_4480 records_join_4480_4608

theorem records_join_4096_4608 : FiniteChecks.Interval recordTest 4096 4608 :=
  FiniteChecks.interval_append recordTest 4096 4352 4608 records_join_4096_4352 records_join_4352_4608

theorem records_part_008 : FiniteChecks.Interval recordTest 4096 4608 := records_join_4096_4608
    end Papers.RationalityTen.FacetUniverses.FullSmall
    