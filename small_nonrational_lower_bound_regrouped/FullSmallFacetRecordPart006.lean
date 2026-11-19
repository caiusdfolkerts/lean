module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_3072 : FiniteChecks.Interval recordTest 3072 3088 :=
      FiniteChecks.interval_of_check recordTest 3072 16 (by decide +kernel)
    
theorem records_3088 : FiniteChecks.Interval recordTest 3088 3104 :=
      FiniteChecks.interval_of_check recordTest 3088 16 (by decide +kernel)
    
theorem records_3104 : FiniteChecks.Interval recordTest 3104 3120 :=
      FiniteChecks.interval_of_check recordTest 3104 16 (by decide +kernel)
    
theorem records_3120 : FiniteChecks.Interval recordTest 3120 3136 :=
      FiniteChecks.interval_of_check recordTest 3120 16 (by decide +kernel)
    
theorem records_3136 : FiniteChecks.Interval recordTest 3136 3152 :=
      FiniteChecks.interval_of_check recordTest 3136 16 (by decide +kernel)
    
theorem records_3152 : FiniteChecks.Interval recordTest 3152 3168 :=
      FiniteChecks.interval_of_check recordTest 3152 16 (by decide +kernel)
    
theorem records_3168 : FiniteChecks.Interval recordTest 3168 3184 :=
      FiniteChecks.interval_of_check recordTest 3168 16 (by decide +kernel)
    
theorem records_3184 : FiniteChecks.Interval recordTest 3184 3200 :=
      FiniteChecks.interval_of_check recordTest 3184 16 (by decide +kernel)
    
theorem records_3200 : FiniteChecks.Interval recordTest 3200 3216 :=
      FiniteChecks.interval_of_check recordTest 3200 16 (by decide +kernel)
    
theorem records_3216 : FiniteChecks.Interval recordTest 3216 3232 :=
      FiniteChecks.interval_of_check recordTest 3216 16 (by decide +kernel)
    
theorem records_3232 : FiniteChecks.Interval recordTest 3232 3248 :=
      FiniteChecks.interval_of_check recordTest 3232 16 (by decide +kernel)
    
theorem records_3248 : FiniteChecks.Interval recordTest 3248 3264 :=
      FiniteChecks.interval_of_check recordTest 3248 16 (by decide +kernel)
    
theorem records_3264 : FiniteChecks.Interval recordTest 3264 3280 :=
      FiniteChecks.interval_of_check recordTest 3264 16 (by decide +kernel)
    
theorem records_3280 : FiniteChecks.Interval recordTest 3280 3296 :=
      FiniteChecks.interval_of_check recordTest 3280 16 (by decide +kernel)
    
theorem records_3296 : FiniteChecks.Interval recordTest 3296 3312 :=
      FiniteChecks.interval_of_check recordTest 3296 16 (by decide +kernel)
    
theorem records_3312 : FiniteChecks.Interval recordTest 3312 3328 :=
      FiniteChecks.interval_of_check recordTest 3312 16 (by decide +kernel)
    
theorem records_3328 : FiniteChecks.Interval recordTest 3328 3344 :=
      FiniteChecks.interval_of_check recordTest 3328 16 (by decide +kernel)
    
theorem records_3344 : FiniteChecks.Interval recordTest 3344 3360 :=
      FiniteChecks.interval_of_check recordTest 3344 16 (by decide +kernel)
    
theorem records_3360 : FiniteChecks.Interval recordTest 3360 3376 :=
      FiniteChecks.interval_of_check recordTest 3360 16 (by decide +kernel)
    
theorem records_3376 : FiniteChecks.Interval recordTest 3376 3392 :=
      FiniteChecks.interval_of_check recordTest 3376 16 (by decide +kernel)
    
theorem records_3392 : FiniteChecks.Interval recordTest 3392 3408 :=
      FiniteChecks.interval_of_check recordTest 3392 16 (by decide +kernel)
    
theorem records_3408 : FiniteChecks.Interval recordTest 3408 3424 :=
      FiniteChecks.interval_of_check recordTest 3408 16 (by decide +kernel)
    
theorem records_3424 : FiniteChecks.Interval recordTest 3424 3440 :=
      FiniteChecks.interval_of_check recordTest 3424 16 (by decide +kernel)
    
theorem records_3440 : FiniteChecks.Interval recordTest 3440 3456 :=
      FiniteChecks.interval_of_check recordTest 3440 16 (by decide +kernel)
    
theorem records_3456 : FiniteChecks.Interval recordTest 3456 3472 :=
      FiniteChecks.interval_of_check recordTest 3456 16 (by decide +kernel)
    
theorem records_3472 : FiniteChecks.Interval recordTest 3472 3488 :=
      FiniteChecks.interval_of_check recordTest 3472 16 (by decide +kernel)
    
theorem records_3488 : FiniteChecks.Interval recordTest 3488 3504 :=
      FiniteChecks.interval_of_check recordTest 3488 16 (by decide +kernel)
    
theorem records_3504 : FiniteChecks.Interval recordTest 3504 3520 :=
      FiniteChecks.interval_of_check recordTest 3504 16 (by decide +kernel)
    
theorem records_3520 : FiniteChecks.Interval recordTest 3520 3536 :=
      FiniteChecks.interval_of_check recordTest 3520 16 (by decide +kernel)
    
theorem records_3536 : FiniteChecks.Interval recordTest 3536 3552 :=
      FiniteChecks.interval_of_check recordTest 3536 16 (by decide +kernel)
    
theorem records_3552 : FiniteChecks.Interval recordTest 3552 3568 :=
      FiniteChecks.interval_of_check recordTest 3552 16 (by decide +kernel)
    
theorem records_3568 : FiniteChecks.Interval recordTest 3568 3584 :=
      FiniteChecks.interval_of_check recordTest 3568 16 (by decide +kernel)
    
theorem records_join_3072_3104 : FiniteChecks.Interval recordTest 3072 3104 :=
  FiniteChecks.interval_append recordTest 3072 3088 3104 records_3072 records_3088

theorem records_join_3104_3136 : FiniteChecks.Interval recordTest 3104 3136 :=
  FiniteChecks.interval_append recordTest 3104 3120 3136 records_3104 records_3120

theorem records_join_3072_3136 : FiniteChecks.Interval recordTest 3072 3136 :=
  FiniteChecks.interval_append recordTest 3072 3104 3136 records_join_3072_3104 records_join_3104_3136

theorem records_join_3136_3168 : FiniteChecks.Interval recordTest 3136 3168 :=
  FiniteChecks.interval_append recordTest 3136 3152 3168 records_3136 records_3152

theorem records_join_3168_3200 : FiniteChecks.Interval recordTest 3168 3200 :=
  FiniteChecks.interval_append recordTest 3168 3184 3200 records_3168 records_3184

theorem records_join_3136_3200 : FiniteChecks.Interval recordTest 3136 3200 :=
  FiniteChecks.interval_append recordTest 3136 3168 3200 records_join_3136_3168 records_join_3168_3200

theorem records_join_3072_3200 : FiniteChecks.Interval recordTest 3072 3200 :=
  FiniteChecks.interval_append recordTest 3072 3136 3200 records_join_3072_3136 records_join_3136_3200

theorem records_join_3200_3232 : FiniteChecks.Interval recordTest 3200 3232 :=
  FiniteChecks.interval_append recordTest 3200 3216 3232 records_3200 records_3216

theorem records_join_3232_3264 : FiniteChecks.Interval recordTest 3232 3264 :=
  FiniteChecks.interval_append recordTest 3232 3248 3264 records_3232 records_3248

theorem records_join_3200_3264 : FiniteChecks.Interval recordTest 3200 3264 :=
  FiniteChecks.interval_append recordTest 3200 3232 3264 records_join_3200_3232 records_join_3232_3264

theorem records_join_3264_3296 : FiniteChecks.Interval recordTest 3264 3296 :=
  FiniteChecks.interval_append recordTest 3264 3280 3296 records_3264 records_3280

theorem records_join_3296_3328 : FiniteChecks.Interval recordTest 3296 3328 :=
  FiniteChecks.interval_append recordTest 3296 3312 3328 records_3296 records_3312

theorem records_join_3264_3328 : FiniteChecks.Interval recordTest 3264 3328 :=
  FiniteChecks.interval_append recordTest 3264 3296 3328 records_join_3264_3296 records_join_3296_3328

theorem records_join_3200_3328 : FiniteChecks.Interval recordTest 3200 3328 :=
  FiniteChecks.interval_append recordTest 3200 3264 3328 records_join_3200_3264 records_join_3264_3328

theorem records_join_3072_3328 : FiniteChecks.Interval recordTest 3072 3328 :=
  FiniteChecks.interval_append recordTest 3072 3200 3328 records_join_3072_3200 records_join_3200_3328

theorem records_join_3328_3360 : FiniteChecks.Interval recordTest 3328 3360 :=
  FiniteChecks.interval_append recordTest 3328 3344 3360 records_3328 records_3344

theorem records_join_3360_3392 : FiniteChecks.Interval recordTest 3360 3392 :=
  FiniteChecks.interval_append recordTest 3360 3376 3392 records_3360 records_3376

theorem records_join_3328_3392 : FiniteChecks.Interval recordTest 3328 3392 :=
  FiniteChecks.interval_append recordTest 3328 3360 3392 records_join_3328_3360 records_join_3360_3392

theorem records_join_3392_3424 : FiniteChecks.Interval recordTest 3392 3424 :=
  FiniteChecks.interval_append recordTest 3392 3408 3424 records_3392 records_3408

theorem records_join_3424_3456 : FiniteChecks.Interval recordTest 3424 3456 :=
  FiniteChecks.interval_append recordTest 3424 3440 3456 records_3424 records_3440

theorem records_join_3392_3456 : FiniteChecks.Interval recordTest 3392 3456 :=
  FiniteChecks.interval_append recordTest 3392 3424 3456 records_join_3392_3424 records_join_3424_3456

theorem records_join_3328_3456 : FiniteChecks.Interval recordTest 3328 3456 :=
  FiniteChecks.interval_append recordTest 3328 3392 3456 records_join_3328_3392 records_join_3392_3456

theorem records_join_3456_3488 : FiniteChecks.Interval recordTest 3456 3488 :=
  FiniteChecks.interval_append recordTest 3456 3472 3488 records_3456 records_3472

theorem records_join_3488_3520 : FiniteChecks.Interval recordTest 3488 3520 :=
  FiniteChecks.interval_append recordTest 3488 3504 3520 records_3488 records_3504

theorem records_join_3456_3520 : FiniteChecks.Interval recordTest 3456 3520 :=
  FiniteChecks.interval_append recordTest 3456 3488 3520 records_join_3456_3488 records_join_3488_3520

theorem records_join_3520_3552 : FiniteChecks.Interval recordTest 3520 3552 :=
  FiniteChecks.interval_append recordTest 3520 3536 3552 records_3520 records_3536

theorem records_join_3552_3584 : FiniteChecks.Interval recordTest 3552 3584 :=
  FiniteChecks.interval_append recordTest 3552 3568 3584 records_3552 records_3568

theorem records_join_3520_3584 : FiniteChecks.Interval recordTest 3520 3584 :=
  FiniteChecks.interval_append recordTest 3520 3552 3584 records_join_3520_3552 records_join_3552_3584

theorem records_join_3456_3584 : FiniteChecks.Interval recordTest 3456 3584 :=
  FiniteChecks.interval_append recordTest 3456 3520 3584 records_join_3456_3520 records_join_3520_3584

theorem records_join_3328_3584 : FiniteChecks.Interval recordTest 3328 3584 :=
  FiniteChecks.interval_append recordTest 3328 3456 3584 records_join_3328_3456 records_join_3456_3584

theorem records_join_3072_3584 : FiniteChecks.Interval recordTest 3072 3584 :=
  FiniteChecks.interval_append recordTest 3072 3328 3584 records_join_3072_3328 records_join_3328_3584

theorem records_part_006 : FiniteChecks.Interval recordTest 3072 3584 := records_join_3072_3584
    end Papers.RationalityTen.FacetUniverses.FullSmall
    