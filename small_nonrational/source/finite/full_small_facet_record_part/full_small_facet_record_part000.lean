module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_0000 : FiniteChecks.Interval recordTest 0 16 :=
      FiniteChecks.interval_of_check recordTest 0 16 (by decide +kernel)
    
theorem records_0016 : FiniteChecks.Interval recordTest 16 32 :=
      FiniteChecks.interval_of_check recordTest 16 16 (by decide +kernel)
    
theorem records_0032 : FiniteChecks.Interval recordTest 32 48 :=
      FiniteChecks.interval_of_check recordTest 32 16 (by decide +kernel)
    
theorem records_0048 : FiniteChecks.Interval recordTest 48 64 :=
      FiniteChecks.interval_of_check recordTest 48 16 (by decide +kernel)
    
theorem records_0064 : FiniteChecks.Interval recordTest 64 80 :=
      FiniteChecks.interval_of_check recordTest 64 16 (by decide +kernel)
    
theorem records_0080 : FiniteChecks.Interval recordTest 80 96 :=
      FiniteChecks.interval_of_check recordTest 80 16 (by decide +kernel)
    
theorem records_0096 : FiniteChecks.Interval recordTest 96 112 :=
      FiniteChecks.interval_of_check recordTest 96 16 (by decide +kernel)
    
theorem records_0112 : FiniteChecks.Interval recordTest 112 128 :=
      FiniteChecks.interval_of_check recordTest 112 16 (by decide +kernel)
    
theorem records_0128 : FiniteChecks.Interval recordTest 128 144 :=
      FiniteChecks.interval_of_check recordTest 128 16 (by decide +kernel)
    
theorem records_0144 : FiniteChecks.Interval recordTest 144 160 :=
      FiniteChecks.interval_of_check recordTest 144 16 (by decide +kernel)
    
theorem records_0160 : FiniteChecks.Interval recordTest 160 176 :=
      FiniteChecks.interval_of_check recordTest 160 16 (by decide +kernel)
    
theorem records_0176 : FiniteChecks.Interval recordTest 176 192 :=
      FiniteChecks.interval_of_check recordTest 176 16 (by decide +kernel)
    
theorem records_0192 : FiniteChecks.Interval recordTest 192 208 :=
      FiniteChecks.interval_of_check recordTest 192 16 (by decide +kernel)
    
theorem records_0208 : FiniteChecks.Interval recordTest 208 224 :=
      FiniteChecks.interval_of_check recordTest 208 16 (by decide +kernel)
    
theorem records_0224 : FiniteChecks.Interval recordTest 224 240 :=
      FiniteChecks.interval_of_check recordTest 224 16 (by decide +kernel)
    
theorem records_0240 : FiniteChecks.Interval recordTest 240 256 :=
      FiniteChecks.interval_of_check recordTest 240 16 (by decide +kernel)
    
theorem records_0256 : FiniteChecks.Interval recordTest 256 272 :=
      FiniteChecks.interval_of_check recordTest 256 16 (by decide +kernel)
    
theorem records_0272 : FiniteChecks.Interval recordTest 272 288 :=
      FiniteChecks.interval_of_check recordTest 272 16 (by decide +kernel)
    
theorem records_0288 : FiniteChecks.Interval recordTest 288 304 :=
      FiniteChecks.interval_of_check recordTest 288 16 (by decide +kernel)
    
theorem records_0304 : FiniteChecks.Interval recordTest 304 320 :=
      FiniteChecks.interval_of_check recordTest 304 16 (by decide +kernel)
    
theorem records_0320 : FiniteChecks.Interval recordTest 320 336 :=
      FiniteChecks.interval_of_check recordTest 320 16 (by decide +kernel)
    
theorem records_0336 : FiniteChecks.Interval recordTest 336 352 :=
      FiniteChecks.interval_of_check recordTest 336 16 (by decide +kernel)
    
theorem records_0352 : FiniteChecks.Interval recordTest 352 368 :=
      FiniteChecks.interval_of_check recordTest 352 16 (by decide +kernel)
    
theorem records_0368 : FiniteChecks.Interval recordTest 368 384 :=
      FiniteChecks.interval_of_check recordTest 368 16 (by decide +kernel)
    
theorem records_0384 : FiniteChecks.Interval recordTest 384 400 :=
      FiniteChecks.interval_of_check recordTest 384 16 (by decide +kernel)
    
theorem records_0400 : FiniteChecks.Interval recordTest 400 416 :=
      FiniteChecks.interval_of_check recordTest 400 16 (by decide +kernel)
    
theorem records_0416 : FiniteChecks.Interval recordTest 416 432 :=
      FiniteChecks.interval_of_check recordTest 416 16 (by decide +kernel)
    
theorem records_0432 : FiniteChecks.Interval recordTest 432 448 :=
      FiniteChecks.interval_of_check recordTest 432 16 (by decide +kernel)
    
theorem records_0448 : FiniteChecks.Interval recordTest 448 464 :=
      FiniteChecks.interval_of_check recordTest 448 16 (by decide +kernel)
    
theorem records_0464 : FiniteChecks.Interval recordTest 464 480 :=
      FiniteChecks.interval_of_check recordTest 464 16 (by decide +kernel)
    
theorem records_0480 : FiniteChecks.Interval recordTest 480 496 :=
      FiniteChecks.interval_of_check recordTest 480 16 (by decide +kernel)
    
theorem records_0496 : FiniteChecks.Interval recordTest 496 512 :=
      FiniteChecks.interval_of_check recordTest 496 16 (by decide +kernel)
    
theorem records_join_0000_0032 : FiniteChecks.Interval recordTest 0 32 :=
  FiniteChecks.interval_append recordTest 0 16 32 records_0000 records_0016

theorem records_join_0032_0064 : FiniteChecks.Interval recordTest 32 64 :=
  FiniteChecks.interval_append recordTest 32 48 64 records_0032 records_0048

theorem records_join_0000_0064 : FiniteChecks.Interval recordTest 0 64 :=
  FiniteChecks.interval_append recordTest 0 32 64 records_join_0000_0032 records_join_0032_0064

theorem records_join_0064_0096 : FiniteChecks.Interval recordTest 64 96 :=
  FiniteChecks.interval_append recordTest 64 80 96 records_0064 records_0080

theorem records_join_0096_0128 : FiniteChecks.Interval recordTest 96 128 :=
  FiniteChecks.interval_append recordTest 96 112 128 records_0096 records_0112

theorem records_join_0064_0128 : FiniteChecks.Interval recordTest 64 128 :=
  FiniteChecks.interval_append recordTest 64 96 128 records_join_0064_0096 records_join_0096_0128

theorem records_join_0000_0128 : FiniteChecks.Interval recordTest 0 128 :=
  FiniteChecks.interval_append recordTest 0 64 128 records_join_0000_0064 records_join_0064_0128

theorem records_join_0128_0160 : FiniteChecks.Interval recordTest 128 160 :=
  FiniteChecks.interval_append recordTest 128 144 160 records_0128 records_0144

theorem records_join_0160_0192 : FiniteChecks.Interval recordTest 160 192 :=
  FiniteChecks.interval_append recordTest 160 176 192 records_0160 records_0176

theorem records_join_0128_0192 : FiniteChecks.Interval recordTest 128 192 :=
  FiniteChecks.interval_append recordTest 128 160 192 records_join_0128_0160 records_join_0160_0192

theorem records_join_0192_0224 : FiniteChecks.Interval recordTest 192 224 :=
  FiniteChecks.interval_append recordTest 192 208 224 records_0192 records_0208

theorem records_join_0224_0256 : FiniteChecks.Interval recordTest 224 256 :=
  FiniteChecks.interval_append recordTest 224 240 256 records_0224 records_0240

theorem records_join_0192_0256 : FiniteChecks.Interval recordTest 192 256 :=
  FiniteChecks.interval_append recordTest 192 224 256 records_join_0192_0224 records_join_0224_0256

theorem records_join_0128_0256 : FiniteChecks.Interval recordTest 128 256 :=
  FiniteChecks.interval_append recordTest 128 192 256 records_join_0128_0192 records_join_0192_0256

theorem records_join_0000_0256 : FiniteChecks.Interval recordTest 0 256 :=
  FiniteChecks.interval_append recordTest 0 128 256 records_join_0000_0128 records_join_0128_0256

theorem records_join_0256_0288 : FiniteChecks.Interval recordTest 256 288 :=
  FiniteChecks.interval_append recordTest 256 272 288 records_0256 records_0272

theorem records_join_0288_0320 : FiniteChecks.Interval recordTest 288 320 :=
  FiniteChecks.interval_append recordTest 288 304 320 records_0288 records_0304

theorem records_join_0256_0320 : FiniteChecks.Interval recordTest 256 320 :=
  FiniteChecks.interval_append recordTest 256 288 320 records_join_0256_0288 records_join_0288_0320

theorem records_join_0320_0352 : FiniteChecks.Interval recordTest 320 352 :=
  FiniteChecks.interval_append recordTest 320 336 352 records_0320 records_0336

theorem records_join_0352_0384 : FiniteChecks.Interval recordTest 352 384 :=
  FiniteChecks.interval_append recordTest 352 368 384 records_0352 records_0368

theorem records_join_0320_0384 : FiniteChecks.Interval recordTest 320 384 :=
  FiniteChecks.interval_append recordTest 320 352 384 records_join_0320_0352 records_join_0352_0384

theorem records_join_0256_0384 : FiniteChecks.Interval recordTest 256 384 :=
  FiniteChecks.interval_append recordTest 256 320 384 records_join_0256_0320 records_join_0320_0384

theorem records_join_0384_0416 : FiniteChecks.Interval recordTest 384 416 :=
  FiniteChecks.interval_append recordTest 384 400 416 records_0384 records_0400

theorem records_join_0416_0448 : FiniteChecks.Interval recordTest 416 448 :=
  FiniteChecks.interval_append recordTest 416 432 448 records_0416 records_0432

theorem records_join_0384_0448 : FiniteChecks.Interval recordTest 384 448 :=
  FiniteChecks.interval_append recordTest 384 416 448 records_join_0384_0416 records_join_0416_0448

theorem records_join_0448_0480 : FiniteChecks.Interval recordTest 448 480 :=
  FiniteChecks.interval_append recordTest 448 464 480 records_0448 records_0464

theorem records_join_0480_0512 : FiniteChecks.Interval recordTest 480 512 :=
  FiniteChecks.interval_append recordTest 480 496 512 records_0480 records_0496

theorem records_join_0448_0512 : FiniteChecks.Interval recordTest 448 512 :=
  FiniteChecks.interval_append recordTest 448 480 512 records_join_0448_0480 records_join_0480_0512

theorem records_join_0384_0512 : FiniteChecks.Interval recordTest 384 512 :=
  FiniteChecks.interval_append recordTest 384 448 512 records_join_0384_0448 records_join_0448_0512

theorem records_join_0256_0512 : FiniteChecks.Interval recordTest 256 512 :=
  FiniteChecks.interval_append recordTest 256 384 512 records_join_0256_0384 records_join_0384_0512

theorem records_join_0000_0512 : FiniteChecks.Interval recordTest 0 512 :=
  FiniteChecks.interval_append recordTest 0 256 512 records_join_0000_0256 records_join_0256_0512

theorem records_part_000 : FiniteChecks.Interval recordTest 0 512 := records_join_0000_0512
    end Papers.RationalityTen.FacetUniverses.FullSmall
    