module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_5120 : FiniteChecks.Interval recordTest 5120 5136 :=
      FiniteChecks.interval_of_check recordTest 5120 16 (by decide +kernel)
    
theorem records_5136 : FiniteChecks.Interval recordTest 5136 5152 :=
      FiniteChecks.interval_of_check recordTest 5136 16 (by decide +kernel)
    
theorem records_5152 : FiniteChecks.Interval recordTest 5152 5168 :=
      FiniteChecks.interval_of_check recordTest 5152 16 (by decide +kernel)
    
theorem records_5168 : FiniteChecks.Interval recordTest 5168 5184 :=
      FiniteChecks.interval_of_check recordTest 5168 16 (by decide +kernel)
    
theorem records_5184 : FiniteChecks.Interval recordTest 5184 5200 :=
      FiniteChecks.interval_of_check recordTest 5184 16 (by decide +kernel)
    
theorem records_5200 : FiniteChecks.Interval recordTest 5200 5216 :=
      FiniteChecks.interval_of_check recordTest 5200 16 (by decide +kernel)
    
theorem records_5216 : FiniteChecks.Interval recordTest 5216 5232 :=
      FiniteChecks.interval_of_check recordTest 5216 16 (by decide +kernel)
    
theorem records_5232 : FiniteChecks.Interval recordTest 5232 5248 :=
      FiniteChecks.interval_of_check recordTest 5232 16 (by decide +kernel)
    
theorem records_5248 : FiniteChecks.Interval recordTest 5248 5264 :=
      FiniteChecks.interval_of_check recordTest 5248 16 (by decide +kernel)
    
theorem records_5264 : FiniteChecks.Interval recordTest 5264 5280 :=
      FiniteChecks.interval_of_check recordTest 5264 16 (by decide +kernel)
    
theorem records_5280 : FiniteChecks.Interval recordTest 5280 5296 :=
      FiniteChecks.interval_of_check recordTest 5280 16 (by decide +kernel)
    
theorem records_5296 : FiniteChecks.Interval recordTest 5296 5312 :=
      FiniteChecks.interval_of_check recordTest 5296 16 (by decide +kernel)
    
theorem records_5312 : FiniteChecks.Interval recordTest 5312 5328 :=
      FiniteChecks.interval_of_check recordTest 5312 16 (by decide +kernel)
    
theorem records_5328 : FiniteChecks.Interval recordTest 5328 5344 :=
      FiniteChecks.interval_of_check recordTest 5328 16 (by decide +kernel)
    
theorem records_5344 : FiniteChecks.Interval recordTest 5344 5360 :=
      FiniteChecks.interval_of_check recordTest 5344 16 (by decide +kernel)
    
theorem records_5360 : FiniteChecks.Interval recordTest 5360 5376 :=
      FiniteChecks.interval_of_check recordTest 5360 16 (by decide +kernel)
    
theorem records_5376 : FiniteChecks.Interval recordTest 5376 5392 :=
      FiniteChecks.interval_of_check recordTest 5376 16 (by decide +kernel)
    
theorem records_5392 : FiniteChecks.Interval recordTest 5392 5408 :=
      FiniteChecks.interval_of_check recordTest 5392 16 (by decide +kernel)
    
theorem records_5408 : FiniteChecks.Interval recordTest 5408 5424 :=
      FiniteChecks.interval_of_check recordTest 5408 16 (by decide +kernel)
    
theorem records_5424 : FiniteChecks.Interval recordTest 5424 5440 :=
      FiniteChecks.interval_of_check recordTest 5424 16 (by decide +kernel)
    
theorem records_5440 : FiniteChecks.Interval recordTest 5440 5456 :=
      FiniteChecks.interval_of_check recordTest 5440 16 (by decide +kernel)
    
theorem records_5456 : FiniteChecks.Interval recordTest 5456 5472 :=
      FiniteChecks.interval_of_check recordTest 5456 16 (by decide +kernel)
    
theorem records_5472 : FiniteChecks.Interval recordTest 5472 5488 :=
      FiniteChecks.interval_of_check recordTest 5472 16 (by decide +kernel)
    
theorem records_5488 : FiniteChecks.Interval recordTest 5488 5504 :=
      FiniteChecks.interval_of_check recordTest 5488 16 (by decide +kernel)
    
theorem records_5504 : FiniteChecks.Interval recordTest 5504 5520 :=
      FiniteChecks.interval_of_check recordTest 5504 16 (by decide +kernel)
    
theorem records_5520 : FiniteChecks.Interval recordTest 5520 5536 :=
      FiniteChecks.interval_of_check recordTest 5520 16 (by decide +kernel)
    
theorem records_5536 : FiniteChecks.Interval recordTest 5536 5552 :=
      FiniteChecks.interval_of_check recordTest 5536 16 (by decide +kernel)
    
theorem records_5552 : FiniteChecks.Interval recordTest 5552 5568 :=
      FiniteChecks.interval_of_check recordTest 5552 16 (by decide +kernel)
    
theorem records_5568 : FiniteChecks.Interval recordTest 5568 5584 :=
      FiniteChecks.interval_of_check recordTest 5568 16 (by decide +kernel)
    
theorem records_5584 : FiniteChecks.Interval recordTest 5584 5600 :=
      FiniteChecks.interval_of_check recordTest 5584 16 (by decide +kernel)
    
theorem records_5600 : FiniteChecks.Interval recordTest 5600 5616 :=
      FiniteChecks.interval_of_check recordTest 5600 16 (by decide +kernel)
    
theorem records_5616 : FiniteChecks.Interval recordTest 5616 5632 :=
      FiniteChecks.interval_of_check recordTest 5616 16 (by decide +kernel)
    
theorem records_join_5120_5152 : FiniteChecks.Interval recordTest 5120 5152 :=
  FiniteChecks.interval_append recordTest 5120 5136 5152 records_5120 records_5136

theorem records_join_5152_5184 : FiniteChecks.Interval recordTest 5152 5184 :=
  FiniteChecks.interval_append recordTest 5152 5168 5184 records_5152 records_5168

theorem records_join_5120_5184 : FiniteChecks.Interval recordTest 5120 5184 :=
  FiniteChecks.interval_append recordTest 5120 5152 5184 records_join_5120_5152 records_join_5152_5184

theorem records_join_5184_5216 : FiniteChecks.Interval recordTest 5184 5216 :=
  FiniteChecks.interval_append recordTest 5184 5200 5216 records_5184 records_5200

theorem records_join_5216_5248 : FiniteChecks.Interval recordTest 5216 5248 :=
  FiniteChecks.interval_append recordTest 5216 5232 5248 records_5216 records_5232

theorem records_join_5184_5248 : FiniteChecks.Interval recordTest 5184 5248 :=
  FiniteChecks.interval_append recordTest 5184 5216 5248 records_join_5184_5216 records_join_5216_5248

theorem records_join_5120_5248 : FiniteChecks.Interval recordTest 5120 5248 :=
  FiniteChecks.interval_append recordTest 5120 5184 5248 records_join_5120_5184 records_join_5184_5248

theorem records_join_5248_5280 : FiniteChecks.Interval recordTest 5248 5280 :=
  FiniteChecks.interval_append recordTest 5248 5264 5280 records_5248 records_5264

theorem records_join_5280_5312 : FiniteChecks.Interval recordTest 5280 5312 :=
  FiniteChecks.interval_append recordTest 5280 5296 5312 records_5280 records_5296

theorem records_join_5248_5312 : FiniteChecks.Interval recordTest 5248 5312 :=
  FiniteChecks.interval_append recordTest 5248 5280 5312 records_join_5248_5280 records_join_5280_5312

theorem records_join_5312_5344 : FiniteChecks.Interval recordTest 5312 5344 :=
  FiniteChecks.interval_append recordTest 5312 5328 5344 records_5312 records_5328

theorem records_join_5344_5376 : FiniteChecks.Interval recordTest 5344 5376 :=
  FiniteChecks.interval_append recordTest 5344 5360 5376 records_5344 records_5360

theorem records_join_5312_5376 : FiniteChecks.Interval recordTest 5312 5376 :=
  FiniteChecks.interval_append recordTest 5312 5344 5376 records_join_5312_5344 records_join_5344_5376

theorem records_join_5248_5376 : FiniteChecks.Interval recordTest 5248 5376 :=
  FiniteChecks.interval_append recordTest 5248 5312 5376 records_join_5248_5312 records_join_5312_5376

theorem records_join_5120_5376 : FiniteChecks.Interval recordTest 5120 5376 :=
  FiniteChecks.interval_append recordTest 5120 5248 5376 records_join_5120_5248 records_join_5248_5376

theorem records_join_5376_5408 : FiniteChecks.Interval recordTest 5376 5408 :=
  FiniteChecks.interval_append recordTest 5376 5392 5408 records_5376 records_5392

theorem records_join_5408_5440 : FiniteChecks.Interval recordTest 5408 5440 :=
  FiniteChecks.interval_append recordTest 5408 5424 5440 records_5408 records_5424

theorem records_join_5376_5440 : FiniteChecks.Interval recordTest 5376 5440 :=
  FiniteChecks.interval_append recordTest 5376 5408 5440 records_join_5376_5408 records_join_5408_5440

theorem records_join_5440_5472 : FiniteChecks.Interval recordTest 5440 5472 :=
  FiniteChecks.interval_append recordTest 5440 5456 5472 records_5440 records_5456

theorem records_join_5472_5504 : FiniteChecks.Interval recordTest 5472 5504 :=
  FiniteChecks.interval_append recordTest 5472 5488 5504 records_5472 records_5488

theorem records_join_5440_5504 : FiniteChecks.Interval recordTest 5440 5504 :=
  FiniteChecks.interval_append recordTest 5440 5472 5504 records_join_5440_5472 records_join_5472_5504

theorem records_join_5376_5504 : FiniteChecks.Interval recordTest 5376 5504 :=
  FiniteChecks.interval_append recordTest 5376 5440 5504 records_join_5376_5440 records_join_5440_5504

theorem records_join_5504_5536 : FiniteChecks.Interval recordTest 5504 5536 :=
  FiniteChecks.interval_append recordTest 5504 5520 5536 records_5504 records_5520

theorem records_join_5536_5568 : FiniteChecks.Interval recordTest 5536 5568 :=
  FiniteChecks.interval_append recordTest 5536 5552 5568 records_5536 records_5552

theorem records_join_5504_5568 : FiniteChecks.Interval recordTest 5504 5568 :=
  FiniteChecks.interval_append recordTest 5504 5536 5568 records_join_5504_5536 records_join_5536_5568

theorem records_join_5568_5600 : FiniteChecks.Interval recordTest 5568 5600 :=
  FiniteChecks.interval_append recordTest 5568 5584 5600 records_5568 records_5584

theorem records_join_5600_5632 : FiniteChecks.Interval recordTest 5600 5632 :=
  FiniteChecks.interval_append recordTest 5600 5616 5632 records_5600 records_5616

theorem records_join_5568_5632 : FiniteChecks.Interval recordTest 5568 5632 :=
  FiniteChecks.interval_append recordTest 5568 5600 5632 records_join_5568_5600 records_join_5600_5632

theorem records_join_5504_5632 : FiniteChecks.Interval recordTest 5504 5632 :=
  FiniteChecks.interval_append recordTest 5504 5568 5632 records_join_5504_5568 records_join_5568_5632

theorem records_join_5376_5632 : FiniteChecks.Interval recordTest 5376 5632 :=
  FiniteChecks.interval_append recordTest 5376 5504 5632 records_join_5376_5504 records_join_5504_5632

theorem records_join_5120_5632 : FiniteChecks.Interval recordTest 5120 5632 :=
  FiniteChecks.interval_append recordTest 5120 5376 5632 records_join_5120_5376 records_join_5376_5632

theorem records_part_010 : FiniteChecks.Interval recordTest 5120 5632 := records_join_5120_5632
    end Papers.RationalityTen.FacetUniverses.FullSmall
    