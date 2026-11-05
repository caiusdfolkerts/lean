module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_1024 : FiniteChecks.Interval recordTest 1024 1040 :=
      FiniteChecks.interval_of_check recordTest 1024 16 (by decide +kernel)
    
theorem records_1040 : FiniteChecks.Interval recordTest 1040 1056 :=
      FiniteChecks.interval_of_check recordTest 1040 16 (by decide +kernel)
    
theorem records_1056 : FiniteChecks.Interval recordTest 1056 1072 :=
      FiniteChecks.interval_of_check recordTest 1056 16 (by decide +kernel)
    
theorem records_1072 : FiniteChecks.Interval recordTest 1072 1088 :=
      FiniteChecks.interval_of_check recordTest 1072 16 (by decide +kernel)
    
theorem records_1088 : FiniteChecks.Interval recordTest 1088 1104 :=
      FiniteChecks.interval_of_check recordTest 1088 16 (by decide +kernel)
    
theorem records_1104 : FiniteChecks.Interval recordTest 1104 1120 :=
      FiniteChecks.interval_of_check recordTest 1104 16 (by decide +kernel)
    
theorem records_1120 : FiniteChecks.Interval recordTest 1120 1136 :=
      FiniteChecks.interval_of_check recordTest 1120 16 (by decide +kernel)
    
theorem records_1136 : FiniteChecks.Interval recordTest 1136 1152 :=
      FiniteChecks.interval_of_check recordTest 1136 16 (by decide +kernel)
    
theorem records_1152 : FiniteChecks.Interval recordTest 1152 1168 :=
      FiniteChecks.interval_of_check recordTest 1152 16 (by decide +kernel)
    
theorem records_1168 : FiniteChecks.Interval recordTest 1168 1184 :=
      FiniteChecks.interval_of_check recordTest 1168 16 (by decide +kernel)
    
theorem records_1184 : FiniteChecks.Interval recordTest 1184 1200 :=
      FiniteChecks.interval_of_check recordTest 1184 16 (by decide +kernel)
    
theorem records_1200 : FiniteChecks.Interval recordTest 1200 1216 :=
      FiniteChecks.interval_of_check recordTest 1200 16 (by decide +kernel)
    
theorem records_1216 : FiniteChecks.Interval recordTest 1216 1232 :=
      FiniteChecks.interval_of_check recordTest 1216 16 (by decide +kernel)
    
theorem records_1232 : FiniteChecks.Interval recordTest 1232 1248 :=
      FiniteChecks.interval_of_check recordTest 1232 16 (by decide +kernel)
    
theorem records_1248 : FiniteChecks.Interval recordTest 1248 1264 :=
      FiniteChecks.interval_of_check recordTest 1248 16 (by decide +kernel)
    
theorem records_1264 : FiniteChecks.Interval recordTest 1264 1280 :=
      FiniteChecks.interval_of_check recordTest 1264 16 (by decide +kernel)
    
theorem records_1280 : FiniteChecks.Interval recordTest 1280 1296 :=
      FiniteChecks.interval_of_check recordTest 1280 16 (by decide +kernel)
    
theorem records_1296 : FiniteChecks.Interval recordTest 1296 1312 :=
      FiniteChecks.interval_of_check recordTest 1296 16 (by decide +kernel)
    
theorem records_1312 : FiniteChecks.Interval recordTest 1312 1328 :=
      FiniteChecks.interval_of_check recordTest 1312 16 (by decide +kernel)
    
theorem records_1328 : FiniteChecks.Interval recordTest 1328 1344 :=
      FiniteChecks.interval_of_check recordTest 1328 16 (by decide +kernel)
    
theorem records_1344 : FiniteChecks.Interval recordTest 1344 1360 :=
      FiniteChecks.interval_of_check recordTest 1344 16 (by decide +kernel)
    
theorem records_1360 : FiniteChecks.Interval recordTest 1360 1376 :=
      FiniteChecks.interval_of_check recordTest 1360 16 (by decide +kernel)
    
theorem records_1376 : FiniteChecks.Interval recordTest 1376 1392 :=
      FiniteChecks.interval_of_check recordTest 1376 16 (by decide +kernel)
    
theorem records_1392 : FiniteChecks.Interval recordTest 1392 1408 :=
      FiniteChecks.interval_of_check recordTest 1392 16 (by decide +kernel)
    
theorem records_1408 : FiniteChecks.Interval recordTest 1408 1424 :=
      FiniteChecks.interval_of_check recordTest 1408 16 (by decide +kernel)
    
theorem records_1424 : FiniteChecks.Interval recordTest 1424 1440 :=
      FiniteChecks.interval_of_check recordTest 1424 16 (by decide +kernel)
    
theorem records_1440 : FiniteChecks.Interval recordTest 1440 1456 :=
      FiniteChecks.interval_of_check recordTest 1440 16 (by decide +kernel)
    
theorem records_1456 : FiniteChecks.Interval recordTest 1456 1472 :=
      FiniteChecks.interval_of_check recordTest 1456 16 (by decide +kernel)
    
theorem records_1472 : FiniteChecks.Interval recordTest 1472 1488 :=
      FiniteChecks.interval_of_check recordTest 1472 16 (by decide +kernel)
    
theorem records_1488 : FiniteChecks.Interval recordTest 1488 1504 :=
      FiniteChecks.interval_of_check recordTest 1488 16 (by decide +kernel)
    
theorem records_1504 : FiniteChecks.Interval recordTest 1504 1520 :=
      FiniteChecks.interval_of_check recordTest 1504 16 (by decide +kernel)
    
theorem records_1520 : FiniteChecks.Interval recordTest 1520 1536 :=
      FiniteChecks.interval_of_check recordTest 1520 16 (by decide +kernel)
    
theorem records_join_1024_1056 : FiniteChecks.Interval recordTest 1024 1056 :=
  FiniteChecks.interval_append recordTest 1024 1040 1056 records_1024 records_1040

theorem records_join_1056_1088 : FiniteChecks.Interval recordTest 1056 1088 :=
  FiniteChecks.interval_append recordTest 1056 1072 1088 records_1056 records_1072

theorem records_join_1024_1088 : FiniteChecks.Interval recordTest 1024 1088 :=
  FiniteChecks.interval_append recordTest 1024 1056 1088 records_join_1024_1056 records_join_1056_1088

theorem records_join_1088_1120 : FiniteChecks.Interval recordTest 1088 1120 :=
  FiniteChecks.interval_append recordTest 1088 1104 1120 records_1088 records_1104

theorem records_join_1120_1152 : FiniteChecks.Interval recordTest 1120 1152 :=
  FiniteChecks.interval_append recordTest 1120 1136 1152 records_1120 records_1136

theorem records_join_1088_1152 : FiniteChecks.Interval recordTest 1088 1152 :=
  FiniteChecks.interval_append recordTest 1088 1120 1152 records_join_1088_1120 records_join_1120_1152

theorem records_join_1024_1152 : FiniteChecks.Interval recordTest 1024 1152 :=
  FiniteChecks.interval_append recordTest 1024 1088 1152 records_join_1024_1088 records_join_1088_1152

theorem records_join_1152_1184 : FiniteChecks.Interval recordTest 1152 1184 :=
  FiniteChecks.interval_append recordTest 1152 1168 1184 records_1152 records_1168

theorem records_join_1184_1216 : FiniteChecks.Interval recordTest 1184 1216 :=
  FiniteChecks.interval_append recordTest 1184 1200 1216 records_1184 records_1200

theorem records_join_1152_1216 : FiniteChecks.Interval recordTest 1152 1216 :=
  FiniteChecks.interval_append recordTest 1152 1184 1216 records_join_1152_1184 records_join_1184_1216

theorem records_join_1216_1248 : FiniteChecks.Interval recordTest 1216 1248 :=
  FiniteChecks.interval_append recordTest 1216 1232 1248 records_1216 records_1232

theorem records_join_1248_1280 : FiniteChecks.Interval recordTest 1248 1280 :=
  FiniteChecks.interval_append recordTest 1248 1264 1280 records_1248 records_1264

theorem records_join_1216_1280 : FiniteChecks.Interval recordTest 1216 1280 :=
  FiniteChecks.interval_append recordTest 1216 1248 1280 records_join_1216_1248 records_join_1248_1280

theorem records_join_1152_1280 : FiniteChecks.Interval recordTest 1152 1280 :=
  FiniteChecks.interval_append recordTest 1152 1216 1280 records_join_1152_1216 records_join_1216_1280

theorem records_join_1024_1280 : FiniteChecks.Interval recordTest 1024 1280 :=
  FiniteChecks.interval_append recordTest 1024 1152 1280 records_join_1024_1152 records_join_1152_1280

theorem records_join_1280_1312 : FiniteChecks.Interval recordTest 1280 1312 :=
  FiniteChecks.interval_append recordTest 1280 1296 1312 records_1280 records_1296

theorem records_join_1312_1344 : FiniteChecks.Interval recordTest 1312 1344 :=
  FiniteChecks.interval_append recordTest 1312 1328 1344 records_1312 records_1328

theorem records_join_1280_1344 : FiniteChecks.Interval recordTest 1280 1344 :=
  FiniteChecks.interval_append recordTest 1280 1312 1344 records_join_1280_1312 records_join_1312_1344

theorem records_join_1344_1376 : FiniteChecks.Interval recordTest 1344 1376 :=
  FiniteChecks.interval_append recordTest 1344 1360 1376 records_1344 records_1360

theorem records_join_1376_1408 : FiniteChecks.Interval recordTest 1376 1408 :=
  FiniteChecks.interval_append recordTest 1376 1392 1408 records_1376 records_1392

theorem records_join_1344_1408 : FiniteChecks.Interval recordTest 1344 1408 :=
  FiniteChecks.interval_append recordTest 1344 1376 1408 records_join_1344_1376 records_join_1376_1408

theorem records_join_1280_1408 : FiniteChecks.Interval recordTest 1280 1408 :=
  FiniteChecks.interval_append recordTest 1280 1344 1408 records_join_1280_1344 records_join_1344_1408

theorem records_join_1408_1440 : FiniteChecks.Interval recordTest 1408 1440 :=
  FiniteChecks.interval_append recordTest 1408 1424 1440 records_1408 records_1424

theorem records_join_1440_1472 : FiniteChecks.Interval recordTest 1440 1472 :=
  FiniteChecks.interval_append recordTest 1440 1456 1472 records_1440 records_1456

theorem records_join_1408_1472 : FiniteChecks.Interval recordTest 1408 1472 :=
  FiniteChecks.interval_append recordTest 1408 1440 1472 records_join_1408_1440 records_join_1440_1472

theorem records_join_1472_1504 : FiniteChecks.Interval recordTest 1472 1504 :=
  FiniteChecks.interval_append recordTest 1472 1488 1504 records_1472 records_1488

theorem records_join_1504_1536 : FiniteChecks.Interval recordTest 1504 1536 :=
  FiniteChecks.interval_append recordTest 1504 1520 1536 records_1504 records_1520

theorem records_join_1472_1536 : FiniteChecks.Interval recordTest 1472 1536 :=
  FiniteChecks.interval_append recordTest 1472 1504 1536 records_join_1472_1504 records_join_1504_1536

theorem records_join_1408_1536 : FiniteChecks.Interval recordTest 1408 1536 :=
  FiniteChecks.interval_append recordTest 1408 1472 1536 records_join_1408_1472 records_join_1472_1536

theorem records_join_1280_1536 : FiniteChecks.Interval recordTest 1280 1536 :=
  FiniteChecks.interval_append recordTest 1280 1408 1536 records_join_1280_1408 records_join_1408_1536

theorem records_join_1024_1536 : FiniteChecks.Interval recordTest 1024 1536 :=
  FiniteChecks.interval_append recordTest 1024 1280 1536 records_join_1024_1280 records_join_1280_1536

theorem records_part_002 : FiniteChecks.Interval recordTest 1024 1536 := records_join_1024_1536
    end Papers.RationalityTen.FacetUniverses.FullSmall
    