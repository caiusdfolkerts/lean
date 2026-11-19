module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check040.part5120 : Interval test 5120 5128 :=
  interval_of_check _ 5120 8 (by decide +kernel)
theorem Check040.part5128 : Interval test 5128 5136 :=
  interval_of_check _ 5128 8 (by decide +kernel)
theorem Check040.part5136 : Interval test 5136 5144 :=
  interval_of_check _ 5136 8 (by decide +kernel)
theorem Check040.part5144 : Interval test 5144 5152 :=
  interval_of_check _ 5144 8 (by decide +kernel)
theorem Check040.part5152 : Interval test 5152 5160 :=
  interval_of_check _ 5152 8 (by decide +kernel)
theorem Check040.part5160 : Interval test 5160 5168 :=
  interval_of_check _ 5160 8 (by decide +kernel)
theorem Check040.part5168 : Interval test 5168 5176 :=
  interval_of_check _ 5168 8 (by decide +kernel)
theorem Check040.part5176 : Interval test 5176 5184 :=
  interval_of_check _ 5176 8 (by decide +kernel)
theorem Check040.part5184 : Interval test 5184 5192 :=
  interval_of_check _ 5184 8 (by decide +kernel)
theorem Check040.part5192 : Interval test 5192 5200 :=
  interval_of_check _ 5192 8 (by decide +kernel)
theorem Check040.part5200 : Interval test 5200 5208 :=
  interval_of_check _ 5200 8 (by decide +kernel)
theorem Check040.part5208 : Interval test 5208 5216 :=
  interval_of_check _ 5208 8 (by decide +kernel)
theorem Check040.part5216 : Interval test 5216 5224 :=
  interval_of_check _ 5216 8 (by decide +kernel)
theorem Check040.part5224 : Interval test 5224 5232 :=
  interval_of_check _ 5224 8 (by decide +kernel)
theorem Check040.part5232 : Interval test 5232 5240 :=
  interval_of_check _ 5232 8 (by decide +kernel)
theorem Check040.part5240 : Interval test 5240 5248 :=
  interval_of_check _ 5240 8 (by decide +kernel)
theorem Check040.checked : Interval test 5120 5248 :=
  (FiniteChecks.interval_append test 5120 5184 5248
  (FiniteChecks.interval_append test 5120 5152 5184
  (FiniteChecks.interval_append test 5120 5136 5152
  (FiniteChecks.interval_append test 5120 5128 5136
  Check040.part5120
  Check040.part5128)
  (FiniteChecks.interval_append test 5136 5144 5152
  Check040.part5136
  Check040.part5144))
  (FiniteChecks.interval_append test 5152 5168 5184
  (FiniteChecks.interval_append test 5152 5160 5168
  Check040.part5152
  Check040.part5160)
  (FiniteChecks.interval_append test 5168 5176 5184
  Check040.part5168
  Check040.part5176)))
  (FiniteChecks.interval_append test 5184 5216 5248
  (FiniteChecks.interval_append test 5184 5200 5216
  (FiniteChecks.interval_append test 5184 5192 5200
  Check040.part5184
  Check040.part5192)
  (FiniteChecks.interval_append test 5200 5208 5216
  Check040.part5200
  Check040.part5208))
  (FiniteChecks.interval_append test 5216 5232 5248
  (FiniteChecks.interval_append test 5216 5224 5232
  Check040.part5216
  Check040.part5224)
  (FiniteChecks.interval_append test 5232 5240 5248
  Check040.part5232
  Check040.part5240))))
theorem Check041.part5248 : Interval test 5248 5256 :=
  interval_of_check _ 5248 8 (by decide +kernel)
theorem Check041.part5256 : Interval test 5256 5264 :=
  interval_of_check _ 5256 8 (by decide +kernel)
theorem Check041.part5264 : Interval test 5264 5272 :=
  interval_of_check _ 5264 8 (by decide +kernel)
theorem Check041.part5272 : Interval test 5272 5280 :=
  interval_of_check _ 5272 8 (by decide +kernel)
theorem Check041.part5280 : Interval test 5280 5288 :=
  interval_of_check _ 5280 8 (by decide +kernel)
theorem Check041.part5288 : Interval test 5288 5296 :=
  interval_of_check _ 5288 8 (by decide +kernel)
theorem Check041.part5296 : Interval test 5296 5304 :=
  interval_of_check _ 5296 8 (by decide +kernel)
theorem Check041.part5304 : Interval test 5304 5312 :=
  interval_of_check _ 5304 8 (by decide +kernel)
theorem Check041.part5312 : Interval test 5312 5320 :=
  interval_of_check _ 5312 8 (by decide +kernel)
theorem Check041.part5320 : Interval test 5320 5328 :=
  interval_of_check _ 5320 8 (by decide +kernel)
theorem Check041.part5328 : Interval test 5328 5336 :=
  interval_of_check _ 5328 8 (by decide +kernel)
theorem Check041.part5336 : Interval test 5336 5344 :=
  interval_of_check _ 5336 8 (by decide +kernel)
theorem Check041.part5344 : Interval test 5344 5352 :=
  interval_of_check _ 5344 8 (by decide +kernel)
theorem Check041.part5352 : Interval test 5352 5360 :=
  interval_of_check _ 5352 8 (by decide +kernel)
theorem Check041.part5360 : Interval test 5360 5368 :=
  interval_of_check _ 5360 8 (by decide +kernel)
theorem Check041.part5368 : Interval test 5368 5376 :=
  interval_of_check _ 5368 8 (by decide +kernel)
theorem Check041.checked : Interval test 5248 5376 :=
  (FiniteChecks.interval_append test 5248 5312 5376
  (FiniteChecks.interval_append test 5248 5280 5312
  (FiniteChecks.interval_append test 5248 5264 5280
  (FiniteChecks.interval_append test 5248 5256 5264
  Check041.part5248
  Check041.part5256)
  (FiniteChecks.interval_append test 5264 5272 5280
  Check041.part5264
  Check041.part5272))
  (FiniteChecks.interval_append test 5280 5296 5312
  (FiniteChecks.interval_append test 5280 5288 5296
  Check041.part5280
  Check041.part5288)
  (FiniteChecks.interval_append test 5296 5304 5312
  Check041.part5296
  Check041.part5304)))
  (FiniteChecks.interval_append test 5312 5344 5376
  (FiniteChecks.interval_append test 5312 5328 5344
  (FiniteChecks.interval_append test 5312 5320 5328
  Check041.part5312
  Check041.part5320)
  (FiniteChecks.interval_append test 5328 5336 5344
  Check041.part5328
  Check041.part5336))
  (FiniteChecks.interval_append test 5344 5360 5376
  (FiniteChecks.interval_append test 5344 5352 5360
  Check041.part5344
  Check041.part5352)
  (FiniteChecks.interval_append test 5360 5368 5376
  Check041.part5360
  Check041.part5368))))
theorem Check042.part5376 : Interval test 5376 5384 :=
  interval_of_check _ 5376 8 (by decide +kernel)
theorem Check042.part5384 : Interval test 5384 5392 :=
  interval_of_check _ 5384 8 (by decide +kernel)
theorem Check042.part5392 : Interval test 5392 5400 :=
  interval_of_check _ 5392 8 (by decide +kernel)
theorem Check042.part5400 : Interval test 5400 5408 :=
  interval_of_check _ 5400 8 (by decide +kernel)
theorem Check042.part5408 : Interval test 5408 5416 :=
  interval_of_check _ 5408 8 (by decide +kernel)
theorem Check042.part5416 : Interval test 5416 5424 :=
  interval_of_check _ 5416 8 (by decide +kernel)
theorem Check042.part5424 : Interval test 5424 5432 :=
  interval_of_check _ 5424 8 (by decide +kernel)
theorem Check042.part5432 : Interval test 5432 5440 :=
  interval_of_check _ 5432 8 (by decide +kernel)
theorem Check042.part5440 : Interval test 5440 5448 :=
  interval_of_check _ 5440 8 (by decide +kernel)
theorem Check042.part5448 : Interval test 5448 5456 :=
  interval_of_check _ 5448 8 (by decide +kernel)
theorem Check042.part5456 : Interval test 5456 5464 :=
  interval_of_check _ 5456 8 (by decide +kernel)
theorem Check042.part5464 : Interval test 5464 5472 :=
  interval_of_check _ 5464 8 (by decide +kernel)
theorem Check042.part5472 : Interval test 5472 5480 :=
  interval_of_check _ 5472 8 (by decide +kernel)
theorem Check042.part5480 : Interval test 5480 5488 :=
  interval_of_check _ 5480 8 (by decide +kernel)
theorem Check042.part5488 : Interval test 5488 5496 :=
  interval_of_check _ 5488 8 (by decide +kernel)
theorem Check042.part5496 : Interval test 5496 5504 :=
  interval_of_check _ 5496 8 (by decide +kernel)
theorem Check042.checked : Interval test 5376 5504 :=
  (FiniteChecks.interval_append test 5376 5440 5504
  (FiniteChecks.interval_append test 5376 5408 5440
  (FiniteChecks.interval_append test 5376 5392 5408
  (FiniteChecks.interval_append test 5376 5384 5392
  Check042.part5376
  Check042.part5384)
  (FiniteChecks.interval_append test 5392 5400 5408
  Check042.part5392
  Check042.part5400))
  (FiniteChecks.interval_append test 5408 5424 5440
  (FiniteChecks.interval_append test 5408 5416 5424
  Check042.part5408
  Check042.part5416)
  (FiniteChecks.interval_append test 5424 5432 5440
  Check042.part5424
  Check042.part5432)))
  (FiniteChecks.interval_append test 5440 5472 5504
  (FiniteChecks.interval_append test 5440 5456 5472
  (FiniteChecks.interval_append test 5440 5448 5456
  Check042.part5440
  Check042.part5448)
  (FiniteChecks.interval_append test 5456 5464 5472
  Check042.part5456
  Check042.part5464))
  (FiniteChecks.interval_append test 5472 5488 5504
  (FiniteChecks.interval_append test 5472 5480 5488
  Check042.part5472
  Check042.part5480)
  (FiniteChecks.interval_append test 5488 5496 5504
  Check042.part5488
  Check042.part5496))))
theorem Check043.part5504 : Interval test 5504 5512 :=
  interval_of_check _ 5504 8 (by decide +kernel)
theorem Check043.part5512 : Interval test 5512 5520 :=
  interval_of_check _ 5512 8 (by decide +kernel)
theorem Check043.part5520 : Interval test 5520 5528 :=
  interval_of_check _ 5520 8 (by decide +kernel)
theorem Check043.part5528 : Interval test 5528 5536 :=
  interval_of_check _ 5528 8 (by decide +kernel)
theorem Check043.part5536 : Interval test 5536 5544 :=
  interval_of_check _ 5536 8 (by decide +kernel)
theorem Check043.part5544 : Interval test 5544 5552 :=
  interval_of_check _ 5544 8 (by decide +kernel)
theorem Check043.part5552 : Interval test 5552 5560 :=
  interval_of_check _ 5552 8 (by decide +kernel)
theorem Check043.part5560 : Interval test 5560 5568 :=
  interval_of_check _ 5560 8 (by decide +kernel)
theorem Check043.part5568 : Interval test 5568 5576 :=
  interval_of_check _ 5568 8 (by decide +kernel)
theorem Check043.part5576 : Interval test 5576 5584 :=
  interval_of_check _ 5576 8 (by decide +kernel)
theorem Check043.part5584 : Interval test 5584 5592 :=
  interval_of_check _ 5584 8 (by decide +kernel)
theorem Check043.part5592 : Interval test 5592 5600 :=
  interval_of_check _ 5592 8 (by decide +kernel)
theorem Check043.part5600 : Interval test 5600 5608 :=
  interval_of_check _ 5600 8 (by decide +kernel)
theorem Check043.part5608 : Interval test 5608 5616 :=
  interval_of_check _ 5608 8 (by decide +kernel)
theorem Check043.part5616 : Interval test 5616 5624 :=
  interval_of_check _ 5616 8 (by decide +kernel)
theorem Check043.part5624 : Interval test 5624 5632 :=
  interval_of_check _ 5624 8 (by decide +kernel)
theorem Check043.checked : Interval test 5504 5632 :=
  (FiniteChecks.interval_append test 5504 5568 5632
  (FiniteChecks.interval_append test 5504 5536 5568
  (FiniteChecks.interval_append test 5504 5520 5536
  (FiniteChecks.interval_append test 5504 5512 5520
  Check043.part5504
  Check043.part5512)
  (FiniteChecks.interval_append test 5520 5528 5536
  Check043.part5520
  Check043.part5528))
  (FiniteChecks.interval_append test 5536 5552 5568
  (FiniteChecks.interval_append test 5536 5544 5552
  Check043.part5536
  Check043.part5544)
  (FiniteChecks.interval_append test 5552 5560 5568
  Check043.part5552
  Check043.part5560)))
  (FiniteChecks.interval_append test 5568 5600 5632
  (FiniteChecks.interval_append test 5568 5584 5600
  (FiniteChecks.interval_append test 5568 5576 5584
  Check043.part5568
  Check043.part5576)
  (FiniteChecks.interval_append test 5584 5592 5600
  Check043.part5584
  Check043.part5592))
  (FiniteChecks.interval_append test 5600 5616 5632
  (FiniteChecks.interval_append test 5600 5608 5616
  Check043.part5600
  Check043.part5608)
  (FiniteChecks.interval_append test 5616 5624 5632
  Check043.part5616
  Check043.part5624))))
theorem Check044.part5632 : Interval test 5632 5640 :=
  interval_of_check _ 5632 8 (by decide +kernel)
theorem Check044.part5640 : Interval test 5640 5648 :=
  interval_of_check _ 5640 8 (by decide +kernel)
theorem Check044.part5648 : Interval test 5648 5656 :=
  interval_of_check _ 5648 8 (by decide +kernel)
theorem Check044.part5656 : Interval test 5656 5664 :=
  interval_of_check _ 5656 8 (by decide +kernel)
theorem Check044.part5664 : Interval test 5664 5672 :=
  interval_of_check _ 5664 8 (by decide +kernel)
theorem Check044.part5672 : Interval test 5672 5680 :=
  interval_of_check _ 5672 8 (by decide +kernel)
theorem Check044.part5680 : Interval test 5680 5688 :=
  interval_of_check _ 5680 8 (by decide +kernel)
theorem Check044.part5688 : Interval test 5688 5696 :=
  interval_of_check _ 5688 8 (by decide +kernel)
theorem Check044.part5696 : Interval test 5696 5704 :=
  interval_of_check _ 5696 8 (by decide +kernel)
theorem Check044.part5704 : Interval test 5704 5712 :=
  interval_of_check _ 5704 8 (by decide +kernel)
theorem Check044.part5712 : Interval test 5712 5720 :=
  interval_of_check _ 5712 8 (by decide +kernel)
theorem Check044.part5720 : Interval test 5720 5728 :=
  interval_of_check _ 5720 8 (by decide +kernel)
theorem Check044.part5728 : Interval test 5728 5736 :=
  interval_of_check _ 5728 8 (by decide +kernel)
theorem Check044.part5736 : Interval test 5736 5744 :=
  interval_of_check _ 5736 8 (by decide +kernel)
theorem Check044.part5744 : Interval test 5744 5752 :=
  interval_of_check _ 5744 8 (by decide +kernel)
theorem Check044.part5752 : Interval test 5752 5760 :=
  interval_of_check _ 5752 8 (by decide +kernel)
theorem Check044.checked : Interval test 5632 5760 :=
  (FiniteChecks.interval_append test 5632 5696 5760
  (FiniteChecks.interval_append test 5632 5664 5696
  (FiniteChecks.interval_append test 5632 5648 5664
  (FiniteChecks.interval_append test 5632 5640 5648
  Check044.part5632
  Check044.part5640)
  (FiniteChecks.interval_append test 5648 5656 5664
  Check044.part5648
  Check044.part5656))
  (FiniteChecks.interval_append test 5664 5680 5696
  (FiniteChecks.interval_append test 5664 5672 5680
  Check044.part5664
  Check044.part5672)
  (FiniteChecks.interval_append test 5680 5688 5696
  Check044.part5680
  Check044.part5688)))
  (FiniteChecks.interval_append test 5696 5728 5760
  (FiniteChecks.interval_append test 5696 5712 5728
  (FiniteChecks.interval_append test 5696 5704 5712
  Check044.part5696
  Check044.part5704)
  (FiniteChecks.interval_append test 5712 5720 5728
  Check044.part5712
  Check044.part5720))
  (FiniteChecks.interval_append test 5728 5744 5760
  (FiniteChecks.interval_append test 5728 5736 5744
  Check044.part5728
  Check044.part5736)
  (FiniteChecks.interval_append test 5744 5752 5760
  Check044.part5744
  Check044.part5752))))
theorem Check045.part5760 : Interval test 5760 5768 :=
  interval_of_check _ 5760 8 (by decide +kernel)
theorem Check045.part5768 : Interval test 5768 5776 :=
  interval_of_check _ 5768 8 (by decide +kernel)
theorem Check045.part5776 : Interval test 5776 5784 :=
  interval_of_check _ 5776 8 (by decide +kernel)
theorem Check045.part5784 : Interval test 5784 5792 :=
  interval_of_check _ 5784 8 (by decide +kernel)
theorem Check045.part5792 : Interval test 5792 5800 :=
  interval_of_check _ 5792 8 (by decide +kernel)
theorem Check045.part5800 : Interval test 5800 5808 :=
  interval_of_check _ 5800 8 (by decide +kernel)
theorem Check045.part5808 : Interval test 5808 5816 :=
  interval_of_check _ 5808 8 (by decide +kernel)
theorem Check045.part5816 : Interval test 5816 5824 :=
  interval_of_check _ 5816 8 (by decide +kernel)
theorem Check045.part5824 : Interval test 5824 5832 :=
  interval_of_check _ 5824 8 (by decide +kernel)
theorem Check045.part5832 : Interval test 5832 5840 :=
  interval_of_check _ 5832 8 (by decide +kernel)
theorem Check045.part5840 : Interval test 5840 5848 :=
  interval_of_check _ 5840 8 (by decide +kernel)
theorem Check045.part5848 : Interval test 5848 5856 :=
  interval_of_check _ 5848 8 (by decide +kernel)
theorem Check045.part5856 : Interval test 5856 5864 :=
  interval_of_check _ 5856 8 (by decide +kernel)
theorem Check045.part5864 : Interval test 5864 5872 :=
  interval_of_check _ 5864 8 (by decide +kernel)
theorem Check045.part5872 : Interval test 5872 5880 :=
  interval_of_check _ 5872 8 (by decide +kernel)
theorem Check045.part5880 : Interval test 5880 5888 :=
  interval_of_check _ 5880 8 (by decide +kernel)
theorem Check045.checked : Interval test 5760 5888 :=
  (FiniteChecks.interval_append test 5760 5824 5888
  (FiniteChecks.interval_append test 5760 5792 5824
  (FiniteChecks.interval_append test 5760 5776 5792
  (FiniteChecks.interval_append test 5760 5768 5776
  Check045.part5760
  Check045.part5768)
  (FiniteChecks.interval_append test 5776 5784 5792
  Check045.part5776
  Check045.part5784))
  (FiniteChecks.interval_append test 5792 5808 5824
  (FiniteChecks.interval_append test 5792 5800 5808
  Check045.part5792
  Check045.part5800)
  (FiniteChecks.interval_append test 5808 5816 5824
  Check045.part5808
  Check045.part5816)))
  (FiniteChecks.interval_append test 5824 5856 5888
  (FiniteChecks.interval_append test 5824 5840 5856
  (FiniteChecks.interval_append test 5824 5832 5840
  Check045.part5824
  Check045.part5832)
  (FiniteChecks.interval_append test 5840 5848 5856
  Check045.part5840
  Check045.part5848))
  (FiniteChecks.interval_append test 5856 5872 5888
  (FiniteChecks.interval_append test 5856 5864 5872
  Check045.part5856
  Check045.part5864)
  (FiniteChecks.interval_append test 5872 5880 5888
  Check045.part5872
  Check045.part5880))))
theorem Check046.part5888 : Interval test 5888 5896 :=
  interval_of_check _ 5888 8 (by decide +kernel)
theorem Check046.part5896 : Interval test 5896 5904 :=
  interval_of_check _ 5896 8 (by decide +kernel)
theorem Check046.part5904 : Interval test 5904 5912 :=
  interval_of_check _ 5904 8 (by decide +kernel)
theorem Check046.part5912 : Interval test 5912 5920 :=
  interval_of_check _ 5912 8 (by decide +kernel)
theorem Check046.part5920 : Interval test 5920 5928 :=
  interval_of_check _ 5920 8 (by decide +kernel)
theorem Check046.part5928 : Interval test 5928 5936 :=
  interval_of_check _ 5928 8 (by decide +kernel)
theorem Check046.part5936 : Interval test 5936 5944 :=
  interval_of_check _ 5936 8 (by decide +kernel)
theorem Check046.part5944 : Interval test 5944 5952 :=
  interval_of_check _ 5944 8 (by decide +kernel)
theorem Check046.part5952 : Interval test 5952 5960 :=
  interval_of_check _ 5952 8 (by decide +kernel)
theorem Check046.part5960 : Interval test 5960 5968 :=
  interval_of_check _ 5960 8 (by decide +kernel)
theorem Check046.part5968 : Interval test 5968 5976 :=
  interval_of_check _ 5968 8 (by decide +kernel)
theorem Check046.part5976 : Interval test 5976 5984 :=
  interval_of_check _ 5976 8 (by decide +kernel)
theorem Check046.part5984 : Interval test 5984 5992 :=
  interval_of_check _ 5984 8 (by decide +kernel)
theorem Check046.part5992 : Interval test 5992 6000 :=
  interval_of_check _ 5992 8 (by decide +kernel)
theorem Check046.part6000 : Interval test 6000 6008 :=
  interval_of_check _ 6000 8 (by decide +kernel)
theorem Check046.part6008 : Interval test 6008 6016 :=
  interval_of_check _ 6008 8 (by decide +kernel)
theorem Check046.checked : Interval test 5888 6016 :=
  (FiniteChecks.interval_append test 5888 5952 6016
  (FiniteChecks.interval_append test 5888 5920 5952
  (FiniteChecks.interval_append test 5888 5904 5920
  (FiniteChecks.interval_append test 5888 5896 5904
  Check046.part5888
  Check046.part5896)
  (FiniteChecks.interval_append test 5904 5912 5920
  Check046.part5904
  Check046.part5912))
  (FiniteChecks.interval_append test 5920 5936 5952
  (FiniteChecks.interval_append test 5920 5928 5936
  Check046.part5920
  Check046.part5928)
  (FiniteChecks.interval_append test 5936 5944 5952
  Check046.part5936
  Check046.part5944)))
  (FiniteChecks.interval_append test 5952 5984 6016
  (FiniteChecks.interval_append test 5952 5968 5984
  (FiniteChecks.interval_append test 5952 5960 5968
  Check046.part5952
  Check046.part5960)
  (FiniteChecks.interval_append test 5968 5976 5984
  Check046.part5968
  Check046.part5976))
  (FiniteChecks.interval_append test 5984 6000 6016
  (FiniteChecks.interval_append test 5984 5992 6000
  Check046.part5984
  Check046.part5992)
  (FiniteChecks.interval_append test 6000 6008 6016
  Check046.part6000
  Check046.part6008))))
theorem Check047.part6016 : Interval test 6016 6024 :=
  interval_of_check _ 6016 8 (by decide +kernel)
theorem Check047.part6024 : Interval test 6024 6032 :=
  interval_of_check _ 6024 8 (by decide +kernel)
theorem Check047.part6032 : Interval test 6032 6040 :=
  interval_of_check _ 6032 8 (by decide +kernel)
theorem Check047.part6040 : Interval test 6040 6048 :=
  interval_of_check _ 6040 8 (by decide +kernel)
theorem Check047.part6048 : Interval test 6048 6056 :=
  interval_of_check _ 6048 8 (by decide +kernel)
theorem Check047.part6056 : Interval test 6056 6064 :=
  interval_of_check _ 6056 8 (by decide +kernel)
theorem Check047.part6064 : Interval test 6064 6072 :=
  interval_of_check _ 6064 8 (by decide +kernel)
theorem Check047.part6072 : Interval test 6072 6080 :=
  interval_of_check _ 6072 8 (by decide +kernel)
theorem Check047.part6080 : Interval test 6080 6088 :=
  interval_of_check _ 6080 8 (by decide +kernel)
theorem Check047.part6088 : Interval test 6088 6096 :=
  interval_of_check _ 6088 8 (by decide +kernel)
theorem Check047.part6096 : Interval test 6096 6104 :=
  interval_of_check _ 6096 8 (by decide +kernel)
theorem Check047.part6104 : Interval test 6104 6112 :=
  interval_of_check _ 6104 8 (by decide +kernel)
theorem Check047.part6112 : Interval test 6112 6120 :=
  interval_of_check _ 6112 8 (by decide +kernel)
theorem Check047.part6120 : Interval test 6120 6128 :=
  interval_of_check _ 6120 8 (by decide +kernel)
theorem Check047.part6128 : Interval test 6128 6136 :=
  interval_of_check _ 6128 8 (by decide +kernel)
theorem Check047.part6136 : Interval test 6136 6144 :=
  interval_of_check _ 6136 8 (by decide +kernel)
theorem Check047.checked : Interval test 6016 6144 :=
  (FiniteChecks.interval_append test 6016 6080 6144
  (FiniteChecks.interval_append test 6016 6048 6080
  (FiniteChecks.interval_append test 6016 6032 6048
  (FiniteChecks.interval_append test 6016 6024 6032
  Check047.part6016
  Check047.part6024)
  (FiniteChecks.interval_append test 6032 6040 6048
  Check047.part6032
  Check047.part6040))
  (FiniteChecks.interval_append test 6048 6064 6080
  (FiniteChecks.interval_append test 6048 6056 6064
  Check047.part6048
  Check047.part6056)
  (FiniteChecks.interval_append test 6064 6072 6080
  Check047.part6064
  Check047.part6072)))
  (FiniteChecks.interval_append test 6080 6112 6144
  (FiniteChecks.interval_append test 6080 6096 6112
  (FiniteChecks.interval_append test 6080 6088 6096
  Check047.part6080
  Check047.part6088)
  (FiniteChecks.interval_append test 6096 6104 6112
  Check047.part6096
  Check047.part6104))
  (FiniteChecks.interval_append test 6112 6128 6144
  (FiniteChecks.interval_append test 6112 6120 6128
  Check047.part6112
  Check047.part6120)
  (FiniteChecks.interval_append test 6128 6136 6144
  Check047.part6128
  Check047.part6136))))
end Papers.RationalityTen.SharedTriangleCounts
