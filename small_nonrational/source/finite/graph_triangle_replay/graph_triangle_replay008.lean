module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check064.part8192 : Interval test 8192 8200 :=
  interval_of_check _ 8192 8 (by decide +kernel)
theorem Check064.part8200 : Interval test 8200 8208 :=
  interval_of_check _ 8200 8 (by decide +kernel)
theorem Check064.part8208 : Interval test 8208 8216 :=
  interval_of_check _ 8208 8 (by decide +kernel)
theorem Check064.part8216 : Interval test 8216 8224 :=
  interval_of_check _ 8216 8 (by decide +kernel)
theorem Check064.part8224 : Interval test 8224 8232 :=
  interval_of_check _ 8224 8 (by decide +kernel)
theorem Check064.part8232 : Interval test 8232 8240 :=
  interval_of_check _ 8232 8 (by decide +kernel)
theorem Check064.part8240 : Interval test 8240 8248 :=
  interval_of_check _ 8240 8 (by decide +kernel)
theorem Check064.part8248 : Interval test 8248 8256 :=
  interval_of_check _ 8248 8 (by decide +kernel)
theorem Check064.part8256 : Interval test 8256 8264 :=
  interval_of_check _ 8256 8 (by decide +kernel)
theorem Check064.part8264 : Interval test 8264 8272 :=
  interval_of_check _ 8264 8 (by decide +kernel)
theorem Check064.part8272 : Interval test 8272 8280 :=
  interval_of_check _ 8272 8 (by decide +kernel)
theorem Check064.part8280 : Interval test 8280 8288 :=
  interval_of_check _ 8280 8 (by decide +kernel)
theorem Check064.part8288 : Interval test 8288 8296 :=
  interval_of_check _ 8288 8 (by decide +kernel)
theorem Check064.part8296 : Interval test 8296 8304 :=
  interval_of_check _ 8296 8 (by decide +kernel)
theorem Check064.part8304 : Interval test 8304 8312 :=
  interval_of_check _ 8304 8 (by decide +kernel)
theorem Check064.part8312 : Interval test 8312 8320 :=
  interval_of_check _ 8312 8 (by decide +kernel)
theorem Check064.checked : Interval test 8192 8320 :=
  (FiniteChecks.interval_append test 8192 8256 8320
  (FiniteChecks.interval_append test 8192 8224 8256
  (FiniteChecks.interval_append test 8192 8208 8224
  (FiniteChecks.interval_append test 8192 8200 8208
  Check064.part8192
  Check064.part8200)
  (FiniteChecks.interval_append test 8208 8216 8224
  Check064.part8208
  Check064.part8216))
  (FiniteChecks.interval_append test 8224 8240 8256
  (FiniteChecks.interval_append test 8224 8232 8240
  Check064.part8224
  Check064.part8232)
  (FiniteChecks.interval_append test 8240 8248 8256
  Check064.part8240
  Check064.part8248)))
  (FiniteChecks.interval_append test 8256 8288 8320
  (FiniteChecks.interval_append test 8256 8272 8288
  (FiniteChecks.interval_append test 8256 8264 8272
  Check064.part8256
  Check064.part8264)
  (FiniteChecks.interval_append test 8272 8280 8288
  Check064.part8272
  Check064.part8280))
  (FiniteChecks.interval_append test 8288 8304 8320
  (FiniteChecks.interval_append test 8288 8296 8304
  Check064.part8288
  Check064.part8296)
  (FiniteChecks.interval_append test 8304 8312 8320
  Check064.part8304
  Check064.part8312))))
theorem Check065.part8320 : Interval test 8320 8328 :=
  interval_of_check _ 8320 8 (by decide +kernel)
theorem Check065.part8328 : Interval test 8328 8336 :=
  interval_of_check _ 8328 8 (by decide +kernel)
theorem Check065.part8336 : Interval test 8336 8344 :=
  interval_of_check _ 8336 8 (by decide +kernel)
theorem Check065.part8344 : Interval test 8344 8352 :=
  interval_of_check _ 8344 8 (by decide +kernel)
theorem Check065.part8352 : Interval test 8352 8360 :=
  interval_of_check _ 8352 8 (by decide +kernel)
theorem Check065.part8360 : Interval test 8360 8368 :=
  interval_of_check _ 8360 8 (by decide +kernel)
theorem Check065.part8368 : Interval test 8368 8376 :=
  interval_of_check _ 8368 8 (by decide +kernel)
theorem Check065.part8376 : Interval test 8376 8384 :=
  interval_of_check _ 8376 8 (by decide +kernel)
theorem Check065.part8384 : Interval test 8384 8392 :=
  interval_of_check _ 8384 8 (by decide +kernel)
theorem Check065.part8392 : Interval test 8392 8400 :=
  interval_of_check _ 8392 8 (by decide +kernel)
theorem Check065.part8400 : Interval test 8400 8408 :=
  interval_of_check _ 8400 8 (by decide +kernel)
theorem Check065.part8408 : Interval test 8408 8416 :=
  interval_of_check _ 8408 8 (by decide +kernel)
theorem Check065.part8416 : Interval test 8416 8424 :=
  interval_of_check _ 8416 8 (by decide +kernel)
theorem Check065.part8424 : Interval test 8424 8432 :=
  interval_of_check _ 8424 8 (by decide +kernel)
theorem Check065.part8432 : Interval test 8432 8440 :=
  interval_of_check _ 8432 8 (by decide +kernel)
theorem Check065.part8440 : Interval test 8440 8448 :=
  interval_of_check _ 8440 8 (by decide +kernel)
theorem Check065.checked : Interval test 8320 8448 :=
  (FiniteChecks.interval_append test 8320 8384 8448
  (FiniteChecks.interval_append test 8320 8352 8384
  (FiniteChecks.interval_append test 8320 8336 8352
  (FiniteChecks.interval_append test 8320 8328 8336
  Check065.part8320
  Check065.part8328)
  (FiniteChecks.interval_append test 8336 8344 8352
  Check065.part8336
  Check065.part8344))
  (FiniteChecks.interval_append test 8352 8368 8384
  (FiniteChecks.interval_append test 8352 8360 8368
  Check065.part8352
  Check065.part8360)
  (FiniteChecks.interval_append test 8368 8376 8384
  Check065.part8368
  Check065.part8376)))
  (FiniteChecks.interval_append test 8384 8416 8448
  (FiniteChecks.interval_append test 8384 8400 8416
  (FiniteChecks.interval_append test 8384 8392 8400
  Check065.part8384
  Check065.part8392)
  (FiniteChecks.interval_append test 8400 8408 8416
  Check065.part8400
  Check065.part8408))
  (FiniteChecks.interval_append test 8416 8432 8448
  (FiniteChecks.interval_append test 8416 8424 8432
  Check065.part8416
  Check065.part8424)
  (FiniteChecks.interval_append test 8432 8440 8448
  Check065.part8432
  Check065.part8440))))
theorem Check066.part8448 : Interval test 8448 8456 :=
  interval_of_check _ 8448 8 (by decide +kernel)
theorem Check066.part8456 : Interval test 8456 8464 :=
  interval_of_check _ 8456 8 (by decide +kernel)
theorem Check066.part8464 : Interval test 8464 8472 :=
  interval_of_check _ 8464 8 (by decide +kernel)
theorem Check066.part8472 : Interval test 8472 8480 :=
  interval_of_check _ 8472 8 (by decide +kernel)
theorem Check066.part8480 : Interval test 8480 8488 :=
  interval_of_check _ 8480 8 (by decide +kernel)
theorem Check066.part8488 : Interval test 8488 8496 :=
  interval_of_check _ 8488 8 (by decide +kernel)
theorem Check066.part8496 : Interval test 8496 8504 :=
  interval_of_check _ 8496 8 (by decide +kernel)
theorem Check066.part8504 : Interval test 8504 8512 :=
  interval_of_check _ 8504 8 (by decide +kernel)
theorem Check066.part8512 : Interval test 8512 8520 :=
  interval_of_check _ 8512 8 (by decide +kernel)
theorem Check066.part8520 : Interval test 8520 8528 :=
  interval_of_check _ 8520 8 (by decide +kernel)
theorem Check066.part8528 : Interval test 8528 8536 :=
  interval_of_check _ 8528 8 (by decide +kernel)
theorem Check066.part8536 : Interval test 8536 8544 :=
  interval_of_check _ 8536 8 (by decide +kernel)
theorem Check066.part8544 : Interval test 8544 8552 :=
  interval_of_check _ 8544 8 (by decide +kernel)
theorem Check066.part8552 : Interval test 8552 8560 :=
  interval_of_check _ 8552 8 (by decide +kernel)
theorem Check066.part8560 : Interval test 8560 8568 :=
  interval_of_check _ 8560 8 (by decide +kernel)
theorem Check066.part8568 : Interval test 8568 8576 :=
  interval_of_check _ 8568 8 (by decide +kernel)
theorem Check066.checked : Interval test 8448 8576 :=
  (FiniteChecks.interval_append test 8448 8512 8576
  (FiniteChecks.interval_append test 8448 8480 8512
  (FiniteChecks.interval_append test 8448 8464 8480
  (FiniteChecks.interval_append test 8448 8456 8464
  Check066.part8448
  Check066.part8456)
  (FiniteChecks.interval_append test 8464 8472 8480
  Check066.part8464
  Check066.part8472))
  (FiniteChecks.interval_append test 8480 8496 8512
  (FiniteChecks.interval_append test 8480 8488 8496
  Check066.part8480
  Check066.part8488)
  (FiniteChecks.interval_append test 8496 8504 8512
  Check066.part8496
  Check066.part8504)))
  (FiniteChecks.interval_append test 8512 8544 8576
  (FiniteChecks.interval_append test 8512 8528 8544
  (FiniteChecks.interval_append test 8512 8520 8528
  Check066.part8512
  Check066.part8520)
  (FiniteChecks.interval_append test 8528 8536 8544
  Check066.part8528
  Check066.part8536))
  (FiniteChecks.interval_append test 8544 8560 8576
  (FiniteChecks.interval_append test 8544 8552 8560
  Check066.part8544
  Check066.part8552)
  (FiniteChecks.interval_append test 8560 8568 8576
  Check066.part8560
  Check066.part8568))))
theorem Check067.part8576 : Interval test 8576 8584 :=
  interval_of_check _ 8576 8 (by decide +kernel)
theorem Check067.part8584 : Interval test 8584 8592 :=
  interval_of_check _ 8584 8 (by decide +kernel)
theorem Check067.part8592 : Interval test 8592 8600 :=
  interval_of_check _ 8592 8 (by decide +kernel)
theorem Check067.part8600 : Interval test 8600 8608 :=
  interval_of_check _ 8600 8 (by decide +kernel)
theorem Check067.part8608 : Interval test 8608 8616 :=
  interval_of_check _ 8608 8 (by decide +kernel)
theorem Check067.part8616 : Interval test 8616 8624 :=
  interval_of_check _ 8616 8 (by decide +kernel)
theorem Check067.part8624 : Interval test 8624 8632 :=
  interval_of_check _ 8624 8 (by decide +kernel)
theorem Check067.part8632 : Interval test 8632 8640 :=
  interval_of_check _ 8632 8 (by decide +kernel)
theorem Check067.part8640 : Interval test 8640 8648 :=
  interval_of_check _ 8640 8 (by decide +kernel)
theorem Check067.part8648 : Interval test 8648 8656 :=
  interval_of_check _ 8648 8 (by decide +kernel)
theorem Check067.part8656 : Interval test 8656 8664 :=
  interval_of_check _ 8656 8 (by decide +kernel)
theorem Check067.part8664 : Interval test 8664 8672 :=
  interval_of_check _ 8664 8 (by decide +kernel)
theorem Check067.part8672 : Interval test 8672 8680 :=
  interval_of_check _ 8672 8 (by decide +kernel)
theorem Check067.part8680 : Interval test 8680 8688 :=
  interval_of_check _ 8680 8 (by decide +kernel)
theorem Check067.part8688 : Interval test 8688 8696 :=
  interval_of_check _ 8688 8 (by decide +kernel)
theorem Check067.part8696 : Interval test 8696 8704 :=
  interval_of_check _ 8696 8 (by decide +kernel)
theorem Check067.checked : Interval test 8576 8704 :=
  (FiniteChecks.interval_append test 8576 8640 8704
  (FiniteChecks.interval_append test 8576 8608 8640
  (FiniteChecks.interval_append test 8576 8592 8608
  (FiniteChecks.interval_append test 8576 8584 8592
  Check067.part8576
  Check067.part8584)
  (FiniteChecks.interval_append test 8592 8600 8608
  Check067.part8592
  Check067.part8600))
  (FiniteChecks.interval_append test 8608 8624 8640
  (FiniteChecks.interval_append test 8608 8616 8624
  Check067.part8608
  Check067.part8616)
  (FiniteChecks.interval_append test 8624 8632 8640
  Check067.part8624
  Check067.part8632)))
  (FiniteChecks.interval_append test 8640 8672 8704
  (FiniteChecks.interval_append test 8640 8656 8672
  (FiniteChecks.interval_append test 8640 8648 8656
  Check067.part8640
  Check067.part8648)
  (FiniteChecks.interval_append test 8656 8664 8672
  Check067.part8656
  Check067.part8664))
  (FiniteChecks.interval_append test 8672 8688 8704
  (FiniteChecks.interval_append test 8672 8680 8688
  Check067.part8672
  Check067.part8680)
  (FiniteChecks.interval_append test 8688 8696 8704
  Check067.part8688
  Check067.part8696))))
theorem Check068.part8704 : Interval test 8704 8712 :=
  interval_of_check _ 8704 8 (by decide +kernel)
theorem Check068.part8712 : Interval test 8712 8720 :=
  interval_of_check _ 8712 8 (by decide +kernel)
theorem Check068.part8720 : Interval test 8720 8728 :=
  interval_of_check _ 8720 8 (by decide +kernel)
theorem Check068.part8728 : Interval test 8728 8736 :=
  interval_of_check _ 8728 8 (by decide +kernel)
theorem Check068.part8736 : Interval test 8736 8744 :=
  interval_of_check _ 8736 8 (by decide +kernel)
theorem Check068.part8744 : Interval test 8744 8752 :=
  interval_of_check _ 8744 8 (by decide +kernel)
theorem Check068.part8752 : Interval test 8752 8760 :=
  interval_of_check _ 8752 8 (by decide +kernel)
theorem Check068.part8760 : Interval test 8760 8768 :=
  interval_of_check _ 8760 8 (by decide +kernel)
theorem Check068.part8768 : Interval test 8768 8776 :=
  interval_of_check _ 8768 8 (by decide +kernel)
theorem Check068.part8776 : Interval test 8776 8784 :=
  interval_of_check _ 8776 8 (by decide +kernel)
theorem Check068.part8784 : Interval test 8784 8792 :=
  interval_of_check _ 8784 8 (by decide +kernel)
theorem Check068.part8792 : Interval test 8792 8800 :=
  interval_of_check _ 8792 8 (by decide +kernel)
theorem Check068.part8800 : Interval test 8800 8808 :=
  interval_of_check _ 8800 8 (by decide +kernel)
theorem Check068.part8808 : Interval test 8808 8816 :=
  interval_of_check _ 8808 8 (by decide +kernel)
theorem Check068.part8816 : Interval test 8816 8824 :=
  interval_of_check _ 8816 8 (by decide +kernel)
theorem Check068.part8824 : Interval test 8824 8832 :=
  interval_of_check _ 8824 8 (by decide +kernel)
theorem Check068.checked : Interval test 8704 8832 :=
  (FiniteChecks.interval_append test 8704 8768 8832
  (FiniteChecks.interval_append test 8704 8736 8768
  (FiniteChecks.interval_append test 8704 8720 8736
  (FiniteChecks.interval_append test 8704 8712 8720
  Check068.part8704
  Check068.part8712)
  (FiniteChecks.interval_append test 8720 8728 8736
  Check068.part8720
  Check068.part8728))
  (FiniteChecks.interval_append test 8736 8752 8768
  (FiniteChecks.interval_append test 8736 8744 8752
  Check068.part8736
  Check068.part8744)
  (FiniteChecks.interval_append test 8752 8760 8768
  Check068.part8752
  Check068.part8760)))
  (FiniteChecks.interval_append test 8768 8800 8832
  (FiniteChecks.interval_append test 8768 8784 8800
  (FiniteChecks.interval_append test 8768 8776 8784
  Check068.part8768
  Check068.part8776)
  (FiniteChecks.interval_append test 8784 8792 8800
  Check068.part8784
  Check068.part8792))
  (FiniteChecks.interval_append test 8800 8816 8832
  (FiniteChecks.interval_append test 8800 8808 8816
  Check068.part8800
  Check068.part8808)
  (FiniteChecks.interval_append test 8816 8824 8832
  Check068.part8816
  Check068.part8824))))
theorem Check069.part8832 : Interval test 8832 8840 :=
  interval_of_check _ 8832 8 (by decide +kernel)
theorem Check069.part8840 : Interval test 8840 8848 :=
  interval_of_check _ 8840 8 (by decide +kernel)
theorem Check069.part8848 : Interval test 8848 8856 :=
  interval_of_check _ 8848 8 (by decide +kernel)
theorem Check069.part8856 : Interval test 8856 8864 :=
  interval_of_check _ 8856 8 (by decide +kernel)
theorem Check069.part8864 : Interval test 8864 8872 :=
  interval_of_check _ 8864 8 (by decide +kernel)
theorem Check069.part8872 : Interval test 8872 8880 :=
  interval_of_check _ 8872 8 (by decide +kernel)
theorem Check069.part8880 : Interval test 8880 8888 :=
  interval_of_check _ 8880 8 (by decide +kernel)
theorem Check069.part8888 : Interval test 8888 8896 :=
  interval_of_check _ 8888 8 (by decide +kernel)
theorem Check069.part8896 : Interval test 8896 8904 :=
  interval_of_check _ 8896 8 (by decide +kernel)
theorem Check069.part8904 : Interval test 8904 8912 :=
  interval_of_check _ 8904 8 (by decide +kernel)
theorem Check069.part8912 : Interval test 8912 8920 :=
  interval_of_check _ 8912 8 (by decide +kernel)
theorem Check069.part8920 : Interval test 8920 8928 :=
  interval_of_check _ 8920 8 (by decide +kernel)
theorem Check069.part8928 : Interval test 8928 8936 :=
  interval_of_check _ 8928 8 (by decide +kernel)
theorem Check069.part8936 : Interval test 8936 8944 :=
  interval_of_check _ 8936 8 (by decide +kernel)
theorem Check069.part8944 : Interval test 8944 8952 :=
  interval_of_check _ 8944 8 (by decide +kernel)
theorem Check069.part8952 : Interval test 8952 8960 :=
  interval_of_check _ 8952 8 (by decide +kernel)
theorem Check069.checked : Interval test 8832 8960 :=
  (FiniteChecks.interval_append test 8832 8896 8960
  (FiniteChecks.interval_append test 8832 8864 8896
  (FiniteChecks.interval_append test 8832 8848 8864
  (FiniteChecks.interval_append test 8832 8840 8848
  Check069.part8832
  Check069.part8840)
  (FiniteChecks.interval_append test 8848 8856 8864
  Check069.part8848
  Check069.part8856))
  (FiniteChecks.interval_append test 8864 8880 8896
  (FiniteChecks.interval_append test 8864 8872 8880
  Check069.part8864
  Check069.part8872)
  (FiniteChecks.interval_append test 8880 8888 8896
  Check069.part8880
  Check069.part8888)))
  (FiniteChecks.interval_append test 8896 8928 8960
  (FiniteChecks.interval_append test 8896 8912 8928
  (FiniteChecks.interval_append test 8896 8904 8912
  Check069.part8896
  Check069.part8904)
  (FiniteChecks.interval_append test 8912 8920 8928
  Check069.part8912
  Check069.part8920))
  (FiniteChecks.interval_append test 8928 8944 8960
  (FiniteChecks.interval_append test 8928 8936 8944
  Check069.part8928
  Check069.part8936)
  (FiniteChecks.interval_append test 8944 8952 8960
  Check069.part8944
  Check069.part8952))))
theorem Check070.part8960 : Interval test 8960 8968 :=
  interval_of_check _ 8960 8 (by decide +kernel)
theorem Check070.part8968 : Interval test 8968 8976 :=
  interval_of_check _ 8968 8 (by decide +kernel)
theorem Check070.part8976 : Interval test 8976 8984 :=
  interval_of_check _ 8976 8 (by decide +kernel)
theorem Check070.part8984 : Interval test 8984 8992 :=
  interval_of_check _ 8984 8 (by decide +kernel)
theorem Check070.part8992 : Interval test 8992 9000 :=
  interval_of_check _ 8992 8 (by decide +kernel)
theorem Check070.part9000 : Interval test 9000 9008 :=
  interval_of_check _ 9000 8 (by decide +kernel)
theorem Check070.part9008 : Interval test 9008 9016 :=
  interval_of_check _ 9008 8 (by decide +kernel)
theorem Check070.part9016 : Interval test 9016 9024 :=
  interval_of_check _ 9016 8 (by decide +kernel)
theorem Check070.part9024 : Interval test 9024 9032 :=
  interval_of_check _ 9024 8 (by decide +kernel)
theorem Check070.part9032 : Interval test 9032 9040 :=
  interval_of_check _ 9032 8 (by decide +kernel)
theorem Check070.part9040 : Interval test 9040 9048 :=
  interval_of_check _ 9040 8 (by decide +kernel)
theorem Check070.part9048 : Interval test 9048 9056 :=
  interval_of_check _ 9048 8 (by decide +kernel)
theorem Check070.part9056 : Interval test 9056 9064 :=
  interval_of_check _ 9056 8 (by decide +kernel)
theorem Check070.part9064 : Interval test 9064 9072 :=
  interval_of_check _ 9064 8 (by decide +kernel)
theorem Check070.part9072 : Interval test 9072 9080 :=
  interval_of_check _ 9072 8 (by decide +kernel)
theorem Check070.part9080 : Interval test 9080 9088 :=
  interval_of_check _ 9080 8 (by decide +kernel)
theorem Check070.checked : Interval test 8960 9088 :=
  (FiniteChecks.interval_append test 8960 9024 9088
  (FiniteChecks.interval_append test 8960 8992 9024
  (FiniteChecks.interval_append test 8960 8976 8992
  (FiniteChecks.interval_append test 8960 8968 8976
  Check070.part8960
  Check070.part8968)
  (FiniteChecks.interval_append test 8976 8984 8992
  Check070.part8976
  Check070.part8984))
  (FiniteChecks.interval_append test 8992 9008 9024
  (FiniteChecks.interval_append test 8992 9000 9008
  Check070.part8992
  Check070.part9000)
  (FiniteChecks.interval_append test 9008 9016 9024
  Check070.part9008
  Check070.part9016)))
  (FiniteChecks.interval_append test 9024 9056 9088
  (FiniteChecks.interval_append test 9024 9040 9056
  (FiniteChecks.interval_append test 9024 9032 9040
  Check070.part9024
  Check070.part9032)
  (FiniteChecks.interval_append test 9040 9048 9056
  Check070.part9040
  Check070.part9048))
  (FiniteChecks.interval_append test 9056 9072 9088
  (FiniteChecks.interval_append test 9056 9064 9072
  Check070.part9056
  Check070.part9064)
  (FiniteChecks.interval_append test 9072 9080 9088
  Check070.part9072
  Check070.part9080))))
theorem Check071.part9088 : Interval test 9088 9096 :=
  interval_of_check _ 9088 8 (by decide +kernel)
theorem Check071.part9096 : Interval test 9096 9104 :=
  interval_of_check _ 9096 8 (by decide +kernel)
theorem Check071.part9104 : Interval test 9104 9112 :=
  interval_of_check _ 9104 8 (by decide +kernel)
theorem Check071.part9112 : Interval test 9112 9120 :=
  interval_of_check _ 9112 8 (by decide +kernel)
theorem Check071.part9120 : Interval test 9120 9128 :=
  interval_of_check _ 9120 8 (by decide +kernel)
theorem Check071.part9128 : Interval test 9128 9136 :=
  interval_of_check _ 9128 8 (by decide +kernel)
theorem Check071.part9136 : Interval test 9136 9144 :=
  interval_of_check _ 9136 8 (by decide +kernel)
theorem Check071.part9144 : Interval test 9144 9152 :=
  interval_of_check _ 9144 8 (by decide +kernel)
theorem Check071.part9152 : Interval test 9152 9160 :=
  interval_of_check _ 9152 8 (by decide +kernel)
theorem Check071.part9160 : Interval test 9160 9168 :=
  interval_of_check _ 9160 8 (by decide +kernel)
theorem Check071.part9168 : Interval test 9168 9176 :=
  interval_of_check _ 9168 8 (by decide +kernel)
theorem Check071.part9176 : Interval test 9176 9184 :=
  interval_of_check _ 9176 8 (by decide +kernel)
theorem Check071.part9184 : Interval test 9184 9192 :=
  interval_of_check _ 9184 8 (by decide +kernel)
theorem Check071.part9192 : Interval test 9192 9200 :=
  interval_of_check _ 9192 8 (by decide +kernel)
theorem Check071.part9200 : Interval test 9200 9208 :=
  interval_of_check _ 9200 8 (by decide +kernel)
theorem Check071.part9208 : Interval test 9208 9216 :=
  interval_of_check _ 9208 8 (by decide +kernel)
theorem Check071.checked : Interval test 9088 9216 :=
  (FiniteChecks.interval_append test 9088 9152 9216
  (FiniteChecks.interval_append test 9088 9120 9152
  (FiniteChecks.interval_append test 9088 9104 9120
  (FiniteChecks.interval_append test 9088 9096 9104
  Check071.part9088
  Check071.part9096)
  (FiniteChecks.interval_append test 9104 9112 9120
  Check071.part9104
  Check071.part9112))
  (FiniteChecks.interval_append test 9120 9136 9152
  (FiniteChecks.interval_append test 9120 9128 9136
  Check071.part9120
  Check071.part9128)
  (FiniteChecks.interval_append test 9136 9144 9152
  Check071.part9136
  Check071.part9144)))
  (FiniteChecks.interval_append test 9152 9184 9216
  (FiniteChecks.interval_append test 9152 9168 9184
  (FiniteChecks.interval_append test 9152 9160 9168
  Check071.part9152
  Check071.part9160)
  (FiniteChecks.interval_append test 9168 9176 9184
  Check071.part9168
  Check071.part9176))
  (FiniteChecks.interval_append test 9184 9200 9216
  (FiniteChecks.interval_append test 9184 9192 9200
  Check071.part9184
  Check071.part9192)
  (FiniteChecks.interval_append test 9200 9208 9216
  Check071.part9200
  Check071.part9208))))
end Papers.RationalityTen.SharedTriangleCounts
