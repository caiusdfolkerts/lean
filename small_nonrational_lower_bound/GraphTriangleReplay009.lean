module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check072.part9216 : Interval test 9216 9224 :=
  interval_of_check _ 9216 8 (by decide +kernel)
theorem Check072.part9224 : Interval test 9224 9232 :=
  interval_of_check _ 9224 8 (by decide +kernel)
theorem Check072.part9232 : Interval test 9232 9240 :=
  interval_of_check _ 9232 8 (by decide +kernel)
theorem Check072.part9240 : Interval test 9240 9248 :=
  interval_of_check _ 9240 8 (by decide +kernel)
theorem Check072.part9248 : Interval test 9248 9256 :=
  interval_of_check _ 9248 8 (by decide +kernel)
theorem Check072.part9256 : Interval test 9256 9264 :=
  interval_of_check _ 9256 8 (by decide +kernel)
theorem Check072.part9264 : Interval test 9264 9272 :=
  interval_of_check _ 9264 8 (by decide +kernel)
theorem Check072.part9272 : Interval test 9272 9280 :=
  interval_of_check _ 9272 8 (by decide +kernel)
theorem Check072.part9280 : Interval test 9280 9288 :=
  interval_of_check _ 9280 8 (by decide +kernel)
theorem Check072.part9288 : Interval test 9288 9296 :=
  interval_of_check _ 9288 8 (by decide +kernel)
theorem Check072.part9296 : Interval test 9296 9304 :=
  interval_of_check _ 9296 8 (by decide +kernel)
theorem Check072.part9304 : Interval test 9304 9312 :=
  interval_of_check _ 9304 8 (by decide +kernel)
theorem Check072.part9312 : Interval test 9312 9320 :=
  interval_of_check _ 9312 8 (by decide +kernel)
theorem Check072.part9320 : Interval test 9320 9328 :=
  interval_of_check _ 9320 8 (by decide +kernel)
theorem Check072.part9328 : Interval test 9328 9336 :=
  interval_of_check _ 9328 8 (by decide +kernel)
theorem Check072.part9336 : Interval test 9336 9344 :=
  interval_of_check _ 9336 8 (by decide +kernel)
theorem Check072.checked : Interval test 9216 9344 :=
  (FiniteChecks.interval_append test 9216 9280 9344
  (FiniteChecks.interval_append test 9216 9248 9280
  (FiniteChecks.interval_append test 9216 9232 9248
  (FiniteChecks.interval_append test 9216 9224 9232
  Check072.part9216
  Check072.part9224)
  (FiniteChecks.interval_append test 9232 9240 9248
  Check072.part9232
  Check072.part9240))
  (FiniteChecks.interval_append test 9248 9264 9280
  (FiniteChecks.interval_append test 9248 9256 9264
  Check072.part9248
  Check072.part9256)
  (FiniteChecks.interval_append test 9264 9272 9280
  Check072.part9264
  Check072.part9272)))
  (FiniteChecks.interval_append test 9280 9312 9344
  (FiniteChecks.interval_append test 9280 9296 9312
  (FiniteChecks.interval_append test 9280 9288 9296
  Check072.part9280
  Check072.part9288)
  (FiniteChecks.interval_append test 9296 9304 9312
  Check072.part9296
  Check072.part9304))
  (FiniteChecks.interval_append test 9312 9328 9344
  (FiniteChecks.interval_append test 9312 9320 9328
  Check072.part9312
  Check072.part9320)
  (FiniteChecks.interval_append test 9328 9336 9344
  Check072.part9328
  Check072.part9336))))
theorem Check073.part9344 : Interval test 9344 9352 :=
  interval_of_check _ 9344 8 (by decide +kernel)
theorem Check073.part9352 : Interval test 9352 9360 :=
  interval_of_check _ 9352 8 (by decide +kernel)
theorem Check073.part9360 : Interval test 9360 9368 :=
  interval_of_check _ 9360 8 (by decide +kernel)
theorem Check073.part9368 : Interval test 9368 9376 :=
  interval_of_check _ 9368 8 (by decide +kernel)
theorem Check073.part9376 : Interval test 9376 9384 :=
  interval_of_check _ 9376 8 (by decide +kernel)
theorem Check073.part9384 : Interval test 9384 9392 :=
  interval_of_check _ 9384 8 (by decide +kernel)
theorem Check073.part9392 : Interval test 9392 9400 :=
  interval_of_check _ 9392 8 (by decide +kernel)
theorem Check073.part9400 : Interval test 9400 9408 :=
  interval_of_check _ 9400 8 (by decide +kernel)
theorem Check073.part9408 : Interval test 9408 9416 :=
  interval_of_check _ 9408 8 (by decide +kernel)
theorem Check073.part9416 : Interval test 9416 9424 :=
  interval_of_check _ 9416 8 (by decide +kernel)
theorem Check073.part9424 : Interval test 9424 9432 :=
  interval_of_check _ 9424 8 (by decide +kernel)
theorem Check073.part9432 : Interval test 9432 9440 :=
  interval_of_check _ 9432 8 (by decide +kernel)
theorem Check073.part9440 : Interval test 9440 9448 :=
  interval_of_check _ 9440 8 (by decide +kernel)
theorem Check073.part9448 : Interval test 9448 9456 :=
  interval_of_check _ 9448 8 (by decide +kernel)
theorem Check073.part9456 : Interval test 9456 9464 :=
  interval_of_check _ 9456 8 (by decide +kernel)
theorem Check073.part9464 : Interval test 9464 9472 :=
  interval_of_check _ 9464 8 (by decide +kernel)
theorem Check073.checked : Interval test 9344 9472 :=
  (FiniteChecks.interval_append test 9344 9408 9472
  (FiniteChecks.interval_append test 9344 9376 9408
  (FiniteChecks.interval_append test 9344 9360 9376
  (FiniteChecks.interval_append test 9344 9352 9360
  Check073.part9344
  Check073.part9352)
  (FiniteChecks.interval_append test 9360 9368 9376
  Check073.part9360
  Check073.part9368))
  (FiniteChecks.interval_append test 9376 9392 9408
  (FiniteChecks.interval_append test 9376 9384 9392
  Check073.part9376
  Check073.part9384)
  (FiniteChecks.interval_append test 9392 9400 9408
  Check073.part9392
  Check073.part9400)))
  (FiniteChecks.interval_append test 9408 9440 9472
  (FiniteChecks.interval_append test 9408 9424 9440
  (FiniteChecks.interval_append test 9408 9416 9424
  Check073.part9408
  Check073.part9416)
  (FiniteChecks.interval_append test 9424 9432 9440
  Check073.part9424
  Check073.part9432))
  (FiniteChecks.interval_append test 9440 9456 9472
  (FiniteChecks.interval_append test 9440 9448 9456
  Check073.part9440
  Check073.part9448)
  (FiniteChecks.interval_append test 9456 9464 9472
  Check073.part9456
  Check073.part9464))))
theorem Check074.part9472 : Interval test 9472 9480 :=
  interval_of_check _ 9472 8 (by decide +kernel)
theorem Check074.part9480 : Interval test 9480 9488 :=
  interval_of_check _ 9480 8 (by decide +kernel)
theorem Check074.part9488 : Interval test 9488 9496 :=
  interval_of_check _ 9488 8 (by decide +kernel)
theorem Check074.part9496 : Interval test 9496 9504 :=
  interval_of_check _ 9496 8 (by decide +kernel)
theorem Check074.part9504 : Interval test 9504 9512 :=
  interval_of_check _ 9504 8 (by decide +kernel)
theorem Check074.part9512 : Interval test 9512 9520 :=
  interval_of_check _ 9512 8 (by decide +kernel)
theorem Check074.part9520 : Interval test 9520 9528 :=
  interval_of_check _ 9520 8 (by decide +kernel)
theorem Check074.part9528 : Interval test 9528 9536 :=
  interval_of_check _ 9528 8 (by decide +kernel)
theorem Check074.part9536 : Interval test 9536 9544 :=
  interval_of_check _ 9536 8 (by decide +kernel)
theorem Check074.part9544 : Interval test 9544 9552 :=
  interval_of_check _ 9544 8 (by decide +kernel)
theorem Check074.part9552 : Interval test 9552 9560 :=
  interval_of_check _ 9552 8 (by decide +kernel)
theorem Check074.part9560 : Interval test 9560 9568 :=
  interval_of_check _ 9560 8 (by decide +kernel)
theorem Check074.part9568 : Interval test 9568 9576 :=
  interval_of_check _ 9568 8 (by decide +kernel)
theorem Check074.part9576 : Interval test 9576 9584 :=
  interval_of_check _ 9576 8 (by decide +kernel)
theorem Check074.part9584 : Interval test 9584 9592 :=
  interval_of_check _ 9584 8 (by decide +kernel)
theorem Check074.part9592 : Interval test 9592 9600 :=
  interval_of_check _ 9592 8 (by decide +kernel)
theorem Check074.checked : Interval test 9472 9600 :=
  (FiniteChecks.interval_append test 9472 9536 9600
  (FiniteChecks.interval_append test 9472 9504 9536
  (FiniteChecks.interval_append test 9472 9488 9504
  (FiniteChecks.interval_append test 9472 9480 9488
  Check074.part9472
  Check074.part9480)
  (FiniteChecks.interval_append test 9488 9496 9504
  Check074.part9488
  Check074.part9496))
  (FiniteChecks.interval_append test 9504 9520 9536
  (FiniteChecks.interval_append test 9504 9512 9520
  Check074.part9504
  Check074.part9512)
  (FiniteChecks.interval_append test 9520 9528 9536
  Check074.part9520
  Check074.part9528)))
  (FiniteChecks.interval_append test 9536 9568 9600
  (FiniteChecks.interval_append test 9536 9552 9568
  (FiniteChecks.interval_append test 9536 9544 9552
  Check074.part9536
  Check074.part9544)
  (FiniteChecks.interval_append test 9552 9560 9568
  Check074.part9552
  Check074.part9560))
  (FiniteChecks.interval_append test 9568 9584 9600
  (FiniteChecks.interval_append test 9568 9576 9584
  Check074.part9568
  Check074.part9576)
  (FiniteChecks.interval_append test 9584 9592 9600
  Check074.part9584
  Check074.part9592))))
theorem Check075.part9600 : Interval test 9600 9608 :=
  interval_of_check _ 9600 8 (by decide +kernel)
theorem Check075.part9608 : Interval test 9608 9616 :=
  interval_of_check _ 9608 8 (by decide +kernel)
theorem Check075.part9616 : Interval test 9616 9624 :=
  interval_of_check _ 9616 8 (by decide +kernel)
theorem Check075.part9624 : Interval test 9624 9632 :=
  interval_of_check _ 9624 8 (by decide +kernel)
theorem Check075.part9632 : Interval test 9632 9640 :=
  interval_of_check _ 9632 8 (by decide +kernel)
theorem Check075.part9640 : Interval test 9640 9648 :=
  interval_of_check _ 9640 8 (by decide +kernel)
theorem Check075.part9648 : Interval test 9648 9656 :=
  interval_of_check _ 9648 8 (by decide +kernel)
theorem Check075.part9656 : Interval test 9656 9664 :=
  interval_of_check _ 9656 8 (by decide +kernel)
theorem Check075.part9664 : Interval test 9664 9672 :=
  interval_of_check _ 9664 8 (by decide +kernel)
theorem Check075.part9672 : Interval test 9672 9680 :=
  interval_of_check _ 9672 8 (by decide +kernel)
theorem Check075.part9680 : Interval test 9680 9688 :=
  interval_of_check _ 9680 8 (by decide +kernel)
theorem Check075.part9688 : Interval test 9688 9696 :=
  interval_of_check _ 9688 8 (by decide +kernel)
theorem Check075.part9696 : Interval test 9696 9704 :=
  interval_of_check _ 9696 8 (by decide +kernel)
theorem Check075.part9704 : Interval test 9704 9712 :=
  interval_of_check _ 9704 8 (by decide +kernel)
theorem Check075.part9712 : Interval test 9712 9720 :=
  interval_of_check _ 9712 8 (by decide +kernel)
theorem Check075.part9720 : Interval test 9720 9728 :=
  interval_of_check _ 9720 8 (by decide +kernel)
theorem Check075.checked : Interval test 9600 9728 :=
  (FiniteChecks.interval_append test 9600 9664 9728
  (FiniteChecks.interval_append test 9600 9632 9664
  (FiniteChecks.interval_append test 9600 9616 9632
  (FiniteChecks.interval_append test 9600 9608 9616
  Check075.part9600
  Check075.part9608)
  (FiniteChecks.interval_append test 9616 9624 9632
  Check075.part9616
  Check075.part9624))
  (FiniteChecks.interval_append test 9632 9648 9664
  (FiniteChecks.interval_append test 9632 9640 9648
  Check075.part9632
  Check075.part9640)
  (FiniteChecks.interval_append test 9648 9656 9664
  Check075.part9648
  Check075.part9656)))
  (FiniteChecks.interval_append test 9664 9696 9728
  (FiniteChecks.interval_append test 9664 9680 9696
  (FiniteChecks.interval_append test 9664 9672 9680
  Check075.part9664
  Check075.part9672)
  (FiniteChecks.interval_append test 9680 9688 9696
  Check075.part9680
  Check075.part9688))
  (FiniteChecks.interval_append test 9696 9712 9728
  (FiniteChecks.interval_append test 9696 9704 9712
  Check075.part9696
  Check075.part9704)
  (FiniteChecks.interval_append test 9712 9720 9728
  Check075.part9712
  Check075.part9720))))
theorem Check076.part9728 : Interval test 9728 9736 :=
  interval_of_check _ 9728 8 (by decide +kernel)
theorem Check076.part9736 : Interval test 9736 9744 :=
  interval_of_check _ 9736 8 (by decide +kernel)
theorem Check076.part9744 : Interval test 9744 9752 :=
  interval_of_check _ 9744 8 (by decide +kernel)
theorem Check076.part9752 : Interval test 9752 9760 :=
  interval_of_check _ 9752 8 (by decide +kernel)
theorem Check076.part9760 : Interval test 9760 9768 :=
  interval_of_check _ 9760 8 (by decide +kernel)
theorem Check076.part9768 : Interval test 9768 9776 :=
  interval_of_check _ 9768 8 (by decide +kernel)
theorem Check076.part9776 : Interval test 9776 9784 :=
  interval_of_check _ 9776 8 (by decide +kernel)
theorem Check076.part9784 : Interval test 9784 9792 :=
  interval_of_check _ 9784 8 (by decide +kernel)
theorem Check076.part9792 : Interval test 9792 9800 :=
  interval_of_check _ 9792 8 (by decide +kernel)
theorem Check076.part9800 : Interval test 9800 9808 :=
  interval_of_check _ 9800 8 (by decide +kernel)
theorem Check076.part9808 : Interval test 9808 9816 :=
  interval_of_check _ 9808 8 (by decide +kernel)
theorem Check076.part9816 : Interval test 9816 9824 :=
  interval_of_check _ 9816 8 (by decide +kernel)
theorem Check076.part9824 : Interval test 9824 9832 :=
  interval_of_check _ 9824 8 (by decide +kernel)
theorem Check076.part9832 : Interval test 9832 9840 :=
  interval_of_check _ 9832 8 (by decide +kernel)
theorem Check076.part9840 : Interval test 9840 9848 :=
  interval_of_check _ 9840 8 (by decide +kernel)
theorem Check076.part9848 : Interval test 9848 9856 :=
  interval_of_check _ 9848 8 (by decide +kernel)
theorem Check076.checked : Interval test 9728 9856 :=
  (FiniteChecks.interval_append test 9728 9792 9856
  (FiniteChecks.interval_append test 9728 9760 9792
  (FiniteChecks.interval_append test 9728 9744 9760
  (FiniteChecks.interval_append test 9728 9736 9744
  Check076.part9728
  Check076.part9736)
  (FiniteChecks.interval_append test 9744 9752 9760
  Check076.part9744
  Check076.part9752))
  (FiniteChecks.interval_append test 9760 9776 9792
  (FiniteChecks.interval_append test 9760 9768 9776
  Check076.part9760
  Check076.part9768)
  (FiniteChecks.interval_append test 9776 9784 9792
  Check076.part9776
  Check076.part9784)))
  (FiniteChecks.interval_append test 9792 9824 9856
  (FiniteChecks.interval_append test 9792 9808 9824
  (FiniteChecks.interval_append test 9792 9800 9808
  Check076.part9792
  Check076.part9800)
  (FiniteChecks.interval_append test 9808 9816 9824
  Check076.part9808
  Check076.part9816))
  (FiniteChecks.interval_append test 9824 9840 9856
  (FiniteChecks.interval_append test 9824 9832 9840
  Check076.part9824
  Check076.part9832)
  (FiniteChecks.interval_append test 9840 9848 9856
  Check076.part9840
  Check076.part9848))))
theorem Check077.part9856 : Interval test 9856 9864 :=
  interval_of_check _ 9856 8 (by decide +kernel)
theorem Check077.part9864 : Interval test 9864 9872 :=
  interval_of_check _ 9864 8 (by decide +kernel)
theorem Check077.part9872 : Interval test 9872 9880 :=
  interval_of_check _ 9872 8 (by decide +kernel)
theorem Check077.part9880 : Interval test 9880 9888 :=
  interval_of_check _ 9880 8 (by decide +kernel)
theorem Check077.part9888 : Interval test 9888 9896 :=
  interval_of_check _ 9888 8 (by decide +kernel)
theorem Check077.part9896 : Interval test 9896 9904 :=
  interval_of_check _ 9896 8 (by decide +kernel)
theorem Check077.part9904 : Interval test 9904 9912 :=
  interval_of_check _ 9904 8 (by decide +kernel)
theorem Check077.part9912 : Interval test 9912 9920 :=
  interval_of_check _ 9912 8 (by decide +kernel)
theorem Check077.part9920 : Interval test 9920 9928 :=
  interval_of_check _ 9920 8 (by decide +kernel)
theorem Check077.part9928 : Interval test 9928 9936 :=
  interval_of_check _ 9928 8 (by decide +kernel)
theorem Check077.part9936 : Interval test 9936 9944 :=
  interval_of_check _ 9936 8 (by decide +kernel)
theorem Check077.part9944 : Interval test 9944 9952 :=
  interval_of_check _ 9944 8 (by decide +kernel)
theorem Check077.part9952 : Interval test 9952 9960 :=
  interval_of_check _ 9952 8 (by decide +kernel)
theorem Check077.part9960 : Interval test 9960 9968 :=
  interval_of_check _ 9960 8 (by decide +kernel)
theorem Check077.part9968 : Interval test 9968 9976 :=
  interval_of_check _ 9968 8 (by decide +kernel)
theorem Check077.part9976 : Interval test 9976 9984 :=
  interval_of_check _ 9976 8 (by decide +kernel)
theorem Check077.checked : Interval test 9856 9984 :=
  (FiniteChecks.interval_append test 9856 9920 9984
  (FiniteChecks.interval_append test 9856 9888 9920
  (FiniteChecks.interval_append test 9856 9872 9888
  (FiniteChecks.interval_append test 9856 9864 9872
  Check077.part9856
  Check077.part9864)
  (FiniteChecks.interval_append test 9872 9880 9888
  Check077.part9872
  Check077.part9880))
  (FiniteChecks.interval_append test 9888 9904 9920
  (FiniteChecks.interval_append test 9888 9896 9904
  Check077.part9888
  Check077.part9896)
  (FiniteChecks.interval_append test 9904 9912 9920
  Check077.part9904
  Check077.part9912)))
  (FiniteChecks.interval_append test 9920 9952 9984
  (FiniteChecks.interval_append test 9920 9936 9952
  (FiniteChecks.interval_append test 9920 9928 9936
  Check077.part9920
  Check077.part9928)
  (FiniteChecks.interval_append test 9936 9944 9952
  Check077.part9936
  Check077.part9944))
  (FiniteChecks.interval_append test 9952 9968 9984
  (FiniteChecks.interval_append test 9952 9960 9968
  Check077.part9952
  Check077.part9960)
  (FiniteChecks.interval_append test 9968 9976 9984
  Check077.part9968
  Check077.part9976))))
theorem Check078.part9984 : Interval test 9984 9992 :=
  interval_of_check _ 9984 8 (by decide +kernel)
theorem Check078.part9992 : Interval test 9992 10000 :=
  interval_of_check _ 9992 8 (by decide +kernel)
theorem Check078.part10000 : Interval test 10000 10008 :=
  interval_of_check _ 10000 8 (by decide +kernel)
theorem Check078.part10008 : Interval test 10008 10016 :=
  interval_of_check _ 10008 8 (by decide +kernel)
theorem Check078.part10016 : Interval test 10016 10024 :=
  interval_of_check _ 10016 8 (by decide +kernel)
theorem Check078.part10024 : Interval test 10024 10032 :=
  interval_of_check _ 10024 8 (by decide +kernel)
theorem Check078.part10032 : Interval test 10032 10040 :=
  interval_of_check _ 10032 8 (by decide +kernel)
theorem Check078.part10040 : Interval test 10040 10048 :=
  interval_of_check _ 10040 8 (by decide +kernel)
theorem Check078.part10048 : Interval test 10048 10056 :=
  interval_of_check _ 10048 8 (by decide +kernel)
theorem Check078.part10056 : Interval test 10056 10064 :=
  interval_of_check _ 10056 8 (by decide +kernel)
theorem Check078.part10064 : Interval test 10064 10072 :=
  interval_of_check _ 10064 8 (by decide +kernel)
theorem Check078.part10072 : Interval test 10072 10080 :=
  interval_of_check _ 10072 8 (by decide +kernel)
theorem Check078.part10080 : Interval test 10080 10088 :=
  interval_of_check _ 10080 8 (by decide +kernel)
theorem Check078.part10088 : Interval test 10088 10096 :=
  interval_of_check _ 10088 8 (by decide +kernel)
theorem Check078.part10096 : Interval test 10096 10104 :=
  interval_of_check _ 10096 8 (by decide +kernel)
theorem Check078.part10104 : Interval test 10104 10112 :=
  interval_of_check _ 10104 8 (by decide +kernel)
theorem Check078.checked : Interval test 9984 10112 :=
  (FiniteChecks.interval_append test 9984 10048 10112
  (FiniteChecks.interval_append test 9984 10016 10048
  (FiniteChecks.interval_append test 9984 10000 10016
  (FiniteChecks.interval_append test 9984 9992 10000
  Check078.part9984
  Check078.part9992)
  (FiniteChecks.interval_append test 10000 10008 10016
  Check078.part10000
  Check078.part10008))
  (FiniteChecks.interval_append test 10016 10032 10048
  (FiniteChecks.interval_append test 10016 10024 10032
  Check078.part10016
  Check078.part10024)
  (FiniteChecks.interval_append test 10032 10040 10048
  Check078.part10032
  Check078.part10040)))
  (FiniteChecks.interval_append test 10048 10080 10112
  (FiniteChecks.interval_append test 10048 10064 10080
  (FiniteChecks.interval_append test 10048 10056 10064
  Check078.part10048
  Check078.part10056)
  (FiniteChecks.interval_append test 10064 10072 10080
  Check078.part10064
  Check078.part10072))
  (FiniteChecks.interval_append test 10080 10096 10112
  (FiniteChecks.interval_append test 10080 10088 10096
  Check078.part10080
  Check078.part10088)
  (FiniteChecks.interval_append test 10096 10104 10112
  Check078.part10096
  Check078.part10104))))
theorem Check079.part10112 : Interval test 10112 10120 :=
  interval_of_check _ 10112 8 (by decide +kernel)
theorem Check079.part10120 : Interval test 10120 10128 :=
  interval_of_check _ 10120 8 (by decide +kernel)
theorem Check079.part10128 : Interval test 10128 10136 :=
  interval_of_check _ 10128 8 (by decide +kernel)
theorem Check079.part10136 : Interval test 10136 10144 :=
  interval_of_check _ 10136 8 (by decide +kernel)
theorem Check079.part10144 : Interval test 10144 10152 :=
  interval_of_check _ 10144 8 (by decide +kernel)
theorem Check079.part10152 : Interval test 10152 10160 :=
  interval_of_check _ 10152 8 (by decide +kernel)
theorem Check079.part10160 : Interval test 10160 10168 :=
  interval_of_check _ 10160 8 (by decide +kernel)
theorem Check079.part10168 : Interval test 10168 10176 :=
  interval_of_check _ 10168 8 (by decide +kernel)
theorem Check079.part10176 : Interval test 10176 10184 :=
  interval_of_check _ 10176 8 (by decide +kernel)
theorem Check079.part10184 : Interval test 10184 10192 :=
  interval_of_check _ 10184 8 (by decide +kernel)
theorem Check079.part10192 : Interval test 10192 10200 :=
  interval_of_check _ 10192 8 (by decide +kernel)
theorem Check079.part10200 : Interval test 10200 10208 :=
  interval_of_check _ 10200 8 (by decide +kernel)
theorem Check079.part10208 : Interval test 10208 10216 :=
  interval_of_check _ 10208 8 (by decide +kernel)
theorem Check079.part10216 : Interval test 10216 10224 :=
  interval_of_check _ 10216 8 (by decide +kernel)
theorem Check079.part10224 : Interval test 10224 10232 :=
  interval_of_check _ 10224 8 (by decide +kernel)
theorem Check079.part10232 : Interval test 10232 10240 :=
  interval_of_check _ 10232 8 (by decide +kernel)
theorem Check079.checked : Interval test 10112 10240 :=
  (FiniteChecks.interval_append test 10112 10176 10240
  (FiniteChecks.interval_append test 10112 10144 10176
  (FiniteChecks.interval_append test 10112 10128 10144
  (FiniteChecks.interval_append test 10112 10120 10128
  Check079.part10112
  Check079.part10120)
  (FiniteChecks.interval_append test 10128 10136 10144
  Check079.part10128
  Check079.part10136))
  (FiniteChecks.interval_append test 10144 10160 10176
  (FiniteChecks.interval_append test 10144 10152 10160
  Check079.part10144
  Check079.part10152)
  (FiniteChecks.interval_append test 10160 10168 10176
  Check079.part10160
  Check079.part10168)))
  (FiniteChecks.interval_append test 10176 10208 10240
  (FiniteChecks.interval_append test 10176 10192 10208
  (FiniteChecks.interval_append test 10176 10184 10192
  Check079.part10176
  Check079.part10184)
  (FiniteChecks.interval_append test 10192 10200 10208
  Check079.part10192
  Check079.part10200))
  (FiniteChecks.interval_append test 10208 10224 10240
  (FiniteChecks.interval_append test 10208 10216 10224
  Check079.part10208
  Check079.part10216)
  (FiniteChecks.interval_append test 10224 10232 10240
  Check079.part10224
  Check079.part10232))))
end Papers.RationalityTen.SharedTriangleCounts
