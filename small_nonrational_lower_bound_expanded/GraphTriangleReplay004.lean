module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check032.part4096 : Interval test 4096 4104 :=
  interval_of_check _ 4096 8 (by decide +kernel)
theorem Check032.part4104 : Interval test 4104 4112 :=
  interval_of_check _ 4104 8 (by decide +kernel)
theorem Check032.part4112 : Interval test 4112 4120 :=
  interval_of_check _ 4112 8 (by decide +kernel)
theorem Check032.part4120 : Interval test 4120 4128 :=
  interval_of_check _ 4120 8 (by decide +kernel)
theorem Check032.part4128 : Interval test 4128 4136 :=
  interval_of_check _ 4128 8 (by decide +kernel)
theorem Check032.part4136 : Interval test 4136 4144 :=
  interval_of_check _ 4136 8 (by decide +kernel)
theorem Check032.part4144 : Interval test 4144 4152 :=
  interval_of_check _ 4144 8 (by decide +kernel)
theorem Check032.part4152 : Interval test 4152 4160 :=
  interval_of_check _ 4152 8 (by decide +kernel)
theorem Check032.part4160 : Interval test 4160 4168 :=
  interval_of_check _ 4160 8 (by decide +kernel)
theorem Check032.part4168 : Interval test 4168 4176 :=
  interval_of_check _ 4168 8 (by decide +kernel)
theorem Check032.part4176 : Interval test 4176 4184 :=
  interval_of_check _ 4176 8 (by decide +kernel)
theorem Check032.part4184 : Interval test 4184 4192 :=
  interval_of_check _ 4184 8 (by decide +kernel)
theorem Check032.part4192 : Interval test 4192 4200 :=
  interval_of_check _ 4192 8 (by decide +kernel)
theorem Check032.part4200 : Interval test 4200 4208 :=
  interval_of_check _ 4200 8 (by decide +kernel)
theorem Check032.part4208 : Interval test 4208 4216 :=
  interval_of_check _ 4208 8 (by decide +kernel)
theorem Check032.part4216 : Interval test 4216 4224 :=
  interval_of_check _ 4216 8 (by decide +kernel)
theorem Check032.checked : Interval test 4096 4224 :=
  (FiniteChecks.interval_append test 4096 4160 4224
  (FiniteChecks.interval_append test 4096 4128 4160
  (FiniteChecks.interval_append test 4096 4112 4128
  (FiniteChecks.interval_append test 4096 4104 4112
  Check032.part4096
  Check032.part4104)
  (FiniteChecks.interval_append test 4112 4120 4128
  Check032.part4112
  Check032.part4120))
  (FiniteChecks.interval_append test 4128 4144 4160
  (FiniteChecks.interval_append test 4128 4136 4144
  Check032.part4128
  Check032.part4136)
  (FiniteChecks.interval_append test 4144 4152 4160
  Check032.part4144
  Check032.part4152)))
  (FiniteChecks.interval_append test 4160 4192 4224
  (FiniteChecks.interval_append test 4160 4176 4192
  (FiniteChecks.interval_append test 4160 4168 4176
  Check032.part4160
  Check032.part4168)
  (FiniteChecks.interval_append test 4176 4184 4192
  Check032.part4176
  Check032.part4184))
  (FiniteChecks.interval_append test 4192 4208 4224
  (FiniteChecks.interval_append test 4192 4200 4208
  Check032.part4192
  Check032.part4200)
  (FiniteChecks.interval_append test 4208 4216 4224
  Check032.part4208
  Check032.part4216))))
theorem Check033.part4224 : Interval test 4224 4232 :=
  interval_of_check _ 4224 8 (by decide +kernel)
theorem Check033.part4232 : Interval test 4232 4240 :=
  interval_of_check _ 4232 8 (by decide +kernel)
theorem Check033.part4240 : Interval test 4240 4248 :=
  interval_of_check _ 4240 8 (by decide +kernel)
theorem Check033.part4248 : Interval test 4248 4256 :=
  interval_of_check _ 4248 8 (by decide +kernel)
theorem Check033.part4256 : Interval test 4256 4264 :=
  interval_of_check _ 4256 8 (by decide +kernel)
theorem Check033.part4264 : Interval test 4264 4272 :=
  interval_of_check _ 4264 8 (by decide +kernel)
theorem Check033.part4272 : Interval test 4272 4280 :=
  interval_of_check _ 4272 8 (by decide +kernel)
theorem Check033.part4280 : Interval test 4280 4288 :=
  interval_of_check _ 4280 8 (by decide +kernel)
theorem Check033.part4288 : Interval test 4288 4296 :=
  interval_of_check _ 4288 8 (by decide +kernel)
theorem Check033.part4296 : Interval test 4296 4304 :=
  interval_of_check _ 4296 8 (by decide +kernel)
theorem Check033.part4304 : Interval test 4304 4312 :=
  interval_of_check _ 4304 8 (by decide +kernel)
theorem Check033.part4312 : Interval test 4312 4320 :=
  interval_of_check _ 4312 8 (by decide +kernel)
theorem Check033.part4320 : Interval test 4320 4328 :=
  interval_of_check _ 4320 8 (by decide +kernel)
theorem Check033.part4328 : Interval test 4328 4336 :=
  interval_of_check _ 4328 8 (by decide +kernel)
theorem Check033.part4336 : Interval test 4336 4344 :=
  interval_of_check _ 4336 8 (by decide +kernel)
theorem Check033.part4344 : Interval test 4344 4352 :=
  interval_of_check _ 4344 8 (by decide +kernel)
theorem Check033.checked : Interval test 4224 4352 :=
  (FiniteChecks.interval_append test 4224 4288 4352
  (FiniteChecks.interval_append test 4224 4256 4288
  (FiniteChecks.interval_append test 4224 4240 4256
  (FiniteChecks.interval_append test 4224 4232 4240
  Check033.part4224
  Check033.part4232)
  (FiniteChecks.interval_append test 4240 4248 4256
  Check033.part4240
  Check033.part4248))
  (FiniteChecks.interval_append test 4256 4272 4288
  (FiniteChecks.interval_append test 4256 4264 4272
  Check033.part4256
  Check033.part4264)
  (FiniteChecks.interval_append test 4272 4280 4288
  Check033.part4272
  Check033.part4280)))
  (FiniteChecks.interval_append test 4288 4320 4352
  (FiniteChecks.interval_append test 4288 4304 4320
  (FiniteChecks.interval_append test 4288 4296 4304
  Check033.part4288
  Check033.part4296)
  (FiniteChecks.interval_append test 4304 4312 4320
  Check033.part4304
  Check033.part4312))
  (FiniteChecks.interval_append test 4320 4336 4352
  (FiniteChecks.interval_append test 4320 4328 4336
  Check033.part4320
  Check033.part4328)
  (FiniteChecks.interval_append test 4336 4344 4352
  Check033.part4336
  Check033.part4344))))
theorem Check034.part4352 : Interval test 4352 4360 :=
  interval_of_check _ 4352 8 (by decide +kernel)
theorem Check034.part4360 : Interval test 4360 4368 :=
  interval_of_check _ 4360 8 (by decide +kernel)
theorem Check034.part4368 : Interval test 4368 4376 :=
  interval_of_check _ 4368 8 (by decide +kernel)
theorem Check034.part4376 : Interval test 4376 4384 :=
  interval_of_check _ 4376 8 (by decide +kernel)
theorem Check034.part4384 : Interval test 4384 4392 :=
  interval_of_check _ 4384 8 (by decide +kernel)
theorem Check034.part4392 : Interval test 4392 4400 :=
  interval_of_check _ 4392 8 (by decide +kernel)
theorem Check034.part4400 : Interval test 4400 4408 :=
  interval_of_check _ 4400 8 (by decide +kernel)
theorem Check034.part4408 : Interval test 4408 4416 :=
  interval_of_check _ 4408 8 (by decide +kernel)
theorem Check034.part4416 : Interval test 4416 4424 :=
  interval_of_check _ 4416 8 (by decide +kernel)
theorem Check034.part4424 : Interval test 4424 4432 :=
  interval_of_check _ 4424 8 (by decide +kernel)
theorem Check034.part4432 : Interval test 4432 4440 :=
  interval_of_check _ 4432 8 (by decide +kernel)
theorem Check034.part4440 : Interval test 4440 4448 :=
  interval_of_check _ 4440 8 (by decide +kernel)
theorem Check034.part4448 : Interval test 4448 4456 :=
  interval_of_check _ 4448 8 (by decide +kernel)
theorem Check034.part4456 : Interval test 4456 4464 :=
  interval_of_check _ 4456 8 (by decide +kernel)
theorem Check034.part4464 : Interval test 4464 4472 :=
  interval_of_check _ 4464 8 (by decide +kernel)
theorem Check034.part4472 : Interval test 4472 4480 :=
  interval_of_check _ 4472 8 (by decide +kernel)
theorem Check034.checked : Interval test 4352 4480 :=
  (FiniteChecks.interval_append test 4352 4416 4480
  (FiniteChecks.interval_append test 4352 4384 4416
  (FiniteChecks.interval_append test 4352 4368 4384
  (FiniteChecks.interval_append test 4352 4360 4368
  Check034.part4352
  Check034.part4360)
  (FiniteChecks.interval_append test 4368 4376 4384
  Check034.part4368
  Check034.part4376))
  (FiniteChecks.interval_append test 4384 4400 4416
  (FiniteChecks.interval_append test 4384 4392 4400
  Check034.part4384
  Check034.part4392)
  (FiniteChecks.interval_append test 4400 4408 4416
  Check034.part4400
  Check034.part4408)))
  (FiniteChecks.interval_append test 4416 4448 4480
  (FiniteChecks.interval_append test 4416 4432 4448
  (FiniteChecks.interval_append test 4416 4424 4432
  Check034.part4416
  Check034.part4424)
  (FiniteChecks.interval_append test 4432 4440 4448
  Check034.part4432
  Check034.part4440))
  (FiniteChecks.interval_append test 4448 4464 4480
  (FiniteChecks.interval_append test 4448 4456 4464
  Check034.part4448
  Check034.part4456)
  (FiniteChecks.interval_append test 4464 4472 4480
  Check034.part4464
  Check034.part4472))))
theorem Check035.part4480 : Interval test 4480 4488 :=
  interval_of_check _ 4480 8 (by decide +kernel)
theorem Check035.part4488 : Interval test 4488 4496 :=
  interval_of_check _ 4488 8 (by decide +kernel)
theorem Check035.part4496 : Interval test 4496 4504 :=
  interval_of_check _ 4496 8 (by decide +kernel)
theorem Check035.part4504 : Interval test 4504 4512 :=
  interval_of_check _ 4504 8 (by decide +kernel)
theorem Check035.part4512 : Interval test 4512 4520 :=
  interval_of_check _ 4512 8 (by decide +kernel)
theorem Check035.part4520 : Interval test 4520 4528 :=
  interval_of_check _ 4520 8 (by decide +kernel)
theorem Check035.part4528 : Interval test 4528 4536 :=
  interval_of_check _ 4528 8 (by decide +kernel)
theorem Check035.part4536 : Interval test 4536 4544 :=
  interval_of_check _ 4536 8 (by decide +kernel)
theorem Check035.part4544 : Interval test 4544 4552 :=
  interval_of_check _ 4544 8 (by decide +kernel)
theorem Check035.part4552 : Interval test 4552 4560 :=
  interval_of_check _ 4552 8 (by decide +kernel)
theorem Check035.part4560 : Interval test 4560 4568 :=
  interval_of_check _ 4560 8 (by decide +kernel)
theorem Check035.part4568 : Interval test 4568 4576 :=
  interval_of_check _ 4568 8 (by decide +kernel)
theorem Check035.part4576 : Interval test 4576 4584 :=
  interval_of_check _ 4576 8 (by decide +kernel)
theorem Check035.part4584 : Interval test 4584 4592 :=
  interval_of_check _ 4584 8 (by decide +kernel)
theorem Check035.part4592 : Interval test 4592 4600 :=
  interval_of_check _ 4592 8 (by decide +kernel)
theorem Check035.part4600 : Interval test 4600 4608 :=
  interval_of_check _ 4600 8 (by decide +kernel)
theorem Check035.checked : Interval test 4480 4608 :=
  (FiniteChecks.interval_append test 4480 4544 4608
  (FiniteChecks.interval_append test 4480 4512 4544
  (FiniteChecks.interval_append test 4480 4496 4512
  (FiniteChecks.interval_append test 4480 4488 4496
  Check035.part4480
  Check035.part4488)
  (FiniteChecks.interval_append test 4496 4504 4512
  Check035.part4496
  Check035.part4504))
  (FiniteChecks.interval_append test 4512 4528 4544
  (FiniteChecks.interval_append test 4512 4520 4528
  Check035.part4512
  Check035.part4520)
  (FiniteChecks.interval_append test 4528 4536 4544
  Check035.part4528
  Check035.part4536)))
  (FiniteChecks.interval_append test 4544 4576 4608
  (FiniteChecks.interval_append test 4544 4560 4576
  (FiniteChecks.interval_append test 4544 4552 4560
  Check035.part4544
  Check035.part4552)
  (FiniteChecks.interval_append test 4560 4568 4576
  Check035.part4560
  Check035.part4568))
  (FiniteChecks.interval_append test 4576 4592 4608
  (FiniteChecks.interval_append test 4576 4584 4592
  Check035.part4576
  Check035.part4584)
  (FiniteChecks.interval_append test 4592 4600 4608
  Check035.part4592
  Check035.part4600))))
theorem Check036.part4608 : Interval test 4608 4616 :=
  interval_of_check _ 4608 8 (by decide +kernel)
theorem Check036.part4616 : Interval test 4616 4624 :=
  interval_of_check _ 4616 8 (by decide +kernel)
theorem Check036.part4624 : Interval test 4624 4632 :=
  interval_of_check _ 4624 8 (by decide +kernel)
theorem Check036.part4632 : Interval test 4632 4640 :=
  interval_of_check _ 4632 8 (by decide +kernel)
theorem Check036.part4640 : Interval test 4640 4648 :=
  interval_of_check _ 4640 8 (by decide +kernel)
theorem Check036.part4648 : Interval test 4648 4656 :=
  interval_of_check _ 4648 8 (by decide +kernel)
theorem Check036.part4656 : Interval test 4656 4664 :=
  interval_of_check _ 4656 8 (by decide +kernel)
theorem Check036.part4664 : Interval test 4664 4672 :=
  interval_of_check _ 4664 8 (by decide +kernel)
theorem Check036.part4672 : Interval test 4672 4680 :=
  interval_of_check _ 4672 8 (by decide +kernel)
theorem Check036.part4680 : Interval test 4680 4688 :=
  interval_of_check _ 4680 8 (by decide +kernel)
theorem Check036.part4688 : Interval test 4688 4696 :=
  interval_of_check _ 4688 8 (by decide +kernel)
theorem Check036.part4696 : Interval test 4696 4704 :=
  interval_of_check _ 4696 8 (by decide +kernel)
theorem Check036.part4704 : Interval test 4704 4712 :=
  interval_of_check _ 4704 8 (by decide +kernel)
theorem Check036.part4712 : Interval test 4712 4720 :=
  interval_of_check _ 4712 8 (by decide +kernel)
theorem Check036.part4720 : Interval test 4720 4728 :=
  interval_of_check _ 4720 8 (by decide +kernel)
theorem Check036.part4728 : Interval test 4728 4736 :=
  interval_of_check _ 4728 8 (by decide +kernel)
theorem Check036.checked : Interval test 4608 4736 :=
  (FiniteChecks.interval_append test 4608 4672 4736
  (FiniteChecks.interval_append test 4608 4640 4672
  (FiniteChecks.interval_append test 4608 4624 4640
  (FiniteChecks.interval_append test 4608 4616 4624
  Check036.part4608
  Check036.part4616)
  (FiniteChecks.interval_append test 4624 4632 4640
  Check036.part4624
  Check036.part4632))
  (FiniteChecks.interval_append test 4640 4656 4672
  (FiniteChecks.interval_append test 4640 4648 4656
  Check036.part4640
  Check036.part4648)
  (FiniteChecks.interval_append test 4656 4664 4672
  Check036.part4656
  Check036.part4664)))
  (FiniteChecks.interval_append test 4672 4704 4736
  (FiniteChecks.interval_append test 4672 4688 4704
  (FiniteChecks.interval_append test 4672 4680 4688
  Check036.part4672
  Check036.part4680)
  (FiniteChecks.interval_append test 4688 4696 4704
  Check036.part4688
  Check036.part4696))
  (FiniteChecks.interval_append test 4704 4720 4736
  (FiniteChecks.interval_append test 4704 4712 4720
  Check036.part4704
  Check036.part4712)
  (FiniteChecks.interval_append test 4720 4728 4736
  Check036.part4720
  Check036.part4728))))
theorem Check037.part4736 : Interval test 4736 4744 :=
  interval_of_check _ 4736 8 (by decide +kernel)
theorem Check037.part4744 : Interval test 4744 4752 :=
  interval_of_check _ 4744 8 (by decide +kernel)
theorem Check037.part4752 : Interval test 4752 4760 :=
  interval_of_check _ 4752 8 (by decide +kernel)
theorem Check037.part4760 : Interval test 4760 4768 :=
  interval_of_check _ 4760 8 (by decide +kernel)
theorem Check037.part4768 : Interval test 4768 4776 :=
  interval_of_check _ 4768 8 (by decide +kernel)
theorem Check037.part4776 : Interval test 4776 4784 :=
  interval_of_check _ 4776 8 (by decide +kernel)
theorem Check037.part4784 : Interval test 4784 4792 :=
  interval_of_check _ 4784 8 (by decide +kernel)
theorem Check037.part4792 : Interval test 4792 4800 :=
  interval_of_check _ 4792 8 (by decide +kernel)
theorem Check037.part4800 : Interval test 4800 4808 :=
  interval_of_check _ 4800 8 (by decide +kernel)
theorem Check037.part4808 : Interval test 4808 4816 :=
  interval_of_check _ 4808 8 (by decide +kernel)
theorem Check037.part4816 : Interval test 4816 4824 :=
  interval_of_check _ 4816 8 (by decide +kernel)
theorem Check037.part4824 : Interval test 4824 4832 :=
  interval_of_check _ 4824 8 (by decide +kernel)
theorem Check037.part4832 : Interval test 4832 4840 :=
  interval_of_check _ 4832 8 (by decide +kernel)
theorem Check037.part4840 : Interval test 4840 4848 :=
  interval_of_check _ 4840 8 (by decide +kernel)
theorem Check037.part4848 : Interval test 4848 4856 :=
  interval_of_check _ 4848 8 (by decide +kernel)
theorem Check037.part4856 : Interval test 4856 4864 :=
  interval_of_check _ 4856 8 (by decide +kernel)
theorem Check037.checked : Interval test 4736 4864 :=
  (FiniteChecks.interval_append test 4736 4800 4864
  (FiniteChecks.interval_append test 4736 4768 4800
  (FiniteChecks.interval_append test 4736 4752 4768
  (FiniteChecks.interval_append test 4736 4744 4752
  Check037.part4736
  Check037.part4744)
  (FiniteChecks.interval_append test 4752 4760 4768
  Check037.part4752
  Check037.part4760))
  (FiniteChecks.interval_append test 4768 4784 4800
  (FiniteChecks.interval_append test 4768 4776 4784
  Check037.part4768
  Check037.part4776)
  (FiniteChecks.interval_append test 4784 4792 4800
  Check037.part4784
  Check037.part4792)))
  (FiniteChecks.interval_append test 4800 4832 4864
  (FiniteChecks.interval_append test 4800 4816 4832
  (FiniteChecks.interval_append test 4800 4808 4816
  Check037.part4800
  Check037.part4808)
  (FiniteChecks.interval_append test 4816 4824 4832
  Check037.part4816
  Check037.part4824))
  (FiniteChecks.interval_append test 4832 4848 4864
  (FiniteChecks.interval_append test 4832 4840 4848
  Check037.part4832
  Check037.part4840)
  (FiniteChecks.interval_append test 4848 4856 4864
  Check037.part4848
  Check037.part4856))))
theorem Check038.part4864 : Interval test 4864 4872 :=
  interval_of_check _ 4864 8 (by decide +kernel)
theorem Check038.part4872 : Interval test 4872 4880 :=
  interval_of_check _ 4872 8 (by decide +kernel)
theorem Check038.part4880 : Interval test 4880 4888 :=
  interval_of_check _ 4880 8 (by decide +kernel)
theorem Check038.part4888 : Interval test 4888 4896 :=
  interval_of_check _ 4888 8 (by decide +kernel)
theorem Check038.part4896 : Interval test 4896 4904 :=
  interval_of_check _ 4896 8 (by decide +kernel)
theorem Check038.part4904 : Interval test 4904 4912 :=
  interval_of_check _ 4904 8 (by decide +kernel)
theorem Check038.part4912 : Interval test 4912 4920 :=
  interval_of_check _ 4912 8 (by decide +kernel)
theorem Check038.part4920 : Interval test 4920 4928 :=
  interval_of_check _ 4920 8 (by decide +kernel)
theorem Check038.part4928 : Interval test 4928 4936 :=
  interval_of_check _ 4928 8 (by decide +kernel)
theorem Check038.part4936 : Interval test 4936 4944 :=
  interval_of_check _ 4936 8 (by decide +kernel)
theorem Check038.part4944 : Interval test 4944 4952 :=
  interval_of_check _ 4944 8 (by decide +kernel)
theorem Check038.part4952 : Interval test 4952 4960 :=
  interval_of_check _ 4952 8 (by decide +kernel)
theorem Check038.part4960 : Interval test 4960 4968 :=
  interval_of_check _ 4960 8 (by decide +kernel)
theorem Check038.part4968 : Interval test 4968 4976 :=
  interval_of_check _ 4968 8 (by decide +kernel)
theorem Check038.part4976 : Interval test 4976 4984 :=
  interval_of_check _ 4976 8 (by decide +kernel)
theorem Check038.part4984 : Interval test 4984 4992 :=
  interval_of_check _ 4984 8 (by decide +kernel)
theorem Check038.checked : Interval test 4864 4992 :=
  (FiniteChecks.interval_append test 4864 4928 4992
  (FiniteChecks.interval_append test 4864 4896 4928
  (FiniteChecks.interval_append test 4864 4880 4896
  (FiniteChecks.interval_append test 4864 4872 4880
  Check038.part4864
  Check038.part4872)
  (FiniteChecks.interval_append test 4880 4888 4896
  Check038.part4880
  Check038.part4888))
  (FiniteChecks.interval_append test 4896 4912 4928
  (FiniteChecks.interval_append test 4896 4904 4912
  Check038.part4896
  Check038.part4904)
  (FiniteChecks.interval_append test 4912 4920 4928
  Check038.part4912
  Check038.part4920)))
  (FiniteChecks.interval_append test 4928 4960 4992
  (FiniteChecks.interval_append test 4928 4944 4960
  (FiniteChecks.interval_append test 4928 4936 4944
  Check038.part4928
  Check038.part4936)
  (FiniteChecks.interval_append test 4944 4952 4960
  Check038.part4944
  Check038.part4952))
  (FiniteChecks.interval_append test 4960 4976 4992
  (FiniteChecks.interval_append test 4960 4968 4976
  Check038.part4960
  Check038.part4968)
  (FiniteChecks.interval_append test 4976 4984 4992
  Check038.part4976
  Check038.part4984))))
theorem Check039.part4992 : Interval test 4992 5000 :=
  interval_of_check _ 4992 8 (by decide +kernel)
theorem Check039.part5000 : Interval test 5000 5008 :=
  interval_of_check _ 5000 8 (by decide +kernel)
theorem Check039.part5008 : Interval test 5008 5016 :=
  interval_of_check _ 5008 8 (by decide +kernel)
theorem Check039.part5016 : Interval test 5016 5024 :=
  interval_of_check _ 5016 8 (by decide +kernel)
theorem Check039.part5024 : Interval test 5024 5032 :=
  interval_of_check _ 5024 8 (by decide +kernel)
theorem Check039.part5032 : Interval test 5032 5040 :=
  interval_of_check _ 5032 8 (by decide +kernel)
theorem Check039.part5040 : Interval test 5040 5048 :=
  interval_of_check _ 5040 8 (by decide +kernel)
theorem Check039.part5048 : Interval test 5048 5056 :=
  interval_of_check _ 5048 8 (by decide +kernel)
theorem Check039.part5056 : Interval test 5056 5064 :=
  interval_of_check _ 5056 8 (by decide +kernel)
theorem Check039.part5064 : Interval test 5064 5072 :=
  interval_of_check _ 5064 8 (by decide +kernel)
theorem Check039.part5072 : Interval test 5072 5080 :=
  interval_of_check _ 5072 8 (by decide +kernel)
theorem Check039.part5080 : Interval test 5080 5088 :=
  interval_of_check _ 5080 8 (by decide +kernel)
theorem Check039.part5088 : Interval test 5088 5096 :=
  interval_of_check _ 5088 8 (by decide +kernel)
theorem Check039.part5096 : Interval test 5096 5104 :=
  interval_of_check _ 5096 8 (by decide +kernel)
theorem Check039.part5104 : Interval test 5104 5112 :=
  interval_of_check _ 5104 8 (by decide +kernel)
theorem Check039.part5112 : Interval test 5112 5120 :=
  interval_of_check _ 5112 8 (by decide +kernel)
theorem Check039.checked : Interval test 4992 5120 :=
  (FiniteChecks.interval_append test 4992 5056 5120
  (FiniteChecks.interval_append test 4992 5024 5056
  (FiniteChecks.interval_append test 4992 5008 5024
  (FiniteChecks.interval_append test 4992 5000 5008
  Check039.part4992
  Check039.part5000)
  (FiniteChecks.interval_append test 5008 5016 5024
  Check039.part5008
  Check039.part5016))
  (FiniteChecks.interval_append test 5024 5040 5056
  (FiniteChecks.interval_append test 5024 5032 5040
  Check039.part5024
  Check039.part5032)
  (FiniteChecks.interval_append test 5040 5048 5056
  Check039.part5040
  Check039.part5048)))
  (FiniteChecks.interval_append test 5056 5088 5120
  (FiniteChecks.interval_append test 5056 5072 5088
  (FiniteChecks.interval_append test 5056 5064 5072
  Check039.part5056
  Check039.part5064)
  (FiniteChecks.interval_append test 5072 5080 5088
  Check039.part5072
  Check039.part5080))
  (FiniteChecks.interval_append test 5088 5104 5120
  (FiniteChecks.interval_append test 5088 5096 5104
  Check039.part5088
  Check039.part5096)
  (FiniteChecks.interval_append test 5104 5112 5120
  Check039.part5104
  Check039.part5112))))
end Papers.RationalityTen.SharedTriangleCounts
