module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check056.part7168 : Interval test 7168 7176 :=
  interval_of_check _ 7168 8 (by decide +kernel)
theorem Check056.part7176 : Interval test 7176 7184 :=
  interval_of_check _ 7176 8 (by decide +kernel)
theorem Check056.part7184 : Interval test 7184 7192 :=
  interval_of_check _ 7184 8 (by decide +kernel)
theorem Check056.part7192 : Interval test 7192 7200 :=
  interval_of_check _ 7192 8 (by decide +kernel)
theorem Check056.part7200 : Interval test 7200 7208 :=
  interval_of_check _ 7200 8 (by decide +kernel)
theorem Check056.part7208 : Interval test 7208 7216 :=
  interval_of_check _ 7208 8 (by decide +kernel)
theorem Check056.part7216 : Interval test 7216 7224 :=
  interval_of_check _ 7216 8 (by decide +kernel)
theorem Check056.part7224 : Interval test 7224 7232 :=
  interval_of_check _ 7224 8 (by decide +kernel)
theorem Check056.part7232 : Interval test 7232 7240 :=
  interval_of_check _ 7232 8 (by decide +kernel)
theorem Check056.part7240 : Interval test 7240 7248 :=
  interval_of_check _ 7240 8 (by decide +kernel)
theorem Check056.part7248 : Interval test 7248 7256 :=
  interval_of_check _ 7248 8 (by decide +kernel)
theorem Check056.part7256 : Interval test 7256 7264 :=
  interval_of_check _ 7256 8 (by decide +kernel)
theorem Check056.part7264 : Interval test 7264 7272 :=
  interval_of_check _ 7264 8 (by decide +kernel)
theorem Check056.part7272 : Interval test 7272 7280 :=
  interval_of_check _ 7272 8 (by decide +kernel)
theorem Check056.part7280 : Interval test 7280 7288 :=
  interval_of_check _ 7280 8 (by decide +kernel)
theorem Check056.part7288 : Interval test 7288 7296 :=
  interval_of_check _ 7288 8 (by decide +kernel)
theorem Check056.checked : Interval test 7168 7296 :=
  (FiniteChecks.interval_append test 7168 7232 7296
  (FiniteChecks.interval_append test 7168 7200 7232
  (FiniteChecks.interval_append test 7168 7184 7200
  (FiniteChecks.interval_append test 7168 7176 7184
  Check056.part7168
  Check056.part7176)
  (FiniteChecks.interval_append test 7184 7192 7200
  Check056.part7184
  Check056.part7192))
  (FiniteChecks.interval_append test 7200 7216 7232
  (FiniteChecks.interval_append test 7200 7208 7216
  Check056.part7200
  Check056.part7208)
  (FiniteChecks.interval_append test 7216 7224 7232
  Check056.part7216
  Check056.part7224)))
  (FiniteChecks.interval_append test 7232 7264 7296
  (FiniteChecks.interval_append test 7232 7248 7264
  (FiniteChecks.interval_append test 7232 7240 7248
  Check056.part7232
  Check056.part7240)
  (FiniteChecks.interval_append test 7248 7256 7264
  Check056.part7248
  Check056.part7256))
  (FiniteChecks.interval_append test 7264 7280 7296
  (FiniteChecks.interval_append test 7264 7272 7280
  Check056.part7264
  Check056.part7272)
  (FiniteChecks.interval_append test 7280 7288 7296
  Check056.part7280
  Check056.part7288))))
theorem Check057.part7296 : Interval test 7296 7304 :=
  interval_of_check _ 7296 8 (by decide +kernel)
theorem Check057.part7304 : Interval test 7304 7312 :=
  interval_of_check _ 7304 8 (by decide +kernel)
theorem Check057.part7312 : Interval test 7312 7320 :=
  interval_of_check _ 7312 8 (by decide +kernel)
theorem Check057.part7320 : Interval test 7320 7328 :=
  interval_of_check _ 7320 8 (by decide +kernel)
theorem Check057.part7328 : Interval test 7328 7336 :=
  interval_of_check _ 7328 8 (by decide +kernel)
theorem Check057.part7336 : Interval test 7336 7344 :=
  interval_of_check _ 7336 8 (by decide +kernel)
theorem Check057.part7344 : Interval test 7344 7352 :=
  interval_of_check _ 7344 8 (by decide +kernel)
theorem Check057.part7352 : Interval test 7352 7360 :=
  interval_of_check _ 7352 8 (by decide +kernel)
theorem Check057.part7360 : Interval test 7360 7368 :=
  interval_of_check _ 7360 8 (by decide +kernel)
theorem Check057.part7368 : Interval test 7368 7376 :=
  interval_of_check _ 7368 8 (by decide +kernel)
theorem Check057.part7376 : Interval test 7376 7384 :=
  interval_of_check _ 7376 8 (by decide +kernel)
theorem Check057.part7384 : Interval test 7384 7392 :=
  interval_of_check _ 7384 8 (by decide +kernel)
theorem Check057.part7392 : Interval test 7392 7400 :=
  interval_of_check _ 7392 8 (by decide +kernel)
theorem Check057.part7400 : Interval test 7400 7408 :=
  interval_of_check _ 7400 8 (by decide +kernel)
theorem Check057.part7408 : Interval test 7408 7416 :=
  interval_of_check _ 7408 8 (by decide +kernel)
theorem Check057.part7416 : Interval test 7416 7424 :=
  interval_of_check _ 7416 8 (by decide +kernel)
theorem Check057.checked : Interval test 7296 7424 :=
  (FiniteChecks.interval_append test 7296 7360 7424
  (FiniteChecks.interval_append test 7296 7328 7360
  (FiniteChecks.interval_append test 7296 7312 7328
  (FiniteChecks.interval_append test 7296 7304 7312
  Check057.part7296
  Check057.part7304)
  (FiniteChecks.interval_append test 7312 7320 7328
  Check057.part7312
  Check057.part7320))
  (FiniteChecks.interval_append test 7328 7344 7360
  (FiniteChecks.interval_append test 7328 7336 7344
  Check057.part7328
  Check057.part7336)
  (FiniteChecks.interval_append test 7344 7352 7360
  Check057.part7344
  Check057.part7352)))
  (FiniteChecks.interval_append test 7360 7392 7424
  (FiniteChecks.interval_append test 7360 7376 7392
  (FiniteChecks.interval_append test 7360 7368 7376
  Check057.part7360
  Check057.part7368)
  (FiniteChecks.interval_append test 7376 7384 7392
  Check057.part7376
  Check057.part7384))
  (FiniteChecks.interval_append test 7392 7408 7424
  (FiniteChecks.interval_append test 7392 7400 7408
  Check057.part7392
  Check057.part7400)
  (FiniteChecks.interval_append test 7408 7416 7424
  Check057.part7408
  Check057.part7416))))
theorem Check058.part7424 : Interval test 7424 7432 :=
  interval_of_check _ 7424 8 (by decide +kernel)
theorem Check058.part7432 : Interval test 7432 7440 :=
  interval_of_check _ 7432 8 (by decide +kernel)
theorem Check058.part7440 : Interval test 7440 7448 :=
  interval_of_check _ 7440 8 (by decide +kernel)
theorem Check058.part7448 : Interval test 7448 7456 :=
  interval_of_check _ 7448 8 (by decide +kernel)
theorem Check058.part7456 : Interval test 7456 7464 :=
  interval_of_check _ 7456 8 (by decide +kernel)
theorem Check058.part7464 : Interval test 7464 7472 :=
  interval_of_check _ 7464 8 (by decide +kernel)
theorem Check058.part7472 : Interval test 7472 7480 :=
  interval_of_check _ 7472 8 (by decide +kernel)
theorem Check058.part7480 : Interval test 7480 7488 :=
  interval_of_check _ 7480 8 (by decide +kernel)
theorem Check058.part7488 : Interval test 7488 7496 :=
  interval_of_check _ 7488 8 (by decide +kernel)
theorem Check058.part7496 : Interval test 7496 7504 :=
  interval_of_check _ 7496 8 (by decide +kernel)
theorem Check058.part7504 : Interval test 7504 7512 :=
  interval_of_check _ 7504 8 (by decide +kernel)
theorem Check058.part7512 : Interval test 7512 7520 :=
  interval_of_check _ 7512 8 (by decide +kernel)
theorem Check058.part7520 : Interval test 7520 7528 :=
  interval_of_check _ 7520 8 (by decide +kernel)
theorem Check058.part7528 : Interval test 7528 7536 :=
  interval_of_check _ 7528 8 (by decide +kernel)
theorem Check058.part7536 : Interval test 7536 7544 :=
  interval_of_check _ 7536 8 (by decide +kernel)
theorem Check058.part7544 : Interval test 7544 7552 :=
  interval_of_check _ 7544 8 (by decide +kernel)
theorem Check058.checked : Interval test 7424 7552 :=
  (FiniteChecks.interval_append test 7424 7488 7552
  (FiniteChecks.interval_append test 7424 7456 7488
  (FiniteChecks.interval_append test 7424 7440 7456
  (FiniteChecks.interval_append test 7424 7432 7440
  Check058.part7424
  Check058.part7432)
  (FiniteChecks.interval_append test 7440 7448 7456
  Check058.part7440
  Check058.part7448))
  (FiniteChecks.interval_append test 7456 7472 7488
  (FiniteChecks.interval_append test 7456 7464 7472
  Check058.part7456
  Check058.part7464)
  (FiniteChecks.interval_append test 7472 7480 7488
  Check058.part7472
  Check058.part7480)))
  (FiniteChecks.interval_append test 7488 7520 7552
  (FiniteChecks.interval_append test 7488 7504 7520
  (FiniteChecks.interval_append test 7488 7496 7504
  Check058.part7488
  Check058.part7496)
  (FiniteChecks.interval_append test 7504 7512 7520
  Check058.part7504
  Check058.part7512))
  (FiniteChecks.interval_append test 7520 7536 7552
  (FiniteChecks.interval_append test 7520 7528 7536
  Check058.part7520
  Check058.part7528)
  (FiniteChecks.interval_append test 7536 7544 7552
  Check058.part7536
  Check058.part7544))))
theorem Check059.part7552 : Interval test 7552 7560 :=
  interval_of_check _ 7552 8 (by decide +kernel)
theorem Check059.part7560 : Interval test 7560 7568 :=
  interval_of_check _ 7560 8 (by decide +kernel)
theorem Check059.part7568 : Interval test 7568 7576 :=
  interval_of_check _ 7568 8 (by decide +kernel)
theorem Check059.part7576 : Interval test 7576 7584 :=
  interval_of_check _ 7576 8 (by decide +kernel)
theorem Check059.part7584 : Interval test 7584 7592 :=
  interval_of_check _ 7584 8 (by decide +kernel)
theorem Check059.part7592 : Interval test 7592 7600 :=
  interval_of_check _ 7592 8 (by decide +kernel)
theorem Check059.part7600 : Interval test 7600 7608 :=
  interval_of_check _ 7600 8 (by decide +kernel)
theorem Check059.part7608 : Interval test 7608 7616 :=
  interval_of_check _ 7608 8 (by decide +kernel)
theorem Check059.part7616 : Interval test 7616 7624 :=
  interval_of_check _ 7616 8 (by decide +kernel)
theorem Check059.part7624 : Interval test 7624 7632 :=
  interval_of_check _ 7624 8 (by decide +kernel)
theorem Check059.part7632 : Interval test 7632 7640 :=
  interval_of_check _ 7632 8 (by decide +kernel)
theorem Check059.part7640 : Interval test 7640 7648 :=
  interval_of_check _ 7640 8 (by decide +kernel)
theorem Check059.part7648 : Interval test 7648 7656 :=
  interval_of_check _ 7648 8 (by decide +kernel)
theorem Check059.part7656 : Interval test 7656 7664 :=
  interval_of_check _ 7656 8 (by decide +kernel)
theorem Check059.part7664 : Interval test 7664 7672 :=
  interval_of_check _ 7664 8 (by decide +kernel)
theorem Check059.part7672 : Interval test 7672 7680 :=
  interval_of_check _ 7672 8 (by decide +kernel)
theorem Check059.checked : Interval test 7552 7680 :=
  (FiniteChecks.interval_append test 7552 7616 7680
  (FiniteChecks.interval_append test 7552 7584 7616
  (FiniteChecks.interval_append test 7552 7568 7584
  (FiniteChecks.interval_append test 7552 7560 7568
  Check059.part7552
  Check059.part7560)
  (FiniteChecks.interval_append test 7568 7576 7584
  Check059.part7568
  Check059.part7576))
  (FiniteChecks.interval_append test 7584 7600 7616
  (FiniteChecks.interval_append test 7584 7592 7600
  Check059.part7584
  Check059.part7592)
  (FiniteChecks.interval_append test 7600 7608 7616
  Check059.part7600
  Check059.part7608)))
  (FiniteChecks.interval_append test 7616 7648 7680
  (FiniteChecks.interval_append test 7616 7632 7648
  (FiniteChecks.interval_append test 7616 7624 7632
  Check059.part7616
  Check059.part7624)
  (FiniteChecks.interval_append test 7632 7640 7648
  Check059.part7632
  Check059.part7640))
  (FiniteChecks.interval_append test 7648 7664 7680
  (FiniteChecks.interval_append test 7648 7656 7664
  Check059.part7648
  Check059.part7656)
  (FiniteChecks.interval_append test 7664 7672 7680
  Check059.part7664
  Check059.part7672))))
theorem Check060.part7680 : Interval test 7680 7688 :=
  interval_of_check _ 7680 8 (by decide +kernel)
theorem Check060.part7688 : Interval test 7688 7696 :=
  interval_of_check _ 7688 8 (by decide +kernel)
theorem Check060.part7696 : Interval test 7696 7704 :=
  interval_of_check _ 7696 8 (by decide +kernel)
theorem Check060.part7704 : Interval test 7704 7712 :=
  interval_of_check _ 7704 8 (by decide +kernel)
theorem Check060.part7712 : Interval test 7712 7720 :=
  interval_of_check _ 7712 8 (by decide +kernel)
theorem Check060.part7720 : Interval test 7720 7728 :=
  interval_of_check _ 7720 8 (by decide +kernel)
theorem Check060.part7728 : Interval test 7728 7736 :=
  interval_of_check _ 7728 8 (by decide +kernel)
theorem Check060.part7736 : Interval test 7736 7744 :=
  interval_of_check _ 7736 8 (by decide +kernel)
theorem Check060.part7744 : Interval test 7744 7752 :=
  interval_of_check _ 7744 8 (by decide +kernel)
theorem Check060.part7752 : Interval test 7752 7760 :=
  interval_of_check _ 7752 8 (by decide +kernel)
theorem Check060.part7760 : Interval test 7760 7768 :=
  interval_of_check _ 7760 8 (by decide +kernel)
theorem Check060.part7768 : Interval test 7768 7776 :=
  interval_of_check _ 7768 8 (by decide +kernel)
theorem Check060.part7776 : Interval test 7776 7784 :=
  interval_of_check _ 7776 8 (by decide +kernel)
theorem Check060.part7784 : Interval test 7784 7792 :=
  interval_of_check _ 7784 8 (by decide +kernel)
theorem Check060.part7792 : Interval test 7792 7800 :=
  interval_of_check _ 7792 8 (by decide +kernel)
theorem Check060.part7800 : Interval test 7800 7808 :=
  interval_of_check _ 7800 8 (by decide +kernel)
theorem Check060.checked : Interval test 7680 7808 :=
  (FiniteChecks.interval_append test 7680 7744 7808
  (FiniteChecks.interval_append test 7680 7712 7744
  (FiniteChecks.interval_append test 7680 7696 7712
  (FiniteChecks.interval_append test 7680 7688 7696
  Check060.part7680
  Check060.part7688)
  (FiniteChecks.interval_append test 7696 7704 7712
  Check060.part7696
  Check060.part7704))
  (FiniteChecks.interval_append test 7712 7728 7744
  (FiniteChecks.interval_append test 7712 7720 7728
  Check060.part7712
  Check060.part7720)
  (FiniteChecks.interval_append test 7728 7736 7744
  Check060.part7728
  Check060.part7736)))
  (FiniteChecks.interval_append test 7744 7776 7808
  (FiniteChecks.interval_append test 7744 7760 7776
  (FiniteChecks.interval_append test 7744 7752 7760
  Check060.part7744
  Check060.part7752)
  (FiniteChecks.interval_append test 7760 7768 7776
  Check060.part7760
  Check060.part7768))
  (FiniteChecks.interval_append test 7776 7792 7808
  (FiniteChecks.interval_append test 7776 7784 7792
  Check060.part7776
  Check060.part7784)
  (FiniteChecks.interval_append test 7792 7800 7808
  Check060.part7792
  Check060.part7800))))
theorem Check061.part7808 : Interval test 7808 7816 :=
  interval_of_check _ 7808 8 (by decide +kernel)
theorem Check061.part7816 : Interval test 7816 7824 :=
  interval_of_check _ 7816 8 (by decide +kernel)
theorem Check061.part7824 : Interval test 7824 7832 :=
  interval_of_check _ 7824 8 (by decide +kernel)
theorem Check061.part7832 : Interval test 7832 7840 :=
  interval_of_check _ 7832 8 (by decide +kernel)
theorem Check061.part7840 : Interval test 7840 7848 :=
  interval_of_check _ 7840 8 (by decide +kernel)
theorem Check061.part7848 : Interval test 7848 7856 :=
  interval_of_check _ 7848 8 (by decide +kernel)
theorem Check061.part7856 : Interval test 7856 7864 :=
  interval_of_check _ 7856 8 (by decide +kernel)
theorem Check061.part7864 : Interval test 7864 7872 :=
  interval_of_check _ 7864 8 (by decide +kernel)
theorem Check061.part7872 : Interval test 7872 7880 :=
  interval_of_check _ 7872 8 (by decide +kernel)
theorem Check061.part7880 : Interval test 7880 7888 :=
  interval_of_check _ 7880 8 (by decide +kernel)
theorem Check061.part7888 : Interval test 7888 7896 :=
  interval_of_check _ 7888 8 (by decide +kernel)
theorem Check061.part7896 : Interval test 7896 7904 :=
  interval_of_check _ 7896 8 (by decide +kernel)
theorem Check061.part7904 : Interval test 7904 7912 :=
  interval_of_check _ 7904 8 (by decide +kernel)
theorem Check061.part7912 : Interval test 7912 7920 :=
  interval_of_check _ 7912 8 (by decide +kernel)
theorem Check061.part7920 : Interval test 7920 7928 :=
  interval_of_check _ 7920 8 (by decide +kernel)
theorem Check061.part7928 : Interval test 7928 7936 :=
  interval_of_check _ 7928 8 (by decide +kernel)
theorem Check061.checked : Interval test 7808 7936 :=
  (FiniteChecks.interval_append test 7808 7872 7936
  (FiniteChecks.interval_append test 7808 7840 7872
  (FiniteChecks.interval_append test 7808 7824 7840
  (FiniteChecks.interval_append test 7808 7816 7824
  Check061.part7808
  Check061.part7816)
  (FiniteChecks.interval_append test 7824 7832 7840
  Check061.part7824
  Check061.part7832))
  (FiniteChecks.interval_append test 7840 7856 7872
  (FiniteChecks.interval_append test 7840 7848 7856
  Check061.part7840
  Check061.part7848)
  (FiniteChecks.interval_append test 7856 7864 7872
  Check061.part7856
  Check061.part7864)))
  (FiniteChecks.interval_append test 7872 7904 7936
  (FiniteChecks.interval_append test 7872 7888 7904
  (FiniteChecks.interval_append test 7872 7880 7888
  Check061.part7872
  Check061.part7880)
  (FiniteChecks.interval_append test 7888 7896 7904
  Check061.part7888
  Check061.part7896))
  (FiniteChecks.interval_append test 7904 7920 7936
  (FiniteChecks.interval_append test 7904 7912 7920
  Check061.part7904
  Check061.part7912)
  (FiniteChecks.interval_append test 7920 7928 7936
  Check061.part7920
  Check061.part7928))))
theorem Check062.part7936 : Interval test 7936 7944 :=
  interval_of_check _ 7936 8 (by decide +kernel)
theorem Check062.part7944 : Interval test 7944 7952 :=
  interval_of_check _ 7944 8 (by decide +kernel)
theorem Check062.part7952 : Interval test 7952 7960 :=
  interval_of_check _ 7952 8 (by decide +kernel)
theorem Check062.part7960 : Interval test 7960 7968 :=
  interval_of_check _ 7960 8 (by decide +kernel)
theorem Check062.part7968 : Interval test 7968 7976 :=
  interval_of_check _ 7968 8 (by decide +kernel)
theorem Check062.part7976 : Interval test 7976 7984 :=
  interval_of_check _ 7976 8 (by decide +kernel)
theorem Check062.part7984 : Interval test 7984 7992 :=
  interval_of_check _ 7984 8 (by decide +kernel)
theorem Check062.part7992 : Interval test 7992 8000 :=
  interval_of_check _ 7992 8 (by decide +kernel)
theorem Check062.part8000 : Interval test 8000 8008 :=
  interval_of_check _ 8000 8 (by decide +kernel)
theorem Check062.part8008 : Interval test 8008 8016 :=
  interval_of_check _ 8008 8 (by decide +kernel)
theorem Check062.part8016 : Interval test 8016 8024 :=
  interval_of_check _ 8016 8 (by decide +kernel)
theorem Check062.part8024 : Interval test 8024 8032 :=
  interval_of_check _ 8024 8 (by decide +kernel)
theorem Check062.part8032 : Interval test 8032 8040 :=
  interval_of_check _ 8032 8 (by decide +kernel)
theorem Check062.part8040 : Interval test 8040 8048 :=
  interval_of_check _ 8040 8 (by decide +kernel)
theorem Check062.part8048 : Interval test 8048 8056 :=
  interval_of_check _ 8048 8 (by decide +kernel)
theorem Check062.part8056 : Interval test 8056 8064 :=
  interval_of_check _ 8056 8 (by decide +kernel)
theorem Check062.checked : Interval test 7936 8064 :=
  (FiniteChecks.interval_append test 7936 8000 8064
  (FiniteChecks.interval_append test 7936 7968 8000
  (FiniteChecks.interval_append test 7936 7952 7968
  (FiniteChecks.interval_append test 7936 7944 7952
  Check062.part7936
  Check062.part7944)
  (FiniteChecks.interval_append test 7952 7960 7968
  Check062.part7952
  Check062.part7960))
  (FiniteChecks.interval_append test 7968 7984 8000
  (FiniteChecks.interval_append test 7968 7976 7984
  Check062.part7968
  Check062.part7976)
  (FiniteChecks.interval_append test 7984 7992 8000
  Check062.part7984
  Check062.part7992)))
  (FiniteChecks.interval_append test 8000 8032 8064
  (FiniteChecks.interval_append test 8000 8016 8032
  (FiniteChecks.interval_append test 8000 8008 8016
  Check062.part8000
  Check062.part8008)
  (FiniteChecks.interval_append test 8016 8024 8032
  Check062.part8016
  Check062.part8024))
  (FiniteChecks.interval_append test 8032 8048 8064
  (FiniteChecks.interval_append test 8032 8040 8048
  Check062.part8032
  Check062.part8040)
  (FiniteChecks.interval_append test 8048 8056 8064
  Check062.part8048
  Check062.part8056))))
theorem Check063.part8064 : Interval test 8064 8072 :=
  interval_of_check _ 8064 8 (by decide +kernel)
theorem Check063.part8072 : Interval test 8072 8080 :=
  interval_of_check _ 8072 8 (by decide +kernel)
theorem Check063.part8080 : Interval test 8080 8088 :=
  interval_of_check _ 8080 8 (by decide +kernel)
theorem Check063.part8088 : Interval test 8088 8096 :=
  interval_of_check _ 8088 8 (by decide +kernel)
theorem Check063.part8096 : Interval test 8096 8104 :=
  interval_of_check _ 8096 8 (by decide +kernel)
theorem Check063.part8104 : Interval test 8104 8112 :=
  interval_of_check _ 8104 8 (by decide +kernel)
theorem Check063.part8112 : Interval test 8112 8120 :=
  interval_of_check _ 8112 8 (by decide +kernel)
theorem Check063.part8120 : Interval test 8120 8128 :=
  interval_of_check _ 8120 8 (by decide +kernel)
theorem Check063.part8128 : Interval test 8128 8136 :=
  interval_of_check _ 8128 8 (by decide +kernel)
theorem Check063.part8136 : Interval test 8136 8144 :=
  interval_of_check _ 8136 8 (by decide +kernel)
theorem Check063.part8144 : Interval test 8144 8152 :=
  interval_of_check _ 8144 8 (by decide +kernel)
theorem Check063.part8152 : Interval test 8152 8160 :=
  interval_of_check _ 8152 8 (by decide +kernel)
theorem Check063.part8160 : Interval test 8160 8168 :=
  interval_of_check _ 8160 8 (by decide +kernel)
theorem Check063.part8168 : Interval test 8168 8176 :=
  interval_of_check _ 8168 8 (by decide +kernel)
theorem Check063.part8176 : Interval test 8176 8184 :=
  interval_of_check _ 8176 8 (by decide +kernel)
theorem Check063.part8184 : Interval test 8184 8192 :=
  interval_of_check _ 8184 8 (by decide +kernel)
theorem Check063.checked : Interval test 8064 8192 :=
  (FiniteChecks.interval_append test 8064 8128 8192
  (FiniteChecks.interval_append test 8064 8096 8128
  (FiniteChecks.interval_append test 8064 8080 8096
  (FiniteChecks.interval_append test 8064 8072 8080
  Check063.part8064
  Check063.part8072)
  (FiniteChecks.interval_append test 8080 8088 8096
  Check063.part8080
  Check063.part8088))
  (FiniteChecks.interval_append test 8096 8112 8128
  (FiniteChecks.interval_append test 8096 8104 8112
  Check063.part8096
  Check063.part8104)
  (FiniteChecks.interval_append test 8112 8120 8128
  Check063.part8112
  Check063.part8120)))
  (FiniteChecks.interval_append test 8128 8160 8192
  (FiniteChecks.interval_append test 8128 8144 8160
  (FiniteChecks.interval_append test 8128 8136 8144
  Check063.part8128
  Check063.part8136)
  (FiniteChecks.interval_append test 8144 8152 8160
  Check063.part8144
  Check063.part8152))
  (FiniteChecks.interval_append test 8160 8176 8192
  (FiniteChecks.interval_append test 8160 8168 8176
  Check063.part8160
  Check063.part8168)
  (FiniteChecks.interval_append test 8176 8184 8192
  Check063.part8176
  Check063.part8184))))
end Papers.RationalityTen.SharedTriangleCounts
