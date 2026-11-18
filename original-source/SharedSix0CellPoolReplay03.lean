module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check060.part7680 : Interval test 7680 7696 :=
  interval_of_check _ 7680 16 (by decide +kernel)
theorem Check060.part7696 : Interval test 7696 7712 :=
  interval_of_check _ 7696 16 (by decide +kernel)
theorem Check060.part7712 : Interval test 7712 7728 :=
  interval_of_check _ 7712 16 (by decide +kernel)
theorem Check060.part7728 : Interval test 7728 7744 :=
  interval_of_check _ 7728 16 (by decide +kernel)
theorem Check060.part7744 : Interval test 7744 7760 :=
  interval_of_check _ 7744 16 (by decide +kernel)
theorem Check060.part7760 : Interval test 7760 7776 :=
  interval_of_check _ 7760 16 (by decide +kernel)
theorem Check060.part7776 : Interval test 7776 7792 :=
  interval_of_check _ 7776 16 (by decide +kernel)
theorem Check060.part7792 : Interval test 7792 7808 :=
  interval_of_check _ 7792 16 (by decide +kernel)
theorem Check060.checked : Interval test 7680 7808 :=
  (FiniteChecks.interval_append test 7680 7744 7808
  (FiniteChecks.interval_append test 7680 7712 7744
  (FiniteChecks.interval_append test 7680 7696 7712
  Check060.part7680
  Check060.part7696)
  (FiniteChecks.interval_append test 7712 7728 7744
  Check060.part7712
  Check060.part7728))
  (FiniteChecks.interval_append test 7744 7776 7808
  (FiniteChecks.interval_append test 7744 7760 7776
  Check060.part7744
  Check060.part7760)
  (FiniteChecks.interval_append test 7776 7792 7808
  Check060.part7776
  Check060.part7792)))
#print axioms Check060.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check061.part7808 : Interval test 7808 7824 :=
  interval_of_check _ 7808 16 (by decide +kernel)
theorem Check061.part7824 : Interval test 7824 7840 :=
  interval_of_check _ 7824 16 (by decide +kernel)
theorem Check061.part7840 : Interval test 7840 7856 :=
  interval_of_check _ 7840 16 (by decide +kernel)
theorem Check061.part7856 : Interval test 7856 7872 :=
  interval_of_check _ 7856 16 (by decide +kernel)
theorem Check061.part7872 : Interval test 7872 7888 :=
  interval_of_check _ 7872 16 (by decide +kernel)
theorem Check061.part7888 : Interval test 7888 7904 :=
  interval_of_check _ 7888 16 (by decide +kernel)
theorem Check061.part7904 : Interval test 7904 7920 :=
  interval_of_check _ 7904 16 (by decide +kernel)
theorem Check061.part7920 : Interval test 7920 7936 :=
  interval_of_check _ 7920 16 (by decide +kernel)
theorem Check061.checked : Interval test 7808 7936 :=
  (FiniteChecks.interval_append test 7808 7872 7936
  (FiniteChecks.interval_append test 7808 7840 7872
  (FiniteChecks.interval_append test 7808 7824 7840
  Check061.part7808
  Check061.part7824)
  (FiniteChecks.interval_append test 7840 7856 7872
  Check061.part7840
  Check061.part7856))
  (FiniteChecks.interval_append test 7872 7904 7936
  (FiniteChecks.interval_append test 7872 7888 7904
  Check061.part7872
  Check061.part7888)
  (FiniteChecks.interval_append test 7904 7920 7936
  Check061.part7904
  Check061.part7920)))
#print axioms Check061.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check062.part7936 : Interval test 7936 7952 :=
  interval_of_check _ 7936 16 (by decide +kernel)
theorem Check062.part7952 : Interval test 7952 7968 :=
  interval_of_check _ 7952 16 (by decide +kernel)
theorem Check062.part7968 : Interval test 7968 7984 :=
  interval_of_check _ 7968 16 (by decide +kernel)
theorem Check062.part7984 : Interval test 7984 8000 :=
  interval_of_check _ 7984 16 (by decide +kernel)
theorem Check062.part8000 : Interval test 8000 8016 :=
  interval_of_check _ 8000 16 (by decide +kernel)
theorem Check062.part8016 : Interval test 8016 8032 :=
  interval_of_check _ 8016 16 (by decide +kernel)
theorem Check062.part8032 : Interval test 8032 8048 :=
  interval_of_check _ 8032 16 (by decide +kernel)
theorem Check062.part8048 : Interval test 8048 8064 :=
  interval_of_check _ 8048 16 (by decide +kernel)
theorem Check062.checked : Interval test 7936 8064 :=
  (FiniteChecks.interval_append test 7936 8000 8064
  (FiniteChecks.interval_append test 7936 7968 8000
  (FiniteChecks.interval_append test 7936 7952 7968
  Check062.part7936
  Check062.part7952)
  (FiniteChecks.interval_append test 7968 7984 8000
  Check062.part7968
  Check062.part7984))
  (FiniteChecks.interval_append test 8000 8032 8064
  (FiniteChecks.interval_append test 8000 8016 8032
  Check062.part8000
  Check062.part8016)
  (FiniteChecks.interval_append test 8032 8048 8064
  Check062.part8032
  Check062.part8048)))
#print axioms Check062.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check063.part8064 : Interval test 8064 8080 :=
  interval_of_check _ 8064 16 (by decide +kernel)
theorem Check063.part8080 : Interval test 8080 8096 :=
  interval_of_check _ 8080 16 (by decide +kernel)
theorem Check063.part8096 : Interval test 8096 8112 :=
  interval_of_check _ 8096 16 (by decide +kernel)
theorem Check063.part8112 : Interval test 8112 8128 :=
  interval_of_check _ 8112 16 (by decide +kernel)
theorem Check063.part8128 : Interval test 8128 8144 :=
  interval_of_check _ 8128 16 (by decide +kernel)
theorem Check063.part8144 : Interval test 8144 8160 :=
  interval_of_check _ 8144 16 (by decide +kernel)
theorem Check063.part8160 : Interval test 8160 8176 :=
  interval_of_check _ 8160 16 (by decide +kernel)
theorem Check063.part8176 : Interval test 8176 8192 :=
  interval_of_check _ 8176 16 (by decide +kernel)
theorem Check063.checked : Interval test 8064 8192 :=
  (FiniteChecks.interval_append test 8064 8128 8192
  (FiniteChecks.interval_append test 8064 8096 8128
  (FiniteChecks.interval_append test 8064 8080 8096
  Check063.part8064
  Check063.part8080)
  (FiniteChecks.interval_append test 8096 8112 8128
  Check063.part8096
  Check063.part8112))
  (FiniteChecks.interval_append test 8128 8160 8192
  (FiniteChecks.interval_append test 8128 8144 8160
  Check063.part8128
  Check063.part8144)
  (FiniteChecks.interval_append test 8160 8176 8192
  Check063.part8160
  Check063.part8176)))
#print axioms Check063.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check064.part8192 : Interval test 8192 8208 :=
  interval_of_check _ 8192 16 (by decide +kernel)
theorem Check064.part8208 : Interval test 8208 8224 :=
  interval_of_check _ 8208 16 (by decide +kernel)
theorem Check064.part8224 : Interval test 8224 8240 :=
  interval_of_check _ 8224 16 (by decide +kernel)
theorem Check064.part8240 : Interval test 8240 8256 :=
  interval_of_check _ 8240 16 (by decide +kernel)
theorem Check064.part8256 : Interval test 8256 8272 :=
  interval_of_check _ 8256 16 (by decide +kernel)
theorem Check064.part8272 : Interval test 8272 8288 :=
  interval_of_check _ 8272 16 (by decide +kernel)
theorem Check064.part8288 : Interval test 8288 8304 :=
  interval_of_check _ 8288 16 (by decide +kernel)
theorem Check064.part8304 : Interval test 8304 8320 :=
  interval_of_check _ 8304 16 (by decide +kernel)
theorem Check064.checked : Interval test 8192 8320 :=
  (FiniteChecks.interval_append test 8192 8256 8320
  (FiniteChecks.interval_append test 8192 8224 8256
  (FiniteChecks.interval_append test 8192 8208 8224
  Check064.part8192
  Check064.part8208)
  (FiniteChecks.interval_append test 8224 8240 8256
  Check064.part8224
  Check064.part8240))
  (FiniteChecks.interval_append test 8256 8288 8320
  (FiniteChecks.interval_append test 8256 8272 8288
  Check064.part8256
  Check064.part8272)
  (FiniteChecks.interval_append test 8288 8304 8320
  Check064.part8288
  Check064.part8304)))
#print axioms Check064.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check065.part8320 : Interval test 8320 8336 :=
  interval_of_check _ 8320 16 (by decide +kernel)
theorem Check065.part8336 : Interval test 8336 8352 :=
  interval_of_check _ 8336 16 (by decide +kernel)
theorem Check065.part8352 : Interval test 8352 8368 :=
  interval_of_check _ 8352 16 (by decide +kernel)
theorem Check065.part8368 : Interval test 8368 8384 :=
  interval_of_check _ 8368 16 (by decide +kernel)
theorem Check065.part8384 : Interval test 8384 8400 :=
  interval_of_check _ 8384 16 (by decide +kernel)
theorem Check065.part8400 : Interval test 8400 8416 :=
  interval_of_check _ 8400 16 (by decide +kernel)
theorem Check065.part8416 : Interval test 8416 8432 :=
  interval_of_check _ 8416 16 (by decide +kernel)
theorem Check065.part8432 : Interval test 8432 8448 :=
  interval_of_check _ 8432 16 (by decide +kernel)
theorem Check065.checked : Interval test 8320 8448 :=
  (FiniteChecks.interval_append test 8320 8384 8448
  (FiniteChecks.interval_append test 8320 8352 8384
  (FiniteChecks.interval_append test 8320 8336 8352
  Check065.part8320
  Check065.part8336)
  (FiniteChecks.interval_append test 8352 8368 8384
  Check065.part8352
  Check065.part8368))
  (FiniteChecks.interval_append test 8384 8416 8448
  (FiniteChecks.interval_append test 8384 8400 8416
  Check065.part8384
  Check065.part8400)
  (FiniteChecks.interval_append test 8416 8432 8448
  Check065.part8416
  Check065.part8432)))
#print axioms Check065.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check066.part8448 : Interval test 8448 8464 :=
  interval_of_check _ 8448 16 (by decide +kernel)
theorem Check066.part8464 : Interval test 8464 8480 :=
  interval_of_check _ 8464 16 (by decide +kernel)
theorem Check066.part8480 : Interval test 8480 8496 :=
  interval_of_check _ 8480 16 (by decide +kernel)
theorem Check066.part8496 : Interval test 8496 8512 :=
  interval_of_check _ 8496 16 (by decide +kernel)
theorem Check066.part8512 : Interval test 8512 8528 :=
  interval_of_check _ 8512 16 (by decide +kernel)
theorem Check066.part8528 : Interval test 8528 8544 :=
  interval_of_check _ 8528 16 (by decide +kernel)
theorem Check066.part8544 : Interval test 8544 8560 :=
  interval_of_check _ 8544 16 (by decide +kernel)
theorem Check066.part8560 : Interval test 8560 8576 :=
  interval_of_check _ 8560 16 (by decide +kernel)
theorem Check066.checked : Interval test 8448 8576 :=
  (FiniteChecks.interval_append test 8448 8512 8576
  (FiniteChecks.interval_append test 8448 8480 8512
  (FiniteChecks.interval_append test 8448 8464 8480
  Check066.part8448
  Check066.part8464)
  (FiniteChecks.interval_append test 8480 8496 8512
  Check066.part8480
  Check066.part8496))
  (FiniteChecks.interval_append test 8512 8544 8576
  (FiniteChecks.interval_append test 8512 8528 8544
  Check066.part8512
  Check066.part8528)
  (FiniteChecks.interval_append test 8544 8560 8576
  Check066.part8544
  Check066.part8560)))
#print axioms Check066.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check067.part8576 : Interval test 8576 8592 :=
  interval_of_check _ 8576 16 (by decide +kernel)
theorem Check067.part8592 : Interval test 8592 8608 :=
  interval_of_check _ 8592 16 (by decide +kernel)
theorem Check067.part8608 : Interval test 8608 8624 :=
  interval_of_check _ 8608 16 (by decide +kernel)
theorem Check067.part8624 : Interval test 8624 8640 :=
  interval_of_check _ 8624 16 (by decide +kernel)
theorem Check067.part8640 : Interval test 8640 8656 :=
  interval_of_check _ 8640 16 (by decide +kernel)
theorem Check067.part8656 : Interval test 8656 8672 :=
  interval_of_check _ 8656 16 (by decide +kernel)
theorem Check067.part8672 : Interval test 8672 8688 :=
  interval_of_check _ 8672 16 (by decide +kernel)
theorem Check067.part8688 : Interval test 8688 8704 :=
  interval_of_check _ 8688 16 (by decide +kernel)
theorem Check067.checked : Interval test 8576 8704 :=
  (FiniteChecks.interval_append test 8576 8640 8704
  (FiniteChecks.interval_append test 8576 8608 8640
  (FiniteChecks.interval_append test 8576 8592 8608
  Check067.part8576
  Check067.part8592)
  (FiniteChecks.interval_append test 8608 8624 8640
  Check067.part8608
  Check067.part8624))
  (FiniteChecks.interval_append test 8640 8672 8704
  (FiniteChecks.interval_append test 8640 8656 8672
  Check067.part8640
  Check067.part8656)
  (FiniteChecks.interval_append test 8672 8688 8704
  Check067.part8672
  Check067.part8688)))
#print axioms Check067.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check068.part8704 : Interval test 8704 8720 :=
  interval_of_check _ 8704 16 (by decide +kernel)
theorem Check068.part8720 : Interval test 8720 8736 :=
  interval_of_check _ 8720 16 (by decide +kernel)
theorem Check068.part8736 : Interval test 8736 8752 :=
  interval_of_check _ 8736 16 (by decide +kernel)
theorem Check068.part8752 : Interval test 8752 8768 :=
  interval_of_check _ 8752 16 (by decide +kernel)
theorem Check068.part8768 : Interval test 8768 8784 :=
  interval_of_check _ 8768 16 (by decide +kernel)
theorem Check068.part8784 : Interval test 8784 8800 :=
  interval_of_check _ 8784 16 (by decide +kernel)
theorem Check068.part8800 : Interval test 8800 8816 :=
  interval_of_check _ 8800 16 (by decide +kernel)
theorem Check068.part8816 : Interval test 8816 8832 :=
  interval_of_check _ 8816 16 (by decide +kernel)
theorem Check068.checked : Interval test 8704 8832 :=
  (FiniteChecks.interval_append test 8704 8768 8832
  (FiniteChecks.interval_append test 8704 8736 8768
  (FiniteChecks.interval_append test 8704 8720 8736
  Check068.part8704
  Check068.part8720)
  (FiniteChecks.interval_append test 8736 8752 8768
  Check068.part8736
  Check068.part8752))
  (FiniteChecks.interval_append test 8768 8800 8832
  (FiniteChecks.interval_append test 8768 8784 8800
  Check068.part8768
  Check068.part8784)
  (FiniteChecks.interval_append test 8800 8816 8832
  Check068.part8800
  Check068.part8816)))
#print axioms Check068.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check069.part8832 : Interval test 8832 8848 :=
  interval_of_check _ 8832 16 (by decide +kernel)
theorem Check069.part8848 : Interval test 8848 8864 :=
  interval_of_check _ 8848 16 (by decide +kernel)
theorem Check069.part8864 : Interval test 8864 8880 :=
  interval_of_check _ 8864 16 (by decide +kernel)
theorem Check069.part8880 : Interval test 8880 8896 :=
  interval_of_check _ 8880 16 (by decide +kernel)
theorem Check069.part8896 : Interval test 8896 8912 :=
  interval_of_check _ 8896 16 (by decide +kernel)
theorem Check069.part8912 : Interval test 8912 8928 :=
  interval_of_check _ 8912 16 (by decide +kernel)
theorem Check069.part8928 : Interval test 8928 8944 :=
  interval_of_check _ 8928 16 (by decide +kernel)
theorem Check069.part8944 : Interval test 8944 8960 :=
  interval_of_check _ 8944 16 (by decide +kernel)
theorem Check069.checked : Interval test 8832 8960 :=
  (FiniteChecks.interval_append test 8832 8896 8960
  (FiniteChecks.interval_append test 8832 8864 8896
  (FiniteChecks.interval_append test 8832 8848 8864
  Check069.part8832
  Check069.part8848)
  (FiniteChecks.interval_append test 8864 8880 8896
  Check069.part8864
  Check069.part8880))
  (FiniteChecks.interval_append test 8896 8928 8960
  (FiniteChecks.interval_append test 8896 8912 8928
  Check069.part8896
  Check069.part8912)
  (FiniteChecks.interval_append test 8928 8944 8960
  Check069.part8928
  Check069.part8944)))
#print axioms Check069.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check070.part8960 : Interval test 8960 8976 :=
  interval_of_check _ 8960 16 (by decide +kernel)
theorem Check070.part8976 : Interval test 8976 8992 :=
  interval_of_check _ 8976 16 (by decide +kernel)
theorem Check070.part8992 : Interval test 8992 9008 :=
  interval_of_check _ 8992 16 (by decide +kernel)
theorem Check070.part9008 : Interval test 9008 9024 :=
  interval_of_check _ 9008 16 (by decide +kernel)
theorem Check070.part9024 : Interval test 9024 9040 :=
  interval_of_check _ 9024 16 (by decide +kernel)
theorem Check070.part9040 : Interval test 9040 9056 :=
  interval_of_check _ 9040 16 (by decide +kernel)
theorem Check070.part9056 : Interval test 9056 9072 :=
  interval_of_check _ 9056 16 (by decide +kernel)
theorem Check070.part9072 : Interval test 9072 9088 :=
  interval_of_check _ 9072 16 (by decide +kernel)
theorem Check070.checked : Interval test 8960 9088 :=
  (FiniteChecks.interval_append test 8960 9024 9088
  (FiniteChecks.interval_append test 8960 8992 9024
  (FiniteChecks.interval_append test 8960 8976 8992
  Check070.part8960
  Check070.part8976)
  (FiniteChecks.interval_append test 8992 9008 9024
  Check070.part8992
  Check070.part9008))
  (FiniteChecks.interval_append test 9024 9056 9088
  (FiniteChecks.interval_append test 9024 9040 9056
  Check070.part9024
  Check070.part9040)
  (FiniteChecks.interval_append test 9056 9072 9088
  Check070.part9056
  Check070.part9072)))
#print axioms Check070.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check071.part9088 : Interval test 9088 9104 :=
  interval_of_check _ 9088 16 (by decide +kernel)
theorem Check071.part9104 : Interval test 9104 9120 :=
  interval_of_check _ 9104 16 (by decide +kernel)
theorem Check071.part9120 : Interval test 9120 9136 :=
  interval_of_check _ 9120 16 (by decide +kernel)
theorem Check071.part9136 : Interval test 9136 9152 :=
  interval_of_check _ 9136 16 (by decide +kernel)
theorem Check071.part9152 : Interval test 9152 9168 :=
  interval_of_check _ 9152 16 (by decide +kernel)
theorem Check071.part9168 : Interval test 9168 9184 :=
  interval_of_check _ 9168 16 (by decide +kernel)
theorem Check071.part9184 : Interval test 9184 9200 :=
  interval_of_check _ 9184 16 (by decide +kernel)
theorem Check071.part9200 : Interval test 9200 9216 :=
  interval_of_check _ 9200 16 (by decide +kernel)
theorem Check071.checked : Interval test 9088 9216 :=
  (FiniteChecks.interval_append test 9088 9152 9216
  (FiniteChecks.interval_append test 9088 9120 9152
  (FiniteChecks.interval_append test 9088 9104 9120
  Check071.part9088
  Check071.part9104)
  (FiniteChecks.interval_append test 9120 9136 9152
  Check071.part9120
  Check071.part9136))
  (FiniteChecks.interval_append test 9152 9184 9216
  (FiniteChecks.interval_append test 9152 9168 9184
  Check071.part9152
  Check071.part9168)
  (FiniteChecks.interval_append test 9184 9200 9216
  Check071.part9184
  Check071.part9200)))
#print axioms Check071.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check072.part9216 : Interval test 9216 9232 :=
  interval_of_check _ 9216 16 (by decide +kernel)
theorem Check072.part9232 : Interval test 9232 9248 :=
  interval_of_check _ 9232 16 (by decide +kernel)
theorem Check072.part9248 : Interval test 9248 9264 :=
  interval_of_check _ 9248 16 (by decide +kernel)
theorem Check072.part9264 : Interval test 9264 9280 :=
  interval_of_check _ 9264 16 (by decide +kernel)
theorem Check072.part9280 : Interval test 9280 9296 :=
  interval_of_check _ 9280 16 (by decide +kernel)
theorem Check072.part9296 : Interval test 9296 9312 :=
  interval_of_check _ 9296 16 (by decide +kernel)
theorem Check072.part9312 : Interval test 9312 9328 :=
  interval_of_check _ 9312 16 (by decide +kernel)
theorem Check072.part9328 : Interval test 9328 9344 :=
  interval_of_check _ 9328 16 (by decide +kernel)
theorem Check072.checked : Interval test 9216 9344 :=
  (FiniteChecks.interval_append test 9216 9280 9344
  (FiniteChecks.interval_append test 9216 9248 9280
  (FiniteChecks.interval_append test 9216 9232 9248
  Check072.part9216
  Check072.part9232)
  (FiniteChecks.interval_append test 9248 9264 9280
  Check072.part9248
  Check072.part9264))
  (FiniteChecks.interval_append test 9280 9312 9344
  (FiniteChecks.interval_append test 9280 9296 9312
  Check072.part9280
  Check072.part9296)
  (FiniteChecks.interval_append test 9312 9328 9344
  Check072.part9312
  Check072.part9328)))
#print axioms Check072.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check073.part9344 : Interval test 9344 9360 :=
  interval_of_check _ 9344 16 (by decide +kernel)
theorem Check073.part9360 : Interval test 9360 9376 :=
  interval_of_check _ 9360 16 (by decide +kernel)
theorem Check073.part9376 : Interval test 9376 9392 :=
  interval_of_check _ 9376 16 (by decide +kernel)
theorem Check073.part9392 : Interval test 9392 9408 :=
  interval_of_check _ 9392 16 (by decide +kernel)
theorem Check073.part9408 : Interval test 9408 9424 :=
  interval_of_check _ 9408 16 (by decide +kernel)
theorem Check073.part9424 : Interval test 9424 9440 :=
  interval_of_check _ 9424 16 (by decide +kernel)
theorem Check073.part9440 : Interval test 9440 9456 :=
  interval_of_check _ 9440 16 (by decide +kernel)
theorem Check073.part9456 : Interval test 9456 9472 :=
  interval_of_check _ 9456 16 (by decide +kernel)
theorem Check073.checked : Interval test 9344 9472 :=
  (FiniteChecks.interval_append test 9344 9408 9472
  (FiniteChecks.interval_append test 9344 9376 9408
  (FiniteChecks.interval_append test 9344 9360 9376
  Check073.part9344
  Check073.part9360)
  (FiniteChecks.interval_append test 9376 9392 9408
  Check073.part9376
  Check073.part9392))
  (FiniteChecks.interval_append test 9408 9440 9472
  (FiniteChecks.interval_append test 9408 9424 9440
  Check073.part9408
  Check073.part9424)
  (FiniteChecks.interval_append test 9440 9456 9472
  Check073.part9440
  Check073.part9456)))
#print axioms Check073.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check074.part9472 : Interval test 9472 9488 :=
  interval_of_check _ 9472 16 (by decide +kernel)
theorem Check074.part9488 : Interval test 9488 9504 :=
  interval_of_check _ 9488 16 (by decide +kernel)
theorem Check074.part9504 : Interval test 9504 9520 :=
  interval_of_check _ 9504 16 (by decide +kernel)
theorem Check074.part9520 : Interval test 9520 9536 :=
  interval_of_check _ 9520 16 (by decide +kernel)
theorem Check074.part9536 : Interval test 9536 9552 :=
  interval_of_check _ 9536 16 (by decide +kernel)
theorem Check074.part9552 : Interval test 9552 9568 :=
  interval_of_check _ 9552 16 (by decide +kernel)
theorem Check074.part9568 : Interval test 9568 9584 :=
  interval_of_check _ 9568 16 (by decide +kernel)
theorem Check074.part9584 : Interval test 9584 9600 :=
  interval_of_check _ 9584 16 (by decide +kernel)
theorem Check074.checked : Interval test 9472 9600 :=
  (FiniteChecks.interval_append test 9472 9536 9600
  (FiniteChecks.interval_append test 9472 9504 9536
  (FiniteChecks.interval_append test 9472 9488 9504
  Check074.part9472
  Check074.part9488)
  (FiniteChecks.interval_append test 9504 9520 9536
  Check074.part9504
  Check074.part9520))
  (FiniteChecks.interval_append test 9536 9568 9600
  (FiniteChecks.interval_append test 9536 9552 9568
  Check074.part9536
  Check074.part9552)
  (FiniteChecks.interval_append test 9568 9584 9600
  Check074.part9568
  Check074.part9584)))
#print axioms Check074.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check075.part9600 : Interval test 9600 9616 :=
  interval_of_check _ 9600 16 (by decide +kernel)
theorem Check075.part9616 : Interval test 9616 9632 :=
  interval_of_check _ 9616 16 (by decide +kernel)
theorem Check075.part9632 : Interval test 9632 9648 :=
  interval_of_check _ 9632 16 (by decide +kernel)
theorem Check075.part9648 : Interval test 9648 9664 :=
  interval_of_check _ 9648 16 (by decide +kernel)
theorem Check075.part9664 : Interval test 9664 9680 :=
  interval_of_check _ 9664 16 (by decide +kernel)
theorem Check075.part9680 : Interval test 9680 9696 :=
  interval_of_check _ 9680 16 (by decide +kernel)
theorem Check075.part9696 : Interval test 9696 9712 :=
  interval_of_check _ 9696 16 (by decide +kernel)
theorem Check075.part9712 : Interval test 9712 9728 :=
  interval_of_check _ 9712 16 (by decide +kernel)
theorem Check075.checked : Interval test 9600 9728 :=
  (FiniteChecks.interval_append test 9600 9664 9728
  (FiniteChecks.interval_append test 9600 9632 9664
  (FiniteChecks.interval_append test 9600 9616 9632
  Check075.part9600
  Check075.part9616)
  (FiniteChecks.interval_append test 9632 9648 9664
  Check075.part9632
  Check075.part9648))
  (FiniteChecks.interval_append test 9664 9696 9728
  (FiniteChecks.interval_append test 9664 9680 9696
  Check075.part9664
  Check075.part9680)
  (FiniteChecks.interval_append test 9696 9712 9728
  Check075.part9696
  Check075.part9712)))
#print axioms Check075.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check076.part9728 : Interval test 9728 9744 :=
  interval_of_check _ 9728 16 (by decide +kernel)
theorem Check076.part9744 : Interval test 9744 9760 :=
  interval_of_check _ 9744 16 (by decide +kernel)
theorem Check076.part9760 : Interval test 9760 9776 :=
  interval_of_check _ 9760 16 (by decide +kernel)
theorem Check076.part9776 : Interval test 9776 9792 :=
  interval_of_check _ 9776 16 (by decide +kernel)
theorem Check076.part9792 : Interval test 9792 9808 :=
  interval_of_check _ 9792 16 (by decide +kernel)
theorem Check076.part9808 : Interval test 9808 9824 :=
  interval_of_check _ 9808 16 (by decide +kernel)
theorem Check076.part9824 : Interval test 9824 9840 :=
  interval_of_check _ 9824 16 (by decide +kernel)
theorem Check076.part9840 : Interval test 9840 9856 :=
  interval_of_check _ 9840 16 (by decide +kernel)
theorem Check076.checked : Interval test 9728 9856 :=
  (FiniteChecks.interval_append test 9728 9792 9856
  (FiniteChecks.interval_append test 9728 9760 9792
  (FiniteChecks.interval_append test 9728 9744 9760
  Check076.part9728
  Check076.part9744)
  (FiniteChecks.interval_append test 9760 9776 9792
  Check076.part9760
  Check076.part9776))
  (FiniteChecks.interval_append test 9792 9824 9856
  (FiniteChecks.interval_append test 9792 9808 9824
  Check076.part9792
  Check076.part9808)
  (FiniteChecks.interval_append test 9824 9840 9856
  Check076.part9824
  Check076.part9840)))
#print axioms Check076.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check077.part9856 : Interval test 9856 9872 :=
  interval_of_check _ 9856 16 (by decide +kernel)
theorem Check077.part9872 : Interval test 9872 9888 :=
  interval_of_check _ 9872 16 (by decide +kernel)
theorem Check077.part9888 : Interval test 9888 9904 :=
  interval_of_check _ 9888 16 (by decide +kernel)
theorem Check077.part9904 : Interval test 9904 9920 :=
  interval_of_check _ 9904 16 (by decide +kernel)
theorem Check077.part9920 : Interval test 9920 9936 :=
  interval_of_check _ 9920 16 (by decide +kernel)
theorem Check077.part9936 : Interval test 9936 9952 :=
  interval_of_check _ 9936 16 (by decide +kernel)
theorem Check077.part9952 : Interval test 9952 9968 :=
  interval_of_check _ 9952 16 (by decide +kernel)
theorem Check077.part9968 : Interval test 9968 9984 :=
  interval_of_check _ 9968 16 (by decide +kernel)
theorem Check077.checked : Interval test 9856 9984 :=
  (FiniteChecks.interval_append test 9856 9920 9984
  (FiniteChecks.interval_append test 9856 9888 9920
  (FiniteChecks.interval_append test 9856 9872 9888
  Check077.part9856
  Check077.part9872)
  (FiniteChecks.interval_append test 9888 9904 9920
  Check077.part9888
  Check077.part9904))
  (FiniteChecks.interval_append test 9920 9952 9984
  (FiniteChecks.interval_append test 9920 9936 9952
  Check077.part9920
  Check077.part9936)
  (FiniteChecks.interval_append test 9952 9968 9984
  Check077.part9952
  Check077.part9968)))
#print axioms Check077.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check078.part9984 : Interval test 9984 10000 :=
  interval_of_check _ 9984 16 (by decide +kernel)
theorem Check078.part10000 : Interval test 10000 10016 :=
  interval_of_check _ 10000 16 (by decide +kernel)
theorem Check078.part10016 : Interval test 10016 10032 :=
  interval_of_check _ 10016 16 (by decide +kernel)
theorem Check078.part10032 : Interval test 10032 10048 :=
  interval_of_check _ 10032 16 (by decide +kernel)
theorem Check078.part10048 : Interval test 10048 10064 :=
  interval_of_check _ 10048 16 (by decide +kernel)
theorem Check078.part10064 : Interval test 10064 10080 :=
  interval_of_check _ 10064 16 (by decide +kernel)
theorem Check078.part10080 : Interval test 10080 10096 :=
  interval_of_check _ 10080 16 (by decide +kernel)
theorem Check078.part10096 : Interval test 10096 10112 :=
  interval_of_check _ 10096 16 (by decide +kernel)
theorem Check078.checked : Interval test 9984 10112 :=
  (FiniteChecks.interval_append test 9984 10048 10112
  (FiniteChecks.interval_append test 9984 10016 10048
  (FiniteChecks.interval_append test 9984 10000 10016
  Check078.part9984
  Check078.part10000)
  (FiniteChecks.interval_append test 10016 10032 10048
  Check078.part10016
  Check078.part10032))
  (FiniteChecks.interval_append test 10048 10080 10112
  (FiniteChecks.interval_append test 10048 10064 10080
  Check078.part10048
  Check078.part10064)
  (FiniteChecks.interval_append test 10080 10096 10112
  Check078.part10080
  Check078.part10096)))
#print axioms Check078.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check079.part10112 : Interval test 10112 10128 :=
  interval_of_check _ 10112 16 (by decide +kernel)
theorem Check079.part10128 : Interval test 10128 10144 :=
  interval_of_check _ 10128 16 (by decide +kernel)
theorem Check079.part10144 : Interval test 10144 10160 :=
  interval_of_check _ 10144 16 (by decide +kernel)
theorem Check079.part10160 : Interval test 10160 10176 :=
  interval_of_check _ 10160 16 (by decide +kernel)
theorem Check079.part10176 : Interval test 10176 10192 :=
  interval_of_check _ 10176 16 (by decide +kernel)
theorem Check079.part10192 : Interval test 10192 10208 :=
  interval_of_check _ 10192 16 (by decide +kernel)
theorem Check079.part10208 : Interval test 10208 10224 :=
  interval_of_check _ 10208 16 (by decide +kernel)
theorem Check079.part10224 : Interval test 10224 10240 :=
  interval_of_check _ 10224 16 (by decide +kernel)
theorem Check079.checked : Interval test 10112 10240 :=
  (FiniteChecks.interval_append test 10112 10176 10240
  (FiniteChecks.interval_append test 10112 10144 10176
  (FiniteChecks.interval_append test 10112 10128 10144
  Check079.part10112
  Check079.part10128)
  (FiniteChecks.interval_append test 10144 10160 10176
  Check079.part10144
  Check079.part10160))
  (FiniteChecks.interval_append test 10176 10208 10240
  (FiniteChecks.interval_append test 10176 10192 10208
  Check079.part10176
  Check079.part10192)
  (FiniteChecks.interval_append test 10208 10224 10240
  Check079.part10208
  Check079.part10224)))
#print axioms Check079.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
