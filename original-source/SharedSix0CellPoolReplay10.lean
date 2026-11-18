module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check200.part25600 : Interval test 25600 25616 :=
  interval_of_check _ 25600 16 (by decide +kernel)
theorem Check200.part25616 : Interval test 25616 25632 :=
  interval_of_check _ 25616 16 (by decide +kernel)
theorem Check200.part25632 : Interval test 25632 25648 :=
  interval_of_check _ 25632 16 (by decide +kernel)
theorem Check200.part25648 : Interval test 25648 25664 :=
  interval_of_check _ 25648 16 (by decide +kernel)
theorem Check200.part25664 : Interval test 25664 25680 :=
  interval_of_check _ 25664 16 (by decide +kernel)
theorem Check200.part25680 : Interval test 25680 25696 :=
  interval_of_check _ 25680 16 (by decide +kernel)
theorem Check200.part25696 : Interval test 25696 25712 :=
  interval_of_check _ 25696 16 (by decide +kernel)
theorem Check200.part25712 : Interval test 25712 25728 :=
  interval_of_check _ 25712 16 (by decide +kernel)
theorem Check200.checked : Interval test 25600 25728 :=
  (FiniteChecks.interval_append test 25600 25664 25728
  (FiniteChecks.interval_append test 25600 25632 25664
  (FiniteChecks.interval_append test 25600 25616 25632
  Check200.part25600
  Check200.part25616)
  (FiniteChecks.interval_append test 25632 25648 25664
  Check200.part25632
  Check200.part25648))
  (FiniteChecks.interval_append test 25664 25696 25728
  (FiniteChecks.interval_append test 25664 25680 25696
  Check200.part25664
  Check200.part25680)
  (FiniteChecks.interval_append test 25696 25712 25728
  Check200.part25696
  Check200.part25712)))
#print axioms Check200.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check201.part25728 : Interval test 25728 25744 :=
  interval_of_check _ 25728 16 (by decide +kernel)
theorem Check201.part25744 : Interval test 25744 25760 :=
  interval_of_check _ 25744 16 (by decide +kernel)
theorem Check201.part25760 : Interval test 25760 25776 :=
  interval_of_check _ 25760 16 (by decide +kernel)
theorem Check201.part25776 : Interval test 25776 25792 :=
  interval_of_check _ 25776 16 (by decide +kernel)
theorem Check201.part25792 : Interval test 25792 25808 :=
  interval_of_check _ 25792 16 (by decide +kernel)
theorem Check201.part25808 : Interval test 25808 25824 :=
  interval_of_check _ 25808 16 (by decide +kernel)
theorem Check201.part25824 : Interval test 25824 25840 :=
  interval_of_check _ 25824 16 (by decide +kernel)
theorem Check201.part25840 : Interval test 25840 25856 :=
  interval_of_check _ 25840 16 (by decide +kernel)
theorem Check201.checked : Interval test 25728 25856 :=
  (FiniteChecks.interval_append test 25728 25792 25856
  (FiniteChecks.interval_append test 25728 25760 25792
  (FiniteChecks.interval_append test 25728 25744 25760
  Check201.part25728
  Check201.part25744)
  (FiniteChecks.interval_append test 25760 25776 25792
  Check201.part25760
  Check201.part25776))
  (FiniteChecks.interval_append test 25792 25824 25856
  (FiniteChecks.interval_append test 25792 25808 25824
  Check201.part25792
  Check201.part25808)
  (FiniteChecks.interval_append test 25824 25840 25856
  Check201.part25824
  Check201.part25840)))
#print axioms Check201.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check202.part25856 : Interval test 25856 25872 :=
  interval_of_check _ 25856 16 (by decide +kernel)
theorem Check202.part25872 : Interval test 25872 25888 :=
  interval_of_check _ 25872 16 (by decide +kernel)
theorem Check202.part25888 : Interval test 25888 25904 :=
  interval_of_check _ 25888 16 (by decide +kernel)
theorem Check202.part25904 : Interval test 25904 25920 :=
  interval_of_check _ 25904 16 (by decide +kernel)
theorem Check202.part25920 : Interval test 25920 25936 :=
  interval_of_check _ 25920 16 (by decide +kernel)
theorem Check202.part25936 : Interval test 25936 25952 :=
  interval_of_check _ 25936 16 (by decide +kernel)
theorem Check202.part25952 : Interval test 25952 25968 :=
  interval_of_check _ 25952 16 (by decide +kernel)
theorem Check202.part25968 : Interval test 25968 25984 :=
  interval_of_check _ 25968 16 (by decide +kernel)
theorem Check202.checked : Interval test 25856 25984 :=
  (FiniteChecks.interval_append test 25856 25920 25984
  (FiniteChecks.interval_append test 25856 25888 25920
  (FiniteChecks.interval_append test 25856 25872 25888
  Check202.part25856
  Check202.part25872)
  (FiniteChecks.interval_append test 25888 25904 25920
  Check202.part25888
  Check202.part25904))
  (FiniteChecks.interval_append test 25920 25952 25984
  (FiniteChecks.interval_append test 25920 25936 25952
  Check202.part25920
  Check202.part25936)
  (FiniteChecks.interval_append test 25952 25968 25984
  Check202.part25952
  Check202.part25968)))
#print axioms Check202.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check203.part25984 : Interval test 25984 26000 :=
  interval_of_check _ 25984 16 (by decide +kernel)
theorem Check203.part26000 : Interval test 26000 26016 :=
  interval_of_check _ 26000 16 (by decide +kernel)
theorem Check203.part26016 : Interval test 26016 26032 :=
  interval_of_check _ 26016 16 (by decide +kernel)
theorem Check203.part26032 : Interval test 26032 26048 :=
  interval_of_check _ 26032 16 (by decide +kernel)
theorem Check203.part26048 : Interval test 26048 26064 :=
  interval_of_check _ 26048 16 (by decide +kernel)
theorem Check203.part26064 : Interval test 26064 26080 :=
  interval_of_check _ 26064 16 (by decide +kernel)
theorem Check203.part26080 : Interval test 26080 26096 :=
  interval_of_check _ 26080 16 (by decide +kernel)
theorem Check203.part26096 : Interval test 26096 26112 :=
  interval_of_check _ 26096 16 (by decide +kernel)
theorem Check203.checked : Interval test 25984 26112 :=
  (FiniteChecks.interval_append test 25984 26048 26112
  (FiniteChecks.interval_append test 25984 26016 26048
  (FiniteChecks.interval_append test 25984 26000 26016
  Check203.part25984
  Check203.part26000)
  (FiniteChecks.interval_append test 26016 26032 26048
  Check203.part26016
  Check203.part26032))
  (FiniteChecks.interval_append test 26048 26080 26112
  (FiniteChecks.interval_append test 26048 26064 26080
  Check203.part26048
  Check203.part26064)
  (FiniteChecks.interval_append test 26080 26096 26112
  Check203.part26080
  Check203.part26096)))
#print axioms Check203.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check204.part26112 : Interval test 26112 26128 :=
  interval_of_check _ 26112 16 (by decide +kernel)
theorem Check204.part26128 : Interval test 26128 26144 :=
  interval_of_check _ 26128 16 (by decide +kernel)
theorem Check204.part26144 : Interval test 26144 26160 :=
  interval_of_check _ 26144 16 (by decide +kernel)
theorem Check204.part26160 : Interval test 26160 26176 :=
  interval_of_check _ 26160 16 (by decide +kernel)
theorem Check204.part26176 : Interval test 26176 26192 :=
  interval_of_check _ 26176 16 (by decide +kernel)
theorem Check204.part26192 : Interval test 26192 26208 :=
  interval_of_check _ 26192 16 (by decide +kernel)
theorem Check204.part26208 : Interval test 26208 26224 :=
  interval_of_check _ 26208 16 (by decide +kernel)
theorem Check204.part26224 : Interval test 26224 26240 :=
  interval_of_check _ 26224 16 (by decide +kernel)
theorem Check204.checked : Interval test 26112 26240 :=
  (FiniteChecks.interval_append test 26112 26176 26240
  (FiniteChecks.interval_append test 26112 26144 26176
  (FiniteChecks.interval_append test 26112 26128 26144
  Check204.part26112
  Check204.part26128)
  (FiniteChecks.interval_append test 26144 26160 26176
  Check204.part26144
  Check204.part26160))
  (FiniteChecks.interval_append test 26176 26208 26240
  (FiniteChecks.interval_append test 26176 26192 26208
  Check204.part26176
  Check204.part26192)
  (FiniteChecks.interval_append test 26208 26224 26240
  Check204.part26208
  Check204.part26224)))
#print axioms Check204.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check205.part26240 : Interval test 26240 26256 :=
  interval_of_check _ 26240 16 (by decide +kernel)
theorem Check205.part26256 : Interval test 26256 26272 :=
  interval_of_check _ 26256 16 (by decide +kernel)
theorem Check205.part26272 : Interval test 26272 26288 :=
  interval_of_check _ 26272 16 (by decide +kernel)
theorem Check205.part26288 : Interval test 26288 26304 :=
  interval_of_check _ 26288 16 (by decide +kernel)
theorem Check205.part26304 : Interval test 26304 26320 :=
  interval_of_check _ 26304 16 (by decide +kernel)
theorem Check205.part26320 : Interval test 26320 26336 :=
  interval_of_check _ 26320 16 (by decide +kernel)
theorem Check205.part26336 : Interval test 26336 26352 :=
  interval_of_check _ 26336 16 (by decide +kernel)
theorem Check205.part26352 : Interval test 26352 26368 :=
  interval_of_check _ 26352 16 (by decide +kernel)
theorem Check205.checked : Interval test 26240 26368 :=
  (FiniteChecks.interval_append test 26240 26304 26368
  (FiniteChecks.interval_append test 26240 26272 26304
  (FiniteChecks.interval_append test 26240 26256 26272
  Check205.part26240
  Check205.part26256)
  (FiniteChecks.interval_append test 26272 26288 26304
  Check205.part26272
  Check205.part26288))
  (FiniteChecks.interval_append test 26304 26336 26368
  (FiniteChecks.interval_append test 26304 26320 26336
  Check205.part26304
  Check205.part26320)
  (FiniteChecks.interval_append test 26336 26352 26368
  Check205.part26336
  Check205.part26352)))
#print axioms Check205.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check206.part26368 : Interval test 26368 26384 :=
  interval_of_check _ 26368 16 (by decide +kernel)
theorem Check206.part26384 : Interval test 26384 26400 :=
  interval_of_check _ 26384 16 (by decide +kernel)
theorem Check206.part26400 : Interval test 26400 26416 :=
  interval_of_check _ 26400 16 (by decide +kernel)
theorem Check206.part26416 : Interval test 26416 26432 :=
  interval_of_check _ 26416 16 (by decide +kernel)
theorem Check206.part26432 : Interval test 26432 26448 :=
  interval_of_check _ 26432 16 (by decide +kernel)
theorem Check206.part26448 : Interval test 26448 26464 :=
  interval_of_check _ 26448 16 (by decide +kernel)
theorem Check206.part26464 : Interval test 26464 26480 :=
  interval_of_check _ 26464 16 (by decide +kernel)
theorem Check206.part26480 : Interval test 26480 26496 :=
  interval_of_check _ 26480 16 (by decide +kernel)
theorem Check206.checked : Interval test 26368 26496 :=
  (FiniteChecks.interval_append test 26368 26432 26496
  (FiniteChecks.interval_append test 26368 26400 26432
  (FiniteChecks.interval_append test 26368 26384 26400
  Check206.part26368
  Check206.part26384)
  (FiniteChecks.interval_append test 26400 26416 26432
  Check206.part26400
  Check206.part26416))
  (FiniteChecks.interval_append test 26432 26464 26496
  (FiniteChecks.interval_append test 26432 26448 26464
  Check206.part26432
  Check206.part26448)
  (FiniteChecks.interval_append test 26464 26480 26496
  Check206.part26464
  Check206.part26480)))
#print axioms Check206.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check207.part26496 : Interval test 26496 26512 :=
  interval_of_check _ 26496 16 (by decide +kernel)
theorem Check207.part26512 : Interval test 26512 26528 :=
  interval_of_check _ 26512 16 (by decide +kernel)
theorem Check207.part26528 : Interval test 26528 26544 :=
  interval_of_check _ 26528 16 (by decide +kernel)
theorem Check207.part26544 : Interval test 26544 26560 :=
  interval_of_check _ 26544 16 (by decide +kernel)
theorem Check207.part26560 : Interval test 26560 26576 :=
  interval_of_check _ 26560 16 (by decide +kernel)
theorem Check207.part26576 : Interval test 26576 26592 :=
  interval_of_check _ 26576 16 (by decide +kernel)
theorem Check207.part26592 : Interval test 26592 26608 :=
  interval_of_check _ 26592 16 (by decide +kernel)
theorem Check207.part26608 : Interval test 26608 26624 :=
  interval_of_check _ 26608 16 (by decide +kernel)
theorem Check207.checked : Interval test 26496 26624 :=
  (FiniteChecks.interval_append test 26496 26560 26624
  (FiniteChecks.interval_append test 26496 26528 26560
  (FiniteChecks.interval_append test 26496 26512 26528
  Check207.part26496
  Check207.part26512)
  (FiniteChecks.interval_append test 26528 26544 26560
  Check207.part26528
  Check207.part26544))
  (FiniteChecks.interval_append test 26560 26592 26624
  (FiniteChecks.interval_append test 26560 26576 26592
  Check207.part26560
  Check207.part26576)
  (FiniteChecks.interval_append test 26592 26608 26624
  Check207.part26592
  Check207.part26608)))
#print axioms Check207.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check208.part26624 : Interval test 26624 26640 :=
  interval_of_check _ 26624 16 (by decide +kernel)
theorem Check208.part26640 : Interval test 26640 26656 :=
  interval_of_check _ 26640 16 (by decide +kernel)
theorem Check208.part26656 : Interval test 26656 26672 :=
  interval_of_check _ 26656 16 (by decide +kernel)
theorem Check208.part26672 : Interval test 26672 26688 :=
  interval_of_check _ 26672 16 (by decide +kernel)
theorem Check208.part26688 : Interval test 26688 26704 :=
  interval_of_check _ 26688 16 (by decide +kernel)
theorem Check208.part26704 : Interval test 26704 26720 :=
  interval_of_check _ 26704 16 (by decide +kernel)
theorem Check208.part26720 : Interval test 26720 26736 :=
  interval_of_check _ 26720 16 (by decide +kernel)
theorem Check208.part26736 : Interval test 26736 26752 :=
  interval_of_check _ 26736 16 (by decide +kernel)
theorem Check208.checked : Interval test 26624 26752 :=
  (FiniteChecks.interval_append test 26624 26688 26752
  (FiniteChecks.interval_append test 26624 26656 26688
  (FiniteChecks.interval_append test 26624 26640 26656
  Check208.part26624
  Check208.part26640)
  (FiniteChecks.interval_append test 26656 26672 26688
  Check208.part26656
  Check208.part26672))
  (FiniteChecks.interval_append test 26688 26720 26752
  (FiniteChecks.interval_append test 26688 26704 26720
  Check208.part26688
  Check208.part26704)
  (FiniteChecks.interval_append test 26720 26736 26752
  Check208.part26720
  Check208.part26736)))
#print axioms Check208.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check209.part26752 : Interval test 26752 26768 :=
  interval_of_check _ 26752 16 (by decide +kernel)
theorem Check209.part26768 : Interval test 26768 26784 :=
  interval_of_check _ 26768 16 (by decide +kernel)
theorem Check209.part26784 : Interval test 26784 26800 :=
  interval_of_check _ 26784 16 (by decide +kernel)
theorem Check209.part26800 : Interval test 26800 26816 :=
  interval_of_check _ 26800 16 (by decide +kernel)
theorem Check209.part26816 : Interval test 26816 26832 :=
  interval_of_check _ 26816 16 (by decide +kernel)
theorem Check209.part26832 : Interval test 26832 26848 :=
  interval_of_check _ 26832 16 (by decide +kernel)
theorem Check209.part26848 : Interval test 26848 26864 :=
  interval_of_check _ 26848 16 (by decide +kernel)
theorem Check209.part26864 : Interval test 26864 26880 :=
  interval_of_check _ 26864 16 (by decide +kernel)
theorem Check209.checked : Interval test 26752 26880 :=
  (FiniteChecks.interval_append test 26752 26816 26880
  (FiniteChecks.interval_append test 26752 26784 26816
  (FiniteChecks.interval_append test 26752 26768 26784
  Check209.part26752
  Check209.part26768)
  (FiniteChecks.interval_append test 26784 26800 26816
  Check209.part26784
  Check209.part26800))
  (FiniteChecks.interval_append test 26816 26848 26880
  (FiniteChecks.interval_append test 26816 26832 26848
  Check209.part26816
  Check209.part26832)
  (FiniteChecks.interval_append test 26848 26864 26880
  Check209.part26848
  Check209.part26864)))
#print axioms Check209.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check210.part26880 : Interval test 26880 26896 :=
  interval_of_check _ 26880 16 (by decide +kernel)
theorem Check210.part26896 : Interval test 26896 26912 :=
  interval_of_check _ 26896 16 (by decide +kernel)
theorem Check210.part26912 : Interval test 26912 26928 :=
  interval_of_check _ 26912 16 (by decide +kernel)
theorem Check210.part26928 : Interval test 26928 26944 :=
  interval_of_check _ 26928 16 (by decide +kernel)
theorem Check210.part26944 : Interval test 26944 26960 :=
  interval_of_check _ 26944 16 (by decide +kernel)
theorem Check210.part26960 : Interval test 26960 26976 :=
  interval_of_check _ 26960 16 (by decide +kernel)
theorem Check210.part26976 : Interval test 26976 26992 :=
  interval_of_check _ 26976 16 (by decide +kernel)
theorem Check210.part26992 : Interval test 26992 27008 :=
  interval_of_check _ 26992 16 (by decide +kernel)
theorem Check210.checked : Interval test 26880 27008 :=
  (FiniteChecks.interval_append test 26880 26944 27008
  (FiniteChecks.interval_append test 26880 26912 26944
  (FiniteChecks.interval_append test 26880 26896 26912
  Check210.part26880
  Check210.part26896)
  (FiniteChecks.interval_append test 26912 26928 26944
  Check210.part26912
  Check210.part26928))
  (FiniteChecks.interval_append test 26944 26976 27008
  (FiniteChecks.interval_append test 26944 26960 26976
  Check210.part26944
  Check210.part26960)
  (FiniteChecks.interval_append test 26976 26992 27008
  Check210.part26976
  Check210.part26992)))
#print axioms Check210.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check211.part27008 : Interval test 27008 27024 :=
  interval_of_check _ 27008 16 (by decide +kernel)
theorem Check211.part27024 : Interval test 27024 27040 :=
  interval_of_check _ 27024 16 (by decide +kernel)
theorem Check211.part27040 : Interval test 27040 27056 :=
  interval_of_check _ 27040 16 (by decide +kernel)
theorem Check211.part27056 : Interval test 27056 27072 :=
  interval_of_check _ 27056 16 (by decide +kernel)
theorem Check211.part27072 : Interval test 27072 27088 :=
  interval_of_check _ 27072 16 (by decide +kernel)
theorem Check211.part27088 : Interval test 27088 27104 :=
  interval_of_check _ 27088 16 (by decide +kernel)
theorem Check211.part27104 : Interval test 27104 27120 :=
  interval_of_check _ 27104 16 (by decide +kernel)
theorem Check211.part27120 : Interval test 27120 27136 :=
  interval_of_check _ 27120 16 (by decide +kernel)
theorem Check211.checked : Interval test 27008 27136 :=
  (FiniteChecks.interval_append test 27008 27072 27136
  (FiniteChecks.interval_append test 27008 27040 27072
  (FiniteChecks.interval_append test 27008 27024 27040
  Check211.part27008
  Check211.part27024)
  (FiniteChecks.interval_append test 27040 27056 27072
  Check211.part27040
  Check211.part27056))
  (FiniteChecks.interval_append test 27072 27104 27136
  (FiniteChecks.interval_append test 27072 27088 27104
  Check211.part27072
  Check211.part27088)
  (FiniteChecks.interval_append test 27104 27120 27136
  Check211.part27104
  Check211.part27120)))
#print axioms Check211.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check212.part27136 : Interval test 27136 27152 :=
  interval_of_check _ 27136 16 (by decide +kernel)
theorem Check212.part27152 : Interval test 27152 27168 :=
  interval_of_check _ 27152 16 (by decide +kernel)
theorem Check212.part27168 : Interval test 27168 27184 :=
  interval_of_check _ 27168 16 (by decide +kernel)
theorem Check212.part27184 : Interval test 27184 27200 :=
  interval_of_check _ 27184 16 (by decide +kernel)
theorem Check212.part27200 : Interval test 27200 27216 :=
  interval_of_check _ 27200 16 (by decide +kernel)
theorem Check212.part27216 : Interval test 27216 27232 :=
  interval_of_check _ 27216 16 (by decide +kernel)
theorem Check212.part27232 : Interval test 27232 27248 :=
  interval_of_check _ 27232 16 (by decide +kernel)
theorem Check212.part27248 : Interval test 27248 27264 :=
  interval_of_check _ 27248 16 (by decide +kernel)
theorem Check212.checked : Interval test 27136 27264 :=
  (FiniteChecks.interval_append test 27136 27200 27264
  (FiniteChecks.interval_append test 27136 27168 27200
  (FiniteChecks.interval_append test 27136 27152 27168
  Check212.part27136
  Check212.part27152)
  (FiniteChecks.interval_append test 27168 27184 27200
  Check212.part27168
  Check212.part27184))
  (FiniteChecks.interval_append test 27200 27232 27264
  (FiniteChecks.interval_append test 27200 27216 27232
  Check212.part27200
  Check212.part27216)
  (FiniteChecks.interval_append test 27232 27248 27264
  Check212.part27232
  Check212.part27248)))
#print axioms Check212.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check213.part27264 : Interval test 27264 27280 :=
  interval_of_check _ 27264 16 (by decide +kernel)
theorem Check213.part27280 : Interval test 27280 27296 :=
  interval_of_check _ 27280 16 (by decide +kernel)
theorem Check213.part27296 : Interval test 27296 27312 :=
  interval_of_check _ 27296 16 (by decide +kernel)
theorem Check213.part27312 : Interval test 27312 27328 :=
  interval_of_check _ 27312 16 (by decide +kernel)
theorem Check213.part27328 : Interval test 27328 27344 :=
  interval_of_check _ 27328 16 (by decide +kernel)
theorem Check213.part27344 : Interval test 27344 27360 :=
  interval_of_check _ 27344 16 (by decide +kernel)
theorem Check213.part27360 : Interval test 27360 27376 :=
  interval_of_check _ 27360 16 (by decide +kernel)
theorem Check213.part27376 : Interval test 27376 27392 :=
  interval_of_check _ 27376 16 (by decide +kernel)
theorem Check213.checked : Interval test 27264 27392 :=
  (FiniteChecks.interval_append test 27264 27328 27392
  (FiniteChecks.interval_append test 27264 27296 27328
  (FiniteChecks.interval_append test 27264 27280 27296
  Check213.part27264
  Check213.part27280)
  (FiniteChecks.interval_append test 27296 27312 27328
  Check213.part27296
  Check213.part27312))
  (FiniteChecks.interval_append test 27328 27360 27392
  (FiniteChecks.interval_append test 27328 27344 27360
  Check213.part27328
  Check213.part27344)
  (FiniteChecks.interval_append test 27360 27376 27392
  Check213.part27360
  Check213.part27376)))
#print axioms Check213.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check214.part27392 : Interval test 27392 27408 :=
  interval_of_check _ 27392 16 (by decide +kernel)
theorem Check214.part27408 : Interval test 27408 27424 :=
  interval_of_check _ 27408 16 (by decide +kernel)
theorem Check214.part27424 : Interval test 27424 27440 :=
  interval_of_check _ 27424 16 (by decide +kernel)
theorem Check214.part27440 : Interval test 27440 27456 :=
  interval_of_check _ 27440 16 (by decide +kernel)
theorem Check214.part27456 : Interval test 27456 27472 :=
  interval_of_check _ 27456 16 (by decide +kernel)
theorem Check214.part27472 : Interval test 27472 27488 :=
  interval_of_check _ 27472 16 (by decide +kernel)
theorem Check214.part27488 : Interval test 27488 27504 :=
  interval_of_check _ 27488 16 (by decide +kernel)
theorem Check214.part27504 : Interval test 27504 27520 :=
  interval_of_check _ 27504 16 (by decide +kernel)
theorem Check214.checked : Interval test 27392 27520 :=
  (FiniteChecks.interval_append test 27392 27456 27520
  (FiniteChecks.interval_append test 27392 27424 27456
  (FiniteChecks.interval_append test 27392 27408 27424
  Check214.part27392
  Check214.part27408)
  (FiniteChecks.interval_append test 27424 27440 27456
  Check214.part27424
  Check214.part27440))
  (FiniteChecks.interval_append test 27456 27488 27520
  (FiniteChecks.interval_append test 27456 27472 27488
  Check214.part27456
  Check214.part27472)
  (FiniteChecks.interval_append test 27488 27504 27520
  Check214.part27488
  Check214.part27504)))
#print axioms Check214.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check215.part27520 : Interval test 27520 27536 :=
  interval_of_check _ 27520 16 (by decide +kernel)
theorem Check215.part27536 : Interval test 27536 27552 :=
  interval_of_check _ 27536 16 (by decide +kernel)
theorem Check215.part27552 : Interval test 27552 27568 :=
  interval_of_check _ 27552 16 (by decide +kernel)
theorem Check215.part27568 : Interval test 27568 27584 :=
  interval_of_check _ 27568 16 (by decide +kernel)
theorem Check215.part27584 : Interval test 27584 27600 :=
  interval_of_check _ 27584 16 (by decide +kernel)
theorem Check215.part27600 : Interval test 27600 27616 :=
  interval_of_check _ 27600 16 (by decide +kernel)
theorem Check215.part27616 : Interval test 27616 27632 :=
  interval_of_check _ 27616 16 (by decide +kernel)
theorem Check215.part27632 : Interval test 27632 27648 :=
  interval_of_check _ 27632 16 (by decide +kernel)
theorem Check215.checked : Interval test 27520 27648 :=
  (FiniteChecks.interval_append test 27520 27584 27648
  (FiniteChecks.interval_append test 27520 27552 27584
  (FiniteChecks.interval_append test 27520 27536 27552
  Check215.part27520
  Check215.part27536)
  (FiniteChecks.interval_append test 27552 27568 27584
  Check215.part27552
  Check215.part27568))
  (FiniteChecks.interval_append test 27584 27616 27648
  (FiniteChecks.interval_append test 27584 27600 27616
  Check215.part27584
  Check215.part27600)
  (FiniteChecks.interval_append test 27616 27632 27648
  Check215.part27616
  Check215.part27632)))
#print axioms Check215.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check216.part27648 : Interval test 27648 27664 :=
  interval_of_check _ 27648 16 (by decide +kernel)
theorem Check216.part27664 : Interval test 27664 27680 :=
  interval_of_check _ 27664 16 (by decide +kernel)
theorem Check216.part27680 : Interval test 27680 27696 :=
  interval_of_check _ 27680 16 (by decide +kernel)
theorem Check216.part27696 : Interval test 27696 27712 :=
  interval_of_check _ 27696 16 (by decide +kernel)
theorem Check216.part27712 : Interval test 27712 27728 :=
  interval_of_check _ 27712 16 (by decide +kernel)
theorem Check216.part27728 : Interval test 27728 27744 :=
  interval_of_check _ 27728 16 (by decide +kernel)
theorem Check216.part27744 : Interval test 27744 27760 :=
  interval_of_check _ 27744 16 (by decide +kernel)
theorem Check216.part27760 : Interval test 27760 27776 :=
  interval_of_check _ 27760 16 (by decide +kernel)
theorem Check216.checked : Interval test 27648 27776 :=
  (FiniteChecks.interval_append test 27648 27712 27776
  (FiniteChecks.interval_append test 27648 27680 27712
  (FiniteChecks.interval_append test 27648 27664 27680
  Check216.part27648
  Check216.part27664)
  (FiniteChecks.interval_append test 27680 27696 27712
  Check216.part27680
  Check216.part27696))
  (FiniteChecks.interval_append test 27712 27744 27776
  (FiniteChecks.interval_append test 27712 27728 27744
  Check216.part27712
  Check216.part27728)
  (FiniteChecks.interval_append test 27744 27760 27776
  Check216.part27744
  Check216.part27760)))
#print axioms Check216.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check217.part27776 : Interval test 27776 27792 :=
  interval_of_check _ 27776 16 (by decide +kernel)
theorem Check217.part27792 : Interval test 27792 27808 :=
  interval_of_check _ 27792 16 (by decide +kernel)
theorem Check217.part27808 : Interval test 27808 27824 :=
  interval_of_check _ 27808 16 (by decide +kernel)
theorem Check217.part27824 : Interval test 27824 27840 :=
  interval_of_check _ 27824 16 (by decide +kernel)
theorem Check217.part27840 : Interval test 27840 27856 :=
  interval_of_check _ 27840 16 (by decide +kernel)
theorem Check217.part27856 : Interval test 27856 27872 :=
  interval_of_check _ 27856 16 (by decide +kernel)
theorem Check217.part27872 : Interval test 27872 27888 :=
  interval_of_check _ 27872 16 (by decide +kernel)
theorem Check217.part27888 : Interval test 27888 27904 :=
  interval_of_check _ 27888 16 (by decide +kernel)
theorem Check217.checked : Interval test 27776 27904 :=
  (FiniteChecks.interval_append test 27776 27840 27904
  (FiniteChecks.interval_append test 27776 27808 27840
  (FiniteChecks.interval_append test 27776 27792 27808
  Check217.part27776
  Check217.part27792)
  (FiniteChecks.interval_append test 27808 27824 27840
  Check217.part27808
  Check217.part27824))
  (FiniteChecks.interval_append test 27840 27872 27904
  (FiniteChecks.interval_append test 27840 27856 27872
  Check217.part27840
  Check217.part27856)
  (FiniteChecks.interval_append test 27872 27888 27904
  Check217.part27872
  Check217.part27888)))
#print axioms Check217.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check218.part27904 : Interval test 27904 27920 :=
  interval_of_check _ 27904 16 (by decide +kernel)
theorem Check218.part27920 : Interval test 27920 27936 :=
  interval_of_check _ 27920 16 (by decide +kernel)
theorem Check218.part27936 : Interval test 27936 27952 :=
  interval_of_check _ 27936 16 (by decide +kernel)
theorem Check218.part27952 : Interval test 27952 27968 :=
  interval_of_check _ 27952 16 (by decide +kernel)
theorem Check218.part27968 : Interval test 27968 27984 :=
  interval_of_check _ 27968 16 (by decide +kernel)
theorem Check218.part27984 : Interval test 27984 28000 :=
  interval_of_check _ 27984 16 (by decide +kernel)
theorem Check218.part28000 : Interval test 28000 28016 :=
  interval_of_check _ 28000 16 (by decide +kernel)
theorem Check218.part28016 : Interval test 28016 28032 :=
  interval_of_check _ 28016 16 (by decide +kernel)
theorem Check218.checked : Interval test 27904 28032 :=
  (FiniteChecks.interval_append test 27904 27968 28032
  (FiniteChecks.interval_append test 27904 27936 27968
  (FiniteChecks.interval_append test 27904 27920 27936
  Check218.part27904
  Check218.part27920)
  (FiniteChecks.interval_append test 27936 27952 27968
  Check218.part27936
  Check218.part27952))
  (FiniteChecks.interval_append test 27968 28000 28032
  (FiniteChecks.interval_append test 27968 27984 28000
  Check218.part27968
  Check218.part27984)
  (FiniteChecks.interval_append test 28000 28016 28032
  Check218.part28000
  Check218.part28016)))
#print axioms Check218.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check219.part28032 : Interval test 28032 28048 :=
  interval_of_check _ 28032 16 (by decide +kernel)
theorem Check219.part28048 : Interval test 28048 28064 :=
  interval_of_check _ 28048 16 (by decide +kernel)
theorem Check219.part28064 : Interval test 28064 28080 :=
  interval_of_check _ 28064 16 (by decide +kernel)
theorem Check219.part28080 : Interval test 28080 28096 :=
  interval_of_check _ 28080 16 (by decide +kernel)
theorem Check219.part28096 : Interval test 28096 28112 :=
  interval_of_check _ 28096 16 (by decide +kernel)
theorem Check219.part28112 : Interval test 28112 28128 :=
  interval_of_check _ 28112 16 (by decide +kernel)
theorem Check219.part28128 : Interval test 28128 28144 :=
  interval_of_check _ 28128 16 (by decide +kernel)
theorem Check219.part28144 : Interval test 28144 28160 :=
  interval_of_check _ 28144 16 (by decide +kernel)
theorem Check219.checked : Interval test 28032 28160 :=
  (FiniteChecks.interval_append test 28032 28096 28160
  (FiniteChecks.interval_append test 28032 28064 28096
  (FiniteChecks.interval_append test 28032 28048 28064
  Check219.part28032
  Check219.part28048)
  (FiniteChecks.interval_append test 28064 28080 28096
  Check219.part28064
  Check219.part28080))
  (FiniteChecks.interval_append test 28096 28128 28160
  (FiniteChecks.interval_append test 28096 28112 28128
  Check219.part28096
  Check219.part28112)
  (FiniteChecks.interval_append test 28128 28144 28160
  Check219.part28128
  Check219.part28144)))
#print axioms Check219.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
