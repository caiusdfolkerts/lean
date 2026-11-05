module
prelude
public import RootedSixExtra05
public import RawKindedFacePlacement
public import RootedSixExtra05OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
open ConcreteGrowth
abbrev blockCount : Nat := 100
noncomputable def template : Cell := ⟨10, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra05.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 104793658))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 107939434))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 111085210))))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 118949650))
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 122095426))
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 125241202)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 128386978))
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 131532754))
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 134678530))))
 (.branch 10
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 106825298))
 (.branch 11
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 109971074))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 113116850))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 120981290))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 124127066))
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 127272842))))
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 130418618))
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 133564394))
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 136710170)))))
 (.branch 21
 (.branch 19
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 107152983))
 (.branch 20
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 110298759))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 113444535))))
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 121308975))
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 124454751)))
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 127600527))
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 130746303)))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 133892079))
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 137037855))
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 2121697095716703064720082634))))
 (.branch 29
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 2556917031707168640880543794))
 (.branch 30
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 104924739))
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 108070515)))))
 (.branch 34
 (.branch 32
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 111216291))
 (.branch 33
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 119080731))
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 122226507))))
 (.branch 35
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 125372283))
 (.branch 36
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 128518059))
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 131663835))))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 134809611))
 (.branch 39
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 106497637))
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 109643413))))
 (.branch 41
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 112789189))
 (.branch 42
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 120653629))
 (.leaf (⟨2, 4, 5509170, 5509170, 357029148225, 361625650950⟩, 123799405)))))
 (.branch 46
 (.branch 44
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 126945181))
 (.branch 45
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 130090957))
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 133236733))))
 (.branch 48
 (.branch 47
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 136382509))
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 2109607634605527545828411091)))
 (.branch 49
 (.leaf (⟨3, 4, 5505825, 5513475, 141893788995, 434917935495⟩, 2544827570595993121988872251))
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 106759785))))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 109905561))
 (.branch 52
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 113051337))
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 120915777))))
 (.branch 54
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 124061553))
 (.branch 55
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 127207329))
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 130353105)))))
 (.branch 59
 (.branch 57
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 133498881))
 (.branch 58
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 136644657))
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 105383498))))
 (.branch 60
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 108529274))
 (.branch 61
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 111675050))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 119539490))))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 122685266))
 (.branch 64
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 125831042))
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 128976818))))
 (.branch 66
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 132122594))
 (.branch 67
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 135268370))
 (.leaf (⟨3, 4, 5309490, 5378115, 361742426640, 434925761040⟩, 2103563134637759102010525402)))))
 (.branch 71
 (.branch 69
 (.leaf (⟨3, 4, 5309490, 5378115, 141893788995, 434917935495⟩, 2538783070628224678170986562))
 (.branch 70
 (.leaf (⟨2, 4, 4399440, 1393440, 361626105360, 361626105360⟩, 104859205))
 (.leaf (⟨2, 4, 4399440, 1393440, 361609328160, 361626104160⟩, 108004981))))
 (.branch 73
 (.branch 72
 (.leaf (⟨2, 4, 4399440, 1393440, 361592550945, 361626104070⟩, 111150757))
 (.leaf (⟨2, 4, 4399440, 1393440, 361340892720, 361626081120⟩, 119015197)))
 (.branch 74
 (.leaf (⟨2, 4, 4399440, 1393440, 357029148225, 361625650950⟩, 122160973))
 (.leaf (⟨2, 4, 4399440, 1393440, 352465745475, 361625618550⟩, 125306749)))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf (⟨2, 4, 4399440, 1393440, 288041236050, 361617784950⟩, 128452525))
 (.branch 77
 (.leaf (⟨2, 4, 4399440, 1393440, 283746268755, 361617754230⟩, 131598301))
 (.leaf (⟨2, 4, 4399440, 1393440, 215026792020, 361617201270⟩, 134744077))))
 (.branch 79
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 106038878))
 (.branch 80
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 109184654))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 112330430)))))
 (.branch 84
 (.branch 82
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 120194870))
 (.branch 83
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 123340646))
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 126486422))))
 (.branch 85
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 129632198))
 (.branch 86
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 132777974))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 135923750))))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf (⟨3, 4, 4396320, 2441520, 361742426640, 434925761040⟩, 2108398690339731788602738389))
 (.branch 89
 (.leaf (⟨3, 4, 4396320, 2441520, 141893788995, 434917935495⟩, 2543618626330197364763199549))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 105580102))))
 (.branch 91
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 108725878))
 (.branch 92
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 111871654))
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 119736094)))))
 (.branch 96
 (.branch 94
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 122881870))
 (.branch 95
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 126027646))
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 129173422))))
 (.branch 98
 (.branch 97
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 132319198))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 135464974)))
 (.branch 99
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 2107189967437679618413299414))
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 2542409903428145194573760574)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2170 :=
  Fin.ofNat 2170 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20485
 (.branch 6184
 (.branch 5129
 (.branch 3108
 (.branch 3081
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3090
 (.leaf 3)
 (.branch 3096
 (.leaf 4)
 (.leaf 5))))
 (.branch 5123
 (.branch 3112
 (.leaf 6)
 (.branch 3120
 (.leaf 7)
 (.leaf 8)))
 (.branch 5125
 (.leaf 9)
 (.branch 5126
 (.leaf 10)
 (.leaf 11)))))
 (.branch 6147
 (.branch 5156
 (.branch 5138
 (.leaf 12)
 (.branch 5144
 (.leaf 13)
 (.leaf 14)))
 (.branch 5160
 (.leaf 15)
 (.branch 5168
 (.leaf 16)
 (.leaf 17))))
 (.branch 6153
 (.branch 6149
 (.leaf 18)
 (.branch 6150
 (.leaf 19)
 (.leaf 20)))
 (.branch 6168
 (.branch 6162
 (.leaf 21)
 (.leaf 22))
 (.branch 6180
 (.leaf 23)
 (.leaf 24))))))
 (.branch 10288
 (.branch 10246
 (.branch 7224
 (.branch 6192
 (.leaf 25)
 (.branch 7175
 (.leaf 26)
 (.leaf 27)))
 (.branch 10243
 (.leaf 28)
 (.branch 10245
 (.leaf 29)
 (.leaf 30))))
 (.branch 10264
 (.branch 10249
 (.leaf 31)
 (.branch 10258
 (.leaf 32)
 (.leaf 33)))
 (.branch 10276
 (.leaf 34)
 (.branch 10280
 (.leaf 35)
 (.leaf 36)))))
 (.branch 12312
 (.branch 12294
 (.branch 12291
 (.leaf 37)
 (.branch 12293
 (.leaf 38)
 (.leaf 39)))
 (.branch 12297
 (.leaf 40)
 (.branch 12306
 (.leaf 41)
 (.leaf 42))))
 (.branch 12336
 (.branch 12324
 (.leaf 43)
 (.branch 12328
 (.leaf 44)
 (.leaf 45)))
 (.branch 14392
 (.branch 14343
 (.leaf 46)
 (.leaf 47))
 (.branch 20483
 (.leaf 48)
 (.leaf 49)))))))
 (.branch 33828
 (.branch 24594
 (.branch 20520
 (.branch 20498
 (.branch 20486
 (.leaf 50)
 (.branch 20489
 (.leaf 51)
 (.leaf 52)))
 (.branch 20504
 (.leaf 53)
 (.branch 20516
 (.leaf 54)
 (.leaf 55))))
 (.branch 24581
 (.branch 20528
 (.leaf 56)
 (.branch 24579
 (.leaf 57)
 (.leaf 58)))
 (.branch 24582
 (.leaf 59)
 (.branch 24585
 (.leaf 60)
 (.leaf 61)))))
 (.branch 28728
 (.branch 24616
 (.branch 24600
 (.leaf 62)
 (.branch 24612
 (.leaf 63)
 (.leaf 64)))
 (.branch 24624
 (.leaf 65)
 (.branch 28679
 (.leaf 66)
 (.leaf 67))))
 (.branch 33798
 (.branch 33795
 (.leaf 68)
 (.branch 33797
 (.leaf 69)
 (.leaf 70)))
 (.branch 33810
 (.branch 33801
 (.leaf 71)
 (.leaf 72))
 (.branch 33816
 (.leaf 73)
 (.leaf 74))))))
 (.branch 37895
 (.branch 36873
 (.branch 36867
 (.branch 33832
 (.leaf 75)
 (.branch 33840
 (.leaf 76)
 (.leaf 77)))
 (.branch 36869
 (.leaf 78)
 (.branch 36870
 (.leaf 79)
 (.leaf 80))))
 (.branch 36900
 (.branch 36882
 (.leaf 81)
 (.branch 36888
 (.leaf 82)
 (.leaf 83)))
 (.branch 36904
 (.leaf 84)
 (.branch 36912
 (.leaf 85)
 (.leaf 86)))))
 (.branch 49170
 (.branch 49157
 (.branch 37944
 (.leaf 87)
 (.branch 49155
 (.leaf 88)
 (.leaf 89)))
 (.branch 49158
 (.leaf 90)
 (.branch 49161
 (.leaf 91)
 (.leaf 92))))
 (.branch 49192
 (.branch 49176
 (.leaf 93)
 (.branch 49188
 (.leaf 94)
 (.leaf 95)))
 (.branch 53255
 (.branch 49200
 (.leaf 96)
 (.leaf 97))
 (.branch 53304
 (.leaf 98)
 (.leaf 99))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixExtra05.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
theorem check_0000_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 0)) 0 2 (by decide +kernel)
theorem block_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 2 :=
  check_0000_0000
theorem check_0001_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 1)) 0 2 (by decide +kernel)
theorem block_0001 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 2 :=
  check_0001_0000
theorem check_0002_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 2)) 0 2 (by decide +kernel)
theorem block_0002 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 2 :=
  check_0002_0000
theorem check_0003_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 3)) 0 2 (by decide +kernel)
theorem block_0003 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 2 :=
  check_0003_0000
theorem check_0004_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 0 2 (by decide +kernel)
theorem block_0004 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 2 :=
  check_0004_0000
theorem check_0005_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 0 2 (by decide +kernel)
theorem block_0005 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 2 :=
  check_0005_0000
theorem check_0006_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 0 2 (by decide +kernel)
theorem block_0006 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 2 :=
  check_0006_0000
theorem check_0007_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 0 2 (by decide +kernel)
theorem block_0007 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 2 :=
  check_0007_0000
theorem check_0008_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 0 2 (by decide +kernel)
theorem block_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 2 :=
  check_0008_0000
theorem check_0009_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 0 2 (by decide +kernel)
theorem block_0009 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 2 :=
  check_0009_0000
theorem check_0010_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 0 2 (by decide +kernel)
theorem block_0010 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 2 :=
  check_0010_0000
theorem check_0011_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 0 2 (by decide +kernel)
theorem block_0011 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 2 :=
  check_0011_0000
theorem check_0012_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 0 2 (by decide +kernel)
theorem block_0012 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 2 :=
  check_0012_0000
theorem check_0013_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 13)) 0 2 (by decide +kernel)
theorem block_0013 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 2 :=
  check_0013_0000
theorem check_0014_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 14)) 0 2 (by decide +kernel)
theorem block_0014 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 2 :=
  check_0014_0000
theorem check_0015_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 15)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 15)) 0 2 (by decide +kernel)
theorem block_0015 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 15)) 0 2 :=
  check_0015_0000
theorem check_0016_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 16)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 16)) 0 2 (by decide +kernel)
theorem block_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 16)) 0 2 :=
  check_0016_0000
theorem check_0017_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 17)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 17)) 0 2 (by decide +kernel)
theorem block_0017 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 17)) 0 2 :=
  check_0017_0000
theorem check_0018_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 18)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 18)) 0 2 (by decide +kernel)
theorem block_0018 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 18)) 0 2 :=
  check_0018_0000
theorem check_0019_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 19)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 19)) 0 2 (by decide +kernel)
theorem block_0019 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 19)) 0 2 :=
  check_0019_0000
theorem check_0020_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 20)) 0 2 (by decide +kernel)
theorem block_0020 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 2 :=
  check_0020_0000
theorem check_0021_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 21)) 0 2 (by decide +kernel)
theorem block_0021 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 2 :=
  check_0021_0000
theorem check_0022_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 22)) 0 2 (by decide +kernel)
theorem block_0022 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 2 :=
  check_0022_0000
theorem check_0023_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 23)) 0 2 (by decide +kernel)
theorem block_0023 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 2 :=
  check_0023_0000
theorem check_0024_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 24)) 0 2 (by decide +kernel)
theorem block_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 2 :=
  check_0024_0000
theorem check_0025_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 0 2 (by decide +kernel)
theorem block_0025 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 2 :=
  check_0025_0000
theorem check_0026_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 26)) 0 2 (by decide +kernel)
theorem block_0026 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 2 :=
  check_0026_0000
theorem check_0027_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 27)) 0 6 (by decide +kernel)
theorem block_0027 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 6 :=
  check_0027_0000
theorem check_0028_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 28)) 0 6 (by decide +kernel)
theorem block_0028 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 6 :=
  check_0028_0000
theorem check_0029_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 29)) 0 2 (by decide +kernel)
theorem block_0029 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 2 :=
  check_0029_0000
theorem check_0030_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 30)) 0 2 (by decide +kernel)
theorem block_0030 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 2 :=
  check_0030_0000
theorem check_0031_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 31)) 0 2 (by decide +kernel)
theorem block_0031 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 2 :=
  check_0031_0000
theorem check_0032_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 32)) 0 2 (by decide +kernel)
theorem block_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 2 :=
  check_0032_0000
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 2 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 2 :=
  check_0033_0000
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 2 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 2 :=
  check_0034_0000
theorem check_0035_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 0 2 (by decide +kernel)
theorem block_0035 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 2 :=
  check_0035_0000
theorem check_0036_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 36)) 0 2 (by decide +kernel)
theorem block_0036 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 2 :=
  check_0036_0000
theorem check_0037_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 37)) 0 2 (by decide +kernel)
theorem block_0037 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 2 :=
  check_0037_0000
theorem check_0038_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 38)) 0 2 (by decide +kernel)
theorem block_0038 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 2 :=
  check_0038_0000
theorem check_0039_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 39)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 39)) 0 2 (by decide +kernel)
theorem block_0039 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 39)) 0 2 :=
  check_0039_0000
theorem check_0040_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 40)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 40)) 0 2 (by decide +kernel)
theorem block_0040 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 40)) 0 2 :=
  check_0040_0000
theorem check_0041_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 41)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 41)) 0 2 (by decide +kernel)
theorem block_0041 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 41)) 0 2 :=
  check_0041_0000
theorem check_0042_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 42)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 42)) 0 2 (by decide +kernel)
theorem block_0042 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 42)) 0 2 :=
  check_0042_0000
theorem check_0043_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 43)) 0 2 (by decide +kernel)
theorem block_0043 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 2 :=
  check_0043_0000
theorem check_0044_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 44)) 0 2 (by decide +kernel)
theorem block_0044 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 2 :=
  check_0044_0000
theorem check_0045_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 45)) 0 2 (by decide +kernel)
theorem block_0045 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 2 :=
  check_0045_0000
theorem check_0046_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 46)) 0 2 (by decide +kernel)
theorem block_0046 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 2 :=
  check_0046_0000
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 6 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 6 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
  check_0048_0000
theorem check_0049_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 49)) 0 2 (by decide +kernel)
theorem block_0049 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 2 :=
  check_0049_0000
theorem check_0050_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 50)) 0 2 (by decide +kernel)
theorem block_0050 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 2 :=
  check_0050_0000
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 2 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 2 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 2 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 2 :=
  check_0052_0000
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 2 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 2 :=
  check_0053_0000
theorem check_0054_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 54)) 0 2 (by decide +kernel)
theorem block_0054 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 2 :=
  check_0054_0000
theorem check_0055_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 55)) 0 2 (by decide +kernel)
theorem block_0055 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 2 :=
  check_0055_0000
theorem check_0056_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 0 2 (by decide +kernel)
theorem block_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 2 :=
  check_0056_0000
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 2 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 2 :=
  check_0057_0000
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 2 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 2 :=
  check_0058_0000
theorem check_0059_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 59)) 0 2 (by decide +kernel)
theorem block_0059 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 2 :=
  check_0059_0000
theorem check_0060_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 60)) 0 2 (by decide +kernel)
theorem block_0060 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 60)) 0 2 :=
  check_0060_0000
theorem check_0061_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 61)) 0 2 (by decide +kernel)
theorem block_0061 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 61)) 0 2 :=
  check_0061_0000
theorem check_0062_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 62)) 0 2 (by decide +kernel)
theorem block_0062 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 62)) 0 2 :=
  check_0062_0000
theorem check_0063_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 63)) 0 2 (by decide +kernel)
theorem block_0063 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 63)) 0 2 :=
  check_0063_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
theorem check_0064_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 0 2 (by decide +kernel)
theorem block_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 2 :=
  check_0064_0000
theorem check_0065_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 0 2 (by decide +kernel)
theorem block_0065 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 2 :=
  check_0065_0000
theorem check_0066_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 66)) 0 2 (by decide +kernel)
theorem block_0066 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 2 :=
  check_0066_0000
theorem check_0067_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 67)) 0 6 (by decide +kernel)
theorem block_0067 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 6 :=
  check_0067_0000
theorem check_0068_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 68)) 0 6 (by decide +kernel)
theorem block_0068 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 6 :=
  check_0068_0000
theorem check_0069_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 69)) 0 2 (by decide +kernel)
theorem block_0069 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 69)) 0 2 :=
  check_0069_0000
theorem check_0070_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 70)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 70)) 0 2 (by decide +kernel)
theorem block_0070 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 70)) 0 2 :=
  check_0070_0000
theorem check_0071_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 71)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 71)) 0 2 (by decide +kernel)
theorem block_0071 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 71)) 0 2 :=
  check_0071_0000
theorem check_0072_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 0 2 (by decide +kernel)
theorem block_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 2 :=
  check_0072_0000
theorem check_0073_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 73)) 0 2 (by decide +kernel)
theorem block_0073 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 2 :=
  check_0073_0000
theorem check_0074_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 74)) 0 2 (by decide +kernel)
theorem block_0074 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 2 :=
  check_0074_0000
theorem check_0075_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 75)) 0 2 (by decide +kernel)
theorem block_0075 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 2 :=
  check_0075_0000
theorem check_0076_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 76)) 0 2 (by decide +kernel)
theorem block_0076 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 2 :=
  check_0076_0000
theorem check_0077_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 0 2 (by decide +kernel)
theorem block_0077 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 2 :=
  check_0077_0000
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 2 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 2 :=
  check_0078_0000
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 2 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 2 :=
  check_0079_0000
theorem check_0080_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 80)) 0 2 (by decide +kernel)
theorem block_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 2 :=
  check_0080_0000
theorem check_0081_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 81)) 0 2 (by decide +kernel)
theorem block_0081 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 2 :=
  check_0081_0000
theorem check_0082_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 82)) 0 2 (by decide +kernel)
theorem block_0082 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 2 :=
  check_0082_0000
theorem check_0083_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 83)) 0 2 (by decide +kernel)
theorem block_0083 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 2 :=
  check_0083_0000
theorem check_0084_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 84)) 0 2 (by decide +kernel)
theorem block_0084 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 2 :=
  check_0084_0000
theorem check_0085_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 85)) 0 2 (by decide +kernel)
theorem block_0085 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 2 :=
  check_0085_0000
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 2 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 2 :=
  check_0086_0000
theorem check_0087_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 0 6 (by decide +kernel)
theorem block_0087 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 6 :=
  check_0087_0000
theorem check_0088_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 88)) 0 6 (by decide +kernel)
theorem block_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 6 :=
  check_0088_0000
theorem check_0089_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 0 2 (by decide +kernel)
theorem block_0089 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 2 :=
  check_0089_0000
theorem check_0090_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 0 2 (by decide +kernel)
theorem block_0090 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 2 :=
  check_0090_0000
theorem check_0091_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 0 2 (by decide +kernel)
theorem block_0091 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 2 :=
  check_0091_0000
theorem check_0092_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 92)) 0 2 (by decide +kernel)
theorem block_0092 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 2 :=
  check_0092_0000
theorem check_0093_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 93)) 0 2 (by decide +kernel)
theorem block_0093 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 2 :=
  check_0093_0000
theorem check_0094_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 94)) 0 2 (by decide +kernel)
theorem block_0094 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 2 :=
  check_0094_0000
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 2 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 2 :=
  check_0095_0000
theorem check_0096_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 96)) 0 2 (by decide +kernel)
theorem block_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 2 :=
  check_0096_0000
theorem check_0097_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 97)) 0 2 (by decide +kernel)
theorem block_0097 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 2 :=
  check_0097_0000
theorem check_0098_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 0 6 (by decide +kernel)
theorem block_0098 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 6 :=
  check_0098_0000
theorem check_0099_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 0 6 (by decide +kernel)
theorem block_0099 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 6 :=
  check_0099_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 32 :=
  FiniteChecks.interval_of_check validity 16 16 (by decide +kernel)
theorem metadata_validity_0032 : FiniteChecks.Interval validity 32 48 :=
  FiniteChecks.interval_of_check validity 32 16 (by decide +kernel)
theorem metadata_validity_0048 : FiniteChecks.Interval validity 48 64 :=
  FiniteChecks.interval_of_check validity 48 16 (by decide +kernel)
theorem metadata_validity_0064 : FiniteChecks.Interval validity 64 80 :=
  FiniteChecks.interval_of_check validity 64 16 (by decide +kernel)
theorem metadata_validity_0080 : FiniteChecks.Interval validity 80 96 :=
  FiniteChecks.interval_of_check validity 80 16 (by decide +kernel)
theorem metadata_validity_0096 : FiniteChecks.Interval validity 96 100 :=
  FiniteChecks.interval_of_check validity 96 4 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 100
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 80 100
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)
  (FiniteChecks.interval_append (validity) 80 96 100
  metadata_validity_0080
  metadata_validity_0096)))
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 32 :=
  FiniteChecks.interval_of_check symmetry 16 16 (by decide +kernel)
theorem metadata_symmetry_0032 : FiniteChecks.Interval symmetry 32 48 :=
  FiniteChecks.interval_of_check symmetry 32 16 (by decide +kernel)
theorem metadata_symmetry_0048 : FiniteChecks.Interval symmetry 48 64 :=
  FiniteChecks.interval_of_check symmetry 48 16 (by decide +kernel)
theorem metadata_symmetry_0064 : FiniteChecks.Interval symmetry 64 80 :=
  FiniteChecks.interval_of_check symmetry 64 16 (by decide +kernel)
theorem metadata_symmetry_0080 : FiniteChecks.Interval symmetry 80 96 :=
  FiniteChecks.interval_of_check symmetry 80 16 (by decide +kernel)
theorem metadata_symmetry_0096 : FiniteChecks.Interval symmetry 96 100 :=
  FiniteChecks.interval_of_check symmetry 96 4 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 100
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 80 100
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)
  (FiniteChecks.interval_append (symmetry) 80 96 100
  metadata_symmetry_0080
  metadata_symmetry_0096)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
