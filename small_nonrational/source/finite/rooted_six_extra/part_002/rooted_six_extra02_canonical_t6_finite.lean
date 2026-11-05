module
prelude
public import RootedSixExtra02
public import RawKindedFacePlacement
public import RootedSixExtra02OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
open ConcreteGrowth
abbrev blockCount : Nat := 104
noncomputable def template : Cell := ⟨9, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra02.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 52
 (.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 350491878))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 352851210))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 355210542))))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 359142762))
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 361502094))
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 365434314)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 367793646))
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 288309671505, 361617786630⟩, 371725866))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 374085198))))
 (.branch 11
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 378017418))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 350819559)))
 (.branch 12
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 353178891))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 355538223))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 359470443))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 361829775))
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 365761995))))
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 368121327))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 288309671505, 361617786630⟩, 372053547))
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 374412879)))))
 (.branch 22
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 378345099))
 (.branch 21
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 350754021))
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 353113353))))
 (.branch 24
 (.branch 23
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 355472685))
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 359404905)))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 361764237))
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 365696457)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 368055789))
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 288309671505, 361617786630⟩, 371988009))
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 374347341))))
 (.branch 30
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 378279561))
 (.branch 31
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 6600835714301857157614671186))
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 6716894363899314644590794162)))))
 (.branch 35
 (.branch 33
 (.leaf (⟨3, 4, 5517840, 5517840, 283627709745, 434918463495⟩, 6949011663094229618543040114))
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 7050562981492004919647147718))
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 352720124))))
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 355079456))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 357438788)))
 (.branch 38
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 361371008))
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 363730340))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 367662560))
 (.branch 41
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 370021892))
 (.leaf (⟨2, 4, 5513265, 5509890, 288309671505, 361617786630⟩, 373954112))))
 (.branch 43
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 376313444))
 (.branch 44
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 380245664))
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 352720124)))))
 (.branch 48
 (.branch 46
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 355079456))
 (.branch 47
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 357438788))
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 361371008))))
 (.branch 50
 (.branch 49
 (.leaf (⟨2, 4, 5448000, 5325600, 361324115505, 361626081030⟩, 363730340))
 (.leaf (⟨2, 4, 5448000, 5325600, 356760712770, 361625649270⟩, 367662560)))
 (.branch 51
 (.leaf (⟨2, 4, 5448000, 5325600, 352465745475, 361625618550⟩, 370021892))
 (.leaf (⟨2, 4, 5448000, 5325600, 288309671505, 361617786630⟩, 373954112))))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.branch 53
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 376313444))
 (.branch 54
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 380245664))
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 351671544))))
 (.branch 56
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 354030876))
 (.branch 57
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 356390208))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 360322428)))))
 (.branch 61
 (.branch 59
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 362681760))
 (.branch 60
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 366613980))
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 368973312))))
 (.branch 63
 (.branch 62
 (.leaf (⟨2, 4, 5378115, 5309490, 288309671505, 361617786630⟩, 372905532))
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 375264864)))
 (.branch 64
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 379197084))
 (.leaf (⟨4, 4, 5391120, 5448720, 350450238240, 508225069440⟩, 51824685776757783799582725207545650085843498088094164511724422453975510992845618073821464458158037277827137536))))))
 (.branch 71
 (.branch 68
 (.branch 66
 (.leaf (⟨4, 4, 5391120, 5448720, 208716321825, 508218741000⟩, 3490122161408550484842729882124703067080491314245943016738805903975471898814954855653855637451788252029135513196204))
 (.branch 67
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 352785661))
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 355144993))))
 (.branch 69
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 357504325))
 (.branch 70
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 361436545))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 363795877)))))
 (.branch 74
 (.branch 72
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 367728097))
 (.branch 73
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 370087429))
 (.leaf (⟨2, 4, 4395090, 1392690, 288309671505, 361617786630⟩, 374019649))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 376378981))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 380311201)))
 (.branch 77
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 351999225))
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 354358557)))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 356717889))
 (.branch 80
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 360650109))
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 363009441))))
 (.branch 82
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 366941661))
 (.branch 83
 (.leaf (⟨2, 4, 4329555, 1377330, 352465745475, 361625618550⟩, 369300993))
 (.leaf (⟨2, 4, 4329555, 1377330, 288309671505, 361617786630⟩, 373233213)))))
 (.branch 87
 (.branch 85
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 375592545))
 (.branch 86
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 379524765))
 (.leaf (⟨4, 4, 4215585, 3481860, 350450238240, 508225069440⟩, 3396330764822882279697185672999577900093227001697717788749806552073481009392929354180083312778519553849830972331536))))
 (.branch 89
 (.branch 88
 (.leaf (⟨4, 4, 4215585, 3481860, 208716321825, 508218741000⟩, 53255037863289460502491217222746100054606601866811926726756173747190030296695317876637788196560861946155106304))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 351933687)))
 (.branch 90
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 354293019))
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 356652351))))))
 (.branch 97
 (.branch 94
 (.branch 92
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 360584571))
 (.branch 93
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 362943903))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 366876123))))
 (.branch 95
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 369235455))
 (.branch 96
 (.leaf (⟨2, 4, 3280980, 1070130, 288309671505, 361617786630⟩, 373167675))
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 375527007)))))
 (.branch 100
 (.branch 98
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 379459227))
 (.branch 99
 (.leaf (⟨4, 4, 3232800, 3297600, 350450238240, 508225069440⟩, 3396330764822882279697185672999577900093227001697717788749806552073481009392929354180083312778519553849830972331536))
 (.leaf (⟨4, 4, 3232800, 3297600, 208716321825, 508218741000⟩, 53255037863289460502491217222746100054606601866811926726756173747190030296695317876637788196560861946155106304))))
 (.branch 102
 (.branch 101
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 6600835714301857157614671186))
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 6716894363899314644590794162)))
 (.branch 103
 (.leaf (⟨3, 4, 2164035, 2164035, 283627709745, 434918463495⟩, 6949011663094229618543040114))
 (.leaf (⟨3, 4, 2164035, 2164035, 141893788995, 434917935495⟩, 7050562981492004919647147718)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 6620 :=
  Fin.ofNat 6620 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 17448
 (.branch 6168
 (.branch 5129
 (.branch 3096
 (.branch 3081
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3082
 (.leaf 3)
 (.branch 3092
 (.leaf 4)
 (.leaf 5))))
 (.branch 3120
 (.branch 3106
 (.leaf 6)
 (.branch 3112
 (.leaf 7)
 (.leaf 8)))
 (.branch 5125
 (.branch 5123
 (.leaf 9)
 (.leaf 10))
 (.branch 5126
 (.leaf 11)
 (.leaf 12)))))
 (.branch 5168
 (.branch 5144
 (.branch 5130
 (.leaf 13)
 (.branch 5140
 (.leaf 14)
 (.leaf 15)))
 (.branch 5154
 (.leaf 16)
 (.branch 5160
 (.leaf 17)
 (.leaf 18))))
 (.branch 6150
 (.branch 6147
 (.leaf 19)
 (.branch 6149
 (.leaf 20)
 (.leaf 21)))
 (.branch 6154
 (.branch 6153
 (.leaf 22)
 (.leaf 23))
 (.branch 6164
 (.leaf 24)
 (.leaf 25))))))
 (.branch 10260
 (.branch 7210
 (.branch 6192
 (.branch 6178
 (.leaf 26)
 (.branch 6184
 (.leaf 27)
 (.leaf 28)))
 (.branch 7175
 (.leaf 29)
 (.branch 7179
 (.leaf 30)
 (.leaf 31))))
 (.branch 10245
 (.branch 7224
 (.leaf 32)
 (.branch 10243
 (.leaf 33)
 (.leaf 34)))
 (.branch 10249
 (.branch 10246
 (.leaf 35)
 (.leaf 36))
 (.branch 10250
 (.leaf 37)
 (.leaf 38)))))
 (.branch 17413
 (.branch 10280
 (.branch 10264
 (.leaf 39)
 (.branch 10274
 (.leaf 40)
 (.leaf 41)))
 (.branch 10288
 (.leaf 42)
 (.branch 17411
 (.leaf 43)
 (.leaf 44))))
 (.branch 17418
 (.branch 17414
 (.leaf 45)
 (.branch 17417
 (.leaf 46)
 (.leaf 47)))
 (.branch 17432
 (.branch 17428
 (.leaf 48)
 (.leaf 49))
 (.branch 17442
 (.leaf 50)
 (.leaf 51)))))))
 (.branch 40966
 (.branch 27702
 (.branch 24586
 (.branch 24581
 (.branch 17456
 (.leaf 52)
 (.branch 24579
 (.leaf 53)
 (.leaf 54)))
 (.branch 24582
 (.leaf 55)
 (.branch 24585
 (.leaf 56)
 (.leaf 57))))
 (.branch 24610
 (.branch 24596
 (.leaf 58)
 (.branch 24600
 (.leaf 59)
 (.leaf 60)))
 (.branch 24624
 (.branch 24616
 (.leaf 61)
 (.leaf 62))
 (.branch 27677
 (.leaf 63)
 (.leaf 64)))))
 (.branch 36884
 (.branch 36870
 (.branch 36867
 (.leaf 65)
 (.branch 36869
 (.leaf 66)
 (.leaf 67)))
 (.branch 36873
 (.leaf 68)
 (.branch 36874
 (.leaf 69)
 (.leaf 70))))
 (.branch 36904
 (.branch 36888
 (.leaf 71)
 (.branch 36898
 (.leaf 72)
 (.leaf 73)))
 (.branch 40963
 (.branch 36912
 (.leaf 74)
 (.leaf 75))
 (.branch 40965
 (.leaf 76)
 (.leaf 77))))))
 (.branch 49161
 (.branch 41000
 (.branch 40980
 (.branch 40969
 (.leaf 78)
 (.branch 40970
 (.leaf 79)
 (.leaf 80)))
 (.branch 40984
 (.leaf 81)
 (.branch 40994
 (.leaf 82)
 (.leaf 83))))
 (.branch 47158
 (.branch 41008
 (.leaf 84)
 (.branch 47133
 (.leaf 85)
 (.leaf 86)))
 (.branch 49157
 (.branch 49155
 (.leaf 87)
 (.leaf 88))
 (.branch 49158
 (.leaf 89)
 (.leaf 90)))))
 (.branch 49200
 (.branch 49176
 (.branch 49162
 (.leaf 91)
 (.branch 49172
 (.leaf 92)
 (.leaf 93)))
 (.branch 49186
 (.leaf 94)
 (.branch 49192
 (.leaf 95)
 (.leaf 96))))
 (.branch 57351
 (.branch 54301
 (.leaf 97)
 (.branch 54326
 (.leaf 98)
 (.leaf 99)))
 (.branch 57386
 (.branch 57355
 (.leaf 100)
 (.leaf 101))
 (.branch 57400
 (.leaf 102)
 (.leaf 103))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixExtra02.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra02.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
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
theorem check_0027_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 27)) 0 2 (by decide +kernel)
theorem block_0027 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 2 :=
  check_0027_0000
theorem check_0028_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 28)) 0 2 (by decide +kernel)
theorem block_0028 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 2 :=
  check_0028_0000
theorem check_0029_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 29)) 0 2 (by decide +kernel)
theorem block_0029 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 2 :=
  check_0029_0000
theorem check_0030_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 30)) 0 6 (by decide +kernel)
theorem block_0030 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 6 :=
  check_0030_0000
theorem check_0031_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 31)) 0 6 (by decide +kernel)
theorem block_0031 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 6 :=
  check_0031_0000
theorem check_0032_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 32)) 0 6 (by decide +kernel)
theorem block_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 6 :=
  check_0032_0000
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 6 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
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
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 2 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 2 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 2 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 2 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
theorem check_0064_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 0 8 (by decide +kernel)
theorem check_0064_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 8 8 (by decide +kernel)
theorem check_0064_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 64)) 16 8 (by decide +kernel)
theorem block_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 64)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 64)) 0 8 24
  check_0064_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 64)) 8 16 24
  check_0064_0008
  check_0064_0016))
theorem check_0065_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 0 8 (by decide +kernel)
theorem check_0065_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 8 8 (by decide +kernel)
theorem check_0065_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 65)) 16 8 (by decide +kernel)
theorem block_0065 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 65)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 65)) 0 8 24
  check_0065_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 65)) 8 16 24
  check_0065_0008
  check_0065_0016))
theorem check_0066_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 66)) 0 2 (by decide +kernel)
theorem block_0066 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 66)) 0 2 :=
  check_0066_0000
theorem check_0067_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 67)) 0 2 (by decide +kernel)
theorem block_0067 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 67)) 0 2 :=
  check_0067_0000
theorem check_0068_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 68)) 0 2 (by decide +kernel)
theorem block_0068 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 68)) 0 2 :=
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
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 8 (by decide +kernel)
theorem check_0086_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 8 8 (by decide +kernel)
theorem check_0086_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 16 8 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 86)) 0 8 24
  check_0086_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 86)) 8 16 24
  check_0086_0008
  check_0086_0016))
theorem check_0087_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 0 8 (by decide +kernel)
theorem check_0087_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 8 8 (by decide +kernel)
theorem check_0087_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 16 8 (by decide +kernel)
theorem block_0087 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 87)) 0 8 24
  check_0087_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 87)) 8 16 24
  check_0087_0008
  check_0087_0016))
theorem check_0088_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 88)) 0 2 (by decide +kernel)
theorem block_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 2 :=
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
theorem check_0098_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 0 8 (by decide +kernel)
theorem check_0098_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 8 8 (by decide +kernel)
theorem check_0098_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 16 8 (by decide +kernel)
theorem block_0098 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 98)) 0 8 24
  check_0098_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 98)) 8 16 24
  check_0098_0008
  check_0098_0016))
theorem check_0099_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 0 8 (by decide +kernel)
theorem check_0099_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 8 8 (by decide +kernel)
theorem check_0099_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 16 8 (by decide +kernel)
theorem block_0099 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 99)) 0 8 24
  check_0099_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 99)) 8 16 24
  check_0099_0008
  check_0099_0016))
theorem check_0100_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 100)) 0 6 (by decide +kernel)
theorem block_0100 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 6 :=
  check_0100_0000
theorem check_0101_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 101)) 0 6 (by decide +kernel)
theorem block_0101 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 6 :=
  check_0101_0000
theorem check_0102_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 102)) 0 6 (by decide +kernel)
theorem block_0102 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 6 :=
  check_0102_0000
theorem check_0103_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 103)) 0 6 (by decide +kernel)
theorem block_0103 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 6 :=
  check_0103_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
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
theorem metadata_validity_0096 : FiniteChecks.Interval validity 96 104 :=
  FiniteChecks.interval_of_check validity 96 8 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 104
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 80 104
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)
  (FiniteChecks.interval_append (validity) 80 96 104
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
theorem metadata_symmetry_0096 : FiniteChecks.Interval symmetry 96 104 :=
  FiniteChecks.interval_of_check symmetry 96 8 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 104
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 80 104
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)
  (FiniteChecks.interval_append (symmetry) 80 96 104
  metadata_symmetry_0080
  metadata_symmetry_0096)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra02.T6
