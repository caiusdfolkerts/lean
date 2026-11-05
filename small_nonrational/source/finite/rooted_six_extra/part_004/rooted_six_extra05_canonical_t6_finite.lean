module
prelude
public import RootedSixExtra05
public import RawKindedFacePlacement
public import RootedSixExtra05OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
open ConcreteGrowth
abbrev blockCount : Nat := 94
noncomputable def template : Cell := ⟨9, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra05.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 47
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 75367552))
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 77726884)))
 (.branch 3
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 80086216))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 84018436))
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 86377768)))))
 (.branch 8
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 88737100))
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 92669320))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 95028652))))
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 98960872))
 (.branch 10
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 75695233))
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 78054565))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 80413897))
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 84346117))
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 86705449))))
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 89064781))
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 92997001))
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 95356333)))))
 (.branch 20
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 99288553))
 (.branch 19
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 75629695))
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 77989027))))
 (.branch 21
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 80348359))
 (.branch 22
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 84280579))
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 86639911)))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 88999243))
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 92931463))
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 95290795))))
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 99223015))
 (.branch 28
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 1525687682946372466721293548))
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 1902878294138109299393693220)))))
 (.branch 32
 (.branch 30
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 77595798))
 (.branch 31
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 79955130))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 82314462))))
 (.branch 33
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 86246682))
 (.branch 34
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 88606014))
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 90965346))))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 94897566))
 (.branch 37
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 97256898))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 101189118))))
 (.branch 39
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 77595798))
 (.branch 40
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 79955130))
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 82314462)))))
 (.branch 44
 (.branch 42
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 86246682))
 (.branch 43
 (.leaf (⟨2, 4, 5448000, 5325600, 357029148225, 361625650950⟩, 88606014))
 (.leaf (⟨2, 4, 5448000, 5325600, 352465745475, 361625618550⟩, 90965346))))
 (.branch 45
 (.leaf (⟨2, 4, 5448000, 5325600, 288041236050, 361617784950⟩, 94897566))
 (.branch 46
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 97256898))
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 101189118))))))))
 (.branch 70
 (.branch 58
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 76547218))
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 78906550)))
 (.branch 50
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 81265882))
 (.branch 51
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 85198102))
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 87557434)))))
 (.branch 55
 (.branch 53
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 89916766))
 (.branch 54
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 93848986))
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 96208318))))
 (.branch 56
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 100140538))
 (.branch 57
 (.leaf (⟨4, 4, 5391120, 5448720, 354745205520, 508225071120⟩, 12761221297145373745681689118940546316990395709531755279926688670671637739400608613144217220555437163842240512))
 (.leaf (⟨4, 4, 5391120, 5448720, 281730765600, 508219171200⟩, 13641938204154014272965507687401347153488727750006624064861536590633397211530885951853708938453476057910476800))))))
 (.branch 64
 (.branch 61
 (.branch 59
 (.leaf (⟨4, 4, 5391120, 5448720, 208716321825, 508218741000⟩, 14192386271034414602517894292689347676300185275303417055445816540609496881612309288547141262139750366703124480))
 (.branch 60
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 77661335))
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 80020667))))
 (.branch 62
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 82379999))
 (.branch 63
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 86312219))
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 88671551)))))
 (.branch 67
 (.branch 65
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 91030883))
 (.branch 66
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 94963103))
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 97322435))))
 (.branch 68
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 101254655))
 (.branch 69
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 76874899))
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 79234231)))))))
 (.branch 82
 (.branch 76
 (.branch 73
 (.branch 71
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 81593563))
 (.branch 72
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 85525783))
 (.leaf (⟨2, 4, 4329555, 1377330, 357029148225, 361625650950⟩, 87885115))))
 (.branch 74
 (.leaf (⟨2, 4, 4329555, 1377330, 352465745475, 361625618550⟩, 90244447))
 (.branch 75
 (.leaf (⟨2, 4, 4329555, 1377330, 288041236050, 361617784950⟩, 94176667))
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 96535999)))))
 (.branch 79
 (.branch 77
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 100468219))
 (.branch 78
 (.leaf (⟨4, 4, 4215585, 3481860, 354745205520, 508225071120⟩, 836306619555430917163933940434838783991122207968142866640258328665873587549001996001608107417313754540598280324462))
 (.leaf (⟨4, 4, 4215585, 3481860, 281730765600, 508219171200⟩, 894024402069680642575674702841183301404415317455704912793972896408271500300767385007041085274212711030425978406350))))
 (.branch 80
 (.leaf (⟨4, 4, 4215585, 3481860, 208716321825, 508218741000⟩, 930098016141086720958012679345148624787723510885431191640044501247270195770620753135436696434774558836568289707530))
 (.branch 81
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 76809361))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 79168693))))))
 (.branch 88
 (.branch 85
 (.branch 83
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 81528025))
 (.branch 84
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 85460245))
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 87819577))))
 (.branch 86
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 90178909))
 (.branch 87
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 94111129))
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 96470461)))))
 (.branch 91
 (.branch 89
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 100402681))
 (.branch 90
 (.leaf (⟨4, 4, 3232800, 3297600, 354745205520, 508225071120⟩, 836306619555430917163933940434838783991122207968142866640258328665873587549001996001608107417313754540598280324462))
 (.leaf (⟨4, 4, 3232800, 3297600, 281730765600, 508219171200⟩, 894024402069680642575674702841183301404415317455704912793972896408271500300767385007041085274212711030425978406350))))
 (.branch 92
 (.leaf (⟨4, 4, 3232800, 3297600, 208716321825, 508218741000⟩, 930098016141086720958012679345148624787723510885431191640044501247270195770620753135436696434774558836568289707530))
 (.branch 93
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 1525687682946372466721293548))
 (.leaf (⟨3, 4, 2164035, 2164035, 141893788995, 434917935495⟩, 1902878294138109299393693220)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2170 :=
  Fin.ofNat 2170 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 24579
 (.branch 6168
 (.branch 5126
 (.branch 3096
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3081
 (.leaf 2)
 (.branch 3090
 (.leaf 3)
 (.leaf 4))))
 (.branch 3120
 (.branch 3108
 (.leaf 5)
 (.branch 3112
 (.leaf 6)
 (.leaf 7)))
 (.branch 5123
 (.leaf 8)
 (.branch 5125
 (.leaf 9)
 (.leaf 10)))))
 (.branch 5168
 (.branch 5144
 (.branch 5129
 (.leaf 11)
 (.branch 5138
 (.leaf 12)
 (.leaf 13)))
 (.branch 5156
 (.leaf 14)
 (.branch 5160
 (.leaf 15)
 (.leaf 16))))
 (.branch 6150
 (.branch 6147
 (.leaf 17)
 (.branch 6149
 (.leaf 18)
 (.leaf 19)))
 (.branch 6153
 (.leaf 20)
 (.branch 6162
 (.leaf 21)
 (.leaf 22))))))
 (.branch 10276
 (.branch 10243
 (.branch 6192
 (.branch 6180
 (.leaf 23)
 (.branch 6184
 (.leaf 24)
 (.leaf 25)))
 (.branch 7175
 (.leaf 26)
 (.branch 7224
 (.leaf 27)
 (.leaf 28))))
 (.branch 10249
 (.branch 10245
 (.leaf 29)
 (.branch 10246
 (.leaf 30)
 (.leaf 31)))
 (.branch 10258
 (.leaf 32)
 (.branch 10264
 (.leaf 33)
 (.leaf 34)))))
 (.branch 17417
 (.branch 17411
 (.branch 10280
 (.leaf 35)
 (.branch 10288
 (.leaf 36)
 (.leaf 37)))
 (.branch 17413
 (.leaf 38)
 (.branch 17414
 (.leaf 39)
 (.leaf 40))))
 (.branch 17444
 (.branch 17426
 (.leaf 41)
 (.branch 17432
 (.leaf 42)
 (.leaf 43)))
 (.branch 17448
 (.leaf 44)
 (.branch 17456
 (.leaf 45)
 (.leaf 46)))))))
 (.branch 40966
 (.branch 27702
 (.branch 24600
 (.branch 24582
 (.branch 24581
 (.leaf 47)
 (.leaf 48))
 (.branch 24585
 (.leaf 49)
 (.branch 24594
 (.leaf 50)
 (.leaf 51))))
 (.branch 24624
 (.branch 24612
 (.leaf 52)
 (.branch 24616
 (.leaf 53)
 (.leaf 54)))
 (.branch 27675
 (.leaf 55)
 (.branch 27693
 (.leaf 56)
 (.leaf 57)))))
 (.branch 36888
 (.branch 36870
 (.branch 36867
 (.leaf 58)
 (.branch 36869
 (.leaf 59)
 (.leaf 60)))
 (.branch 36873
 (.leaf 61)
 (.branch 36882
 (.leaf 62)
 (.leaf 63))))
 (.branch 36912
 (.branch 36900
 (.leaf 64)
 (.branch 36904
 (.leaf 65)
 (.leaf 66)))
 (.branch 40963
 (.leaf 67)
 (.branch 40965
 (.leaf 68)
 (.leaf 69))))))
 (.branch 49158
 (.branch 41008
 (.branch 40984
 (.branch 40969
 (.leaf 70)
 (.branch 40978
 (.leaf 71)
 (.leaf 72)))
 (.branch 40996
 (.leaf 73)
 (.branch 41000
 (.leaf 74)
 (.leaf 75))))
 (.branch 47158
 (.branch 47131
 (.leaf 76)
 (.branch 47149
 (.leaf 77)
 (.leaf 78)))
 (.branch 49155
 (.leaf 79)
 (.branch 49157
 (.leaf 80)
 (.leaf 81)))))
 (.branch 49200
 (.branch 49176
 (.branch 49161
 (.leaf 82)
 (.branch 49170
 (.leaf 83)
 (.leaf 84)))
 (.branch 49188
 (.leaf 85)
 (.branch 49192
 (.leaf 86)
 (.leaf 87))))
 (.branch 54326
 (.branch 54299
 (.leaf 88)
 (.branch 54317
 (.leaf 89)
 (.leaf 90)))
 (.branch 57351
 (.leaf 91)
 (.branch 57400
 (.leaf 92)
 (.leaf 93))))))))
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
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
theorem check_0056_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 0 8 (by decide +kernel)
theorem check_0056_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 8 8 (by decide +kernel)
theorem check_0056_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 16 8 (by decide +kernel)
theorem block_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 56)) 0 8 24
  check_0056_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 56)) 8 16 24
  check_0056_0008
  check_0056_0016))
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 8 (by decide +kernel)
theorem check_0057_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 8 8 (by decide +kernel)
theorem check_0057_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 16 8 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 57)) 0 8 24
  check_0057_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 57)) 8 16 24
  check_0057_0008
  check_0057_0016))
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 8 (by decide +kernel)
theorem check_0058_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 8 8 (by decide +kernel)
theorem check_0058_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 16 8 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 58)) 0 8 24
  check_0058_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 58)) 8 16 24
  check_0058_0008
  check_0058_0016))
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
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
theorem check_0077_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 0 8 (by decide +kernel)
theorem check_0077_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 8 8 (by decide +kernel)
theorem check_0077_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 16 8 (by decide +kernel)
theorem block_0077 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 77)) 0 8 24
  check_0077_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 77)) 8 16 24
  check_0077_0008
  check_0077_0016))
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 8 (by decide +kernel)
theorem check_0078_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 8 8 (by decide +kernel)
theorem check_0078_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 16 8 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 78)) 0 8 24
  check_0078_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 78)) 8 16 24
  check_0078_0008
  check_0078_0016))
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 8 (by decide +kernel)
theorem check_0079_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 8 8 (by decide +kernel)
theorem check_0079_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 16 8 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 79)) 0 8 24
  check_0079_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 79)) 8 16 24
  check_0079_0008
  check_0079_0016))
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
theorem check_0087_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 87)) 0 2 (by decide +kernel)
theorem block_0087 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 87)) 0 2 :=
  check_0087_0000
theorem check_0088_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 88)) 0 2 (by decide +kernel)
theorem block_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 88)) 0 2 :=
  check_0088_0000
theorem check_0089_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 0 8 (by decide +kernel)
theorem check_0089_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 8 8 (by decide +kernel)
theorem check_0089_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 16 8 (by decide +kernel)
theorem block_0089 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 89)) 0 8 24
  check_0089_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 89)) 8 16 24
  check_0089_0008
  check_0089_0016))
theorem check_0090_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 0 8 (by decide +kernel)
theorem check_0090_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 8 8 (by decide +kernel)
theorem check_0090_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 16 8 (by decide +kernel)
theorem block_0090 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 90)) 0 8 24
  check_0090_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 90)) 8 16 24
  check_0090_0008
  check_0090_0016))
theorem check_0091_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 0 8 (by decide +kernel)
theorem check_0091_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 8 8 (by decide +kernel)
theorem check_0091_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 16 8 (by decide +kernel)
theorem block_0091 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 91)) 0 8 24
  check_0091_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 91)) 8 16 24
  check_0091_0008
  check_0091_0016))
theorem check_0092_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 92)) 0 6 (by decide +kernel)
theorem block_0092 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 6 :=
  check_0092_0000
theorem check_0093_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 93)) 0 6 (by decide +kernel)
theorem block_0093 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 6 :=
  check_0093_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
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
theorem metadata_validity_0080 : FiniteChecks.Interval validity 80 94 :=
  FiniteChecks.interval_of_check validity 80 14 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 94
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 64 94
  metadata_validity_0048
  (FiniteChecks.interval_append (validity) 64 80 94
  metadata_validity_0064
  metadata_validity_0080)))
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
theorem metadata_symmetry_0080 : FiniteChecks.Interval symmetry 80 94 :=
  FiniteChecks.interval_of_check symmetry 80 14 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 94
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 64 94
  metadata_symmetry_0048
  (FiniteChecks.interval_append (symmetry) 64 80 94
  metadata_symmetry_0064
  metadata_symmetry_0080)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
