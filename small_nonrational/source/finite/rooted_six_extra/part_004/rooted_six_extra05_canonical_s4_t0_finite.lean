module
prelude
public import RootedSixExtra05
public import RawKindedFacePlacement
public import RootedSixExtra05OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
open ConcreteGrowth
abbrev blockCount : Nat := 87
noncomputable def template : Cell := ⟨1, 15, [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra05.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨0, 4, 12816, 12816, 361617201270, 215026792020⟩, 87))
 (.leaf (⟨1, 4, 12816, 12816, 361617786720, 288326448720⟩, 23)))
 (.branch 3
 (.leaf (⟨1, 4, 12816, 12816, 361616738145, 288326448645⟩, 39))
 (.branch 4
 (.leaf (⟨1, 4, 12816, 12816, 361599960930, 288326447205⟩, 49))
 (.leaf (⟨1, 4, 12816, 12816, 361331525475, 288326420325⟩, 69)))))
 (.branch 7
 (.branch 6
 (.leaf (⟨1, 4, 12816, 12816, 357036558180, 288325928805⟩, 79))
 (.leaf (⟨1, 4, 12816, 12816, 288317081445, 288317081445⟩, 83)))
 (.branch 8
 (.leaf (⟨1, 4, 12801, 12801, 361617786720, 288326448720⟩, 23))
 (.branch 9
 (.leaf (⟨1, 4, 12801, 12801, 361616738145, 288326448645⟩, 39))
 (.leaf (⟨1, 4, 12801, 12801, 361599960930, 288326447205⟩, 49))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (⟨1, 4, 12801, 12801, 361331525475, 288326420325⟩, 69))
 (.leaf (⟨1, 4, 12801, 12801, 357036558180, 288325928805⟩, 79)))
 (.branch 13
 (.leaf (⟨1, 4, 12801, 12801, 288317081445, 288317081445⟩, 83))
 (.branch 14
 (.leaf (⟨2, 4, 12816, 12816, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 12816, 12816, 361609328160, 361626104160⟩, 720907)))))
 (.branch 18
 (.branch 16
 (.leaf (⟨2, 4, 12816, 12816, 361592550945, 361626104070⟩, 1769499))
 (.branch 17
 (.leaf (⟨2, 4, 12816, 12816, 361340892720, 361626081120⟩, 1114129))
 (.leaf (⟨2, 4, 12816, 12816, 357029148225, 361625650950⟩, 2162721))))
 (.branch 19
 (.leaf (⟨2, 4, 12816, 12816, 352465745475, 361625618550⟩, 3735609))
 (.branch 20
 (.leaf (⟨2, 4, 12816, 12816, 288041236050, 361617784950⟩, 2818091))
 (.leaf (⟨2, 4, 12816, 12816, 283746268755, 361617754230⟩, 4128831)))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 4, 12816, 12816, 215026792020, 361617201270⟩, 4784201))
 (.leaf (⟨1, 4, 12546, 12321, 361617786720, 288326448720⟩, 23)))
 (.branch 24
 (.leaf (⟨1, 4, 12546, 12321, 361616738145, 288326448645⟩, 39))
 (.branch 25
 (.leaf (⟨1, 4, 12546, 12321, 361599960930, 288326447205⟩, 49))
 (.leaf (⟨1, 4, 12546, 12321, 361331525475, 288326420325⟩, 69)))))
 (.branch 29
 (.branch 27
 (.leaf (⟨1, 4, 12546, 12321, 357036558180, 288325928805⟩, 79))
 (.branch 28
 (.leaf (⟨1, 4, 12546, 12321, 288317081445, 288317081445⟩, 83))
 (.leaf (⟨2, 4, 12576, 12576, 361626105360, 361626105360⟩, 327685))))
 (.branch 30
 (.leaf (⟨2, 4, 12576, 12576, 361609328160, 361626104160⟩, 720907))
 (.branch 31
 (.leaf (⟨2, 4, 12576, 12576, 361592550945, 361626104070⟩, 1769499))
 (.leaf (⟨2, 4, 12576, 12576, 361340892720, 361626081120⟩, 1114129))))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 4, 12576, 12576, 357029148225, 361625650950⟩, 2162721))
 (.leaf (⟨2, 4, 12576, 12576, 352465745475, 361625618550⟩, 3735609)))
 (.branch 35
 (.leaf (⟨2, 4, 12576, 12576, 288041236050, 361617784950⟩, 2818091))
 (.branch 36
 (.leaf (⟨2, 4, 12576, 12576, 283746268755, 361617754230⟩, 4128831))
 (.leaf (⟨2, 4, 12576, 12576, 215026792020, 361617201270⟩, 4784201)))))
 (.branch 40
 (.branch 38
 (.leaf (⟨2, 4, 12321, 12546, 361626105360, 361626105360⟩, 327685))
 (.branch 39
 (.leaf (⟨2, 4, 12321, 12546, 361609328160, 361626104160⟩, 720907))
 (.leaf (⟨2, 4, 12321, 12546, 361592550945, 361626104070⟩, 1769499))))
 (.branch 41
 (.leaf (⟨2, 4, 12321, 12546, 361340892720, 361626081120⟩, 1114129))
 (.branch 42
 (.leaf (⟨2, 4, 12321, 12546, 357029148225, 361625650950⟩, 2162721))
 (.leaf (⟨2, 4, 12321, 12546, 352465745475, 361625618550⟩, 3735609))))))))
 (.branch 65
 (.branch 54
 (.branch 48
 (.branch 45
 (.branch 44
 (.leaf (⟨2, 4, 12321, 12546, 288041236050, 361617784950⟩, 2818091))
 (.leaf (⟨2, 4, 12321, 12546, 283746268755, 361617754230⟩, 4128831)))
 (.branch 46
 (.leaf (⟨2, 4, 12321, 12546, 215026792020, 361617201270⟩, 4784201))
 (.branch 47
 (.leaf (⟨3, 4, 12816, 12816, 361742426640, 434925761040⟩, 1208944266640182156001281))
 (.leaf (⟨3, 4, 12816, 12816, 141893788995, 434917935495⟩, 64074046131929654268067893)))))
 (.branch 51
 (.branch 49
 (.leaf (⟨1, 4, 8451, 801, 361617786720, 288326448720⟩, 23))
 (.branch 50
 (.leaf (⟨1, 4, 8451, 801, 361616738145, 288326448645⟩, 39))
 (.leaf (⟨1, 4, 8451, 801, 361599960930, 288326447205⟩, 49))))
 (.branch 52
 (.leaf (⟨1, 4, 8451, 801, 361331525475, 288326420325⟩, 69))
 (.branch 53
 (.leaf (⟨1, 4, 8451, 801, 357036558180, 288325928805⟩, 79))
 (.leaf (⟨1, 4, 8451, 801, 288317081445, 288317081445⟩, 83))))))
 (.branch 59
 (.branch 56
 (.branch 55
 (.leaf (⟨2, 4, 8496, 4896, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 8496, 4896, 361609328160, 361626104160⟩, 720907)))
 (.branch 57
 (.leaf (⟨2, 4, 8496, 4896, 361592550945, 361626104070⟩, 1769499))
 (.branch 58
 (.leaf (⟨2, 4, 8496, 4896, 361340892720, 361626081120⟩, 1114129))
 (.leaf (⟨2, 4, 8496, 4896, 357029148225, 361625650950⟩, 2162721)))))
 (.branch 62
 (.branch 60
 (.leaf (⟨2, 4, 8496, 4896, 352465745475, 361625618550⟩, 3735609))
 (.branch 61
 (.leaf (⟨2, 4, 8496, 4896, 288041236050, 361617784950⟩, 2818091))
 (.leaf (⟨2, 4, 8496, 4896, 283746268755, 361617754230⟩, 4128831))))
 (.branch 63
 (.leaf (⟨2, 4, 8496, 4896, 215026792020, 361617201270⟩, 4784201))
 (.branch 64
 (.leaf (⟨2, 4, 8241, 4866, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 8241, 4866, 361609328160, 361626104160⟩, 720907)))))))
 (.branch 76
 (.branch 70
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 4, 8241, 4866, 361592550945, 361626104070⟩, 1769499))
 (.leaf (⟨2, 4, 8241, 4866, 361340892720, 361626081120⟩, 1114129)))
 (.branch 68
 (.leaf (⟨2, 4, 8241, 4866, 357029148225, 361625650950⟩, 2162721))
 (.branch 69
 (.leaf (⟨2, 4, 8241, 4866, 352465745475, 361625618550⟩, 3735609))
 (.leaf (⟨2, 4, 8241, 4866, 288041236050, 361617784950⟩, 2818091)))))
 (.branch 73
 (.branch 71
 (.leaf (⟨2, 4, 8241, 4866, 283746268755, 361617754230⟩, 4128831))
 (.branch 72
 (.leaf (⟨2, 4, 8241, 4866, 215026792020, 361617201270⟩, 4784201))
 (.leaf (⟨3, 4, 8976, 8976, 361742426640, 434925761040⟩, 1208944266640182156001281))))
 (.branch 74
 (.leaf (⟨3, 4, 8976, 8976, 141893788995, 434917935495⟩, 64074046131929654268067893))
 (.branch 75
 (.leaf (⟨2, 4, 4146, 4146, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 4146, 4146, 361609328160, 361626104160⟩, 720907))))))
 (.branch 81
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 4146, 4146, 361592550945, 361626104070⟩, 1769499))
 (.leaf (⟨2, 4, 4146, 4146, 361340892720, 361626081120⟩, 1114129)))
 (.branch 79
 (.leaf (⟨2, 4, 4146, 4146, 357029148225, 361625650950⟩, 2162721))
 (.branch 80
 (.leaf (⟨2, 4, 4146, 4146, 352465745475, 361625618550⟩, 3735609))
 (.leaf (⟨2, 4, 4146, 4146, 288041236050, 361617784950⟩, 2818091)))))
 (.branch 84
 (.branch 82
 (.leaf (⟨2, 4, 4146, 4146, 283746268755, 361617754230⟩, 4128831))
 (.branch 83
 (.leaf (⟨2, 4, 4146, 4146, 215026792020, 361617201270⟩, 4784201))
 (.leaf (⟨3, 4, 4896, 8496, 361742426640, 434925761040⟩, 1208944266640182156001281))))
 (.branch 85
 (.leaf (⟨3, 4, 4896, 8496, 141893788995, 434917935495⟩, 64074046131929654268067893))
 (.branch 86
 (.leaf (⟨3, 4, 801, 8451, 361742426640, 434925761040⟩, 1208944266640182156001281))
 (.leaf (⟨3, 4, 801, 8451, 141893788995, 434917935495⟩, 64074046131929654268067893)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2170 :=
  Fin.ofNat 2170 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 6180
 (.branch 3120
 (.branch 2056
 (.branch 1040
 (.branch 1026
 (.branch 1025
 (.leaf 0)
 (.leaf 1))
 (.branch 1028
 (.leaf 2)
 (.branch 1032
 (.leaf 3)
 (.leaf 4))))
 (.branch 2049
 (.branch 1056
 (.leaf 5)
 (.leaf 6))
 (.branch 2050
 (.leaf 7)
 (.branch 2052
 (.leaf 8)
 (.leaf 9)))))
 (.branch 3078
 (.branch 2080
 (.branch 2064
 (.leaf 10)
 (.leaf 11))
 (.branch 3075
 (.leaf 12)
 (.branch 3077
 (.leaf 13)
 (.leaf 14))))
 (.branch 3096
 (.branch 3081
 (.leaf 15)
 (.branch 3090
 (.leaf 16)
 (.leaf 17)))
 (.branch 3108
 (.leaf 18)
 (.branch 3112
 (.leaf 19)
 (.leaf 20))))))
 (.branch 5138
 (.branch 4112
 (.branch 4098
 (.branch 4097
 (.leaf 21)
 (.leaf 22))
 (.branch 4100
 (.leaf 23)
 (.branch 4104
 (.leaf 24)
 (.leaf 25))))
 (.branch 5125
 (.branch 4128
 (.leaf 26)
 (.branch 5123
 (.leaf 27)
 (.leaf 28)))
 (.branch 5126
 (.leaf 29)
 (.branch 5129
 (.leaf 30)
 (.leaf 31)))))
 (.branch 6147
 (.branch 5156
 (.branch 5144
 (.leaf 32)
 (.leaf 33))
 (.branch 5160
 (.leaf 34)
 (.branch 5168
 (.leaf 35)
 (.leaf 36))))
 (.branch 6153
 (.branch 6149
 (.leaf 37)
 (.branch 6150
 (.leaf 38)
 (.leaf 39)))
 (.branch 6162
 (.leaf 40)
 (.branch 6168
 (.leaf 41)
 (.leaf 42)))))))
 (.branch 10246
 (.branch 9219
 (.branch 8193
 (.branch 6192
 (.branch 6184
 (.leaf 43)
 (.leaf 44))
 (.branch 7175
 (.leaf 45)
 (.branch 7224
 (.leaf 46)
 (.leaf 47))))
 (.branch 8200
 (.branch 8194
 (.leaf 48)
 (.branch 8196
 (.leaf 49)
 (.leaf 50)))
 (.branch 8208
 (.leaf 51)
 (.branch 8224
 (.leaf 52)
 (.leaf 53)))))
 (.branch 9240
 (.branch 9222
 (.branch 9221
 (.leaf 54)
 (.leaf 55))
 (.branch 9225
 (.leaf 56)
 (.branch 9234
 (.leaf 57)
 (.leaf 58))))
 (.branch 9264
 (.branch 9252
 (.leaf 59)
 (.branch 9256
 (.leaf 60)
 (.leaf 61)))
 (.branch 10243
 (.leaf 62)
 (.branch 10245
 (.leaf 63)
 (.leaf 64))))))
 (.branch 12294
 (.branch 10280
 (.branch 10258
 (.branch 10249
 (.leaf 65)
 (.leaf 66))
 (.branch 10264
 (.leaf 67)
 (.branch 10276
 (.leaf 68)
 (.leaf 69))))
 (.branch 11320
 (.branch 10288
 (.leaf 70)
 (.branch 11271
 (.leaf 71)
 (.leaf 72)))
 (.branch 12291
 (.leaf 73)
 (.branch 12293
 (.leaf 74)
 (.leaf 75)))))
 (.branch 12328
 (.branch 12306
 (.branch 12297
 (.leaf 76)
 (.leaf 77))
 (.branch 12312
 (.leaf 78)
 (.branch 12324
 (.leaf 79)
 (.leaf 80))))
 (.branch 13368
 (.branch 12336
 (.leaf 81)
 (.branch 13319
 (.leaf 82)
 (.leaf 83)))
 (.branch 14343
 (.leaf 84)
 (.branch 14392
 (.leaf 85)
 (.leaf 86))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 4 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 4 (raw b) template root FacetUniverses.RootedSixExtra05.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra05.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
theorem check_0000_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 0)) 0 1 (by decide +kernel)
theorem block_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 1 :=
  check_0000_0000
theorem check_0001_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 1)) 0 1 (by decide +kernel)
theorem block_0001 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 1 :=
  check_0001_0000
theorem check_0002_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 2)) 0 1 (by decide +kernel)
theorem block_0002 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 1 :=
  check_0002_0000
theorem check_0003_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 3)) 0 1 (by decide +kernel)
theorem block_0003 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 1 :=
  check_0003_0000
theorem check_0004_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 0 1 (by decide +kernel)
theorem block_0004 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 1 :=
  check_0004_0000
theorem check_0005_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 0 1 (by decide +kernel)
theorem block_0005 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 1 :=
  check_0005_0000
theorem check_0006_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 0 1 (by decide +kernel)
theorem block_0006 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 1 :=
  check_0006_0000
theorem check_0007_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 0 1 (by decide +kernel)
theorem block_0007 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 1 :=
  check_0007_0000
theorem check_0008_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 0 1 (by decide +kernel)
theorem block_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 1 :=
  check_0008_0000
theorem check_0009_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 0 1 (by decide +kernel)
theorem block_0009 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 1 :=
  check_0009_0000
theorem check_0010_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 0 1 (by decide +kernel)
theorem block_0010 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 1 :=
  check_0010_0000
theorem check_0011_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 0 1 (by decide +kernel)
theorem block_0011 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 1 :=
  check_0011_0000
theorem check_0012_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 0 1 (by decide +kernel)
theorem block_0012 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 1 :=
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
theorem check_0022_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 22)) 0 1 (by decide +kernel)
theorem block_0022 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 1 :=
  check_0022_0000
theorem check_0023_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 23)) 0 1 (by decide +kernel)
theorem block_0023 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 1 :=
  check_0023_0000
theorem check_0024_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 24)) 0 1 (by decide +kernel)
theorem block_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 1 :=
  check_0024_0000
theorem check_0025_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 0 1 (by decide +kernel)
theorem block_0025 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 1 :=
  check_0025_0000
theorem check_0026_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 26)) 0 1 (by decide +kernel)
theorem block_0026 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 1 :=
  check_0026_0000
theorem check_0027_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 27)) 0 1 (by decide +kernel)
theorem block_0027 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 1 :=
  check_0027_0000
theorem check_0028_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 28)) 0 2 (by decide +kernel)
theorem block_0028 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 2 :=
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
theorem check_0046_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 46)) 0 6 (by decide +kernel)
theorem block_0046 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  check_0046_0000
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 6 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 1 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 1 :=
  check_0048_0000
theorem check_0049_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 49)) 0 1 (by decide +kernel)
theorem block_0049 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 1 :=
  check_0049_0000
theorem check_0050_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 50)) 0 1 (by decide +kernel)
theorem block_0050 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 1 :=
  check_0050_0000
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 1 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 1 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 1 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 1 :=
  check_0052_0000
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 1 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 1 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
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
theorem check_0072_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 0 6 (by decide +kernel)
theorem block_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 6 :=
  check_0072_0000
theorem check_0073_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 73)) 0 6 (by decide +kernel)
theorem block_0073 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 73)) 0 6 :=
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
theorem check_0083_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 83)) 0 6 (by decide +kernel)
theorem block_0083 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 6 :=
  check_0083_0000
theorem check_0084_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 84)) 0 6 (by decide +kernel)
theorem block_0084 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 6 :=
  check_0084_0000
theorem check_0085_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 85)) 0 6 (by decide +kernel)
theorem block_0085 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 6 :=
  check_0085_0000
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 6 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 6 :=
  check_0086_0000
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
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
theorem metadata_validity_0080 : FiniteChecks.Interval validity 80 87 :=
  FiniteChecks.interval_of_check validity 80 7 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 87
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 64 87
  metadata_validity_0048
  (FiniteChecks.interval_append (validity) 64 80 87
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
theorem metadata_symmetry_0080 : FiniteChecks.Interval symmetry 80 87 :=
  FiniteChecks.interval_of_check symmetry 80 7 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 87
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 64 87
  metadata_symmetry_0048
  (FiniteChecks.interval_append (symmetry) 64 80 87
  metadata_symmetry_0064
  metadata_symmetry_0080)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 4 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
