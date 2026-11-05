module
prelude
public import SmallFacetUniverse
public import RawKindedFacePlacement
public import SmallFacetUniverseOutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
open ConcreteGrowth
abbrev blockCount : Nat := 99
noncomputable def template : Cell := ⟨1, 15, [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]⟩
noncomputable def root : Cell := FacetUniverses.Small.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨0, 5, 12816, 12816, 288317081445, 288317081445⟩, 171))
 (.branch 2
 (.leaf (⟨1, 5, 12816, 12816, 288326448720, 361617786720⟩, 61))
 (.leaf (⟨1, 5, 12816, 12816, 288309671505, 361617786630⟩, 111))))
 (.branch 4
 (.leaf (⟨1, 5, 12816, 12816, 288041236050, 361617784950⟩, 141))
 (.branch 5
 (.leaf (⟨1, 5, 12816, 12816, 283746268755, 361617754230⟩, 151))
 (.leaf (⟨1, 5, 12816, 12816, 215026792020, 361617201270⟩, 161)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨1, 5, 12801, 12801, 288326448720, 361617786720⟩, 61))
 (.branch 8
 (.leaf (⟨1, 5, 12801, 12801, 288309671505, 361617786630⟩, 111))
 (.leaf (⟨1, 5, 12801, 12801, 288041236050, 361617784950⟩, 141))))
 (.branch 10
 (.leaf (⟨1, 5, 12801, 12801, 283746268755, 361617754230⟩, 151))
 (.branch 11
 (.leaf (⟨1, 5, 12801, 12801, 215026792020, 361617201270⟩, 161))
 (.leaf (⟨2, 5, 12816, 12816, 288459547920, 434918491920⟩, 720907))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (⟨2, 5, 12816, 12816, 288191112480, 434918490480⟩, 2031647))
 (.branch 14
 (.leaf (⟨2, 5, 12816, 12816, 287922677025, 434918490375⟩, 5308497))
 (.leaf (⟨2, 5, 12816, 12816, 283896145200, 434918463600⟩, 2687017))))
 (.branch 16
 (.leaf (⟨2, 5, 12816, 12816, 283627709745, 434918463495⟩, 5963867))
 (.branch 17
 (.leaf (⟨2, 5, 12816, 12816, 279332742450, 434918461575⟩, 7929977))
 (.leaf (⟨2, 5, 12816, 12816, 215176668480, 434917972080⟩, 3342387)))))
 (.branch 21
 (.branch 19
 (.leaf (⟨2, 5, 12816, 12816, 214908233025, 434917971975⟩, 6619237))
 (.branch 20
 (.leaf (⟨2, 5, 12816, 12816, 210613265730, 434917970055⟩, 8585347))
 (.leaf (⟨1, 5, 12546, 12321, 288326448720, 361617786720⟩, 61))))
 (.branch 22
 (.leaf (⟨1, 5, 12546, 12321, 288309671505, 361617786630⟩, 111))
 (.branch 23
 (.leaf (⟨1, 5, 12546, 12321, 288041236050, 361617784950⟩, 141))
 (.leaf (⟨1, 5, 12546, 12321, 283746268755, 361617754230⟩, 151)))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf (⟨1, 5, 12546, 12321, 215026792020, 361617201270⟩, 161))
 (.branch 26
 (.leaf (⟨2, 5, 12576, 12576, 288459547920, 434918491920⟩, 720907))
 (.leaf (⟨2, 5, 12576, 12576, 288191112480, 434918490480⟩, 2031647))))
 (.branch 28
 (.leaf (⟨2, 5, 12576, 12576, 287922677025, 434918490375⟩, 5308497))
 (.branch 29
 (.leaf (⟨2, 5, 12576, 12576, 283896145200, 434918463600⟩, 2687017))
 (.leaf (⟨2, 5, 12576, 12576, 283627709745, 434918463495⟩, 5963867)))))
 (.branch 33
 (.branch 31
 (.leaf (⟨2, 5, 12576, 12576, 279332742450, 434918461575⟩, 7929977))
 (.branch 32
 (.leaf (⟨2, 5, 12576, 12576, 215176668480, 434917972080⟩, 3342387))
 (.leaf (⟨2, 5, 12576, 12576, 214908233025, 434917971975⟩, 6619237))))
 (.branch 34
 (.leaf (⟨2, 5, 12576, 12576, 210613265730, 434917970055⟩, 8585347))
 (.branch 35
 (.leaf (⟨2, 5, 12321, 12546, 288459547920, 434918491920⟩, 720907))
 (.leaf (⟨2, 5, 12321, 12546, 288191112480, 434918490480⟩, 2031647))))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf (⟨2, 5, 12321, 12546, 287922677025, 434918490375⟩, 5308497))
 (.branch 38
 (.leaf (⟨2, 5, 12321, 12546, 283896145200, 434918463600⟩, 2687017))
 (.leaf (⟨2, 5, 12321, 12546, 283627709745, 434918463495⟩, 5963867))))
 (.branch 40
 (.leaf (⟨2, 5, 12321, 12546, 279332742450, 434918461575⟩, 7929977))
 (.branch 41
 (.leaf (⟨2, 5, 12321, 12546, 215176668480, 434917972080⟩, 3342387))
 (.leaf (⟨2, 5, 12321, 12546, 214908233025, 434917971975⟩, 6619237)))))
 (.branch 45
 (.branch 43
 (.leaf (⟨2, 5, 12321, 12546, 210613265730, 434917970055⟩, 8585347))
 (.branch 44
 (.leaf (⟨3, 5, 12816, 12816, 286025732880, 508219172880⟩, 1208944266640182156001281))
 (.leaf (⟨3, 5, 12816, 12816, 281730765600, 508219171200⟩, 25387829599443825276026901))))
 (.branch 47
 (.branch 46
 (.leaf (⟨3, 5, 12816, 12816, 277435798305, 508219171080⟩, 85835042931452933076090951))
 (.leaf (⟨3, 5, 12816, 12816, 217306256400, 508218742800⟩, 7253665599841092936007686)))
 (.branch 48
 (.leaf (⟨3, 5, 12816, 12816, 213011289120, 508218741120⟩, 31432550932644736056033306))
 (.leaf (⟨3, 5, 12816, 12816, 208716321825, 508218741000⟩, 91879764264653843856097356))))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf (⟨1, 5, 8451, 801, 288326448720, 361617786720⟩, 61))
 (.branch 51
 (.leaf (⟨1, 5, 8451, 801, 288309671505, 361617786630⟩, 111))
 (.leaf (⟨1, 5, 8451, 801, 288041236050, 361617784950⟩, 141))))
 (.branch 53
 (.leaf (⟨1, 5, 8451, 801, 283746268755, 361617754230⟩, 151))
 (.branch 54
 (.leaf (⟨1, 5, 8451, 801, 215026792020, 361617201270⟩, 161))
 (.leaf (⟨2, 5, 8496, 4896, 288459547920, 434918491920⟩, 720907)))))
 (.branch 58
 (.branch 56
 (.leaf (⟨2, 5, 8496, 4896, 288191112480, 434918490480⟩, 2031647))
 (.branch 57
 (.leaf (⟨2, 5, 8496, 4896, 287922677025, 434918490375⟩, 5308497))
 (.leaf (⟨2, 5, 8496, 4896, 283896145200, 434918463600⟩, 2687017))))
 (.branch 59
 (.leaf (⟨2, 5, 8496, 4896, 283627709745, 434918463495⟩, 5963867))
 (.branch 60
 (.leaf (⟨2, 5, 8496, 4896, 279332742450, 434918461575⟩, 7929977))
 (.leaf (⟨2, 5, 8496, 4896, 215176668480, 434917972080⟩, 3342387))))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf (⟨2, 5, 8496, 4896, 214908233025, 434917971975⟩, 6619237))
 (.branch 63
 (.leaf (⟨2, 5, 8496, 4896, 210613265730, 434917970055⟩, 8585347))
 (.leaf (⟨2, 5, 8241, 4866, 288459547920, 434918491920⟩, 720907))))
 (.branch 65
 (.leaf (⟨2, 5, 8241, 4866, 288191112480, 434918490480⟩, 2031647))
 (.branch 66
 (.leaf (⟨2, 5, 8241, 4866, 287922677025, 434918490375⟩, 5308497))
 (.leaf (⟨2, 5, 8241, 4866, 283896145200, 434918463600⟩, 2687017)))))
 (.branch 70
 (.branch 68
 (.leaf (⟨2, 5, 8241, 4866, 283627709745, 434918463495⟩, 5963867))
 (.branch 69
 (.leaf (⟨2, 5, 8241, 4866, 279332742450, 434918461575⟩, 7929977))
 (.leaf (⟨2, 5, 8241, 4866, 215176668480, 434917972080⟩, 3342387))))
 (.branch 72
 (.branch 71
 (.leaf (⟨2, 5, 8241, 4866, 214908233025, 434917971975⟩, 6619237))
 (.leaf (⟨2, 5, 8241, 4866, 210613265730, 434917970055⟩, 8585347)))
 (.branch 73
 (.leaf (⟨3, 5, 8976, 8976, 286025732880, 508219172880⟩, 1208944266640182156001281))
 (.leaf (⟨3, 5, 8976, 8976, 281730765600, 508219171200⟩, 25387829599443825276026901)))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf (⟨3, 5, 8976, 8976, 277435798305, 508219171080⟩, 85835042931452933076090951))
 (.branch 76
 (.leaf (⟨3, 5, 8976, 8976, 217306256400, 508218742800⟩, 7253665599841092936007686))
 (.leaf (⟨3, 5, 8976, 8976, 213011289120, 508218741120⟩, 31432550932644736056033306))))
 (.branch 78
 (.leaf (⟨3, 5, 8976, 8976, 208716321825, 508218741000⟩, 91879764264653843856097356))
 (.branch 79
 (.leaf (⟨2, 5, 4146, 4146, 288459547920, 434918491920⟩, 720907))
 (.leaf (⟨2, 5, 4146, 4146, 288191112480, 434918490480⟩, 2031647)))))
 (.branch 83
 (.branch 81
 (.leaf (⟨2, 5, 4146, 4146, 287922677025, 434918490375⟩, 5308497))
 (.branch 82
 (.leaf (⟨2, 5, 4146, 4146, 283896145200, 434918463600⟩, 2687017))
 (.leaf (⟨2, 5, 4146, 4146, 283627709745, 434918463495⟩, 5963867))))
 (.branch 84
 (.leaf (⟨2, 5, 4146, 4146, 279332742450, 434918461575⟩, 7929977))
 (.branch 85
 (.leaf (⟨2, 5, 4146, 4146, 215176668480, 434917972080⟩, 3342387))
 (.leaf (⟨2, 5, 4146, 4146, 214908233025, 434917971975⟩, 6619237))))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf (⟨2, 5, 4146, 4146, 210613265730, 434917970055⟩, 8585347))
 (.branch 88
 (.leaf (⟨3, 5, 4896, 8496, 286025732880, 508219172880⟩, 1208944266640182156001281))
 (.leaf (⟨3, 5, 4896, 8496, 281730765600, 508219171200⟩, 25387829599443825276026901))))
 (.branch 90
 (.leaf (⟨3, 5, 4896, 8496, 277435798305, 508219171080⟩, 85835042931452933076090951))
 (.branch 91
 (.leaf (⟨3, 5, 4896, 8496, 217306256400, 508218742800⟩, 7253665599841092936007686))
 (.leaf (⟨3, 5, 4896, 8496, 213011289120, 508218741120⟩, 31432550932644736056033306)))))
 (.branch 95
 (.branch 93
 (.leaf (⟨3, 5, 4896, 8496, 208716321825, 508218741000⟩, 91879764264653843856097356))
 (.branch 94
 (.leaf (⟨3, 5, 801, 8451, 286025732880, 508219172880⟩, 1208944266640182156001281))
 (.leaf (⟨3, 5, 801, 8451, 281730765600, 508219171200⟩, 25387829599443825276026901))))
 (.branch 97
 (.branch 96
 (.leaf (⟨3, 5, 801, 8451, 277435798305, 508219171080⟩, 85835042931452933076090951))
 (.leaf (⟨3, 5, 801, 8451, 217306256400, 508218742800⟩, 7253665599841092936007686)))
 (.branch 98
 (.leaf (⟨3, 5, 801, 8451, 213011289120, 508218741120⟩, 31432550932644736056033306))
 (.leaf (⟨3, 5, 801, 8451, 208716321825, 508218741000⟩, 91879764264653843856097356)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 3436 :=
  Fin.ofNat 3436 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 8193
 (.branch 4112
 (.branch 3077
 (.branch 2049
 (.branch 1028
 (.branch 1025
 (.leaf 0)
 (.branch 1026
 (.leaf 1)
 (.leaf 2)))
 (.branch 1032
 (.leaf 3)
 (.branch 1040
 (.leaf 4)
 (.leaf 5))))
 (.branch 2056
 (.branch 2050
 (.leaf 6)
 (.branch 2052
 (.leaf 7)
 (.leaf 8)))
 (.branch 2064
 (.leaf 9)
 (.branch 3075
 (.leaf 10)
 (.leaf 11)))))
 (.branch 3090
 (.branch 3082
 (.branch 3078
 (.leaf 12)
 (.branch 3081
 (.leaf 13)
 (.leaf 14)))
 (.branch 3084
 (.leaf 15)
 (.branch 3089
 (.leaf 16)
 (.leaf 17))))
 (.branch 4098
 (.branch 3092
 (.leaf 18)
 (.branch 4097
 (.leaf 19)
 (.leaf 20)))
 (.branch 4100
 (.leaf 21)
 (.branch 4104
 (.leaf 22)
 (.leaf 23))))))
 (.branch 6150
 (.branch 5132
 (.branch 5126
 (.branch 5123
 (.leaf 24)
 (.branch 5125
 (.leaf 25)
 (.leaf 26)))
 (.branch 5129
 (.leaf 27)
 (.branch 5130
 (.leaf 28)
 (.leaf 29))))
 (.branch 5140
 (.branch 5137
 (.leaf 30)
 (.branch 5138
 (.leaf 31)
 (.leaf 32)))
 (.branch 6147
 (.leaf 33)
 (.branch 6149
 (.leaf 34)
 (.leaf 35)))))
 (.branch 6164
 (.branch 6156
 (.branch 6153
 (.leaf 36)
 (.branch 6154
 (.leaf 37)
 (.leaf 38)))
 (.branch 6161
 (.leaf 39)
 (.branch 6162
 (.leaf 40)
 (.leaf 41))))
 (.branch 7182
 (.branch 7179
 (.leaf 42)
 (.branch 7181
 (.leaf 43)
 (.leaf 44)))
 (.branch 7189
 (.branch 7187
 (.leaf 45)
 (.leaf 46))
 (.branch 7190
 (.leaf 47)
 (.leaf 48)))))))
 (.branch 11278
 (.branch 9234
 (.branch 9221
 (.branch 8200
 (.branch 8194
 (.leaf 49)
 (.branch 8196
 (.leaf 50)
 (.leaf 51)))
 (.branch 8208
 (.leaf 52)
 (.branch 9219
 (.leaf 53)
 (.leaf 54))))
 (.branch 9226
 (.branch 9222
 (.leaf 55)
 (.branch 9225
 (.leaf 56)
 (.leaf 57)))
 (.branch 9228
 (.leaf 58)
 (.branch 9233
 (.leaf 59)
 (.leaf 60)))))
 (.branch 10250
 (.branch 10245
 (.branch 9236
 (.leaf 61)
 (.branch 10243
 (.leaf 62)
 (.leaf 63)))
 (.branch 10246
 (.leaf 64)
 (.branch 10249
 (.leaf 65)
 (.leaf 66))))
 (.branch 10258
 (.branch 10252
 (.leaf 67)
 (.branch 10257
 (.leaf 68)
 (.leaf 69)))
 (.branch 11275
 (.branch 10260
 (.leaf 70)
 (.leaf 71))
 (.branch 11277
 (.leaf 72)
 (.leaf 73))))))
 (.branch 12308
 (.branch 12294
 (.branch 11286
 (.branch 11283
 (.leaf 74)
 (.branch 11285
 (.leaf 75)
 (.leaf 76)))
 (.branch 12291
 (.leaf 77)
 (.branch 12293
 (.leaf 78)
 (.leaf 79))))
 (.branch 12300
 (.branch 12297
 (.leaf 80)
 (.branch 12298
 (.leaf 81)
 (.leaf 82)))
 (.branch 12305
 (.leaf 83)
 (.branch 12306
 (.leaf 84)
 (.leaf 85)))))
 (.branch 13334
 (.branch 13326
 (.branch 13323
 (.leaf 86)
 (.branch 13325
 (.leaf 87)
 (.leaf 88)))
 (.branch 13331
 (.leaf 89)
 (.branch 13333
 (.leaf 90)
 (.leaf 91))))
 (.branch 14350
 (.branch 14347
 (.leaf 92)
 (.branch 14349
 (.leaf 93)
 (.leaf 94)))
 (.branch 14357
 (.branch 14355
 (.leaf 95)
 (.leaf 96))
 (.branch 14358
 (.leaf 97)
 (.leaf 98))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 4 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 4 (raw b) template root FacetUniverses.Small.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.Small.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
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
theorem check_0020_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 20)) 0 1 (by decide +kernel)
theorem block_0020 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 1 :=
  check_0020_0000
theorem check_0021_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 21)) 0 1 (by decide +kernel)
theorem block_0021 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 1 :=
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
theorem check_0043_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 43)) 0 6 (by decide +kernel)
theorem block_0043 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 43)) 0 6 :=
  check_0043_0000
theorem check_0044_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 44)) 0 6 (by decide +kernel)
theorem block_0044 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 44)) 0 6 :=
  check_0044_0000
theorem check_0045_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 45)) 0 6 (by decide +kernel)
theorem block_0045 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 45)) 0 6 :=
  check_0045_0000
theorem check_0046_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 46)) 0 6 (by decide +kernel)
theorem block_0046 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 46)) 0 6 :=
  check_0046_0000
theorem check_0047_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 47)) 0 6 (by decide +kernel)
theorem block_0047 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 47)) 0 6 :=
  check_0047_0000
theorem check_0048_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 48)) 0 6 (by decide +kernel)
theorem block_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 48)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
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
theorem check_0074_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 74)) 0 6 (by decide +kernel)
theorem block_0074 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 74)) 0 6 :=
  check_0074_0000
theorem check_0075_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 75)) 0 6 (by decide +kernel)
theorem block_0075 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 75)) 0 6 :=
  check_0075_0000
theorem check_0076_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 76)) 0 6 (by decide +kernel)
theorem block_0076 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 76)) 0 6 :=
  check_0076_0000
theorem check_0077_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 77)) 0 6 (by decide +kernel)
theorem block_0077 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 77)) 0 6 :=
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
theorem check_0089_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 89)) 0 6 (by decide +kernel)
theorem block_0089 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 89)) 0 6 :=
  check_0089_0000
theorem check_0090_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 90)) 0 6 (by decide +kernel)
theorem block_0090 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 90)) 0 6 :=
  check_0090_0000
theorem check_0091_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 91)) 0 6 (by decide +kernel)
theorem block_0091 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 91)) 0 6 :=
  check_0091_0000
theorem check_0092_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 92)) 0 6 (by decide +kernel)
theorem block_0092 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 92)) 0 6 :=
  check_0092_0000
theorem check_0093_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 93)) 0 6 (by decide +kernel)
theorem block_0093 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 93)) 0 6 :=
  check_0093_0000
theorem check_0094_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 94)) 0 6 (by decide +kernel)
theorem block_0094 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 94)) 0 6 :=
  check_0094_0000
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 6 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 6 :=
  check_0095_0000
theorem check_0096_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 96)) 0 6 (by decide +kernel)
theorem block_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 96)) 0 6 :=
  check_0096_0000
theorem check_0097_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 97)) 0 6 (by decide +kernel)
theorem block_0097 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 97)) 0 6 :=
  check_0097_0000
theorem check_0098_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 0 6 (by decide +kernel)
theorem block_0098 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 6 :=
  check_0098_0000
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
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
theorem metadata_validity_0096 : FiniteChecks.Interval validity 96 99 :=
  FiniteChecks.interval_of_check validity 96 3 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 99
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 80 99
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)
  (FiniteChecks.interval_append (validity) 80 96 99
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
theorem metadata_symmetry_0096 : FiniteChecks.Interval symmetry 96 99 :=
  FiniteChecks.interval_of_check symmetry 96 3 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 99
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 80 99
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)
  (FiniteChecks.interval_append (symmetry) 80 96 99
  metadata_symmetry_0080
  metadata_symmetry_0096)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 4 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S4T0
