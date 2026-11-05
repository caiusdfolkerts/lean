module
prelude
public import SmallFacetUniverse
public import RawKindedFacePlacement
public import SmallFacetUniverseOutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 122
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.Small.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 61
 (.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (⟨0, 5, 274960, 274960, 288317081445, 288317081445⟩, 3427))
 (.branch 2
 (.leaf (⟨1, 5, 274960, 274960, 288326448720, 361617786720⟩, 1512))
 (.leaf (⟨1, 5, 274960, 274960, 288309671505, 361617786630⟩, 2507))))
 (.branch 5
 (.branch 4
 (.leaf (⟨1, 5, 274960, 274960, 288041236050, 361617784950⟩, 3052))
 (.leaf (⟨1, 5, 274960, 274960, 283746268755, 361617754230⟩, 3177)))
 (.branch 6
 (.leaf (⟨1, 5, 274960, 274960, 215026792020, 361617201270⟩, 3302))
 (.leaf (⟨1, 5, 274945, 274945, 288326448720, 361617786720⟩, 1513)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (⟨1, 5, 274945, 274945, 288309671505, 361617786630⟩, 2508))
 (.leaf (⟨1, 5, 274945, 274945, 288041236050, 361617784950⟩, 3053)))
 (.branch 10
 (.leaf (⟨1, 5, 274945, 274945, 283746268755, 361617754230⟩, 3178))
 (.leaf (⟨1, 5, 274945, 274945, 215026792020, 361617201270⟩, 3303))))
 (.branch 13
 (.branch 12
 (.leaf (⟨2, 5, 274960, 274960, 288459547920, 434918491920⟩, 28311983))
 (.leaf (⟨2, 5, 274960, 274960, 288191112480, 434918490480⟩, 57803633)))
 (.branch 14
 (.leaf (⟨2, 5, 274960, 274960, 287922677025, 434918490375⟩, 123012948))
 (.leaf (⟨2, 5, 274960, 274960, 283896145200, 434918463600⟩, 71566403))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (⟨2, 5, 274960, 274960, 283627709745, 434918463495⟩, 136775718))
 (.branch 17
 (.leaf (⟨2, 5, 274960, 274960, 279332742450, 434918461575⟩, 172493383))
 (.leaf (⟨2, 5, 274960, 274960, 215176668480, 434917972080⟩, 85329173))))
 (.branch 20
 (.branch 19
 (.leaf (⟨2, 5, 274960, 274960, 214908233025, 434917971975⟩, 150538488))
 (.leaf (⟨2, 5, 274960, 274960, 210613265730, 434917970055⟩, 186256153)))
 (.branch 21
 (.leaf (⟨1, 5, 274690, 274465, 288326448720, 361617786720⟩, 1506))
 (.leaf (⟨1, 5, 274690, 274465, 288309671505, 361617786630⟩, 2501)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (⟨1, 5, 274690, 274465, 288041236050, 361617784950⟩, 3046))
 (.leaf (⟨1, 5, 274690, 274465, 283746268755, 361617754230⟩, 3171)))
 (.branch 25
 (.leaf (⟨1, 5, 274690, 274465, 215026792020, 361617201270⟩, 3296))
 (.leaf (⟨2, 5, 274720, 274720, 288459547920, 434918491920⟩, 27853228))))
 (.branch 28
 (.branch 27
 (.leaf (⟨2, 5, 274720, 274720, 288191112480, 434918490480⟩, 57344878))
 (.leaf (⟨2, 5, 274720, 274720, 287922677025, 434918490375⟩, 122554193)))
 (.branch 29
 (.leaf (⟨2, 5, 274720, 274720, 283896145200, 434918463600⟩, 71107648))
 (.leaf (⟨2, 5, 274720, 274720, 283627709745, 434918463495⟩, 136316963)))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf (⟨2, 5, 274720, 274720, 279332742450, 434918461575⟩, 172034628))
 (.branch 32
 (.leaf (⟨2, 5, 274720, 274720, 215176668480, 434917972080⟩, 84870418))
 (.leaf (⟨2, 5, 274720, 274720, 214908233025, 434917971975⟩, 150079733))))
 (.branch 35
 (.branch 34
 (.leaf (⟨2, 5, 274720, 274720, 210613265730, 434917970055⟩, 185797398))
 (.leaf (⟨2, 5, 274465, 274690, 288459547920, 434918491920⟩, 27918765)))
 (.branch 36
 (.leaf (⟨2, 5, 274465, 274690, 288191112480, 434918490480⟩, 57410415))
 (.leaf (⟨2, 5, 274465, 274690, 287922677025, 434918490375⟩, 122619730)))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf (⟨2, 5, 274465, 274690, 283896145200, 434918463600⟩, 71173185))
 (.leaf (⟨2, 5, 274465, 274690, 283627709745, 434918463495⟩, 136382500)))
 (.branch 40
 (.leaf (⟨2, 5, 274465, 274690, 279332742450, 434918461575⟩, 172100165))
 (.leaf (⟨2, 5, 274465, 274690, 215176668480, 434917972080⟩, 84935955))))
 (.branch 43
 (.branch 42
 (.leaf (⟨2, 5, 274465, 274690, 214908233025, 434917971975⟩, 150145270))
 (.leaf (⟨2, 5, 274465, 274690, 210613265730, 434917970055⟩, 185862935)))
 (.branch 44
 (.leaf (⟨3, 5, 274960, 274960, 286025732880, 508219172880⟩, 221236782348690744405590202))
 (.leaf (⟨3, 5, 274960, 274960, 281730765600, 508219171200⟩, 765261702336772714606166652))))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (⟨3, 5, 274960, 274960, 277435798305, 508219171080⟩, 1968161247643753959827441247))
 (.leaf (⟨3, 5, 274960, 274960, 217306256400, 508218742800⟩, 366310094345512603125743922)))
 (.branch 48
 (.leaf (⟨3, 5, 274960, 274960, 213011289120, 508218741120⟩, 910335014333594573326320372))
 (.leaf (⟨3, 5, 274960, 274960, 208716321825, 508218741000⟩, 2113234559640575818547594967))))
 (.branch 51
 (.branch 50
 (.leaf (⟨1, 5, 270595, 262945, 288326448720, 361617786720⟩, 1517))
 (.leaf (⟨1, 5, 270595, 262945, 288309671505, 361617786630⟩, 2512)))
 (.branch 52
 (.leaf (⟨1, 5, 270595, 262945, 288041236050, 361617784950⟩, 3057))
 (.leaf (⟨1, 5, 270595, 262945, 283746268755, 361617754230⟩, 3182)))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf (⟨1, 5, 270595, 262945, 215026792020, 361617201270⟩, 3307))
 (.leaf (⟨2, 5, 270385, 267010, 288459547920, 434918491920⟩, 28377522)))
 (.branch 56
 (.leaf (⟨2, 5, 270385, 267010, 288191112480, 434918490480⟩, 57869172))
 (.leaf (⟨2, 5, 270385, 267010, 287922677025, 434918490375⟩, 123078487))))
 (.branch 59
 (.branch 58
 (.leaf (⟨2, 5, 270385, 267010, 283896145200, 434918463600⟩, 71631942))
 (.leaf (⟨2, 5, 270385, 267010, 283627709745, 434918463495⟩, 136841257)))
 (.branch 60
 (.leaf (⟨2, 5, 270385, 267010, 279332742450, 434918461575⟩, 172558922))
 (.leaf (⟨2, 5, 270385, 267010, 215176668480, 434917972080⟩, 85394712))))))))
 (.branch 91
 (.branch 76
 (.branch 68
 (.branch 64
 (.branch 62
 (.leaf (⟨2, 5, 270385, 267010, 214908233025, 434917971975⟩, 150604027))
 (.branch 63
 (.leaf (⟨2, 5, 270385, 267010, 210613265730, 434917970055⟩, 186321692))
 (.leaf (⟨2, 5, 266290, 266290, 288459547920, 434918491920⟩, 28180907))))
 (.branch 66
 (.branch 65
 (.leaf (⟨2, 5, 266290, 266290, 288191112480, 434918490480⟩, 57672557))
 (.leaf (⟨2, 5, 266290, 266290, 287922677025, 434918490375⟩, 122881872)))
 (.branch 67
 (.leaf (⟨2, 5, 266290, 266290, 283896145200, 434918463600⟩, 71435327))
 (.leaf (⟨2, 5, 266290, 266290, 283627709745, 434918463495⟩, 136644642)))))
 (.branch 72
 (.branch 70
 (.branch 69
 (.leaf (⟨2, 5, 266290, 266290, 279332742450, 434918461575⟩, 172362307))
 (.leaf (⟨2, 5, 266290, 266290, 215176668480, 434917972080⟩, 85198097)))
 (.branch 71
 (.leaf (⟨2, 5, 266290, 266290, 214908233025, 434917971975⟩, 150407412))
 (.leaf (⟨2, 5, 266290, 266290, 210613265730, 434917970055⟩, 186125077))))
 (.branch 74
 (.branch 73
 (.leaf (⟨3, 5, 262945, 270595, 286025732880, 508219172880⟩, 222445781956126080463470777))
 (.leaf (⟨3, 5, 262945, 270595, 281730765600, 508219171200⟩, 766470701944208050664047227)))
 (.branch 75
 (.leaf (⟨3, 5, 262945, 270595, 277435798305, 508219171080⟩, 1969370247251189295885321822))
 (.leaf (⟨3, 5, 262945, 270595, 217306256400, 508218742800⟩, 367519093952947939183624497))))))
 (.branch 83
 (.branch 79
 (.branch 77
 (.leaf (⟨3, 5, 262945, 270595, 213011289120, 508218741120⟩, 911544013941029909384200947))
 (.branch 78
 (.leaf (⟨3, 5, 262945, 270595, 208716321825, 508218741000⟩, 2114443559248011154605475542))
 (.leaf (⟨1, 5, 205060, 17185, 288326448720, 361617786720⟩, 1515))))
 (.branch 81
 (.branch 80
 (.leaf (⟨1, 5, 205060, 17185, 288309671505, 361617786630⟩, 2510))
 (.leaf (⟨1, 5, 205060, 17185, 288041236050, 361617784950⟩, 3055)))
 (.branch 82
 (.leaf (⟨1, 5, 205060, 17185, 283746268755, 361617754230⟩, 3180))
 (.leaf (⟨1, 5, 205060, 17185, 215026792020, 361617201270⟩, 3305)))))
 (.branch 87
 (.branch 85
 (.branch 84
 (.leaf (⟨2, 5, 205120, 82720, 288459547920, 434918491920⟩, 28377522))
 (.leaf (⟨2, 5, 205120, 82720, 288191112480, 434918490480⟩, 57869172)))
 (.branch 86
 (.leaf (⟨2, 5, 205120, 82720, 287922677025, 434918490375⟩, 123078487))
 (.leaf (⟨2, 5, 205120, 82720, 283896145200, 434918463600⟩, 71631942))))
 (.branch 89
 (.branch 88
 (.leaf (⟨2, 5, 205120, 82720, 283627709745, 434918463495⟩, 136841257))
 (.leaf (⟨2, 5, 205120, 82720, 279332742450, 434918461575⟩, 172558922)))
 (.branch 90
 (.leaf (⟨2, 5, 205120, 82720, 215176668480, 434917972080⟩, 85394712))
 (.leaf (⟨2, 5, 205120, 82720, 214908233025, 434917971975⟩, 150604027)))))))
 (.branch 106
 (.branch 98
 (.branch 94
 (.branch 92
 (.leaf (⟨2, 5, 205120, 82720, 210613265730, 434917970055⟩, 186321692))
 (.branch 93
 (.leaf (⟨2, 5, 200770, 81970, 288459547920, 434918491920⟩, 28049833))
 (.leaf (⟨2, 5, 200770, 81970, 288191112480, 434918490480⟩, 57541483))))
 (.branch 96
 (.branch 95
 (.leaf (⟨2, 5, 200770, 81970, 287922677025, 434918490375⟩, 122750798))
 (.leaf (⟨2, 5, 200770, 81970, 283896145200, 434918463600⟩, 71304253)))
 (.branch 97
 (.leaf (⟨2, 5, 200770, 81970, 283627709745, 434918463495⟩, 136513568))
 (.leaf (⟨2, 5, 200770, 81970, 279332742450, 434918461575⟩, 172231233)))))
 (.branch 102
 (.branch 100
 (.branch 99
 (.leaf (⟨2, 5, 200770, 81970, 215176668480, 434917972080⟩, 85067023))
 (.leaf (⟨2, 5, 200770, 81970, 214908233025, 434917971975⟩, 150276338)))
 (.branch 101
 (.leaf (⟨2, 5, 200770, 81970, 210613265730, 434917970055⟩, 185994003))
 (.leaf (⟨3, 5, 201760, 147760, 286025732880, 508219172880⟩, 222445781956126080463470777))))
 (.branch 104
 (.branch 103
 (.leaf (⟨3, 5, 201760, 147760, 281730765600, 508219171200⟩, 766470701944208050664047227))
 (.leaf (⟨3, 5, 201760, 147760, 277435798305, 508219171080⟩, 1969370247251189295885321822)))
 (.branch 105
 (.leaf (⟨3, 5, 201760, 147760, 217306256400, 508218742800⟩, 367519093952947939183624497))
 (.leaf (⟨3, 5, 201760, 147760, 213011289120, 508218741120⟩, 911544013941029909384200947))))))
 (.branch 114
 (.branch 110
 (.branch 108
 (.branch 107
 (.leaf (⟨3, 5, 201760, 147760, 208716321825, 508218741000⟩, 2114443559248011154605475542))
 (.leaf (⟨2, 5, 135235, 66610, 288459547920, 434918491920⟩, 28574131)))
 (.branch 109
 (.leaf (⟨2, 5, 135235, 66610, 288191112480, 434918490480⟩, 58065781))
 (.leaf (⟨2, 5, 135235, 66610, 287922677025, 434918490375⟩, 123275096))))
 (.branch 112
 (.branch 111
 (.leaf (⟨2, 5, 135235, 66610, 283896145200, 434918463600⟩, 71828551))
 (.leaf (⟨2, 5, 135235, 66610, 283627709745, 434918463495⟩, 137037866)))
 (.branch 113
 (.leaf (⟨2, 5, 135235, 66610, 279332742450, 434918461575⟩, 172755531))
 (.leaf (⟨2, 5, 135235, 66610, 215176668480, 434917972080⟩, 85591321)))))
 (.branch 118
 (.branch 116
 (.branch 115
 (.leaf (⟨2, 5, 135235, 66610, 214908233025, 434917971975⟩, 150800636))
 (.leaf (⟨2, 5, 135235, 66610, 210613265730, 434917970055⟩, 186518301)))
 (.branch 117
 (.leaf (⟨3, 5, 66610, 135235, 286025732880, 508219172880⟩, 226072540967100011551129782))
 (.leaf (⟨3, 5, 66610, 135235, 281730765600, 508219171200⟩, 770097460955181981751706232))))
 (.branch 120
 (.branch 119
 (.leaf (⟨3, 5, 66610, 135235, 277435798305, 508219171080⟩, 1972997006262163226972980827))
 (.leaf (⟨3, 5, 66610, 135235, 217306256400, 508218742800⟩, 371145852963921870271283502)))
 (.branch 121
 (.leaf (⟨3, 5, 66610, 135235, 213011289120, 508218741120⟩, 915170772952003840471859952))
 (.leaf (⟨3, 5, 66610, 135235, 208716321825, 508218741000⟩, 2118070318258985085693134547)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 3436 :=
  Fin.ofNat 3436 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 10258
 (.branch 5132
 (.branch 3082
 (.branch 2050
 (.branch 1028
 (.branch 1025
 (.leaf 0)
 (.branch 1026
 (.leaf 1)
 (.leaf 2)))
 (.branch 1040
 (.branch 1032
 (.leaf 3)
 (.leaf 4))
 (.branch 2049
 (.leaf 5)
 (.leaf 6))))
 (.branch 3075
 (.branch 2056
 (.branch 2052
 (.leaf 7)
 (.leaf 8))
 (.branch 2064
 (.leaf 9)
 (.leaf 10)))
 (.branch 3078
 (.branch 3077
 (.leaf 11)
 (.leaf 12))
 (.branch 3081
 (.leaf 13)
 (.leaf 14)))))
 (.branch 4100
 (.branch 3090
 (.branch 3084
 (.leaf 15)
 (.branch 3089
 (.leaf 16)
 (.leaf 17)))
 (.branch 4097
 (.branch 3092
 (.leaf 18)
 (.leaf 19))
 (.branch 4098
 (.leaf 20)
 (.leaf 21))))
 (.branch 5125
 (.branch 4112
 (.branch 4104
 (.leaf 22)
 (.leaf 23))
 (.branch 5123
 (.leaf 24)
 (.leaf 25)))
 (.branch 5129
 (.branch 5126
 (.leaf 26)
 (.leaf 27))
 (.branch 5130
 (.leaf 28)
 (.leaf 29))))))
 (.branch 7182
 (.branch 6153
 (.branch 5140
 (.branch 5137
 (.leaf 30)
 (.branch 5138
 (.leaf 31)
 (.leaf 32)))
 (.branch 6149
 (.branch 6147
 (.leaf 33)
 (.leaf 34))
 (.branch 6150
 (.leaf 35)
 (.leaf 36))))
 (.branch 6162
 (.branch 6156
 (.branch 6154
 (.leaf 37)
 (.leaf 38))
 (.branch 6161
 (.leaf 39)
 (.leaf 40)))
 (.branch 7179
 (.branch 6164
 (.leaf 41)
 (.leaf 42))
 (.branch 7181
 (.leaf 43)
 (.leaf 44)))))
 (.branch 8208
 (.branch 8193
 (.branch 7189
 (.branch 7187
 (.leaf 45)
 (.leaf 46))
 (.branch 7190
 (.leaf 47)
 (.leaf 48)))
 (.branch 8196
 (.branch 8194
 (.leaf 49)
 (.leaf 50))
 (.branch 8200
 (.leaf 51)
 (.leaf 52))))
 (.branch 10249
 (.branch 10245
 (.branch 10243
 (.leaf 53)
 (.leaf 54))
 (.branch 10246
 (.leaf 55)
 (.leaf 56)))
 (.branch 10252
 (.branch 10250
 (.leaf 57)
 (.leaf 58))
 (.branch 10257
 (.leaf 59)
 (.leaf 60)))))))
 (.branch 17428
 (.branch 14357
 (.branch 12300
 (.branch 12293
 (.branch 10260
 (.leaf 61)
 (.branch 12291
 (.leaf 62)
 (.leaf 63)))
 (.branch 12297
 (.branch 12294
 (.leaf 64)
 (.leaf 65))
 (.branch 12298
 (.leaf 66)
 (.leaf 67))))
 (.branch 14347
 (.branch 12306
 (.branch 12305
 (.leaf 68)
 (.leaf 69))
 (.branch 12308
 (.leaf 70)
 (.leaf 71)))
 (.branch 14350
 (.branch 14349
 (.leaf 72)
 (.leaf 73))
 (.branch 14355
 (.leaf 74)
 (.leaf 75)))))
 (.branch 17411
 (.branch 16386
 (.branch 14358
 (.leaf 76)
 (.branch 16385
 (.leaf 77)
 (.leaf 78)))
 (.branch 16392
 (.branch 16388
 (.leaf 79)
 (.leaf 80))
 (.branch 16400
 (.leaf 81)
 (.leaf 82))))
 (.branch 17418
 (.branch 17414
 (.branch 17413
 (.leaf 83)
 (.leaf 84))
 (.branch 17417
 (.leaf 85)
 (.leaf 86)))
 (.branch 17425
 (.branch 17420
 (.leaf 87)
 (.leaf 88))
 (.branch 17426
 (.leaf 89)
 (.leaf 90))))))
 (.branch 21526
 (.branch 20497
 (.branch 20486
 (.branch 20483
 (.leaf 91)
 (.branch 20485
 (.leaf 92)
 (.leaf 93)))
 (.branch 20490
 (.branch 20489
 (.leaf 94)
 (.leaf 95))
 (.branch 20492
 (.leaf 96)
 (.leaf 97))))
 (.branch 21517
 (.branch 20500
 (.branch 20498
 (.leaf 98)
 (.leaf 99))
 (.branch 21515
 (.leaf 100)
 (.leaf 101)))
 (.branch 21523
 (.branch 21518
 (.leaf 102)
 (.leaf 103))
 (.branch 21525
 (.leaf 104)
 (.leaf 105)))))
 (.branch 24594
 (.branch 24585
 (.branch 24581
 (.branch 24579
 (.leaf 106)
 (.leaf 107))
 (.branch 24582
 (.leaf 108)
 (.leaf 109)))
 (.branch 24588
 (.branch 24586
 (.leaf 110)
 (.leaf 111))
 (.branch 24593
 (.leaf 112)
 (.leaf 113))))
 (.branch 28686
 (.branch 28683
 (.branch 24596
 (.leaf 114)
 (.leaf 115))
 (.branch 28685
 (.leaf 116)
 (.leaf 117)))
 (.branch 28693
 (.branch 28691
 (.leaf 118)
 (.leaf 119))
 (.branch 28694
 (.leaf 120)
 (.leaf 121))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.Small.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.Small.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
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
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
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
theorem check_0078_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 78)) 0 1 (by decide +kernel)
theorem block_0078 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 78)) 0 1 :=
  check_0078_0000
theorem check_0079_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 79)) 0 1 (by decide +kernel)
theorem block_0079 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 79)) 0 1 :=
  check_0079_0000
theorem check_0080_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 80)) 0 1 (by decide +kernel)
theorem block_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 1 :=
  check_0080_0000
theorem check_0081_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 81)) 0 1 (by decide +kernel)
theorem block_0081 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 1 :=
  check_0081_0000
theorem check_0082_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 1 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 82)) 0 1 (by decide +kernel)
theorem block_0082 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 1 :=
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
theorem check_0098_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 98)) 0 2 (by decide +kernel)
theorem block_0098 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 98)) 0 2 :=
  check_0098_0000
theorem check_0099_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 99)) 0 2 (by decide +kernel)
theorem block_0099 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 99)) 0 2 :=
  check_0099_0000
theorem check_0100_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 100)) 0 2 (by decide +kernel)
theorem block_0100 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 100)) 0 2 :=
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
theorem check_0104_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 104)) 0 6 (by decide +kernel)
theorem block_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 6 :=
  check_0104_0000
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 6 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 6 :=
  check_0105_0000
theorem check_0106_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 106)) 0 6 (by decide +kernel)
theorem block_0106 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 6 :=
  check_0106_0000
theorem check_0107_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 0 2 (by decide +kernel)
theorem block_0107 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 2 :=
  check_0107_0000
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 2 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 2 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 2 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 2 :=
  check_0109_0000
theorem check_0110_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 110)) 0 2 (by decide +kernel)
theorem block_0110 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 2 :=
  check_0110_0000
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 2 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 2 :=
  check_0111_0000
theorem check_0112_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 112)) 0 2 (by decide +kernel)
theorem block_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 2 :=
  check_0112_0000
theorem check_0113_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 113)) 0 2 (by decide +kernel)
theorem block_0113 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 2 :=
  check_0113_0000
theorem check_0114_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 114)) 0 2 (by decide +kernel)
theorem block_0114 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 114)) 0 2 :=
  check_0114_0000
theorem check_0115_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 115)) 0 2 (by decide +kernel)
theorem block_0115 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 115)) 0 2 :=
  check_0115_0000
theorem check_0116_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 116)) 0 6 (by decide +kernel)
theorem block_0116 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 6 :=
  check_0116_0000
theorem check_0117_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 117)) 0 6 (by decide +kernel)
theorem block_0117 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 6 :=
  check_0117_0000
theorem check_0118_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 118)) 0 6 (by decide +kernel)
theorem block_0118 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 6 :=
  check_0118_0000
theorem check_0119_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 119)) 0 6 (by decide +kernel)
theorem block_0119 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 6 :=
  check_0119_0000
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 6 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 6 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  check_0121_0000
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
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
theorem metadata_validity_0096 : FiniteChecks.Interval validity 96 112 :=
  FiniteChecks.interval_of_check validity 96 16 (by decide +kernel)
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 122 :=
  FiniteChecks.interval_of_check validity 112 10 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 122
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 122
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 122
  metadata_validity_0096
  metadata_validity_0112)))
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
theorem metadata_symmetry_0096 : FiniteChecks.Interval symmetry 96 112 :=
  FiniteChecks.interval_of_check symmetry 96 16 (by decide +kernel)
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 122 :=
  FiniteChecks.interval_of_check symmetry 112 10 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 122
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 122
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 122
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.SmallFacetUniverse.S5T1
