module
prelude
public import RootedSixBase01
public import RawKindedFacePlacement
public import RootedSixBase01OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6
open ConcreteGrowth
abbrev blockCount : Nat := 114
noncomputable def template : Cell := ⟨9, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixBase01.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 57
 (.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 962214236))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 964573568))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 966932900))))
 (.branch 5
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 970865120))
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 973224452)))
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 977156672))
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 981088892)))))
 (.branch 10
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 983448224))
 (.branch 9
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 987380444))
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 989739776))))
 (.branch 12
 (.branch 11
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 993671996))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 962541917)))
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 964901249))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 967260581))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 971192801))
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 973552133))
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 977484353))))
 (.branch 19
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 981416573))
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 983775905)))
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 987708125))
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 990067457)))))
 (.branch 24
 (.branch 22
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 993999677))
 (.branch 23
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 962476379))
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 964835711))))
 (.branch 26
 (.branch 25
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 967195043))
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 971127263)))
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 973486595))
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 977418815)))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 981351035))
 (.branch 30
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 983710367))
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 987642587))))
 (.branch 33
 (.branch 32
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 990001919))
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 993934139)))
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 17885121499121317401730628040))
 (.leaf (⟨3, 4, 5517840, 5517840, 361473991440, 434925741840⟩, 18001180148718774888706751016)))))
 (.branch 38
 (.branch 36
 (.leaf (⟨3, 4, 5517840, 5517840, 361205556000, 434925740400⟩, 18073716804717185818066827876))
 (.branch 37
 (.leaf (⟨3, 4, 5517840, 5517840, 356642153505, 434925371655⟩, 18189775454314643305042950852))
 (.leaf (⟨3, 4, 5517840, 5517840, 279332742450, 434918461575⟩, 18305834103912100792019073828))))
 (.branch 40
 (.branch 39
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 18378370759910511721379150688))
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 964442482)))
 (.branch 41
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 966801814))
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 969161146))))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 973093366))
 (.branch 44
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 975452698))
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 979384918))))
 (.branch 47
 (.branch 46
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 983317138))
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 985676470)))
 (.branch 48
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 989608690))
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 991968022)))))
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 995900242))
 (.leaf (⟨2, 4, 5448000, 5325600, 361626105360, 361626105360⟩, 964442482)))
 (.branch 52
 (.leaf (⟨2, 4, 5448000, 5325600, 361609328160, 361626104160⟩, 966801814))
 (.leaf (⟨2, 4, 5448000, 5325600, 361592550945, 361626104070⟩, 969161146))))
 (.branch 55
 (.branch 54
 (.leaf (⟨2, 4, 5448000, 5325600, 361340892720, 361626081120⟩, 973093366))
 (.leaf (⟨2, 4, 5448000, 5325600, 361324115505, 361626081030⟩, 975452698)))
 (.branch 56
 (.leaf (⟨2, 4, 5448000, 5325600, 361055680050, 361626079350⟩, 979384918))
 (.leaf (⟨2, 4, 5448000, 5325600, 357029148225, 361625650950⟩, 983317138))))))))
 (.branch 85
 (.branch 71
 (.branch 64
 (.branch 60
 (.branch 58
 (.leaf (⟨2, 4, 5448000, 5325600, 356760712770, 361625649270⟩, 985676470))
 (.branch 59
 (.leaf (⟨2, 4, 5448000, 5325600, 288041236050, 361617784950⟩, 989608690))
 (.leaf (⟨2, 4, 5448000, 5325600, 283746268755, 361617754230⟩, 991968022))))
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 4, 5448000, 5325600, 215026792020, 361617201270⟩, 995900242))
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 963393902)))
 (.branch 63
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 965753234))
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 968112566)))))
 (.branch 67
 (.branch 65
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 972044786))
 (.branch 66
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 974404118))
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 978336338))))
 (.branch 69
 (.branch 68
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 982268558))
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 984627890)))
 (.branch 70
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 988560110))
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 990919442))))))
 (.branch 78
 (.branch 74
 (.branch 72
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 994851662))
 (.branch 73
 (.leaf (⟨4, 4, 5391120, 5448720, 139996845105, 508218710280⟩, 139657848981973663051825214524667600175791737207952432709289359805161815015504735165536815574364541150840619008))
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 964508019))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 966867351))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 969226683)))
 (.branch 77
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 973158903))
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 975518235)))))
 (.branch 81
 (.branch 79
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 979450455))
 (.branch 80
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 983382675))
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 985742007))))
 (.branch 83
 (.branch 82
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 989674227))
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 992033559)))
 (.branch 84
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 995965779))
 (.leaf (⟨2, 4, 4329555, 1377330, 361626105360, 361626105360⟩, 963721583)))))))
 (.branch 99
 (.branch 92
 (.branch 88
 (.branch 86
 (.leaf (⟨2, 4, 4329555, 1377330, 361609328160, 361626104160⟩, 966080915))
 (.branch 87
 (.leaf (⟨2, 4, 4329555, 1377330, 361592550945, 361626104070⟩, 968440247))
 (.leaf (⟨2, 4, 4329555, 1377330, 361340892720, 361626081120⟩, 972372467))))
 (.branch 90
 (.branch 89
 (.leaf (⟨2, 4, 4329555, 1377330, 361324115505, 361626081030⟩, 974731799))
 (.leaf (⟨2, 4, 4329555, 1377330, 361055680050, 361626079350⟩, 978664019)))
 (.branch 91
 (.leaf (⟨2, 4, 4329555, 1377330, 357029148225, 361625650950⟩, 982596239))
 (.leaf (⟨2, 4, 4329555, 1377330, 356760712770, 361625649270⟩, 984955571)))))
 (.branch 95
 (.branch 93
 (.leaf (⟨2, 4, 4329555, 1377330, 288041236050, 361617784950⟩, 988887791))
 (.branch 94
 (.leaf (⟨2, 4, 4329555, 1377330, 283746268755, 361617754230⟩, 991247123))
 (.leaf (⟨2, 4, 4329555, 1377330, 215026792020, 361617201270⟩, 995179343))))
 (.branch 97
 (.branch 96
 (.leaf (⟨4, 4, 4215585, 3481860, 139996845105, 508218710280⟩, 9152477116816912186905582123815644667956437733301041016621298964216372849865865128534409666965505068783272445623158))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 963656045)))
 (.branch 98
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 966015377))
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 968374709))))))
 (.branch 106
 (.branch 102
 (.branch 100
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 972306929))
 (.branch 101
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 974666261))
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 978598481))))
 (.branch 104
 (.branch 103
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 982530701))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 984890033)))
 (.branch 105
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 988822253))
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 991181585)))))
 (.branch 110
 (.branch 108
 (.branch 107
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 995113805))
 (.leaf (⟨4, 4, 3232800, 3297600, 139996845105, 508218710280⟩, 9152477116816912186905582123815644667956437733301041016621298964216372849865865128534409666965505068783272445623158)))
 (.branch 109
 (.leaf (⟨3, 4, 2164035, 2164035, 361742426640, 434925761040⟩, 17885121499121317401730628040))
 (.leaf (⟨3, 4, 2164035, 2164035, 361473991440, 434925741840⟩, 18001180148718774888706751016))))
 (.branch 112
 (.branch 111
 (.leaf (⟨3, 4, 2164035, 2164035, 361205556000, 434925740400⟩, 18073716804717185818066827876))
 (.leaf (⟨3, 4, 2164035, 2164035, 356642153505, 434925371655⟩, 18189775454314643305042950852)))
 (.branch 113
 (.leaf (⟨3, 4, 2164035, 2164035, 279332742450, 434918461575⟩, 18305834103912100792019073828))
 (.leaf (⟨3, 4, 2164035, 2164035, 210613265730, 434917970055⟩, 18378370759910511721379150688)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 15246 :=
  Fin.ofNat 15246 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 17428
 (.branch 6162
 (.branch 5129
 (.branch 3092
 (.branch 3081
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3084
 (.branch 3082
 (.leaf 3)
 (.leaf 4))
 (.branch 3090
 (.leaf 5)
 (.leaf 6))))
 (.branch 3120
 (.branch 3108
 (.leaf 7)
 (.branch 3112
 (.leaf 8)
 (.leaf 9)))
 (.branch 5125
 (.branch 5123
 (.leaf 10)
 (.leaf 11))
 (.branch 5126
 (.leaf 12)
 (.leaf 13)))))
 (.branch 5168
 (.branch 5138
 (.branch 5130
 (.leaf 14)
 (.branch 5132
 (.leaf 15)
 (.leaf 16)))
 (.branch 5156
 (.branch 5140
 (.leaf 17)
 (.leaf 18))
 (.branch 5160
 (.leaf 19)
 (.leaf 20))))
 (.branch 6150
 (.branch 6147
 (.leaf 21)
 (.branch 6149
 (.leaf 22)
 (.leaf 23)))
 (.branch 6154
 (.branch 6153
 (.leaf 24)
 (.leaf 25))
 (.branch 6156
 (.leaf 26)
 (.leaf 27))))))
 (.branch 10249
 (.branch 7181
 (.branch 6184
 (.branch 6164
 (.leaf 28)
 (.branch 6180
 (.leaf 29)
 (.leaf 30)))
 (.branch 7175
 (.branch 6192
 (.leaf 31)
 (.leaf 32))
 (.branch 7179
 (.leaf 33)
 (.leaf 34))))
 (.branch 7220
 (.branch 7190
 (.leaf 35)
 (.branch 7212
 (.leaf 36)
 (.leaf 37)))
 (.branch 10245
 (.branch 10243
 (.leaf 38)
 (.leaf 39))
 (.branch 10246
 (.leaf 40)
 (.leaf 41)))))
 (.branch 10288
 (.branch 10258
 (.branch 10250
 (.leaf 42)
 (.branch 10252
 (.leaf 43)
 (.leaf 44)))
 (.branch 10276
 (.branch 10260
 (.leaf 45)
 (.leaf 46))
 (.branch 10280
 (.leaf 47)
 (.leaf 48))))
 (.branch 17417
 (.branch 17413
 (.branch 17411
 (.leaf 49)
 (.leaf 50))
 (.branch 17414
 (.leaf 51)
 (.leaf 52)))
 (.branch 17420
 (.branch 17418
 (.leaf 53)
 (.leaf 54))
 (.branch 17426
 (.leaf 55)
 (.leaf 56)))))))
 (.branch 40965
 (.branch 24624
 (.branch 24585
 (.branch 17456
 (.branch 17444
 (.leaf 57)
 (.branch 17448
 (.leaf 58)
 (.leaf 59)))
 (.branch 24581
 (.branch 24579
 (.leaf 60)
 (.leaf 61))
 (.branch 24582
 (.leaf 62)
 (.leaf 63))))
 (.branch 24594
 (.branch 24586
 (.leaf 64)
 (.branch 24588
 (.leaf 65)
 (.leaf 66)))
 (.branch 24612
 (.branch 24596
 (.leaf 67)
 (.leaf 68))
 (.branch 24616
 (.leaf 69)
 (.leaf 70)))))
 (.branch 36876
 (.branch 36869
 (.branch 27706
 (.leaf 71)
 (.branch 36867
 (.leaf 72)
 (.leaf 73)))
 (.branch 36873
 (.branch 36870
 (.leaf 74)
 (.leaf 75))
 (.branch 36874
 (.leaf 76)
 (.leaf 77))))
 (.branch 36900
 (.branch 36882
 (.leaf 78)
 (.branch 36884
 (.leaf 79)
 (.leaf 80)))
 (.branch 36912
 (.branch 36904
 (.leaf 81)
 (.leaf 82))
 (.branch 40963
 (.leaf 83)
 (.leaf 84))))))
 (.branch 49161
 (.branch 40996
 (.branch 40970
 (.branch 40966
 (.leaf 85)
 (.branch 40969
 (.leaf 86)
 (.leaf 87)))
 (.branch 40978
 (.branch 40972
 (.leaf 88)
 (.leaf 89))
 (.branch 40980
 (.leaf 90)
 (.leaf 91))))
 (.branch 47162
 (.branch 41000
 (.leaf 92)
 (.branch 41008
 (.leaf 93)
 (.leaf 94)))
 (.branch 49157
 (.branch 49155
 (.leaf 95)
 (.leaf 96))
 (.branch 49158
 (.leaf 97)
 (.leaf 98)))))
 (.branch 49200
 (.branch 49170
 (.branch 49162
 (.leaf 99)
 (.branch 49164
 (.leaf 100)
 (.leaf 101)))
 (.branch 49188
 (.branch 49172
 (.leaf 102)
 (.leaf 103))
 (.branch 49192
 (.leaf 104)
 (.leaf 105))))
 (.branch 57357
 (.branch 57351
 (.branch 54330
 (.leaf 106)
 (.leaf 107))
 (.branch 57355
 (.leaf 108)
 (.leaf 109)))
 (.branch 57388
 (.branch 57366
 (.leaf 110)
 (.leaf 111))
 (.branch 57396
 (.leaf 112)
 (.leaf 113))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixBase01.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase01.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6
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
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 6 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  check_0033_0000
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 6 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  check_0034_0000
theorem check_0035_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 0 6 (by decide +kernel)
theorem block_0035 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 6 :=
  check_0035_0000
theorem check_0036_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 36)) 0 6 (by decide +kernel)
theorem block_0036 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 36)) 0 6 :=
  check_0036_0000
theorem check_0037_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 37)) 0 6 (by decide +kernel)
theorem block_0037 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 37)) 0 6 :=
  check_0037_0000
theorem check_0038_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 38)) 0 6 (by decide +kernel)
theorem block_0038 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 38)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6
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
theorem check_0072_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 0 8 (by decide +kernel)
theorem check_0072_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 8 8 (by decide +kernel)
theorem check_0072_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 72)) 16 8 (by decide +kernel)
theorem block_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 72)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 72)) 0 8 24
  check_0072_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 72)) 8 16 24
  check_0072_0008
  check_0072_0016))
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
theorem check_0095_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 0 8 (by decide +kernel)
theorem check_0095_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 8 8 (by decide +kernel)
theorem check_0095_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 95)) 16 8 (by decide +kernel)
theorem block_0095 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 95)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 95)) 0 8 24
  check_0095_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 95)) 8 16 24
  check_0095_0008
  check_0095_0016))
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
theorem check_0101_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 101)) 0 2 (by decide +kernel)
theorem block_0101 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 101)) 0 2 :=
  check_0101_0000
theorem check_0102_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 102)) 0 2 (by decide +kernel)
theorem block_0102 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 102)) 0 2 :=
  check_0102_0000
theorem check_0103_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 103)) 0 2 (by decide +kernel)
theorem block_0103 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 103)) 0 2 :=
  check_0103_0000
theorem check_0104_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 104)) 0 2 (by decide +kernel)
theorem block_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 104)) 0 2 :=
  check_0104_0000
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 2 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 2 :=
  check_0105_0000
theorem check_0106_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 106)) 0 2 (by decide +kernel)
theorem block_0106 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 2 :=
  check_0106_0000
theorem check_0107_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 0 8 (by decide +kernel)
theorem check_0107_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 8 8 (by decide +kernel)
theorem check_0107_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 16 8 (by decide +kernel)
theorem block_0107 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 107)) 0 8 24
  check_0107_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 107)) 8 16 24
  check_0107_0008
  check_0107_0016))
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 6 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 6 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
  check_0109_0000
theorem check_0110_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 110)) 0 6 (by decide +kernel)
theorem block_0110 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 110)) 0 6 :=
  check_0110_0000
theorem check_0111_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 111)) 0 6 (by decide +kernel)
theorem block_0111 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 111)) 0 6 :=
  check_0111_0000
theorem check_0112_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 112)) 0 6 (by decide +kernel)
theorem block_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 112)) 0 6 :=
  check_0112_0000
theorem check_0113_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 113)) 0 6 (by decide +kernel)
theorem block_0113 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 113)) 0 6 :=
  check_0113_0000
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6
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
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 114 :=
  FiniteChecks.interval_of_check validity 112 2 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 114
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 114
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 114
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 114 :=
  FiniteChecks.interval_of_check symmetry 112 2 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 114
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 114
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 114
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T6
