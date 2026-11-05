module
prelude
public import RootedSixExtra06
public import RawKindedFacePlacement
public import RootedSixExtra06OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
open ConcreteGrowth
abbrev blockCount : Nat := 126
noncomputable def template : Cell := ⟨10, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSixExtra06.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 63
 (.branch 31
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 95749552))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 98895328))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 102041104))))
 (.branch 5
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361324115505, 361626081030⟩, 109905544))
 (.leaf (⟨2, 4, 5517840, 5517840, 361055680050, 361626079350⟩, 113051320)))
 (.branch 6
 (.leaf (⟨2, 4, 5517840, 5517840, 356760712770, 361625649270⟩, 120915760))
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 124061536)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 288326448720, 361617786720⟩, 131925976))
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 135071752)))
 (.branch 10
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 142936192))
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 97781192))))
 (.branch 13
 (.branch 12
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 100926968))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 104072744)))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 361324115505, 361626081030⟩, 111937184))
 (.leaf (⟨2, 4, 5517600, 5517600, 361055680050, 361626079350⟩, 115082960))))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 356760712770, 361625649270⟩, 122947400))
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 126093176)))
 (.branch 18
 (.leaf (⟨2, 4, 5517600, 5517600, 288326448720, 361617786720⟩, 133957616))
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 137103392))))
 (.branch 21
 (.branch 20
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 144967832))
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 98108877)))
 (.branch 22
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 101254653))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 104400429)))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 361324115505, 361626081030⟩, 112264869))
 (.leaf (⟨2, 4, 5517345, 5517570, 361055680050, 361626079350⟩, 115410645)))
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 356760712770, 361625649270⟩, 123275085))
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 126420861))))
 (.branch 29
 (.branch 28
 (.leaf (⟨2, 4, 5517345, 5517570, 288326448720, 361617786720⟩, 134285301))
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 137431077)))
 (.branch 30
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 145295517))
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 1954862786920357927191905856)))))))
 (.branch 47
 (.branch 39
 (.branch 35
 (.branch 33
 (.branch 32
 (.leaf (⟨3, 4, 5517840, 5517840, 360937120545, 434925740295⟩, 2157965423715908529400121064))
 (.leaf (⟨3, 4, 5517840, 5517840, 348052218930, 434925342855⟩, 2361068060511459131608336272)))
 (.branch 34
 (.leaf (⟨3, 4, 5517840, 5517840, 288191112480, 434918490480⟩, 2564170697307009733816551480))
 (.leaf (⟨3, 4, 5517840, 5517840, 210613265730, 434917970055⟩, 2709244009303831592536705200))))
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 95880633))
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 99026409)))
 (.branch 38
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 102172185))
 (.leaf (⟨2, 4, 5513265, 5509890, 361324115505, 361626081030⟩, 110036625)))))
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf (⟨2, 4, 5513265, 5509890, 361055680050, 361626079350⟩, 113182401))
 (.leaf (⟨2, 4, 5513265, 5509890, 356760712770, 361625649270⟩, 121046841)))
 (.branch 42
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 124192617))
 (.leaf (⟨2, 4, 5513265, 5509890, 288326448720, 361617786720⟩, 132057057))))
 (.branch 45
 (.branch 44
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 135202833))
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 143067273)))
 (.branch 46
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 97453531))
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 100599307))))))
 (.branch 55
 (.branch 51
 (.branch 49
 (.branch 48
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 103745083))
 (.leaf (⟨2, 4, 5509170, 5509170, 361324115505, 361626081030⟩, 111609523)))
 (.branch 50
 (.leaf (⟨2, 4, 5509170, 5509170, 361055680050, 361626079350⟩, 114755299))
 (.leaf (⟨2, 4, 5509170, 5509170, 356760712770, 361625649270⟩, 122619739))))
 (.branch 53
 (.branch 52
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 125765515))
 (.leaf (⟨2, 4, 5509170, 5509170, 288326448720, 361617786720⟩, 133629955)))
 (.branch 54
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 136775731))
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 144640171)))))
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 1942773325809182408300234313))
 (.leaf (⟨3, 4, 5505825, 5513475, 360937120545, 434925740295⟩, 2145875962604733010508449521)))
 (.branch 58
 (.leaf (⟨3, 4, 5505825, 5513475, 348052218930, 434925342855⟩, 2348978599400283612716664729))
 (.leaf (⟨3, 4, 5505825, 5513475, 288191112480, 434918490480⟩, 2552081236195834214924879937))))
 (.branch 61
 (.branch 60
 (.leaf (⟨3, 4, 5505825, 5513475, 210613265730, 434917970055⟩, 2697154548192656073645033657))
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 97715679)))
 (.branch 62
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 100861455))
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 104007231))))))))
 (.branch 94
 (.branch 78
 (.branch 70
 (.branch 66
 (.branch 64
 (.leaf (⟨2, 4, 5443650, 5324850, 361324115505, 361626081030⟩, 111871671))
 (.branch 65
 (.leaf (⟨2, 4, 5443650, 5324850, 361055680050, 361626079350⟩, 115017447))
 (.leaf (⟨2, 4, 5443650, 5324850, 356760712770, 361625649270⟩, 122881887))))
 (.branch 68
 (.branch 67
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 126027663))
 (.leaf (⟨2, 4, 5443650, 5324850, 288326448720, 361617786720⟩, 133892103)))
 (.branch 69
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 137037879))
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 144902319)))))
 (.branch 74
 (.branch 72
 (.branch 71
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 96339392))
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 99485168)))
 (.branch 73
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 102630944))
 (.leaf (⟨2, 4, 5378115, 5309490, 361324115505, 361626081030⟩, 110495384))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 4, 5378115, 5309490, 361055680050, 361626079350⟩, 113641160))
 (.leaf (⟨2, 4, 5378115, 5309490, 356760712770, 361625649270⟩, 121505600)))
 (.branch 77
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 124651376))
 (.leaf (⟨2, 4, 5378115, 5309490, 288326448720, 361617786720⟩, 132515816))))))
 (.branch 86
 (.branch 82
 (.branch 80
 (.branch 79
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 135661592))
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 143526032)))
 (.branch 81
 (.leaf (⟨3, 4, 5309490, 5378115, 361742426640, 434925761040⟩, 1936728825841413964482348624))
 (.leaf (⟨3, 4, 5309490, 5378115, 360937120545, 434925740295⟩, 2139831462636964566690563832))))
 (.branch 84
 (.branch 83
 (.leaf (⟨3, 4, 5309490, 5378115, 348052218930, 434925342855⟩, 2342934099432515168898779040))
 (.leaf (⟨3, 4, 5309490, 5378115, 288191112480, 434918490480⟩, 2546036736228065771106994248)))
 (.branch 85
 (.leaf (⟨3, 4, 5309490, 5378115, 210613265730, 434917970055⟩, 2691110048224887629827147968))
 (.leaf (⟨2, 4, 4399440, 1393440, 361626105360, 361626105360⟩, 95815099)))))
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf (⟨2, 4, 4399440, 1393440, 361609328160, 361626104160⟩, 98960875))
 (.leaf (⟨2, 4, 4399440, 1393440, 361592550945, 361626104070⟩, 102106651)))
 (.branch 89
 (.leaf (⟨2, 4, 4399440, 1393440, 361324115505, 361626081030⟩, 109971091))
 (.leaf (⟨2, 4, 4399440, 1393440, 361055680050, 361626079350⟩, 113116867))))
 (.branch 92
 (.branch 91
 (.leaf (⟨2, 4, 4399440, 1393440, 356760712770, 361625649270⟩, 120981307))
 (.leaf (⟨2, 4, 4399440, 1393440, 352465745475, 361625618550⟩, 124127083)))
 (.branch 93
 (.leaf (⟨2, 4, 4399440, 1393440, 288326448720, 361617786720⟩, 131991523))
 (.leaf (⟨2, 4, 4399440, 1393440, 288041236050, 361617784950⟩, 135137299)))))))
 (.branch 110
 (.branch 102
 (.branch 98
 (.branch 96
 (.branch 95
 (.leaf (⟨2, 4, 4399440, 1393440, 215026792020, 361617201270⟩, 143001739))
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 96994772)))
 (.branch 97
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 100140548))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 103286324))))
 (.branch 100
 (.branch 99
 (.leaf (⟨2, 4, 4395090, 1392690, 361324115505, 361626081030⟩, 111150764))
 (.leaf (⟨2, 4, 4395090, 1392690, 361055680050, 361626079350⟩, 114296540)))
 (.branch 101
 (.leaf (⟨2, 4, 4395090, 1392690, 356760712770, 361625649270⟩, 122160980))
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 125306756)))))
 (.branch 106
 (.branch 104
 (.branch 103
 (.leaf (⟨2, 4, 4395090, 1392690, 288326448720, 361617786720⟩, 133171196))
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 136316972)))
 (.branch 105
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 144181412))
 (.leaf (⟨3, 4, 4396320, 2441520, 361742426640, 434925761040⟩, 1941564381543386651074561611))))
 (.branch 108
 (.branch 107
 (.leaf (⟨3, 4, 4396320, 2441520, 360937120545, 434925740295⟩, 2144667018338937253282776819))
 (.leaf (⟨3, 4, 4396320, 2441520, 348052218930, 434925342855⟩, 2347769655134487855490992027)))
 (.branch 109
 (.leaf (⟨3, 4, 4396320, 2441520, 288191112480, 434918490480⟩, 2550872291930038457699207235))
 (.leaf (⟨3, 4, 4396320, 2441520, 210613265730, 434917970055⟩, 2695945603926860316419360955))))))
 (.branch 118
 (.branch 114
 (.branch 112
 (.branch 111
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 96535996))
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 99681772)))
 (.branch 113
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 102827548))
 (.leaf (⟨2, 4, 3280980, 1070130, 361324115505, 361626081030⟩, 110691988))))
 (.branch 116
 (.branch 115
 (.leaf (⟨2, 4, 3280980, 1070130, 361055680050, 361626079350⟩, 113837764))
 (.leaf (⟨2, 4, 3280980, 1070130, 356760712770, 361625649270⟩, 121702204)))
 (.branch 117
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 124847980))
 (.leaf (⟨2, 4, 3280980, 1070130, 288326448720, 361617786720⟩, 132712420)))))
 (.branch 122
 (.branch 120
 (.branch 119
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 135858196))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 143722636)))
 (.branch 121
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 1940355658641334480885122636))
 (.leaf (⟨3, 4, 3212610, 2183235, 360937120545, 434925740295⟩, 2143458295436885083093337844))))
 (.branch 124
 (.branch 123
 (.leaf (⟨3, 4, 3212610, 2183235, 348052218930, 434925342855⟩, 2346560932232435685301553052))
 (.leaf (⟨3, 4, 3212610, 2183235, 288191112480, 434918490480⟩, 2549663569027986287509768260)))
 (.branch 125
 (.leaf (⟨3, 4, 3212610, 2183235, 210613265730, 434917970055⟩, 2694736881024808146229921980))
 (.leaf (⟨5, 4, 2442000, 4400400, 178365219600, 581519485200⟩, 3327236165391416453228447334032252535976402664174016158451770139510883629986178786298851583167671262207573246100508662366585204163140052481183871757210719974348454396492055070123691908306934456098829160869148808269724665275127114629995071301401501837656844013142817036714300143210904506768092125476651036188784030920154897345149199521811375433686074902799910738414318303476357036791736850090169430813536484718936584525435683577469828175683607232197311426510083911321155283351819365958162566947081992900142319266437240019718665334344820705387576371803496073018842087176603175160)))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 2300 :=
  Fin.ofNat 2300 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 20490
 (.branch 7182
 (.branch 5140
 (.branch 3105
 (.branch 3082
 (.branch 3077
 (.leaf 0)
 (.branch 3078
 (.leaf 1)
 (.leaf 2)))
 (.branch 3092
 (.branch 3084
 (.leaf 3)
 (.leaf 4))
 (.branch 3096
 (.leaf 5)
 (.leaf 6))))
 (.branch 5125
 (.branch 3120
 (.branch 3108
 (.leaf 7)
 (.leaf 8))
 (.branch 5123
 (.leaf 9)
 (.leaf 10)))
 (.branch 5130
 (.branch 5126
 (.leaf 11)
 (.leaf 12))
 (.branch 5132
 (.leaf 13)
 (.leaf 14)))))
 (.branch 6154
 (.branch 5168
 (.branch 5153
 (.branch 5144
 (.leaf 15)
 (.leaf 16))
 (.branch 5156
 (.leaf 17)
 (.leaf 18)))
 (.branch 6149
 (.branch 6147
 (.leaf 19)
 (.leaf 20))
 (.branch 6150
 (.leaf 21)
 (.leaf 22))))
 (.branch 6177
 (.branch 6164
 (.branch 6156
 (.leaf 23)
 (.leaf 24))
 (.branch 6168
 (.leaf 25)
 (.leaf 26)))
 (.branch 6192
 (.branch 6180
 (.leaf 27)
 (.leaf 28))
 (.branch 7175
 (.leaf 29)
 (.leaf 30))))))
 (.branch 12294
 (.branch 10252
 (.branch 10243
 (.branch 7205
 (.branch 7196
 (.leaf 31)
 (.leaf 32))
 (.branch 7220
 (.leaf 33)
 (.leaf 34)))
 (.branch 10246
 (.branch 10245
 (.leaf 35)
 (.leaf 36))
 (.branch 10250
 (.leaf 37)
 (.leaf 38))))
 (.branch 10276
 (.branch 10264
 (.branch 10260
 (.leaf 39)
 (.leaf 40))
 (.branch 10273
 (.leaf 41)
 (.leaf 42)))
 (.branch 12291
 (.branch 10288
 (.leaf 43)
 (.leaf 44))
 (.branch 12293
 (.leaf 45)
 (.leaf 46)))))
 (.branch 14343
 (.branch 12312
 (.branch 12300
 (.branch 12298
 (.leaf 47)
 (.leaf 48))
 (.branch 12308
 (.leaf 49)
 (.leaf 50)))
 (.branch 12324
 (.branch 12321
 (.leaf 51)
 (.leaf 52))
 (.branch 12336
 (.leaf 53)
 (.leaf 54))))
 (.branch 14388
 (.branch 14364
 (.branch 14350
 (.leaf 55)
 (.leaf 56))
 (.branch 14373
 (.leaf 57)
 (.leaf 58)))
 (.branch 20485
 (.branch 20483
 (.leaf 59)
 (.leaf 60))
 (.branch 20486
 (.leaf 61)
 (.leaf 62)))))))
 (.branch 33840
 (.branch 24612
 (.branch 24579
 (.branch 20504
 (.branch 20492
 (.leaf 63)
 (.branch 20500
 (.leaf 64)
 (.leaf 65)))
 (.branch 20516
 (.branch 20513
 (.leaf 66)
 (.leaf 67))
 (.branch 20528
 (.leaf 68)
 (.leaf 69))))
 (.branch 24588
 (.branch 24582
 (.branch 24581
 (.leaf 70)
 (.leaf 71))
 (.branch 24586
 (.leaf 72)
 (.leaf 73)))
 (.branch 24600
 (.branch 24596
 (.leaf 74)
 (.leaf 75))
 (.branch 24609
 (.leaf 76)
 (.leaf 77)))))
 (.branch 33797
 (.branch 28700
 (.branch 28679
 (.branch 24624
 (.leaf 78)
 (.leaf 79))
 (.branch 28686
 (.leaf 80)
 (.leaf 81)))
 (.branch 28724
 (.branch 28709
 (.leaf 82)
 (.leaf 83))
 (.branch 33795
 (.leaf 84)
 (.leaf 85))))
 (.branch 33812
 (.branch 33802
 (.branch 33798
 (.leaf 86)
 (.leaf 87))
 (.branch 33804
 (.leaf 88)
 (.leaf 89)))
 (.branch 33825
 (.branch 33816
 (.leaf 90)
 (.leaf 91))
 (.branch 33828
 (.leaf 92)
 (.leaf 93))))))
 (.branch 49155
 (.branch 36897
 (.branch 36874
 (.branch 36869
 (.branch 36867
 (.leaf 94)
 (.leaf 95))
 (.branch 36870
 (.leaf 96)
 (.leaf 97)))
 (.branch 36884
 (.branch 36876
 (.leaf 98)
 (.leaf 99))
 (.branch 36888
 (.leaf 100)
 (.leaf 101))))
 (.branch 37902
 (.branch 36912
 (.branch 36900
 (.leaf 102)
 (.leaf 103))
 (.branch 37895
 (.leaf 104)
 (.leaf 105)))
 (.branch 37925
 (.branch 37916
 (.leaf 106)
 (.leaf 107))
 (.branch 37940
 (.leaf 108)
 (.leaf 109)))))
 (.branch 49188
 (.branch 49164
 (.branch 49158
 (.branch 49157
 (.leaf 110)
 (.leaf 111))
 (.branch 49162
 (.leaf 112)
 (.leaf 113)))
 (.branch 49176
 (.branch 49172
 (.leaf 114)
 (.leaf 115))
 (.branch 49185
 (.leaf 116)
 (.leaf 117))))
 (.branch 53276
 (.branch 53255
 (.branch 49200
 (.leaf 118)
 (.leaf 119))
 (.branch 53262
 (.leaf 120)
 (.leaf 121)))
 (.branch 53300
 (.branch 53285
 (.leaf 122)
 (.leaf 123))
 (.branch 60475
 (.leaf 124)
 (.leaf 125))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSixExtra06.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra06.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
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
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 6 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
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
theorem check_0055_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 55)) 0 6 (by decide +kernel)
theorem block_0055 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 55)) 0 6 :=
  check_0055_0000
theorem check_0056_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 56)) 0 6 (by decide +kernel)
theorem block_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 56)) 0 6 :=
  check_0056_0000
theorem check_0057_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 57)) 0 6 (by decide +kernel)
theorem block_0057 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 57)) 0 6 :=
  check_0057_0000
theorem check_0058_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 58)) 0 6 (by decide +kernel)
theorem block_0058 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 58)) 0 6 :=
  check_0058_0000
theorem check_0059_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 59)) 0 6 (by decide +kernel)
theorem block_0059 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 59)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
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
theorem check_0080_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 80)) 0 6 (by decide +kernel)
theorem block_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 80)) 0 6 :=
  check_0080_0000
theorem check_0081_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 81)) 0 6 (by decide +kernel)
theorem block_0081 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 81)) 0 6 :=
  check_0081_0000
theorem check_0082_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 82)) 0 6 (by decide +kernel)
theorem block_0082 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 82)) 0 6 :=
  check_0082_0000
theorem check_0083_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 83)) 0 6 (by decide +kernel)
theorem block_0083 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 83)) 0 6 :=
  check_0083_0000
theorem check_0084_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 84)) 0 6 (by decide +kernel)
theorem block_0084 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 84)) 0 6 :=
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
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 6 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 6 :=
  check_0105_0000
theorem check_0106_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 106)) 0 6 (by decide +kernel)
theorem block_0106 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 6 :=
  check_0106_0000
theorem check_0107_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 107)) 0 6 (by decide +kernel)
theorem block_0107 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 107)) 0 6 :=
  check_0107_0000
theorem check_0108_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 108)) 0 6 (by decide +kernel)
theorem block_0108 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 108)) 0 6 :=
  check_0108_0000
theorem check_0109_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 109)) 0 6 (by decide +kernel)
theorem block_0109 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 109)) 0 6 :=
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
theorem check_0116_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 116)) 0 2 (by decide +kernel)
theorem block_0116 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 116)) 0 2 :=
  check_0116_0000
theorem check_0117_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 117)) 0 2 (by decide +kernel)
theorem block_0117 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 117)) 0 2 :=
  check_0117_0000
theorem check_0118_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 118)) 0 2 (by decide +kernel)
theorem block_0118 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 118)) 0 2 :=
  check_0118_0000
theorem check_0119_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 119)) 0 2 (by decide +kernel)
theorem block_0119 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 119)) 0 2 :=
  check_0119_0000
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 6 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 6 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 6 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 6 :=
  check_0121_0000
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 6 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 6 :=
  check_0122_0000
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 6 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 6 :=
  check_0123_0000
theorem check_0124_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 124)) 0 6 (by decide +kernel)
theorem block_0124 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 6 :=
  check_0124_0000
theorem check_0125_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 0 8 (by decide +kernel)
theorem check_0125_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 8 8 (by decide +kernel)
theorem check_0125_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 16 8 (by decide +kernel)
theorem check_0125_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 24 32 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 24 8 (by decide +kernel)
theorem check_0125_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 32 40 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 32 8 (by decide +kernel)
theorem check_0125_0040 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 40 48 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 40 8 (by decide +kernel)
theorem check_0125_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 48 56 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 48 8 (by decide +kernel)
theorem check_0125_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 56 64 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 56 8 (by decide +kernel)
theorem check_0125_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 64 72 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 64 8 (by decide +kernel)
theorem check_0125_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 72 80 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 72 8 (by decide +kernel)
theorem check_0125_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 80 88 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 80 8 (by decide +kernel)
theorem check_0125_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 88 96 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 88 8 (by decide +kernel)
theorem check_0125_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 96 104 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 96 8 (by decide +kernel)
theorem check_0125_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 104 112 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 104 8 (by decide +kernel)
theorem check_0125_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 112 120 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 112 8 (by decide +kernel)
theorem block_0125 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 120 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 0 56 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 0 24 56
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 0 8 24
  check_0125_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 8 16 24
  check_0125_0008
  check_0125_0016))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 24 40 56
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 24 32 40
  check_0125_0024
  check_0125_0032)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 40 48 56
  check_0125_0040
  check_0125_0048)))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 56 88 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 56 72 88
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 56 64 72
  check_0125_0056
  check_0125_0064)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 72 80 88
  check_0125_0072
  check_0125_0080))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 88 104 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 88 96 104
  check_0125_0088
  check_0125_0096)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 125)) 104 112 120
  check_0125_0104
  check_0125_0112))))
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
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
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 126 :=
  FiniteChecks.interval_of_check validity 112 14 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 126
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 126
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 126
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 126 :=
  FiniteChecks.interval_of_check symmetry 112 14 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 126
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 126
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 126
  metadata_symmetry_0096
  metadata_symmetry_0112)))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
