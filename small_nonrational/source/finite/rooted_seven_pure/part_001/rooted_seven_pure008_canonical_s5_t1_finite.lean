module
prelude
public import RootedSevenPure008
public import RawKindedFacePlacement
public import RootedSevenPure008OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 160
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenPure008.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 80
 (.branch 40
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨2, 3, 274960, 274960, 434918491920, 288459547920⟩, 11206826))
 (.leaf (⟨2, 3, 274960, 274960, 434917443360, 288459546960⟩, 14942435)))
 (.branch 3
 (.leaf (⟨2, 3, 274960, 274960, 434916394785, 288459546885⟩, 20054321))
 (.branch 4
 (.leaf (⟨2, 3, 274960, 274960, 434900666160, 288459527760⟩, 16318712))
 (.leaf (⟨2, 3, 274960, 274960, 434899617585, 288459527685⟩, 23789930)))))
 (.branch 7
 (.branch 6
 (.leaf (⟨2, 3, 274960, 274960, 434882840370, 288459526245⟩, 32637425))
 (.leaf (⟨2, 3, 274960, 274960, 434631182145, 288459159045⟩, 27525539)))
 (.branch 8
 (.leaf (⟨2, 3, 274960, 274960, 434614404930, 288459157605⟩, 36373034))
 (.branch 9
 (.leaf (⟨2, 3, 274960, 274960, 430336214865, 288452277765⟩, 28901816))
 (.leaf (⟨2, 3, 274960, 274960, 430319437650, 288452276325⟩, 40108643))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (⟨2, 3, 274960, 274960, 430051002195, 288452249445⟩, 45220529))
 (.leaf (⟨2, 3, 274960, 274960, 425756034900, 288451757925⟩, 47973083)))
 (.branch 13
 (.leaf (⟨2, 3, 274960, 274960, 361599960930, 288326447205⟩, 41484920))
 (.branch 14
 (.leaf (⟨2, 3, 274960, 274960, 361331525475, 288326420325⟩, 46596806))
 (.leaf (⟨2, 3, 274960, 274960, 288317081445, 288317081445⟩, 49349360)))))
 (.branch 17
 (.branch 16
 (.leaf (⟨2, 3, 274720, 274720, 434918491920, 288459547920⟩, 10748071))
 (.leaf (⟨2, 3, 274720, 274720, 434917443360, 288459546960⟩, 14483680)))
 (.branch 18
 (.leaf (⟨2, 3, 274720, 274720, 434916394785, 288459546885⟩, 19595566))
 (.branch 19
 (.leaf (⟨2, 3, 274720, 274720, 434900666160, 288459527760⟩, 15859957))
 (.leaf (⟨2, 3, 274720, 274720, 434899617585, 288459527685⟩, 23331175)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 3, 274720, 274720, 434882840370, 288459526245⟩, 32178670))
 (.leaf (⟨2, 3, 274720, 274720, 434631182145, 288459159045⟩, 27066784)))
 (.branch 23
 (.leaf (⟨2, 3, 274720, 274720, 434614404930, 288459157605⟩, 35914279))
 (.branch 24
 (.leaf (⟨2, 3, 274720, 274720, 430336214865, 288452277765⟩, 28443061))
 (.leaf (⟨2, 3, 274720, 274720, 430319437650, 288452276325⟩, 39649888)))))
 (.branch 27
 (.branch 26
 (.leaf (⟨2, 3, 274720, 274720, 430051002195, 288452249445⟩, 44761774))
 (.leaf (⟨2, 3, 274720, 274720, 425756034900, 288451757925⟩, 47514328)))
 (.branch 28
 (.leaf (⟨2, 3, 274720, 274720, 361599960930, 288326447205⟩, 41026165))
 (.branch 29
 (.leaf (⟨2, 3, 274720, 274720, 361331525475, 288326420325⟩, 46138051))
 (.leaf (⟨2, 3, 274720, 274720, 288317081445, 288317081445⟩, 48890605))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (⟨2, 3, 274465, 274690, 434918491920, 288459547920⟩, 10813608))
 (.leaf (⟨2, 3, 274465, 274690, 434917443360, 288459546960⟩, 14549217)))
 (.branch 33
 (.leaf (⟨2, 3, 274465, 274690, 434916394785, 288459546885⟩, 19661103))
 (.branch 34
 (.leaf (⟨2, 3, 274465, 274690, 434900666160, 288459527760⟩, 15925494))
 (.leaf (⟨2, 3, 274465, 274690, 434899617585, 288459527685⟩, 23396712)))))
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 3, 274465, 274690, 434882840370, 288459526245⟩, 32244207))
 (.leaf (⟨2, 3, 274465, 274690, 434631182145, 288459159045⟩, 27132321)))
 (.branch 38
 (.leaf (⟨2, 3, 274465, 274690, 434614404930, 288459157605⟩, 35979816))
 (.branch 39
 (.leaf (⟨2, 3, 274465, 274690, 430336214865, 288452277765⟩, 28508598))
 (.leaf (⟨2, 3, 274465, 274690, 430319437650, 288452276325⟩, 39715425))))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.branch 41
 (.leaf (⟨2, 3, 274465, 274690, 430051002195, 288452249445⟩, 44827311))
 (.leaf (⟨2, 3, 274465, 274690, 425756034900, 288451757925⟩, 47579865)))
 (.branch 43
 (.leaf (⟨2, 3, 274465, 274690, 361599960930, 288326447205⟩, 41091702))
 (.branch 44
 (.leaf (⟨2, 3, 274465, 274690, 361331525475, 288326420325⟩, 46203588))
 (.leaf (⟨2, 3, 274465, 274690, 288317081445, 288317081445⟩, 48956142)))))
 (.branch 47
 (.branch 46
 (.leaf (⟨3, 3, 274960, 274960, 434925761040, 361742426640⟩, 108804965551153803897471069))
 (.leaf (⟨3, 3, 274960, 274960, 434908984080, 361742411280⟩, 152326959150200361513517185)))
 (.branch 48
 (.leaf (⟨3, 3, 274960, 274960, 434892206880, 361742410080⟩, 221236782348690744405590202))
 (.branch 49
 (.leaf (⟨3, 3, 274960, 274960, 434606994465, 361742102790⟩, 315534435146624952573690120))
 (.leaf (⟨3, 3, 274960, 274960, 430043591985, 361736181510⟩, 384444258345115335465763137))))))
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf (⟨3, 3, 274960, 274960, 425748624705, 361735751430⟩, 453354081543605718357836154))
 (.leaf (⟨3, 3, 274960, 274960, 425480189250, 361735749750⟩, 616561557540030309418009089)))
 (.branch 53
 (.leaf (⟨3, 3, 274960, 274960, 361055680050, 361626079350⟩, 547651734341539926525936072))
 (.branch 54
 (.leaf (⟨3, 3, 274960, 274960, 288041236050, 361617784950⟩, 685471380738520692310082106))
 (.leaf (⟨3, 3, 274960, 274960, 283746268755, 361617754230⟩, 779769033536454900478182024)))))
 (.branch 57
 (.branch 56
 (.leaf (⟨2, 3, 270385, 267010, 434918491920, 288459547920⟩, 11272365))
 (.leaf (⟨2, 3, 270385, 267010, 434917443360, 288459546960⟩, 15007974)))
 (.branch 58
 (.leaf (⟨2, 3, 270385, 267010, 434916394785, 288459546885⟩, 20119860))
 (.branch 59
 (.leaf (⟨2, 3, 270385, 267010, 434900666160, 288459527760⟩, 16384251))
 (.leaf (⟨2, 3, 270385, 267010, 434899617585, 288459527685⟩, 23855469)))))))
 (.branch 70
 (.branch 65
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 3, 270385, 267010, 434882840370, 288459526245⟩, 32702964))
 (.leaf (⟨2, 3, 270385, 267010, 434631182145, 288459159045⟩, 27591078)))
 (.branch 63
 (.leaf (⟨2, 3, 270385, 267010, 434614404930, 288459157605⟩, 36438573))
 (.branch 64
 (.leaf (⟨2, 3, 270385, 267010, 430336214865, 288452277765⟩, 28967355))
 (.leaf (⟨2, 3, 270385, 267010, 430319437650, 288452276325⟩, 40174182)))))
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 3, 270385, 267010, 430051002195, 288452249445⟩, 45286068))
 (.leaf (⟨2, 3, 270385, 267010, 425756034900, 288451757925⟩, 48038622)))
 (.branch 68
 (.leaf (⟨2, 3, 270385, 267010, 361599960930, 288326447205⟩, 41550459))
 (.branch 69
 (.leaf (⟨2, 3, 270385, 267010, 361331525475, 288326420325⟩, 46662345))
 (.leaf (⟨2, 3, 270385, 267010, 288317081445, 288317081445⟩, 49414899))))))
 (.branch 75
 (.branch 72
 (.branch 71
 (.leaf (⟨2, 3, 266290, 266290, 434918491920, 288459547920⟩, 11075750))
 (.leaf (⟨2, 3, 266290, 266290, 434917443360, 288459546960⟩, 14811359)))
 (.branch 73
 (.leaf (⟨2, 3, 266290, 266290, 434916394785, 288459546885⟩, 19923245))
 (.branch 74
 (.leaf (⟨2, 3, 266290, 266290, 434900666160, 288459527760⟩, 16187636))
 (.leaf (⟨2, 3, 266290, 266290, 434899617585, 288459527685⟩, 23658854)))))
 (.branch 77
 (.branch 76
 (.leaf (⟨2, 3, 266290, 266290, 434882840370, 288459526245⟩, 32506349))
 (.leaf (⟨2, 3, 266290, 266290, 434631182145, 288459159045⟩, 27394463)))
 (.branch 78
 (.leaf (⟨2, 3, 266290, 266290, 434614404930, 288459157605⟩, 36241958))
 (.branch 79
 (.leaf (⟨2, 3, 266290, 266290, 430336214865, 288452277765⟩, 28770740))
 (.leaf (⟨2, 3, 266290, 266290, 430319437650, 288452276325⟩, 39977567)))))))))
 (.branch 120
 (.branch 100
 (.branch 90
 (.branch 85
 (.branch 82
 (.branch 81
 (.leaf (⟨2, 3, 266290, 266290, 430051002195, 288452249445⟩, 45089453))
 (.leaf (⟨2, 3, 266290, 266290, 425756034900, 288451757925⟩, 47842007)))
 (.branch 83
 (.leaf (⟨2, 3, 266290, 266290, 361599960930, 288326447205⟩, 41353844))
 (.branch 84
 (.leaf (⟨2, 3, 266290, 266290, 361331525475, 288326420325⟩, 46465730))
 (.leaf (⟨2, 3, 266290, 266290, 288317081445, 288317081445⟩, 49218284)))))
 (.branch 87
 (.branch 86
 (.leaf (⟨3, 3, 262945, 270595, 434925761040, 361742426640⟩, 110013965158589139955351644))
 (.leaf (⟨3, 3, 262945, 270595, 434908984080, 361742411280⟩, 153535958757635697571397760)))
 (.branch 88
 (.leaf (⟨3, 3, 262945, 270595, 434892206880, 361742410080⟩, 222445781956126080463470777))
 (.branch 89
 (.leaf (⟨3, 3, 262945, 270595, 434606994465, 361742102790⟩, 316743434754060288631570695))
 (.leaf (⟨3, 3, 262945, 270595, 430043591985, 361736181510⟩, 385653257952550671523643712))))))
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (⟨3, 3, 262945, 270595, 425748624705, 361735751430⟩, 454563081151041054415716729))
 (.leaf (⟨3, 3, 262945, 270595, 425480189250, 361735749750⟩, 617770557147465645475889664)))
 (.branch 93
 (.leaf (⟨3, 3, 262945, 270595, 361055680050, 361626079350⟩, 548860733948975262583816647))
 (.branch 94
 (.leaf (⟨3, 3, 262945, 270595, 288041236050, 361617784950⟩, 686680380345956028367962681))
 (.leaf (⟨3, 3, 262945, 270595, 283746268755, 361617754230⟩, 780978033143890236536062599)))))
 (.branch 97
 (.branch 96
 (.leaf (⟨2, 3, 205120, 82720, 434918491920, 288459547920⟩, 11272365))
 (.leaf (⟨2, 3, 205120, 82720, 434917443360, 288459546960⟩, 15007974)))
 (.branch 98
 (.leaf (⟨2, 3, 205120, 82720, 434916394785, 288459546885⟩, 20119860))
 (.branch 99
 (.leaf (⟨2, 3, 205120, 82720, 434900666160, 288459527760⟩, 16384251))
 (.leaf (⟨2, 3, 205120, 82720, 434899617585, 288459527685⟩, 23855469)))))))
 (.branch 110
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf (⟨2, 3, 205120, 82720, 434882840370, 288459526245⟩, 32702964))
 (.leaf (⟨2, 3, 205120, 82720, 434631182145, 288459159045⟩, 27591078)))
 (.branch 103
 (.leaf (⟨2, 3, 205120, 82720, 434614404930, 288459157605⟩, 36438573))
 (.branch 104
 (.leaf (⟨2, 3, 205120, 82720, 430336214865, 288452277765⟩, 28967355))
 (.leaf (⟨2, 3, 205120, 82720, 430319437650, 288452276325⟩, 40174182)))))
 (.branch 107
 (.branch 106
 (.leaf (⟨2, 3, 205120, 82720, 430051002195, 288452249445⟩, 45286068))
 (.leaf (⟨2, 3, 205120, 82720, 425756034900, 288451757925⟩, 48038622)))
 (.branch 108
 (.leaf (⟨2, 3, 205120, 82720, 361599960930, 288326447205⟩, 41550459))
 (.branch 109
 (.leaf (⟨2, 3, 205120, 82720, 361331525475, 288326420325⟩, 46662345))
 (.leaf (⟨2, 3, 205120, 82720, 288317081445, 288317081445⟩, 49414899))))))
 (.branch 115
 (.branch 112
 (.branch 111
 (.leaf (⟨2, 3, 200770, 81970, 434918491920, 288459547920⟩, 10944676))
 (.leaf (⟨2, 3, 200770, 81970, 434917443360, 288459546960⟩, 14680285)))
 (.branch 113
 (.leaf (⟨2, 3, 200770, 81970, 434916394785, 288459546885⟩, 19792171))
 (.branch 114
 (.leaf (⟨2, 3, 200770, 81970, 434900666160, 288459527760⟩, 16056562))
 (.leaf (⟨2, 3, 200770, 81970, 434899617585, 288459527685⟩, 23527780)))))
 (.branch 117
 (.branch 116
 (.leaf (⟨2, 3, 200770, 81970, 434882840370, 288459526245⟩, 32375275))
 (.leaf (⟨2, 3, 200770, 81970, 434631182145, 288459159045⟩, 27263389)))
 (.branch 118
 (.leaf (⟨2, 3, 200770, 81970, 434614404930, 288459157605⟩, 36110884))
 (.branch 119
 (.leaf (⟨2, 3, 200770, 81970, 430336214865, 288452277765⟩, 28639666))
 (.leaf (⟨2, 3, 200770, 81970, 430319437650, 288452276325⟩, 39846493))))))))
 (.branch 140
 (.branch 130
 (.branch 125
 (.branch 122
 (.branch 121
 (.leaf (⟨2, 3, 200770, 81970, 430051002195, 288452249445⟩, 44958379))
 (.leaf (⟨2, 3, 200770, 81970, 425756034900, 288451757925⟩, 47710933)))
 (.branch 123
 (.leaf (⟨2, 3, 200770, 81970, 361599960930, 288326447205⟩, 41222770))
 (.branch 124
 (.leaf (⟨2, 3, 200770, 81970, 361331525475, 288326420325⟩, 46334656))
 (.leaf (⟨2, 3, 200770, 81970, 288317081445, 288317081445⟩, 49087210)))))
 (.branch 127
 (.branch 126
 (.leaf (⟨3, 3, 201760, 147760, 434925761040, 361742426640⟩, 110013965158589139955351644))
 (.leaf (⟨3, 3, 201760, 147760, 434908984080, 361742411280⟩, 153535958757635697571397760)))
 (.branch 128
 (.leaf (⟨3, 3, 201760, 147760, 434892206880, 361742410080⟩, 222445781956126080463470777))
 (.branch 129
 (.leaf (⟨3, 3, 201760, 147760, 434606994465, 361742102790⟩, 316743434754060288631570695))
 (.leaf (⟨3, 3, 201760, 147760, 430043591985, 361736181510⟩, 385653257952550671523643712))))))
 (.branch 135
 (.branch 132
 (.branch 131
 (.leaf (⟨3, 3, 201760, 147760, 425748624705, 361735751430⟩, 454563081151041054415716729))
 (.leaf (⟨3, 3, 201760, 147760, 425480189250, 361735749750⟩, 617770557147465645475889664)))
 (.branch 133
 (.leaf (⟨3, 3, 201760, 147760, 361055680050, 361626079350⟩, 548860733948975262583816647))
 (.branch 134
 (.leaf (⟨3, 3, 201760, 147760, 288041236050, 361617784950⟩, 686680380345956028367962681))
 (.leaf (⟨3, 3, 201760, 147760, 283746268755, 361617754230⟩, 780978033143890236536062599)))))
 (.branch 137
 (.branch 136
 (.leaf (⟨2, 3, 135235, 66610, 434918491920, 288459547920⟩, 11468974))
 (.leaf (⟨2, 3, 135235, 66610, 434917443360, 288459546960⟩, 15204583)))
 (.branch 138
 (.leaf (⟨2, 3, 135235, 66610, 434916394785, 288459546885⟩, 20316469))
 (.branch 139
 (.leaf (⟨2, 3, 135235, 66610, 434900666160, 288459527760⟩, 16580860))
 (.leaf (⟨2, 3, 135235, 66610, 434899617585, 288459527685⟩, 24052078)))))))
 (.branch 150
 (.branch 145
 (.branch 142
 (.branch 141
 (.leaf (⟨2, 3, 135235, 66610, 434882840370, 288459526245⟩, 32899573))
 (.leaf (⟨2, 3, 135235, 66610, 434631182145, 288459159045⟩, 27787687)))
 (.branch 143
 (.leaf (⟨2, 3, 135235, 66610, 434614404930, 288459157605⟩, 36635182))
 (.branch 144
 (.leaf (⟨2, 3, 135235, 66610, 430336214865, 288452277765⟩, 29163964))
 (.leaf (⟨2, 3, 135235, 66610, 430319437650, 288452276325⟩, 40370791)))))
 (.branch 147
 (.branch 146
 (.leaf (⟨2, 3, 135235, 66610, 430051002195, 288452249445⟩, 45482677))
 (.leaf (⟨2, 3, 135235, 66610, 425756034900, 288451757925⟩, 48235231)))
 (.branch 148
 (.leaf (⟨2, 3, 135235, 66610, 361599960930, 288326447205⟩, 41747068))
 (.branch 149
 (.leaf (⟨2, 3, 135235, 66610, 361331525475, 288326420325⟩, 46858954))
 (.leaf (⟨2, 3, 135235, 66610, 288317081445, 288317081445⟩, 49611508))))))
 (.branch 155
 (.branch 152
 (.branch 151
 (.leaf (⟨3, 3, 66610, 135235, 434925761040, 361742426640⟩, 113640724169563071043010649))
 (.leaf (⟨3, 3, 66610, 135235, 434908984080, 361742411280⟩, 157162717768609628659056765)))
 (.branch 153
 (.leaf (⟨3, 3, 66610, 135235, 434892206880, 361742410080⟩, 226072540967100011551129782))
 (.branch 154
 (.leaf (⟨3, 3, 66610, 135235, 434606994465, 361742102790⟩, 320370193765034219719229700))
 (.leaf (⟨3, 3, 66610, 135235, 430043591985, 361736181510⟩, 389280016963524602611302717)))))
 (.branch 157
 (.branch 156
 (.leaf (⟨3, 3, 66610, 135235, 425748624705, 361735751430⟩, 458189840162014985503375734))
 (.leaf (⟨3, 3, 66610, 135235, 425480189250, 361735749750⟩, 621397316158439576563548669)))
 (.branch 158
 (.leaf (⟨3, 3, 66610, 135235, 361055680050, 361626079350⟩, 552487492959949193671475652))
 (.branch 159
 (.leaf (⟨3, 3, 66610, 135235, 288041236050, 361617784950⟩, 690307139356929959455621686))
 (.leaf (⟨3, 3, 66610, 135235, 283746268755, 361617754230⟩, 784604792154864167623721604))))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 758 :=
  Fin.ofNat 758 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 12328
 (.branch 6184
 (.branch 5132
 (.branch 3112
 (.branch 3084
 (.branch 3078
 (.branch 3077
 (.leaf 0)
 (.leaf 1))
 (.branch 3081
 (.leaf 2)
 (.branch 3082
 (.leaf 3)
 (.leaf 4))))
 (.branch 3092
 (.branch 3090
 (.leaf 5)
 (.leaf 6))
 (.branch 3106
 (.leaf 7)
 (.branch 3108
 (.leaf 8)
 (.leaf 9)))))
 (.branch 5123
 (.branch 3140
 (.branch 3120
 (.leaf 10)
 (.leaf 11))
 (.branch 3144
 (.leaf 12)
 (.branch 3168
 (.leaf 13)
 (.leaf 14))))
 (.branch 5126
 (.branch 5125
 (.leaf 15)
 (.leaf 16))
 (.branch 5129
 (.leaf 17)
 (.branch 5130
 (.leaf 18)
 (.leaf 19))))))
 (.branch 6147
 (.branch 5160
 (.branch 5140
 (.branch 5138
 (.leaf 20)
 (.leaf 21))
 (.branch 5154
 (.leaf 22)
 (.branch 5156
 (.leaf 23)
 (.leaf 24))))
 (.branch 5188
 (.branch 5168
 (.leaf 25)
 (.leaf 26))
 (.branch 5192
 (.leaf 27)
 (.branch 5216
 (.leaf 28)
 (.leaf 29)))))
 (.branch 6156
 (.branch 6150
 (.branch 6149
 (.leaf 30)
 (.leaf 31))
 (.branch 6153
 (.leaf 32)
 (.branch 6154
 (.leaf 33)
 (.leaf 34))))
 (.branch 6164
 (.branch 6162
 (.leaf 35)
 (.leaf 36))
 (.branch 6178
 (.leaf 37)
 (.branch 6180
 (.leaf 38)
 (.leaf 39)))))))
 (.branch 10252
 (.branch 7218
 (.branch 7175
 (.branch 6212
 (.branch 6192
 (.leaf 40)
 (.leaf 41))
 (.branch 6216
 (.leaf 42)
 (.branch 6240
 (.leaf 43)
 (.leaf 44))))
 (.branch 7181
 (.branch 7179
 (.leaf 45)
 (.leaf 46))
 (.branch 7190
 (.leaf 47)
 (.branch 7210
 (.leaf 48)
 (.leaf 49)))))
 (.branch 10243
 (.branch 7244
 (.branch 7220
 (.leaf 50)
 (.leaf 51))
 (.branch 7268
 (.leaf 52)
 (.branch 7272
 (.leaf 53)
 (.leaf 54))))
 (.branch 10246
 (.branch 10245
 (.leaf 55)
 (.leaf 56))
 (.branch 10249
 (.leaf 57)
 (.branch 10250
 (.leaf 58)
 (.leaf 59))))))
 (.branch 12291
 (.branch 10280
 (.branch 10260
 (.branch 10258
 (.leaf 60)
 (.leaf 61))
 (.branch 10274
 (.leaf 62)
 (.branch 10276
 (.leaf 63)
 (.leaf 64))))
 (.branch 10308
 (.branch 10288
 (.leaf 65)
 (.leaf 66))
 (.branch 10312
 (.leaf 67)
 (.branch 10336
 (.leaf 68)
 (.leaf 69)))))
 (.branch 12300
 (.branch 12294
 (.branch 12293
 (.leaf 70)
 (.leaf 71))
 (.branch 12297
 (.leaf 72)
 (.branch 12298
 (.leaf 73)
 (.leaf 74))))
 (.branch 12308
 (.branch 12306
 (.leaf 75)
 (.leaf 76))
 (.branch 12322
 (.leaf 77)
 (.branch 12324
 (.leaf 78)
 (.leaf 79))))))))
 (.branch 20520
 (.branch 17420
 (.branch 14386
 (.branch 14343
 (.branch 12356
 (.branch 12336
 (.leaf 80)
 (.leaf 81))
 (.branch 12360
 (.leaf 82)
 (.branch 12384
 (.leaf 83)
 (.leaf 84))))
 (.branch 14349
 (.branch 14347
 (.leaf 85)
 (.leaf 86))
 (.branch 14358
 (.leaf 87)
 (.branch 14378
 (.leaf 88)
 (.leaf 89)))))
 (.branch 17411
 (.branch 14412
 (.branch 14388
 (.leaf 90)
 (.leaf 91))
 (.branch 14436
 (.leaf 92)
 (.branch 14440
 (.leaf 93)
 (.leaf 94))))
 (.branch 17414
 (.branch 17413
 (.leaf 95)
 (.leaf 96))
 (.branch 17417
 (.leaf 97)
 (.branch 17418
 (.leaf 98)
 (.leaf 99))))))
 (.branch 20483
 (.branch 17448
 (.branch 17428
 (.branch 17426
 (.leaf 100)
 (.leaf 101))
 (.branch 17442
 (.leaf 102)
 (.branch 17444
 (.leaf 103)
 (.leaf 104))))
 (.branch 17476
 (.branch 17456
 (.leaf 105)
 (.leaf 106))
 (.branch 17480
 (.leaf 107)
 (.branch 17504
 (.leaf 108)
 (.leaf 109)))))
 (.branch 20492
 (.branch 20486
 (.branch 20485
 (.leaf 110)
 (.leaf 111))
 (.branch 20489
 (.leaf 112)
 (.branch 20490
 (.leaf 113)
 (.leaf 114))))
 (.branch 20500
 (.branch 20498
 (.leaf 115)
 (.leaf 116))
 (.branch 20514
 (.leaf 117)
 (.branch 20516
 (.leaf 118)
 (.leaf 119)))))))
 (.branch 24588
 (.branch 21554
 (.branch 21511
 (.branch 20548
 (.branch 20528
 (.leaf 120)
 (.leaf 121))
 (.branch 20552
 (.leaf 122)
 (.branch 20576
 (.leaf 123)
 (.leaf 124))))
 (.branch 21517
 (.branch 21515
 (.leaf 125)
 (.leaf 126))
 (.branch 21526
 (.leaf 127)
 (.branch 21546
 (.leaf 128)
 (.leaf 129)))))
 (.branch 24579
 (.branch 21580
 (.branch 21556
 (.leaf 130)
 (.leaf 131))
 (.branch 21604
 (.leaf 132)
 (.branch 21608
 (.leaf 133)
 (.leaf 134))))
 (.branch 24582
 (.branch 24581
 (.leaf 135)
 (.leaf 136))
 (.branch 24585
 (.leaf 137)
 (.branch 24586
 (.leaf 138)
 (.leaf 139))))))
 (.branch 28679
 (.branch 24616
 (.branch 24596
 (.branch 24594
 (.leaf 140)
 (.leaf 141))
 (.branch 24610
 (.leaf 142)
 (.branch 24612
 (.leaf 143)
 (.leaf 144))))
 (.branch 24644
 (.branch 24624
 (.leaf 145)
 (.leaf 146))
 (.branch 24648
 (.leaf 147)
 (.branch 24672
 (.leaf 148)
 (.leaf 149)))))
 (.branch 28722
 (.branch 28685
 (.branch 28683
 (.leaf 150)
 (.leaf 151))
 (.branch 28694
 (.leaf 152)
 (.branch 28714
 (.leaf 153)
 (.leaf 154))))
 (.branch 28748
 (.branch 28724
 (.leaf 155)
 (.leaf 156))
 (.branch 28772
 (.leaf 157)
 (.branch 28776
 (.leaf 158)
 (.leaf 159)))))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 5 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 5 (raw b) template root FacetUniverses.RootedSevenPure008.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenPure008.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
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
theorem check_0049_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 49)) 0 6 (by decide +kernel)
theorem block_0049 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 49)) 0 6 :=
  check_0049_0000
theorem check_0050_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 50)) 0 6 (by decide +kernel)
theorem block_0050 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 50)) 0 6 :=
  check_0050_0000
theorem check_0051_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 51)) 0 6 (by decide +kernel)
theorem block_0051 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 51)) 0 6 :=
  check_0051_0000
theorem check_0052_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 52)) 0 6 (by decide +kernel)
theorem block_0052 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 52)) 0 6 :=
  check_0052_0000
theorem check_0053_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 53)) 0 6 (by decide +kernel)
theorem block_0053 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 53)) 0 6 :=
  check_0053_0000
theorem check_0054_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 54)) 0 6 (by decide +kernel)
theorem block_0054 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 54)) 0 6 :=
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
end Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
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
theorem check_0085_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 85)) 0 6 (by decide +kernel)
theorem block_0085 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 85)) 0 6 :=
  check_0085_0000
theorem check_0086_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 86)) 0 6 (by decide +kernel)
theorem block_0086 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 86)) 0 6 :=
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
theorem check_0105_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 105)) 0 2 (by decide +kernel)
theorem block_0105 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 105)) 0 2 :=
  check_0105_0000
theorem check_0106_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 106)) 0 2 (by decide +kernel)
theorem block_0106 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 106)) 0 2 :=
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
theorem check_0120_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 120)) 0 2 (by decide +kernel)
theorem block_0120 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 120)) 0 2 :=
  check_0120_0000
theorem check_0121_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 121)) 0 2 (by decide +kernel)
theorem block_0121 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 121)) 0 2 :=
  check_0121_0000
theorem check_0122_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 122)) 0 2 (by decide +kernel)
theorem block_0122 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 122)) 0 2 :=
  check_0122_0000
theorem check_0123_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 123)) 0 2 (by decide +kernel)
theorem block_0123 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 123)) 0 2 :=
  check_0123_0000
theorem check_0124_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 124)) 0 2 (by decide +kernel)
theorem block_0124 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 124)) 0 2 :=
  check_0124_0000
theorem check_0125_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 125)) 0 6 (by decide +kernel)
theorem block_0125 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 125)) 0 6 :=
  check_0125_0000
theorem check_0126_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 126)) 0 6 (by decide +kernel)
theorem block_0126 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 126)) 0 6 :=
  check_0126_0000
theorem check_0127_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 127)) 0 6 (by decide +kernel)
theorem block_0127 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 127)) 0 6 :=
  check_0127_0000
end Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
theorem check_0128_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 128)) 0 6 (by decide +kernel)
theorem block_0128 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 128)) 0 6 :=
  check_0128_0000
theorem check_0129_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 129)) 0 6 (by decide +kernel)
theorem block_0129 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 129)) 0 6 :=
  check_0129_0000
theorem check_0130_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 130)) 0 6 (by decide +kernel)
theorem block_0130 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 130)) 0 6 :=
  check_0130_0000
theorem check_0131_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 131)) 0 6 (by decide +kernel)
theorem block_0131 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 131)) 0 6 :=
  check_0131_0000
theorem check_0132_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 132)) 0 6 (by decide +kernel)
theorem block_0132 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 132)) 0 6 :=
  check_0132_0000
theorem check_0133_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 133)) 0 6 (by decide +kernel)
theorem block_0133 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 133)) 0 6 :=
  check_0133_0000
theorem check_0134_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 134)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 134)) 0 6 (by decide +kernel)
theorem block_0134 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 134)) 0 6 :=
  check_0134_0000
theorem check_0135_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 135)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 135)) 0 2 (by decide +kernel)
theorem block_0135 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 135)) 0 2 :=
  check_0135_0000
theorem check_0136_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 136)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 136)) 0 2 (by decide +kernel)
theorem block_0136 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 136)) 0 2 :=
  check_0136_0000
theorem check_0137_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 137)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 137)) 0 2 (by decide +kernel)
theorem block_0137 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 137)) 0 2 :=
  check_0137_0000
theorem check_0138_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 138)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 138)) 0 2 (by decide +kernel)
theorem block_0138 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 138)) 0 2 :=
  check_0138_0000
theorem check_0139_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 139)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 139)) 0 2 (by decide +kernel)
theorem block_0139 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 139)) 0 2 :=
  check_0139_0000
theorem check_0140_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 140)) 0 2 (by decide +kernel)
theorem block_0140 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 140)) 0 2 :=
  check_0140_0000
theorem check_0141_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 141)) 0 2 (by decide +kernel)
theorem block_0141 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 141)) 0 2 :=
  check_0141_0000
theorem check_0142_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 142)) 0 2 (by decide +kernel)
theorem block_0142 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 142)) 0 2 :=
  check_0142_0000
theorem check_0143_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 143)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 143)) 0 2 (by decide +kernel)
theorem block_0143 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 143)) 0 2 :=
  check_0143_0000
theorem check_0144_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 144)) 0 2 (by decide +kernel)
theorem block_0144 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 144)) 0 2 :=
  check_0144_0000
theorem check_0145_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 145)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 145)) 0 2 (by decide +kernel)
theorem block_0145 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 145)) 0 2 :=
  check_0145_0000
theorem check_0146_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 146)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 146)) 0 2 (by decide +kernel)
theorem block_0146 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 146)) 0 2 :=
  check_0146_0000
theorem check_0147_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 147)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 147)) 0 2 (by decide +kernel)
theorem block_0147 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 147)) 0 2 :=
  check_0147_0000
theorem check_0148_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 148)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 148)) 0 2 (by decide +kernel)
theorem block_0148 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 148)) 0 2 :=
  check_0148_0000
theorem check_0149_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 149)) 0 2 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 149)) 0 2 (by decide +kernel)
theorem block_0149 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 149)) 0 2 :=
  check_0149_0000
theorem check_0150_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 150)) 0 6 (by decide +kernel)
theorem block_0150 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 150)) 0 6 :=
  check_0150_0000
theorem check_0151_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 151)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 151)) 0 6 (by decide +kernel)
theorem block_0151 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 151)) 0 6 :=
  check_0151_0000
theorem check_0152_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 152)) 0 6 (by decide +kernel)
theorem block_0152 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 152)) 0 6 :=
  check_0152_0000
theorem check_0153_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 153)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 153)) 0 6 (by decide +kernel)
theorem block_0153 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 153)) 0 6 :=
  check_0153_0000
theorem check_0154_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 154)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 154)) 0 6 (by decide +kernel)
theorem block_0154 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 154)) 0 6 :=
  check_0154_0000
theorem check_0155_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 155)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 155)) 0 6 (by decide +kernel)
theorem block_0155 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 155)) 0 6 :=
  check_0155_0000
theorem check_0156_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 156)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 156)) 0 6 (by decide +kernel)
theorem block_0156 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 156)) 0 6 :=
  check_0156_0000
theorem check_0157_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 157)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 157)) 0 6 (by decide +kernel)
theorem block_0157 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 157)) 0 6 :=
  check_0157_0000
theorem check_0158_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 158)) 0 6 (by decide +kernel)
theorem block_0158 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 158)) 0 6 :=
  check_0158_0000
theorem check_0159_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 159)) 0 6 (by decide +kernel)
theorem block_0159 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 159)) 0 6 :=
  check_0159_0000
end Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
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
theorem metadata_validity_0112 : FiniteChecks.Interval validity 112 128 :=
  FiniteChecks.interval_of_check validity 112 16 (by decide +kernel)
theorem metadata_validity_0128 : FiniteChecks.Interval validity 128 144 :=
  FiniteChecks.interval_of_check validity 128 16 (by decide +kernel)
theorem metadata_validity_0144 : FiniteChecks.Interval validity 144 160 :=
  FiniteChecks.interval_of_check validity 144 16 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 160
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 112 160
  (FiniteChecks.interval_append (validity) 80 96 112
  metadata_validity_0080
  metadata_validity_0096)
  (FiniteChecks.interval_append (validity) 112 128 160
  metadata_validity_0112
  (FiniteChecks.interval_append (validity) 128 144 160
  metadata_validity_0128
  metadata_validity_0144))))
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
theorem metadata_symmetry_0112 : FiniteChecks.Interval symmetry 112 128 :=
  FiniteChecks.interval_of_check symmetry 112 16 (by decide +kernel)
theorem metadata_symmetry_0128 : FiniteChecks.Interval symmetry 128 144 :=
  FiniteChecks.interval_of_check symmetry 128 16 (by decide +kernel)
theorem metadata_symmetry_0144 : FiniteChecks.Interval symmetry 144 160 :=
  FiniteChecks.interval_of_check symmetry 144 16 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 160
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 112 160
  (FiniteChecks.interval_append (symmetry) 80 96 112
  metadata_symmetry_0080
  metadata_symmetry_0096)
  (FiniteChecks.interval_append (symmetry) 112 128 160
  metadata_symmetry_0112
  (FiniteChecks.interval_append (symmetry) 128 144 160
  metadata_symmetry_0128
  metadata_symmetry_0144))))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 5 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenPure008.S5T1
