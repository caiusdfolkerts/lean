module
prelude
public import SharedSmallRootReplay
public import Graph13Level10

@[expose] public section
namespace Papers.RationalityTen.SharedSmallRootCertificates.Row28.Part000
open Papers.RationalityTen ConcreteGrowth FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def quota (j : Nat) : Nat := ([0,5,10,0,0] : List Nat).getD j 0
noncomputable def records : Table (Nat × Nat) :=
(.branch 128
 (.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (2,85536298468499393821638912))
 (.leaf (3,84931982844414293027422336)))
 (.branch 3
 (.leaf (5,89923376931085296173416704))
 (.leaf (12,247234922995415282767429888))))
 (.branch 6
 (.branch 5
 (.leaf (18,256604098097428663032152320))
 (.leaf (21,237280100662549788569403648)))
 (.branch 7
 (.leaf (32,430684619968476177013702912))
 (.leaf (36,83746484389773565969318016)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (39,1490048296340704240930455808))
 (.leaf (40,1470119984146431385538691328)))
 (.branch 11
 (.leaf (42,96828058517963008))
 (.leaf (44,1470101094104039163244347648))))
 (.branch 14
 (.branch 13
 (.leaf (45,1509995646151321926009716736))
 (.leaf (46,94576271587049728)))
 (.branch 15
 (.leaf (47,1490010517408841301460320512))
 (.leaf (48,1470053796654485980609249281))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (49,1490010664982793891145121792))
 (.leaf (50,1569946163014789145762529536)))
 (.branch 19
 (.leaf (51,99079889275093248))
 (.leaf (53,1569365201256931737414418688))))
 (.branch 22
 (.branch 21
 (.leaf (54,1550612794633920826843398400))
 (.leaf (55,99079897596592384)))
 (.branch 23
 (.leaf (58,1551226628489717586155569408))
 (.leaf (61,96828126838980864)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (62,1653810816381563050265870592))
 (.leaf (63,99079926916907264)))
 (.branch 27
 (.leaf (65,1654414984143465185768702208))
 (.leaf (66,1664733429271972411747631360))))
 (.branch 30
 (.branch 29
 (.leaf (68,94576336011559168))
 (.leaf (69,1636290689732624838004113664)))
 (.branch 31
 (.leaf (72,1644748448103444376874713344))
 (.leaf (76,99080035303981184)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (77,1898193023903880642811674752))
 (.leaf (78,96828264273740032)))
 (.branch 35
 (.leaf (80,99080073079980288))
 (.leaf (81,1983252251813862006425911297))))
 (.branch 38
 (.branch 37
 (.leaf (83,1375157916542405913515950336))
 (.leaf (85,1567374723784402473130672384)))
 (.branch 39
 (.leaf (87,2807300518175829692422045952))
 (.leaf (89,99080447616631040)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (93,2892052791973942352995746048))
 (.leaf (94,96828681038610688)))
 (.branch 43
 (.leaf (96,94576881231216704))
 (.leaf (97,2872719571743487376056451328))))
 (.branch 46
 (.branch 45
 (.leaf (98,2872738313061257312479477761))
 (.leaf (99,2872738460632958102342270976)))
 (.branch 47
 (.leaf (100,2873016932681494821857198336))
 (.leaf (101,2969291966318171646383423744))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (102,2946464046739979787925782784))
 (.leaf (104,2946761555828400575706366208)))
 (.branch 51
 (.leaf (106,661008544664900798915813440))
 (.leaf (108,99080622701576448))))
 (.branch 54
 (.branch 53
 (.leaf (110,2603426549270869700478271744))
 (.leaf (112,96828827314962688)))
 (.branch 55
 (.leaf (113,3269542277801800832153305344))
 (.leaf (114,96829157496914176)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (116,99080965896339712))
 (.leaf (119,96829170243404032)))
 (.branch 59
 (.leaf (121,96829260844564736))
 (.leaf (123,96829265152114944))))
 (.branch 62
 (.branch 61
 (.leaf (125,96829269166063872))
 (.leaf (128,96829273461031168)))
 (.branch 63
 (.leaf (130,96829286345933056))
 (.leaf (135,96829333876260992))))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (136,99081134876426496))
 (.leaf (137,4374205291556695918497497089)))
 (.branch 67
 (.leaf (139,96829335194861824))
 (.leaf (141,96829363516932352))))
 (.branch 70
 (.branch 69
 (.leaf (145,99081206414508288))
 (.leaf (149,96829410761572608)))
 (.branch 71
 (.leaf (150,99081210709475584))
 (.leaf (151,3888509900520683441722753792)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (154,99081223594377472))
 (.leaf (160,96829479481049344)))
 (.branch 75
 (.leaf (168,524071741456978938468253952))
 (.leaf (170,94578122585833600))))
 (.branch 78
 (.branch 77
 (.leaf (171,94578122717954176))
 (.leaf (172,94578127012905088)))
 (.branch 79
 (.leaf (173,833556750990093768480276608))
 (.leaf (175,99082125403291904))))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (177,94578706298732800))
 (.leaf (179,94578710459482368)))
 (.branch 83
 (.leaf (180,1452524373708976378049725056))
 (.leaf (182,6519132483569772129886929472))))
 (.branch 86
 (.branch 85
 (.leaf (186,94579328932675840))
 (.leaf (188,99083114453729536)))
 (.branch 87
 (.leaf (198,96831451009450240))
 (.leaf (206,99083388257894656)))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (224,9988456797844784499247874304))
 (.leaf (225,85238752486594857205252352)))
 (.branch 91
 (.leaf (229,9166518851374590386522545851479788235050920194174469943439808362414795194624))
 (.leaf (230,99083704340644096))))
 (.branch 94
 (.branch 93
 (.leaf (232,92328307178144000))
 (.leaf (233,99083712662143232)))
 (.branch 95
 (.leaf (235,277453272332326258572558592))
 (.leaf (236,282286614427543342595211520)))))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (238,10234919503238941726947164416))
 (.leaf (240,10295821613265734592920355072)))
 (.branch 99
 (.leaf (241,436726887883312288249184512))
 (.leaf (242,92328418847236352))))
 (.branch 102
 (.branch 101
 (.leaf (244,10563747325885890632344420480))
 (.leaf (245,96832112561291520)))
 (.branch 103
 (.leaf (246,99083912643379456))
 (.leaf (250,9987545455477027995970994432)))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (259,11393559165890785098875339008))
 (.leaf (260,11392964295864356865822490880)))
 (.branch 107
 (.leaf (261,11393521386958922158876721408))
 (.leaf (262,1490001074405262217122415360))))
 (.branch 110
 (.branch 109
 (.leaf (263,11393540423998806227670859776))
 (.leaf (264,11454272418728212078678573312)))
 (.branch 111
 (.leaf (267,99084295969210624))
 (.leaf (270,11557330835516704468152418560))))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (271,1664733429271976809785753856))
 (.leaf (274,11538611522929022544826663168)))
 (.branch 115
 (.leaf (275,1674966724806300545276969728))
 (.leaf (277,11625181797142575577357680896))))
 (.branch 118
 (.branch 117
 (.leaf (278,11172289161584270722772508928))
 (.leaf (279,99084433139728640)))
 (.branch 119
 (.leaf (281,11248469326221511671746199808))
 (.leaf (282,11249659216154163737798902528)))))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (283,11249678251464665549154353152))
 (.leaf (284,99084470589653248)))
 (.branch 123
 (.leaf (287,11277171869704393388101533952))
 (.leaf (288,11354392006432277860928520448))))
 (.branch 126
 (.branch 125
 (.leaf (294,12546839128204933663873368320))
 (.leaf (299,12691459240559575195124302080)))
 (.branch 127
 (.leaf (300,99084845667319809))
 (.leaf (301,99084845667385344)))))))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.branch 129
 (.leaf (302,12795270874802085292807356672))
 (.leaf (303,12766299156429680023726784768)))
 (.branch 131
 (.leaf (304,2902673394196172387121102849))
 (.leaf (305,12806193856050915376176889856))))
 (.branch 134
 (.branch 133
 (.leaf (306,12776551562214403369481601280))
 (.leaf (307,12777760487457557246889754624)))
 (.branch 135
 (.leaf (308,12785901699700071929185632512))
 (.leaf (309,13039629802821612240040395008)))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf (310,99084983106306048))
 (.leaf (312,13040080751927238143939461376)))
 (.branch 139
 (.leaf (313,99085020345467136))
 (.leaf (314,99085020748120064))))
 (.branch 142
 (.branch 141
 (.leaf (315,12468256442325710504248476416))
 (.leaf (316,99085020882337792)))
 (.branch 143
 (.leaf (318,12515111908989774212756472064))
 (.leaf (320,12543975012933073514300244224))))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf (324,12708384202034180285427417344))
 (.leaf (325,99085279121441024)))
 (.branch 147
 (.leaf (327,9299034403259822457989050381736549234375941085805453851471343593270420766976))
 (.leaf (332,99085294988493056))))
 (.branch 150
 (.branch 149
 (.leaf (334,13868797002619876476687810816))
 (.leaf (335,13868797445918195014655213824)))
 (.branch 151
 (.leaf (336,13870024965479375191299653632))
 (.leaf (337,96833654596108544)))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf (338,96833671775977472))
 (.leaf (339,14158976978259250564107927808)))
 (.branch 155
 (.leaf (340,14158996015299134649545064448))
 (.leaf (341,14158939199327387624646180864))))
 (.branch 158
 (.branch 157
 (.leaf (343,13631932692722514323182780672))
 (.leaf (345,13617379391665769263141486593)))
 (.branch 159
 (.leaf (346,99085531736473600))
 (.leaf (350,99085532520317184)))))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf (351,13620362747841991867614888704))
 (.leaf (352,99085533057187840)))
 (.branch 163
 (.leaf (355,13705006591678439245670842624))
 (.leaf (356,99085569828749568))))
 (.branch 166
 (.branch 165
 (.leaf (357,99085570105475072))
 (.leaf (362,99085591580311808)))
 (.branch 167
 (.leaf (363,13791426045312445646012350720))
 (.leaf (364,99085608760180736)))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf (366,13849501561321284714088169728))
 (.leaf (368,13870024965479375448997691392)))
 (.branch 171
 (.leaf (374,96833856191136000))
 (.leaf (375,13946168550223118249094217984))))
 (.branch 174
 (.branch 173
 (.leaf (376,96833877531754496))
 (.leaf (378,168647587383770348730220800)))
 (.branch 175
 (.leaf (380,10080932687645994908170387712))
 (.leaf (381,5129776919627304828591440128))))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf (388,10160124412380477458749653248))
 (.leaf (389,10160738319446789760596639744)))
 (.branch 179
 (.leaf (393,290298109165733898281320704))
 (.leaf (395,332473803599570112411213888))))
 (.branch 182
 (.branch 181
 (.leaf (396,10255924589354748116663812352))
 (.leaf (397,10396932202030458792799437056)))
 (.branch 183
 (.leaf (398,10416265570411327128890048768))
 (.leaf (399,10417918251754897262113718816)))))
 (.branch 188
 (.branch 186
 (.branch 185
 (.leaf (400,10417920759287112187969077248))
 (.leaf (401,10450266609087988589528154368)))
 (.branch 187
 (.leaf (408,5613198492640715943180271744))
 (.leaf (409,661889284604820747482841216))))
 (.branch 190
 (.branch 189
 (.leaf (411,96834311319257344))
 (.leaf (412,96834311583433472)))
 (.branch 191
 (.leaf (413,96834311591886848))
 (.leaf (414,99086111669813248))))))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.branch 193
 (.leaf (416,5696770212576290467792060672))
 (.leaf (417,5697979137819444345200214016)))
 (.branch 195
 (.leaf (418,5659586225967889715663209088))
 (.leaf (419,5698276646907865132980797440))))
 (.branch 198
 (.branch 197
 (.leaf (420,5668048706561076936105263680))
 (.leaf (421,5773990349304174940619047168)))
 (.branch 199
 (.leaf (423,831896876353088009067856128))
 (.leaf (425,986639381263760612149723392)))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf (427,99086378628874496))
 (.leaf (434,99086385910186240)))
 (.branch 203
 (.leaf (436,6325180242818237305093914880))
 (.leaf (437,11393540424575269161280798976))))
 (.branch 206
 (.branch 205
 (.leaf (438,1528082605505085203927957760))
 (.leaf (439,11432226050226476559747842048)))
 (.branch 207
 (.leaf (442,11465537623973099804181987584))
 (.leaf (444,11473178412365922141227515904))))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf (453,11538611522929024726670049536))
 (.leaf (454,11557331278815025187963207936)))
 (.branch 211
 (.leaf (455,11558558798376205364607647744))
 (.leaf (456,1673153703858840769317208320))))
 (.branch 214
 (.branch 213
 (.leaf (457,11577297148580232125137092608))
 (.leaf (460,99086564113678592)))
 (.branch 215
 (.leaf (461,99086564390404096))
 (.leaf (464,99086652433039616)))))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf (465,99086669612908544))
 (.leaf (468,1450711353049749177264931072)))
 (.branch 219
 (.leaf (470,99086725451677696))
 (.leaf (475,12075062910650050921887760640))))
 (.branch 222
 (.branch 221
 (.leaf (478,7128440688241891998565466368))
 (.leaf (480,2224423877603111917796360448)))
 (.branch 223
 (.leaf (481,7176495488995112777297231872))
 (.leaf (484,7195569054008907740250931456)))))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf (499,7708111395375070090486776064))
 (.leaf (503,8366078496072369165792510208)))
 (.branch 227
 (.leaf (504,2804708234124646323992019200))
 (.leaf (505,8414430805914010732304859136))))
 (.branch 230
 (.branch 229
 (.leaf (511,85576652176294144))
 (.leaf (517,13775124289216089693087662336)))
 (.branch 231
 (.leaf (518,13791464857838439390195024128))
 (.leaf (519,99087515725660416)))))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf (522,13793844045102090154380820736))
 (.leaf (523,13795071564663270331025260544)))
 (.branch 235
 (.leaf (531,13830111681339948492906434816))
 (.leaf (532,13830205971295820507017969664))))
 (.branch 238
 (.branch 237
 (.leaf (533,14081605725803916461590249728))
 (.leaf (534,99087653433049088)))
 (.branch 239
 (.leaf (536,18571830265259069067757682944))
 (.leaf (538,18598115113900046151221121280))))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf (539,18598209403855918165332656128))
 (.leaf (547,13772130308865950611570491648)))
 (.branch 243
 (.leaf (548,99087790603567104))
 (.leaf (549,14449081397196829640584331780))))
 (.branch 246
 (.branch 245
 (.leaf (550,14449081838756758705752178688))
 (.leaf (555,14081568247208105729364986112)))
 (.branch 247
 (.leaf (557,14081624762843800804725424128))
 (.leaf (564,99915867515358118548619520)))))
 (.branch 252
 (.branch 250
 (.branch 249
 (.leaf (565,119863143250769132637929600))
 (.leaf (566,257208561007244773435703552)))
 (.branch 251
 (.leaf (568,332022541331642718700454144))
 (.leaf (572,412853037916145479153942784))))
 (.branch 254
 (.branch 253
 (.leaf (573,416779685646651590892912896))
 (.leaf (574,426809881087571903372083328)))
 (.branch 255
 (.leaf (576,432195777243003259700936960))
 (.leaf (582,1490048444491126378994925824))))))))))
noncomputable def lookup (i : Nat) : Nat × Nat := records.get i
noncomputable def test (i : Nat) : Bool :=
  let r := lookup i
  decide (r.1 < GraphCatalogue.Generated.Graph13.Level10.count) &&
  (decide (SharedSmallRootReplay.complement r.2 =
    (GraphCatalogue.Generated.Graph13.Level10.lookup r.1).mask) &&
  SharedSmallRootReplay.check quota 10 r.2)
theorem checked_0 : Interval test 0 8 :=
  interval_of_check test 0 8 (by decide +kernel)
theorem checked_8 : Interval test 8 16 :=
  interval_of_check test 8 8 (by decide +kernel)
theorem checked_16 : Interval test 16 24 :=
  interval_of_check test 16 8 (by decide +kernel)
theorem checked_24 : Interval test 24 32 :=
  interval_of_check test 24 8 (by decide +kernel)
theorem checked_32 : Interval test 32 40 :=
  interval_of_check test 32 8 (by decide +kernel)
theorem checked_40 : Interval test 40 48 :=
  interval_of_check test 40 8 (by decide +kernel)
theorem checked_48 : Interval test 48 56 :=
  interval_of_check test 48 8 (by decide +kernel)
theorem checked_56 : Interval test 56 64 :=
  interval_of_check test 56 8 (by decide +kernel)
theorem checked_64 : Interval test 64 72 :=
  interval_of_check test 64 8 (by decide +kernel)
theorem checked_72 : Interval test 72 80 :=
  interval_of_check test 72 8 (by decide +kernel)
theorem checked_80 : Interval test 80 88 :=
  interval_of_check test 80 8 (by decide +kernel)
theorem checked_88 : Interval test 88 96 :=
  interval_of_check test 88 8 (by decide +kernel)
theorem checked_96 : Interval test 96 104 :=
  interval_of_check test 96 8 (by decide +kernel)
theorem checked_104 : Interval test 104 112 :=
  interval_of_check test 104 8 (by decide +kernel)
theorem checked_112 : Interval test 112 120 :=
  interval_of_check test 112 8 (by decide +kernel)
theorem checked_120 : Interval test 120 128 :=
  interval_of_check test 120 8 (by decide +kernel)
theorem checked_128 : Interval test 128 136 :=
  interval_of_check test 128 8 (by decide +kernel)
theorem checked_136 : Interval test 136 144 :=
  interval_of_check test 136 8 (by decide +kernel)
theorem checked_144 : Interval test 144 152 :=
  interval_of_check test 144 8 (by decide +kernel)
theorem checked_152 : Interval test 152 160 :=
  interval_of_check test 152 8 (by decide +kernel)
theorem checked_160 : Interval test 160 168 :=
  interval_of_check test 160 8 (by decide +kernel)
theorem checked_168 : Interval test 168 176 :=
  interval_of_check test 168 8 (by decide +kernel)
theorem checked_176 : Interval test 176 184 :=
  interval_of_check test 176 8 (by decide +kernel)
theorem checked_184 : Interval test 184 192 :=
  interval_of_check test 184 8 (by decide +kernel)
theorem checked_192 : Interval test 192 200 :=
  interval_of_check test 192 8 (by decide +kernel)
theorem checked_200 : Interval test 200 208 :=
  interval_of_check test 200 8 (by decide +kernel)
theorem checked_208 : Interval test 208 216 :=
  interval_of_check test 208 8 (by decide +kernel)
theorem checked_216 : Interval test 216 224 :=
  interval_of_check test 216 8 (by decide +kernel)
theorem checked_224 : Interval test 224 232 :=
  interval_of_check test 224 8 (by decide +kernel)
theorem checked_232 : Interval test 232 240 :=
  interval_of_check test 232 8 (by decide +kernel)
theorem checked_240 : Interval test 240 248 :=
  interval_of_check test 240 8 (by decide +kernel)
theorem checked_248 : Interval test 248 256 :=
  interval_of_check test 248 8 (by decide +kernel)
theorem checked : Interval test 0 256 :=
  (interval_append test 0 128 256
 (interval_append test 0 64 128
 (interval_append test 0 32 64
 (interval_append test 0 16 32
 (interval_append test 0 8 16
 checked_0
 checked_8)
 (interval_append test 16 24 32
 checked_16
 checked_24))
 (interval_append test 32 48 64
 (interval_append test 32 40 48
 checked_32
 checked_40)
 (interval_append test 48 56 64
 checked_48
 checked_56)))
 (interval_append test 64 96 128
 (interval_append test 64 80 96
 (interval_append test 64 72 80
 checked_64
 checked_72)
 (interval_append test 80 88 96
 checked_80
 checked_88))
 (interval_append test 96 112 128
 (interval_append test 96 104 112
 checked_96
 checked_104)
 (interval_append test 112 120 128
 checked_112
 checked_120))))
 (interval_append test 128 192 256
 (interval_append test 128 160 192
 (interval_append test 128 144 160
 (interval_append test 128 136 144
 checked_128
 checked_136)
 (interval_append test 144 152 160
 checked_144
 checked_152))
 (interval_append test 160 176 192
 (interval_append test 160 168 176
 checked_160
 checked_168)
 (interval_append test 176 184 192
 checked_176
 checked_184)))
 (interval_append test 192 224 256
 (interval_append test 192 208 224
 (interval_append test 192 200 208
 checked_192
 checked_200)
 (interval_append test 208 216 224
 checked_208
 checked_216))
 (interval_append test 224 240 256
 (interval_append test 224 232 240
 checked_224
 checked_232)
 (interval_append test 240 248 256
 checked_240
 checked_248)))))
end Papers.RationalityTen.SharedSmallRootCertificates.Row28.Part000
