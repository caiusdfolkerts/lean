module
prelude
public import RootedSevenMixed030OutsideData
public import CachedCellRelabel

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed030.Outside.Verified
open Papers.RationalityTen ConcreteGrowth FiniteChecks RawGraphGrowthFrames
open Papers.RationalityTen.FacetUniverses.RootedSevenMixed030.Outside
def renameCodeTable : Table Nat :=
(.branch 1
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031146030589498667320720657435786943876640617635033896965876224008760669254716045618505484360510611417475693317113244219394193022105682971070419849199805181521194122771861778347860674360904551003493259609466268914802112140802300264465436082758351468504083373030676834124164682495780213699535577237315851059241084800838922155445364026793605174776615498923969614649496735348018722058196192487243910623735724470863359775349714596491429202506130480662860453138401345954923622846667820257670784995350262766293930925262961314679420913259255841326080175338145883663219025173565117717273879342072550721130914408767511662895790267567177070806880835070107453164803403956517654221581528467672390149160760716233637473551690622457008937732986412141241351717100422413538757004990784127801436831448112910522884917242759320209960034561886783184510595812861900846950287523659622407826097891042737232751435405421070551440298182578648095534765877454648846008789148608941422244798999240989422143250887421321361250440622713919721284568169679345968750190644328424171188217616002190444482894308609128219023995855596014152592844791940243540031853302824513879696100797901649256152720045576225569153128866394419163629051667838870256967010007519061451266853692170175909090495758570291293038726158930619226207444250597969704010733100037326017967858988847358235912648583681140018841611980192216793705944182229757372736255376586131033535068352362439279233470050569015898315722269653505203200921626363009966699069042727008593869087684643952573661641968533434329079974310940935055221728227459653094506741259618673571897291973266234502042650275013270633901289439544244588339581007081650397235098468052099652950655617964422632011071372421959923924990771888033290333161266283970073059282016551093661143289596941286400091463928105164728049142377301595276392189206671338018865820178273915705429814451336545903117809252212866273450408548489120134951729980532537016019253735998892133821531532164760095277863671016459608522210103254819955090643430949265338298769491610610737785720861711696321699361454823239605697746463113144576549414177367093848125498322689985305652860449603085402312893215891109052745472397891324038637548926152365026960023769347510008900831893564307685285990527026659461170788862745508434094073554805763083438724864631859987985818768190209667622603606151886783400470715399568263225608366941993467362144689430583904095830212025530145497587776043257144483604876568700026935092924997384515854941321534072055684908078774533887286672259798344258343524955275535042027409507394805925827313593461562518242369037733858273458667762855863946294742167580824887029554745403732393639504546460188465876511991658077863309149223932287975852616561217772846967545797026085294276099935141912653727616657142269508196639620678821511488701268219352389696261292565606237236830384048991402477975840910780167754675329602244500462807352869888)
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031146030589498667320720657435786943876640617635033896965876224008760669254716045618505484360510611417475693317113244219394193022105682971070419849199805181521194122771861778347860674360904551003493471492159798365977693560546646479025542718964713745284361464244356982126907626488107970066061452013137519401013935588845305467961265247145220072294543368037087371529177491384137169726733007090447205874059034157368417435975012489809584639678566423444637272269780656971790160146024174047151729913203233321669897850452700466606927559250713256933784280915065580872203402047231272167528503202925913053875735844940907796331800714006563552686986237930878565671009834360245129043182133995172589349104307785570271449736307787247422555947763980195740648518052247437638806246987204201503043026646764243530349958188087304060068444676635882939208192031432851205894448065854247934539000548113206570945398377155531688130710685494231999373792204285144836261240020985980666050342747214621695671661050964103766725726223808441025376929828612291146655324922653674067001619855784915927204111533068260239916672023297009996535563496337134223823969861744393130674137350943748913317837702952430739992017784743378622029626536537719924809404789703043837566527728587492294490294363932781963328291360585720142743560342948562384723155796498787015242077320027892735722235229527534578097192387065900760259072304217968176474370538996611131010132069592739645335972383847845354206349221486746374592655832522148253796962239556415962412041040665244145325911720126104161911635337034468844527643242910688600191820212892555514319833145774774262198134511576730618547545257860759270433551615420730436006550170516832050187450227969901968566267665615513701949603364998372989186681022647989056998931444208579787726914161540378863374289631332505101137266975299884295510326412243747235161983238646638075599811599603809642248026605966244618136990805673984420085711595434808025800283368753816682786363780121255368833602608540909412124546482332328311318365977024541724209091408565047629100920831955385651069793623996481856335988214260846383308056328676818466540656986732289284172425322280077525299081472540070563200460404560388010764851365993882681307196636112064488421143305403059629657526175956622777906966255645102900132850175359836080229673025312953977614795411434631585276635215917133702193218407506615028969853972340940578945225269009487975852120035196798822494401340479189191889226428280791320430361516459088235587944535546485014636119591473795168390685708762196502229642133837906644647082185694972109213015811374267349875440787126083457770002997860877530005184567091171340731106470899528456290464346818554058416569620352042088088456262178609541493871229301871835520030357815462155516773013264843524684624051989113111296146895765811940274361227265439273237301529974142061374326598431564754674237442977517272949915229587246678216803681829888))
def renameCode (g : Fin generatorCount) := renameCodeTable.get g.val
def maskTest0 (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode 0) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode 0)) j)
theorem maskTest0_block_0 : Interval maskTest0 0 16 :=
  interval_of_check maskTest0 0 16 (by decide +kernel)

theorem maskTest0_block_1 : Interval maskTest0 16 32 :=
  interval_of_check maskTest0 16 16 (by decide +kernel)

theorem maskTest0_block_2 : Interval maskTest0 32 48 :=
  interval_of_check maskTest0 32 16 (by decide +kernel)

theorem maskTest0_block_3 : Interval maskTest0 48 64 :=
  interval_of_check maskTest0 48 16 (by decide +kernel)

theorem maskTest0_block_4 : Interval maskTest0 64 80 :=
  interval_of_check maskTest0 64 16 (by decide +kernel)

theorem maskTest0_block_5 : Interval maskTest0 80 96 :=
  interval_of_check maskTest0 80 16 (by decide +kernel)

theorem maskTest0_block_6 : Interval maskTest0 96 112 :=
  interval_of_check maskTest0 96 16 (by decide +kernel)

theorem maskTest0_block_7 : Interval maskTest0 112 128 :=
  interval_of_check maskTest0 112 16 (by decide +kernel)

theorem maskTest0_block_8 : Interval maskTest0 128 144 :=
  interval_of_check maskTest0 128 16 (by decide +kernel)

theorem maskTest0_block_9 : Interval maskTest0 144 160 :=
  interval_of_check maskTest0 144 16 (by decide +kernel)

theorem maskTest0_block_10 : Interval maskTest0 160 176 :=
  interval_of_check maskTest0 160 16 (by decide +kernel)

theorem maskTest0_block_11 : Interval maskTest0 176 192 :=
  interval_of_check maskTest0 176 16 (by decide +kernel)

theorem maskTest0_block_12 : Interval maskTest0 192 208 :=
  interval_of_check maskTest0 192 16 (by decide +kernel)

theorem maskTest0_block_13 : Interval maskTest0 208 224 :=
  interval_of_check maskTest0 208 16 (by decide +kernel)

theorem maskTest0_block_14 : Interval maskTest0 224 240 :=
  interval_of_check maskTest0 224 16 (by decide +kernel)

theorem maskTest0_block_15 : Interval maskTest0 240 256 :=
  interval_of_check maskTest0 240 16 (by decide +kernel)

theorem maskTest0_block_16 : Interval maskTest0 256 272 :=
  interval_of_check maskTest0 256 16 (by decide +kernel)

theorem maskTest0_block_17 : Interval maskTest0 272 288 :=
  interval_of_check maskTest0 272 16 (by decide +kernel)

theorem maskTest0_block_18 : Interval maskTest0 288 304 :=
  interval_of_check maskTest0 288 16 (by decide +kernel)

theorem maskTest0_block_19 : Interval maskTest0 304 320 :=
  interval_of_check maskTest0 304 16 (by decide +kernel)

theorem maskTest0_block_20 : Interval maskTest0 320 336 :=
  interval_of_check maskTest0 320 16 (by decide +kernel)

theorem maskTest0_block_21 : Interval maskTest0 336 352 :=
  interval_of_check maskTest0 336 16 (by decide +kernel)

theorem maskTest0_block_22 : Interval maskTest0 352 368 :=
  interval_of_check maskTest0 352 16 (by decide +kernel)

theorem maskTest0_block_23 : Interval maskTest0 368 384 :=
  interval_of_check maskTest0 368 16 (by decide +kernel)

theorem maskTest0_block_24 : Interval maskTest0 384 400 :=
  interval_of_check maskTest0 384 16 (by decide +kernel)

theorem maskTest0_block_25 : Interval maskTest0 400 416 :=
  interval_of_check maskTest0 400 16 (by decide +kernel)

theorem maskTest0_block_26 : Interval maskTest0 416 432 :=
  interval_of_check maskTest0 416 16 (by decide +kernel)

theorem maskTest0_block_27 : Interval maskTest0 432 448 :=
  interval_of_check maskTest0 432 16 (by decide +kernel)

theorem maskTest0_block_28 : Interval maskTest0 448 464 :=
  interval_of_check maskTest0 448 16 (by decide +kernel)

theorem maskTest0_block_29 : Interval maskTest0 464 480 :=
  interval_of_check maskTest0 464 16 (by decide +kernel)

theorem maskTest0_block_30 : Interval maskTest0 480 496 :=
  interval_of_check maskTest0 480 16 (by decide +kernel)

theorem maskTest0_block_31 : Interval maskTest0 496 512 :=
  interval_of_check maskTest0 496 16 (by decide +kernel)

theorem maskTest0_block_32 : Interval maskTest0 512 528 :=
  interval_of_check maskTest0 512 16 (by decide +kernel)

theorem maskTest0_block_33 : Interval maskTest0 528 544 :=
  interval_of_check maskTest0 528 16 (by decide +kernel)

theorem maskTest0_block_34 : Interval maskTest0 544 560 :=
  interval_of_check maskTest0 544 16 (by decide +kernel)

theorem maskTest0_block_35 : Interval maskTest0 560 576 :=
  interval_of_check maskTest0 560 16 (by decide +kernel)

theorem maskTest0_block_36 : Interval maskTest0 576 592 :=
  interval_of_check maskTest0 576 16 (by decide +kernel)

theorem maskTest0_block_37 : Interval maskTest0 592 608 :=
  interval_of_check maskTest0 592 16 (by decide +kernel)

theorem maskTest0_block_38 : Interval maskTest0 608 624 :=
  interval_of_check maskTest0 608 16 (by decide +kernel)

theorem maskTest0_block_39 : Interval maskTest0 624 640 :=
  interval_of_check maskTest0 624 16 (by decide +kernel)

theorem maskTest0_block_40 : Interval maskTest0 640 656 :=
  interval_of_check maskTest0 640 16 (by decide +kernel)

theorem maskTest0_block_41 : Interval maskTest0 656 672 :=
  interval_of_check maskTest0 656 16 (by decide +kernel)

theorem maskTest0_block_42 : Interval maskTest0 672 688 :=
  interval_of_check maskTest0 672 16 (by decide +kernel)

theorem maskTest0_block_43 : Interval maskTest0 688 704 :=
  interval_of_check maskTest0 688 16 (by decide +kernel)

theorem maskTest0_block_44 : Interval maskTest0 704 720 :=
  interval_of_check maskTest0 704 16 (by decide +kernel)

theorem maskTest0_block_45 : Interval maskTest0 720 736 :=
  interval_of_check maskTest0 720 16 (by decide +kernel)

theorem maskTest0_block_46 : Interval maskTest0 736 752 :=
  interval_of_check maskTest0 736 16 (by decide +kernel)

theorem maskTest0_block_47 : Interval maskTest0 752 768 :=
  interval_of_check maskTest0 752 16 (by decide +kernel)

theorem maskTest0_block_48 : Interval maskTest0 768 784 :=
  interval_of_check maskTest0 768 16 (by decide +kernel)

theorem maskTest0_block_49 : Interval maskTest0 784 800 :=
  interval_of_check maskTest0 784 16 (by decide +kernel)

theorem maskTest0_block_50 : Interval maskTest0 800 816 :=
  interval_of_check maskTest0 800 16 (by decide +kernel)

theorem maskTest0_block_51 : Interval maskTest0 816 832 :=
  interval_of_check maskTest0 816 16 (by decide +kernel)

theorem maskTest0_block_52 : Interval maskTest0 832 848 :=
  interval_of_check maskTest0 832 16 (by decide +kernel)

theorem maskTest0_block_53 : Interval maskTest0 848 864 :=
  interval_of_check maskTest0 848 16 (by decide +kernel)

theorem maskTest0_block_54 : Interval maskTest0 864 880 :=
  interval_of_check maskTest0 864 16 (by decide +kernel)

theorem maskTest0_block_55 : Interval maskTest0 880 896 :=
  interval_of_check maskTest0 880 16 (by decide +kernel)

theorem maskTest0_block_56 : Interval maskTest0 896 912 :=
  interval_of_check maskTest0 896 16 (by decide +kernel)

theorem maskTest0_block_57 : Interval maskTest0 912 928 :=
  interval_of_check maskTest0 912 16 (by decide +kernel)

theorem maskTest0_block_58 : Interval maskTest0 928 944 :=
  interval_of_check maskTest0 928 16 (by decide +kernel)

theorem maskTest0_block_59 : Interval maskTest0 944 960 :=
  interval_of_check maskTest0 944 16 (by decide +kernel)

theorem maskTest0_block_60 : Interval maskTest0 960 976 :=
  interval_of_check maskTest0 960 16 (by decide +kernel)

theorem maskTest0_block_61 : Interval maskTest0 976 992 :=
  interval_of_check maskTest0 976 16 (by decide +kernel)

theorem maskTest0_block_62 : Interval maskTest0 992 1008 :=
  interval_of_check maskTest0 992 16 (by decide +kernel)

theorem maskTest0_block_63 : Interval maskTest0 1008 1024 :=
  interval_of_check maskTest0 1008 16 (by decide +kernel)

theorem maskTest0_complete : Interval maskTest0 0 1024 :=
  (interval_append maskTest0 0 512 1024
  (interval_append maskTest0 0 256 512
  (interval_append maskTest0 0 128 256
  (interval_append maskTest0 0 64 128
  (interval_append maskTest0 0 32 64
  (interval_append maskTest0 0 16 32
  maskTest0_block_0
  maskTest0_block_1)
  (interval_append maskTest0 32 48 64
  maskTest0_block_2
  maskTest0_block_3))
  (interval_append maskTest0 64 96 128
  (interval_append maskTest0 64 80 96
  maskTest0_block_4
  maskTest0_block_5)
  (interval_append maskTest0 96 112 128
  maskTest0_block_6
  maskTest0_block_7)))
  (interval_append maskTest0 128 192 256
  (interval_append maskTest0 128 160 192
  (interval_append maskTest0 128 144 160
  maskTest0_block_8
  maskTest0_block_9)
  (interval_append maskTest0 160 176 192
  maskTest0_block_10
  maskTest0_block_11))
  (interval_append maskTest0 192 224 256
  (interval_append maskTest0 192 208 224
  maskTest0_block_12
  maskTest0_block_13)
  (interval_append maskTest0 224 240 256
  maskTest0_block_14
  maskTest0_block_15))))
  (interval_append maskTest0 256 384 512
  (interval_append maskTest0 256 320 384
  (interval_append maskTest0 256 288 320
  (interval_append maskTest0 256 272 288
  maskTest0_block_16
  maskTest0_block_17)
  (interval_append maskTest0 288 304 320
  maskTest0_block_18
  maskTest0_block_19))
  (interval_append maskTest0 320 352 384
  (interval_append maskTest0 320 336 352
  maskTest0_block_20
  maskTest0_block_21)
  (interval_append maskTest0 352 368 384
  maskTest0_block_22
  maskTest0_block_23)))
  (interval_append maskTest0 384 448 512
  (interval_append maskTest0 384 416 448
  (interval_append maskTest0 384 400 416
  maskTest0_block_24
  maskTest0_block_25)
  (interval_append maskTest0 416 432 448
  maskTest0_block_26
  maskTest0_block_27))
  (interval_append maskTest0 448 480 512
  (interval_append maskTest0 448 464 480
  maskTest0_block_28
  maskTest0_block_29)
  (interval_append maskTest0 480 496 512
  maskTest0_block_30
  maskTest0_block_31)))))
  (interval_append maskTest0 512 768 1024
  (interval_append maskTest0 512 640 768
  (interval_append maskTest0 512 576 640
  (interval_append maskTest0 512 544 576
  (interval_append maskTest0 512 528 544
  maskTest0_block_32
  maskTest0_block_33)
  (interval_append maskTest0 544 560 576
  maskTest0_block_34
  maskTest0_block_35))
  (interval_append maskTest0 576 608 640
  (interval_append maskTest0 576 592 608
  maskTest0_block_36
  maskTest0_block_37)
  (interval_append maskTest0 608 624 640
  maskTest0_block_38
  maskTest0_block_39)))
  (interval_append maskTest0 640 704 768
  (interval_append maskTest0 640 672 704
  (interval_append maskTest0 640 656 672
  maskTest0_block_40
  maskTest0_block_41)
  (interval_append maskTest0 672 688 704
  maskTest0_block_42
  maskTest0_block_43))
  (interval_append maskTest0 704 736 768
  (interval_append maskTest0 704 720 736
  maskTest0_block_44
  maskTest0_block_45)
  (interval_append maskTest0 736 752 768
  maskTest0_block_46
  maskTest0_block_47))))
  (interval_append maskTest0 768 896 1024
  (interval_append maskTest0 768 832 896
  (interval_append maskTest0 768 800 832
  (interval_append maskTest0 768 784 800
  maskTest0_block_48
  maskTest0_block_49)
  (interval_append maskTest0 800 816 832
  maskTest0_block_50
  maskTest0_block_51))
  (interval_append maskTest0 832 864 896
  (interval_append maskTest0 832 848 864
  maskTest0_block_52
  maskTest0_block_53)
  (interval_append maskTest0 864 880 896
  maskTest0_block_54
  maskTest0_block_55)))
  (interval_append maskTest0 896 960 1024
  (interval_append maskTest0 896 928 960
  (interval_append maskTest0 896 912 928
  maskTest0_block_56
  maskTest0_block_57)
  (interval_append maskTest0 928 944 960
  maskTest0_block_58
  maskTest0_block_59))
  (interval_append maskTest0 960 992 1024
  (interval_append maskTest0 960 976 992
  maskTest0_block_60
  maskTest0_block_61)
  (interval_append maskTest0 992 1008 1024
  maskTest0_block_62
  maskTest0_block_63))))))
def maskTest1 (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode 1) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode 1)) j)
theorem maskTest1_block_0 : Interval maskTest1 0 16 :=
  interval_of_check maskTest1 0 16 (by decide +kernel)

theorem maskTest1_block_1 : Interval maskTest1 16 32 :=
  interval_of_check maskTest1 16 16 (by decide +kernel)

theorem maskTest1_block_2 : Interval maskTest1 32 48 :=
  interval_of_check maskTest1 32 16 (by decide +kernel)

theorem maskTest1_block_3 : Interval maskTest1 48 64 :=
  interval_of_check maskTest1 48 16 (by decide +kernel)

theorem maskTest1_block_4 : Interval maskTest1 64 80 :=
  interval_of_check maskTest1 64 16 (by decide +kernel)

theorem maskTest1_block_5 : Interval maskTest1 80 96 :=
  interval_of_check maskTest1 80 16 (by decide +kernel)

theorem maskTest1_block_6 : Interval maskTest1 96 112 :=
  interval_of_check maskTest1 96 16 (by decide +kernel)

theorem maskTest1_block_7 : Interval maskTest1 112 128 :=
  interval_of_check maskTest1 112 16 (by decide +kernel)

theorem maskTest1_block_8 : Interval maskTest1 128 144 :=
  interval_of_check maskTest1 128 16 (by decide +kernel)

theorem maskTest1_block_9 : Interval maskTest1 144 160 :=
  interval_of_check maskTest1 144 16 (by decide +kernel)

theorem maskTest1_block_10 : Interval maskTest1 160 176 :=
  interval_of_check maskTest1 160 16 (by decide +kernel)

theorem maskTest1_block_11 : Interval maskTest1 176 192 :=
  interval_of_check maskTest1 176 16 (by decide +kernel)

theorem maskTest1_block_12 : Interval maskTest1 192 208 :=
  interval_of_check maskTest1 192 16 (by decide +kernel)

theorem maskTest1_block_13 : Interval maskTest1 208 224 :=
  interval_of_check maskTest1 208 16 (by decide +kernel)

theorem maskTest1_block_14 : Interval maskTest1 224 240 :=
  interval_of_check maskTest1 224 16 (by decide +kernel)

theorem maskTest1_block_15 : Interval maskTest1 240 256 :=
  interval_of_check maskTest1 240 16 (by decide +kernel)

theorem maskTest1_block_16 : Interval maskTest1 256 272 :=
  interval_of_check maskTest1 256 16 (by decide +kernel)

theorem maskTest1_block_17 : Interval maskTest1 272 288 :=
  interval_of_check maskTest1 272 16 (by decide +kernel)

theorem maskTest1_block_18 : Interval maskTest1 288 304 :=
  interval_of_check maskTest1 288 16 (by decide +kernel)

theorem maskTest1_block_19 : Interval maskTest1 304 320 :=
  interval_of_check maskTest1 304 16 (by decide +kernel)

theorem maskTest1_block_20 : Interval maskTest1 320 336 :=
  interval_of_check maskTest1 320 16 (by decide +kernel)

theorem maskTest1_block_21 : Interval maskTest1 336 352 :=
  interval_of_check maskTest1 336 16 (by decide +kernel)

theorem maskTest1_block_22 : Interval maskTest1 352 368 :=
  interval_of_check maskTest1 352 16 (by decide +kernel)

theorem maskTest1_block_23 : Interval maskTest1 368 384 :=
  interval_of_check maskTest1 368 16 (by decide +kernel)

theorem maskTest1_block_24 : Interval maskTest1 384 400 :=
  interval_of_check maskTest1 384 16 (by decide +kernel)

theorem maskTest1_block_25 : Interval maskTest1 400 416 :=
  interval_of_check maskTest1 400 16 (by decide +kernel)

theorem maskTest1_block_26 : Interval maskTest1 416 432 :=
  interval_of_check maskTest1 416 16 (by decide +kernel)

theorem maskTest1_block_27 : Interval maskTest1 432 448 :=
  interval_of_check maskTest1 432 16 (by decide +kernel)

theorem maskTest1_block_28 : Interval maskTest1 448 464 :=
  interval_of_check maskTest1 448 16 (by decide +kernel)

theorem maskTest1_block_29 : Interval maskTest1 464 480 :=
  interval_of_check maskTest1 464 16 (by decide +kernel)

theorem maskTest1_block_30 : Interval maskTest1 480 496 :=
  interval_of_check maskTest1 480 16 (by decide +kernel)

theorem maskTest1_block_31 : Interval maskTest1 496 512 :=
  interval_of_check maskTest1 496 16 (by decide +kernel)

theorem maskTest1_block_32 : Interval maskTest1 512 528 :=
  interval_of_check maskTest1 512 16 (by decide +kernel)

theorem maskTest1_block_33 : Interval maskTest1 528 544 :=
  interval_of_check maskTest1 528 16 (by decide +kernel)

theorem maskTest1_block_34 : Interval maskTest1 544 560 :=
  interval_of_check maskTest1 544 16 (by decide +kernel)

theorem maskTest1_block_35 : Interval maskTest1 560 576 :=
  interval_of_check maskTest1 560 16 (by decide +kernel)

theorem maskTest1_block_36 : Interval maskTest1 576 592 :=
  interval_of_check maskTest1 576 16 (by decide +kernel)

theorem maskTest1_block_37 : Interval maskTest1 592 608 :=
  interval_of_check maskTest1 592 16 (by decide +kernel)

theorem maskTest1_block_38 : Interval maskTest1 608 624 :=
  interval_of_check maskTest1 608 16 (by decide +kernel)

theorem maskTest1_block_39 : Interval maskTest1 624 640 :=
  interval_of_check maskTest1 624 16 (by decide +kernel)

theorem maskTest1_block_40 : Interval maskTest1 640 656 :=
  interval_of_check maskTest1 640 16 (by decide +kernel)

theorem maskTest1_block_41 : Interval maskTest1 656 672 :=
  interval_of_check maskTest1 656 16 (by decide +kernel)

theorem maskTest1_block_42 : Interval maskTest1 672 688 :=
  interval_of_check maskTest1 672 16 (by decide +kernel)

theorem maskTest1_block_43 : Interval maskTest1 688 704 :=
  interval_of_check maskTest1 688 16 (by decide +kernel)

theorem maskTest1_block_44 : Interval maskTest1 704 720 :=
  interval_of_check maskTest1 704 16 (by decide +kernel)

theorem maskTest1_block_45 : Interval maskTest1 720 736 :=
  interval_of_check maskTest1 720 16 (by decide +kernel)

theorem maskTest1_block_46 : Interval maskTest1 736 752 :=
  interval_of_check maskTest1 736 16 (by decide +kernel)

theorem maskTest1_block_47 : Interval maskTest1 752 768 :=
  interval_of_check maskTest1 752 16 (by decide +kernel)

theorem maskTest1_block_48 : Interval maskTest1 768 784 :=
  interval_of_check maskTest1 768 16 (by decide +kernel)

theorem maskTest1_block_49 : Interval maskTest1 784 800 :=
  interval_of_check maskTest1 784 16 (by decide +kernel)

theorem maskTest1_block_50 : Interval maskTest1 800 816 :=
  interval_of_check maskTest1 800 16 (by decide +kernel)

theorem maskTest1_block_51 : Interval maskTest1 816 832 :=
  interval_of_check maskTest1 816 16 (by decide +kernel)

theorem maskTest1_block_52 : Interval maskTest1 832 848 :=
  interval_of_check maskTest1 832 16 (by decide +kernel)

theorem maskTest1_block_53 : Interval maskTest1 848 864 :=
  interval_of_check maskTest1 848 16 (by decide +kernel)

theorem maskTest1_block_54 : Interval maskTest1 864 880 :=
  interval_of_check maskTest1 864 16 (by decide +kernel)

theorem maskTest1_block_55 : Interval maskTest1 880 896 :=
  interval_of_check maskTest1 880 16 (by decide +kernel)

theorem maskTest1_block_56 : Interval maskTest1 896 912 :=
  interval_of_check maskTest1 896 16 (by decide +kernel)

theorem maskTest1_block_57 : Interval maskTest1 912 928 :=
  interval_of_check maskTest1 912 16 (by decide +kernel)

theorem maskTest1_block_58 : Interval maskTest1 928 944 :=
  interval_of_check maskTest1 928 16 (by decide +kernel)

theorem maskTest1_block_59 : Interval maskTest1 944 960 :=
  interval_of_check maskTest1 944 16 (by decide +kernel)

theorem maskTest1_block_60 : Interval maskTest1 960 976 :=
  interval_of_check maskTest1 960 16 (by decide +kernel)

theorem maskTest1_block_61 : Interval maskTest1 976 992 :=
  interval_of_check maskTest1 976 16 (by decide +kernel)

theorem maskTest1_block_62 : Interval maskTest1 992 1008 :=
  interval_of_check maskTest1 992 16 (by decide +kernel)

theorem maskTest1_block_63 : Interval maskTest1 1008 1024 :=
  interval_of_check maskTest1 1008 16 (by decide +kernel)

theorem maskTest1_complete : Interval maskTest1 0 1024 :=
  (interval_append maskTest1 0 512 1024
  (interval_append maskTest1 0 256 512
  (interval_append maskTest1 0 128 256
  (interval_append maskTest1 0 64 128
  (interval_append maskTest1 0 32 64
  (interval_append maskTest1 0 16 32
  maskTest1_block_0
  maskTest1_block_1)
  (interval_append maskTest1 32 48 64
  maskTest1_block_2
  maskTest1_block_3))
  (interval_append maskTest1 64 96 128
  (interval_append maskTest1 64 80 96
  maskTest1_block_4
  maskTest1_block_5)
  (interval_append maskTest1 96 112 128
  maskTest1_block_6
  maskTest1_block_7)))
  (interval_append maskTest1 128 192 256
  (interval_append maskTest1 128 160 192
  (interval_append maskTest1 128 144 160
  maskTest1_block_8
  maskTest1_block_9)
  (interval_append maskTest1 160 176 192
  maskTest1_block_10
  maskTest1_block_11))
  (interval_append maskTest1 192 224 256
  (interval_append maskTest1 192 208 224
  maskTest1_block_12
  maskTest1_block_13)
  (interval_append maskTest1 224 240 256
  maskTest1_block_14
  maskTest1_block_15))))
  (interval_append maskTest1 256 384 512
  (interval_append maskTest1 256 320 384
  (interval_append maskTest1 256 288 320
  (interval_append maskTest1 256 272 288
  maskTest1_block_16
  maskTest1_block_17)
  (interval_append maskTest1 288 304 320
  maskTest1_block_18
  maskTest1_block_19))
  (interval_append maskTest1 320 352 384
  (interval_append maskTest1 320 336 352
  maskTest1_block_20
  maskTest1_block_21)
  (interval_append maskTest1 352 368 384
  maskTest1_block_22
  maskTest1_block_23)))
  (interval_append maskTest1 384 448 512
  (interval_append maskTest1 384 416 448
  (interval_append maskTest1 384 400 416
  maskTest1_block_24
  maskTest1_block_25)
  (interval_append maskTest1 416 432 448
  maskTest1_block_26
  maskTest1_block_27))
  (interval_append maskTest1 448 480 512
  (interval_append maskTest1 448 464 480
  maskTest1_block_28
  maskTest1_block_29)
  (interval_append maskTest1 480 496 512
  maskTest1_block_30
  maskTest1_block_31)))))
  (interval_append maskTest1 512 768 1024
  (interval_append maskTest1 512 640 768
  (interval_append maskTest1 512 576 640
  (interval_append maskTest1 512 544 576
  (interval_append maskTest1 512 528 544
  maskTest1_block_32
  maskTest1_block_33)
  (interval_append maskTest1 544 560 576
  maskTest1_block_34
  maskTest1_block_35))
  (interval_append maskTest1 576 608 640
  (interval_append maskTest1 576 592 608
  maskTest1_block_36
  maskTest1_block_37)
  (interval_append maskTest1 608 624 640
  maskTest1_block_38
  maskTest1_block_39)))
  (interval_append maskTest1 640 704 768
  (interval_append maskTest1 640 672 704
  (interval_append maskTest1 640 656 672
  maskTest1_block_40
  maskTest1_block_41)
  (interval_append maskTest1 672 688 704
  maskTest1_block_42
  maskTest1_block_43))
  (interval_append maskTest1 704 736 768
  (interval_append maskTest1 704 720 736
  maskTest1_block_44
  maskTest1_block_45)
  (interval_append maskTest1 736 752 768
  maskTest1_block_46
  maskTest1_block_47))))
  (interval_append maskTest1 768 896 1024
  (interval_append maskTest1 768 832 896
  (interval_append maskTest1 768 800 832
  (interval_append maskTest1 768 784 800
  maskTest1_block_48
  maskTest1_block_49)
  (interval_append maskTest1 800 816 832
  maskTest1_block_50
  maskTest1_block_51))
  (interval_append maskTest1 832 864 896
  (interval_append maskTest1 832 848 864
  maskTest1_block_52
  maskTest1_block_53)
  (interval_append maskTest1 864 880 896
  maskTest1_block_54
  maskTest1_block_55)))
  (interval_append maskTest1 896 960 1024
  (interval_append maskTest1 896 928 960
  (interval_append maskTest1 896 912 928
  maskTest1_block_56
  maskTest1_block_57)
  (interval_append maskTest1 928 944 960
  maskTest1_block_58
  maskTest1_block_59))
  (interval_append maskTest1 960 992 1024
  (interval_append maskTest1 960 976 992
  maskTest1_block_60
  maskTest1_block_61)
  (interval_append maskTest1 992 1008 1024
  maskTest1_block_62
  maskTest1_block_63))))))
theorem mask_checked (g : Fin generatorCount) (i : Fin 1024) :
    CachedCellRelabel.lookup (renameCode g) i.val =
      RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode g)) i.val := by
  have hg : g.val < 2 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 := by omega
  rcases hc with h | h
  · have hg : g = (⟨0, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest0_complete i.val (Nat.zero_le _) i.isLt)
  · have hg : g = (⟨1, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest1_complete i.val (Nat.zero_le _) i.isLt)
def fastCellTest (g i : Nat) : Bool :=
  let gen := Fin.ofNat generatorCount g
  let cell := Fin.ofNat 655 i
  inverseCheckAt (forward gen) (forward gen) cell &&
    CachedCellRelabel.bitsetCellCheck (CachedCellRelabel.lookup (renameCode gen))
      (cells cell) (cells (forward gen cell))
theorem fastCellTest_eq (g i : Nat) : fastCellTest g i = cellTest g i := by
  simp only [fastCellTest, cellTest,
    CachedCellRelabel.cached_bitsetCellCheck_eq _ _ (mask_checked _)]
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed030.Outside.Verified
