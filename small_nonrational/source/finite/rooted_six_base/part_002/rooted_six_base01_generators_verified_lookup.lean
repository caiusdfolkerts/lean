module
prelude
public import RootedSixBase01GeneratorsData
public import CachedCellRelabel

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Verified
open Papers.RationalityTen ConcreteGrowth FiniteChecks RawGraphGrowthFrames
open Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators
def renameCodeTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031145547238395102338956648483155657604595117303494244013493206253842587057700716963271495972200914990860301547892481297282810213141235861184926516544140583400871819349673156344064094296272497590019243228141277413873637418210876983179989694215895075193112307190880587548418078505494680244878221043126428462463921520940711276956874226936895476643573730240061492807126204620525622086078467512791057444705126091950202830618601225705059295709081114819916707967987868524068568479275313525618537312089083216379889823190514935757708123349072203522085408953879776208240042676130572982717345537513844679346669482626506519417077284113007958503500290249905016243253745163795006879478108930694718045776918477288750500779369067129512171476476769134391985438177069208821024037673170942278684177732223361355977153458169600702782941425760567894362288195899296899750958553333505340169719445001839637553646968424433526096187624019470895604306452281246260306431878708960085021620247949975049412749077260855291758555966695182125646071706686455247893053291219503300876120449587718467919817201476039495469301118536832433615531068785454613017423760805564436012700226905274194873164111520946723678972765160903812575950149412361391821232857661544856863279293706653291952548730651675837483858301847524633674694313359918226024756901204627086120312910193328819244381783685320023799340777317823769699264689832660589376153487308527757836023815208139482480249652513929574112856048950743820454927744613205414582222891469811131068679869286783374917236025526324419409455972291042762813238601172696765427112978191961139535119914975020093341239820367258782375029163052078980322727343891280878600366270520526914149518591611381862596059192423875847900633819932203479948016688384129589059584465718975157110369772027178248675545445389514892342434382999365362616734121712638000529810645842434931183255302557701688710205966928650491496795128338612328547835671212755447393394016080482469611079649097324076248176548132379085302785892543332472901457534587317452610358134437242524781783319304667914388419818083373134891427922136877128606898245135326735024710355887530553956681158534782359704076432467082843580275805323094224858416609470680681529045693837298880629935751970271606026584487989157600881730195573928166315129157883707686975566129456275103066987332888723957165585408250172919887959361063515780199674972471143671007721305147051895210545581700079161393770321677528431615666277682538379747797283690019231154925999757510174260018026293203884747578961009280553796490911783016439191020387879703234492859059328345490608344612724678472372170471331460712599705794970517067528081346423978313800753711679674685468382201840639481436657780193972060972457916264788795009662885835232290190609174111048774302981785652922918053875252917467379300021757438690044029391391451082071860224155387341092780832749726758663508606061251570675032052270629888)
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031146030589498667320720657435786943876640617635033896965876224008760669254716045618505484360510611417475693317113244219394193022105682971070419849199805181521194122771861778347860674360904551003493259609466268914802112140802300264465436082758351468504083373030676834124164682495780213699535577237315851059241084800838922155445364026793605174776615498923969614649496735348018722058196192487243910623735724470863359775349714596491429202506130480662860453138401345954923622846667820257670784995350262766293930925262961314679420913259255841326080175338145883663219025173565117717273879342072550721130914408767511662895790267567177070806880835070107453164803403956517654221581528467672390149160760716233637473551690622457008937732986412141241351717100422413538757004990784127801436831448112910522884917242759320209960034561886783184510595812861900846950287523659622407826097891042737232751435405421070551440298182578648095534765877454648846008789148608941422244798999240989422143250887421321361250440622713919721284568169679345968750190644328424171188217616002190444482894308609128219023995855596014152592844791940243540031853302824513879696100797901649256152720045576225569153128866394419163629051667838870256967010007519061451266853692170175909090495758570291293038726158930619226207444250597969704010733100037326017967858988847358235912648583681140018841611980192216793705944182229757372736255376586131033535068352362439279233470050569015898315722269653505203200921626363009966699069042727008593869087684643952573661641968533434329079974310940935055221728227459653094506741259618673571897291973266234502042650275013270633901289439544244588339581007081650397235098468052099652950655617964422632011071372421959923924990771888033290333161266283970073059282016551093661143289596941286400091463928105164728049142377301595276392189206671338018865820178273915705429814451336545903117809252212866273450408548489120134951729980532537016019253735998892133821531532164760095277863671016459608522210103254819955090643430949265338298769491610610737785720861711696321699361454823239605697746463113144576549414177367093848125498322689985305652860449603085402312893215891109052745472397891324038637548926152365026960023769347510008900831893564307685285990527026659461170788862745508434094073554805763083438724864631859987985818768190209667622603606151886783400470715399568263225608366941993467362144689430583904095830212025530145497587776043257144483604876568700026935092924997384515854941321534072055684908078774533887286672259798344258343524955275535042027409507394805925827313593461562518242369037733858273458667762855863946294742167580824887029554745403732393639504546460188465876511991658077863309149223932287975852616561217772846967545797026085294276099935141912653727616657142269508196639620678821511488701268219352389696261292565606237236830384048991402477975840910780167754675329602244500462807352869888))
 (.branch 3
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031146030589498667320720657435786943876640617635033896965876224008760669254716045618505484360510611417475693317113244219394193022105682971070419849199805181521194122771861778347860674360904551003493471492159798365977693560546646479025542718964713745284361464244356982126907626488107970066061452013137519401013935588845305467961265247145220072294543368037087371529177491384137169726733007090447205874059034157368417435975012489809584639678566423444637272269780656971790160146024174047151729913203233321669897850452700466606927559250713256933784280915065580872203402047231272167528503202925913053875735844940907796331800714006563552686986237930878565671009834360245129043182133995172589349104307785570271449736307787247422555947763980195740648518052247437638806246987204201503043026646764243530349958188087304060068444676635882939208192031432851205894448065854247934539000548113206570945398377155531688130710685494231999373792204285144836261240020985980666050342747214621695671661050964103766725726223808441025376929828612291146655324922653674067001619855784915927204111533068260239916672023297009996535563496337134223823969861744393130674137350943748913317837702952430739992017784743378622029626536537719924809404789703043837566527728587492294490294363932781963328291360585720142743560342948562384723155796498787015242077320027892735722235229527534578097192387065900760259072304217968176474370538996611131010132069592739645335972383847845354206349221486746374592655832522148253796962239556415962412041040665244145325911720126104161911635337034468844527643242910688600191820212892555514319833145774774262198134511576730618547545257860759270433551615420730436006550170516832050187450227969901968566267665615513701949603364998372989186681022647989056998931444208579787726914161540378863374289631332505101137266975299884295510326412243747235161983238646638075599811599603809642248026605966244618136990805673984420085711595434808025800283368753816682786363780121255368833602608540909412124546482332328311318365977024541724209091408565047629100920831955385651069793623996481856335988214260846383308056328676818466540656986732289284172425322280077525299081472540070563200460404560388010764851365993882681307196636112064488421143305403059629657526175956622777906966255645102900132850175359836080229673025312953977614795411434631585276635215917133702193218407506615028969853972340940578945225269009487975852120035196798822494401340479189191889226428280791320430361516459088235587944535546485014636119591473795168390685708762196502229642133837906644647082185694972109213015811374267349875440787126083457770002997860877530005184567091171340731106470899528456290464346818554058416569620352042088088456262178609541493871229301871835520030357815462155516773013264843524684624051989113111296146895765811940274361227265439273237301529974142061374326598431564754674237442977517272949915229587246678216803681829888)
 (.leaf 35249680241417312313872578120498056202372474352151724075373124344763123026428304712027487895440507945259634035151349101415885247216769211347327071240998363579006899137784668503730068996521708650390633901389946913161603732914203132692858072421947392767501029502841899699455611476964713519685758861379343449542736833311009991069477105092581871725616156792134010438695296385971870591041221486891029221388125377598306652138367216825047132041091510736849837599842610459893998574272172820074826962825730716274217186571387186386283137891411498767028387380291578092422326172856314548168046375470931060087589462062158568385024033548978903923070303522490521921603461521420302627947382993671576448582913034705005247904867821738022822100254180416137941117314607416413746618043115691325390156166811158569657785433218713045800478352715306664564280631862212694313745138866700530484380410771980868886585425886564472666707651490706857992640516031143013493054200464123345550502765992736036291979618474363734009732190584358953024674665882999821107593582658490600184093015532993378343709759827640505136966607043231378936465523820391065402508499456938100141788642690654473107040343239998102167000783188119180523403835836521631271763807636965826955937402971371260425330896451647385058879011295959741530892482221734928350335561500114531007496648285793276055517826177188302142387695931985781243211785011075341679140432296184473783631745543894497468589198790648102246996145041623884336793938858925251601645321984620006930449622688835322604879043280411469448137351404056700226276551627222123710178632668580645737069090365768915393556493483528686787715378291996846308781296916287828313474379616047313072497275339037658151740403859507734091842019086055220168333407982737655597134049710564320258091269756959571621913270277624868152349297677752641027177797300250734828029534875816432241092903480673713728939545259645335726770412527529040063366848744096402803461308517887481755113036577938848625403080810963255066477491580994564904764151700217076652988643853307780344268619503210578809853739503442126774576508636147742416075260410642971139727274238172867722982037003172593235878394439296646095996687490530457922992922719424853415130379901863458299144125237603703986229934824087306674450444900834811940942245392531464384562831018160624974231158480096242771092355972485970782925259272441158541973782128289746508254555661128557725376406193844461124871254444804248292137553645635050150403597512574289259273158868056111909385054267039074714846771720040097614194168065230530021214121412894863955677544110876697650933429111001149049731723518288439132445235155035165560858806997440675148390194829907546036180008148125653926289801127080786009960512284907332908396494555939143168695215860331423037000311524842339529541598323540914288628921073966942885674740178576709923782035907181591040004378770817382842665387915425049779802131899574560471950840682149806361010072747627010696444282177434419532094560074985811226430796362749861034695280745494836457601247911345880588421070813018932008081395985451403500564294521297372709888)))
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
def maskTest2 (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode 2) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode 2)) j)
theorem maskTest2_block_0 : Interval maskTest2 0 16 :=
  interval_of_check maskTest2 0 16 (by decide +kernel)

theorem maskTest2_block_1 : Interval maskTest2 16 32 :=
  interval_of_check maskTest2 16 16 (by decide +kernel)

theorem maskTest2_block_2 : Interval maskTest2 32 48 :=
  interval_of_check maskTest2 32 16 (by decide +kernel)

theorem maskTest2_block_3 : Interval maskTest2 48 64 :=
  interval_of_check maskTest2 48 16 (by decide +kernel)

theorem maskTest2_block_4 : Interval maskTest2 64 80 :=
  interval_of_check maskTest2 64 16 (by decide +kernel)

theorem maskTest2_block_5 : Interval maskTest2 80 96 :=
  interval_of_check maskTest2 80 16 (by decide +kernel)

theorem maskTest2_block_6 : Interval maskTest2 96 112 :=
  interval_of_check maskTest2 96 16 (by decide +kernel)

theorem maskTest2_block_7 : Interval maskTest2 112 128 :=
  interval_of_check maskTest2 112 16 (by decide +kernel)

theorem maskTest2_block_8 : Interval maskTest2 128 144 :=
  interval_of_check maskTest2 128 16 (by decide +kernel)

theorem maskTest2_block_9 : Interval maskTest2 144 160 :=
  interval_of_check maskTest2 144 16 (by decide +kernel)

theorem maskTest2_block_10 : Interval maskTest2 160 176 :=
  interval_of_check maskTest2 160 16 (by decide +kernel)

theorem maskTest2_block_11 : Interval maskTest2 176 192 :=
  interval_of_check maskTest2 176 16 (by decide +kernel)

theorem maskTest2_block_12 : Interval maskTest2 192 208 :=
  interval_of_check maskTest2 192 16 (by decide +kernel)

theorem maskTest2_block_13 : Interval maskTest2 208 224 :=
  interval_of_check maskTest2 208 16 (by decide +kernel)

theorem maskTest2_block_14 : Interval maskTest2 224 240 :=
  interval_of_check maskTest2 224 16 (by decide +kernel)

theorem maskTest2_block_15 : Interval maskTest2 240 256 :=
  interval_of_check maskTest2 240 16 (by decide +kernel)

theorem maskTest2_block_16 : Interval maskTest2 256 272 :=
  interval_of_check maskTest2 256 16 (by decide +kernel)

theorem maskTest2_block_17 : Interval maskTest2 272 288 :=
  interval_of_check maskTest2 272 16 (by decide +kernel)

theorem maskTest2_block_18 : Interval maskTest2 288 304 :=
  interval_of_check maskTest2 288 16 (by decide +kernel)

theorem maskTest2_block_19 : Interval maskTest2 304 320 :=
  interval_of_check maskTest2 304 16 (by decide +kernel)

theorem maskTest2_block_20 : Interval maskTest2 320 336 :=
  interval_of_check maskTest2 320 16 (by decide +kernel)

theorem maskTest2_block_21 : Interval maskTest2 336 352 :=
  interval_of_check maskTest2 336 16 (by decide +kernel)

theorem maskTest2_block_22 : Interval maskTest2 352 368 :=
  interval_of_check maskTest2 352 16 (by decide +kernel)

theorem maskTest2_block_23 : Interval maskTest2 368 384 :=
  interval_of_check maskTest2 368 16 (by decide +kernel)

theorem maskTest2_block_24 : Interval maskTest2 384 400 :=
  interval_of_check maskTest2 384 16 (by decide +kernel)

theorem maskTest2_block_25 : Interval maskTest2 400 416 :=
  interval_of_check maskTest2 400 16 (by decide +kernel)

theorem maskTest2_block_26 : Interval maskTest2 416 432 :=
  interval_of_check maskTest2 416 16 (by decide +kernel)

theorem maskTest2_block_27 : Interval maskTest2 432 448 :=
  interval_of_check maskTest2 432 16 (by decide +kernel)

theorem maskTest2_block_28 : Interval maskTest2 448 464 :=
  interval_of_check maskTest2 448 16 (by decide +kernel)

theorem maskTest2_block_29 : Interval maskTest2 464 480 :=
  interval_of_check maskTest2 464 16 (by decide +kernel)

theorem maskTest2_block_30 : Interval maskTest2 480 496 :=
  interval_of_check maskTest2 480 16 (by decide +kernel)

theorem maskTest2_block_31 : Interval maskTest2 496 512 :=
  interval_of_check maskTest2 496 16 (by decide +kernel)

theorem maskTest2_block_32 : Interval maskTest2 512 528 :=
  interval_of_check maskTest2 512 16 (by decide +kernel)

theorem maskTest2_block_33 : Interval maskTest2 528 544 :=
  interval_of_check maskTest2 528 16 (by decide +kernel)

theorem maskTest2_block_34 : Interval maskTest2 544 560 :=
  interval_of_check maskTest2 544 16 (by decide +kernel)

theorem maskTest2_block_35 : Interval maskTest2 560 576 :=
  interval_of_check maskTest2 560 16 (by decide +kernel)

theorem maskTest2_block_36 : Interval maskTest2 576 592 :=
  interval_of_check maskTest2 576 16 (by decide +kernel)

theorem maskTest2_block_37 : Interval maskTest2 592 608 :=
  interval_of_check maskTest2 592 16 (by decide +kernel)

theorem maskTest2_block_38 : Interval maskTest2 608 624 :=
  interval_of_check maskTest2 608 16 (by decide +kernel)

theorem maskTest2_block_39 : Interval maskTest2 624 640 :=
  interval_of_check maskTest2 624 16 (by decide +kernel)

theorem maskTest2_block_40 : Interval maskTest2 640 656 :=
  interval_of_check maskTest2 640 16 (by decide +kernel)

theorem maskTest2_block_41 : Interval maskTest2 656 672 :=
  interval_of_check maskTest2 656 16 (by decide +kernel)

theorem maskTest2_block_42 : Interval maskTest2 672 688 :=
  interval_of_check maskTest2 672 16 (by decide +kernel)

theorem maskTest2_block_43 : Interval maskTest2 688 704 :=
  interval_of_check maskTest2 688 16 (by decide +kernel)

theorem maskTest2_block_44 : Interval maskTest2 704 720 :=
  interval_of_check maskTest2 704 16 (by decide +kernel)

theorem maskTest2_block_45 : Interval maskTest2 720 736 :=
  interval_of_check maskTest2 720 16 (by decide +kernel)

theorem maskTest2_block_46 : Interval maskTest2 736 752 :=
  interval_of_check maskTest2 736 16 (by decide +kernel)

theorem maskTest2_block_47 : Interval maskTest2 752 768 :=
  interval_of_check maskTest2 752 16 (by decide +kernel)

theorem maskTest2_block_48 : Interval maskTest2 768 784 :=
  interval_of_check maskTest2 768 16 (by decide +kernel)

theorem maskTest2_block_49 : Interval maskTest2 784 800 :=
  interval_of_check maskTest2 784 16 (by decide +kernel)

theorem maskTest2_block_50 : Interval maskTest2 800 816 :=
  interval_of_check maskTest2 800 16 (by decide +kernel)

theorem maskTest2_block_51 : Interval maskTest2 816 832 :=
  interval_of_check maskTest2 816 16 (by decide +kernel)

theorem maskTest2_block_52 : Interval maskTest2 832 848 :=
  interval_of_check maskTest2 832 16 (by decide +kernel)

theorem maskTest2_block_53 : Interval maskTest2 848 864 :=
  interval_of_check maskTest2 848 16 (by decide +kernel)

theorem maskTest2_block_54 : Interval maskTest2 864 880 :=
  interval_of_check maskTest2 864 16 (by decide +kernel)

theorem maskTest2_block_55 : Interval maskTest2 880 896 :=
  interval_of_check maskTest2 880 16 (by decide +kernel)

theorem maskTest2_block_56 : Interval maskTest2 896 912 :=
  interval_of_check maskTest2 896 16 (by decide +kernel)

theorem maskTest2_block_57 : Interval maskTest2 912 928 :=
  interval_of_check maskTest2 912 16 (by decide +kernel)

theorem maskTest2_block_58 : Interval maskTest2 928 944 :=
  interval_of_check maskTest2 928 16 (by decide +kernel)

theorem maskTest2_block_59 : Interval maskTest2 944 960 :=
  interval_of_check maskTest2 944 16 (by decide +kernel)

theorem maskTest2_block_60 : Interval maskTest2 960 976 :=
  interval_of_check maskTest2 960 16 (by decide +kernel)

theorem maskTest2_block_61 : Interval maskTest2 976 992 :=
  interval_of_check maskTest2 976 16 (by decide +kernel)

theorem maskTest2_block_62 : Interval maskTest2 992 1008 :=
  interval_of_check maskTest2 992 16 (by decide +kernel)

theorem maskTest2_block_63 : Interval maskTest2 1008 1024 :=
  interval_of_check maskTest2 1008 16 (by decide +kernel)

theorem maskTest2_complete : Interval maskTest2 0 1024 :=
  (interval_append maskTest2 0 512 1024
  (interval_append maskTest2 0 256 512
  (interval_append maskTest2 0 128 256
  (interval_append maskTest2 0 64 128
  (interval_append maskTest2 0 32 64
  (interval_append maskTest2 0 16 32
  maskTest2_block_0
  maskTest2_block_1)
  (interval_append maskTest2 32 48 64
  maskTest2_block_2
  maskTest2_block_3))
  (interval_append maskTest2 64 96 128
  (interval_append maskTest2 64 80 96
  maskTest2_block_4
  maskTest2_block_5)
  (interval_append maskTest2 96 112 128
  maskTest2_block_6
  maskTest2_block_7)))
  (interval_append maskTest2 128 192 256
  (interval_append maskTest2 128 160 192
  (interval_append maskTest2 128 144 160
  maskTest2_block_8
  maskTest2_block_9)
  (interval_append maskTest2 160 176 192
  maskTest2_block_10
  maskTest2_block_11))
  (interval_append maskTest2 192 224 256
  (interval_append maskTest2 192 208 224
  maskTest2_block_12
  maskTest2_block_13)
  (interval_append maskTest2 224 240 256
  maskTest2_block_14
  maskTest2_block_15))))
  (interval_append maskTest2 256 384 512
  (interval_append maskTest2 256 320 384
  (interval_append maskTest2 256 288 320
  (interval_append maskTest2 256 272 288
  maskTest2_block_16
  maskTest2_block_17)
  (interval_append maskTest2 288 304 320
  maskTest2_block_18
  maskTest2_block_19))
  (interval_append maskTest2 320 352 384
  (interval_append maskTest2 320 336 352
  maskTest2_block_20
  maskTest2_block_21)
  (interval_append maskTest2 352 368 384
  maskTest2_block_22
  maskTest2_block_23)))
  (interval_append maskTest2 384 448 512
  (interval_append maskTest2 384 416 448
  (interval_append maskTest2 384 400 416
  maskTest2_block_24
  maskTest2_block_25)
  (interval_append maskTest2 416 432 448
  maskTest2_block_26
  maskTest2_block_27))
  (interval_append maskTest2 448 480 512
  (interval_append maskTest2 448 464 480
  maskTest2_block_28
  maskTest2_block_29)
  (interval_append maskTest2 480 496 512
  maskTest2_block_30
  maskTest2_block_31)))))
  (interval_append maskTest2 512 768 1024
  (interval_append maskTest2 512 640 768
  (interval_append maskTest2 512 576 640
  (interval_append maskTest2 512 544 576
  (interval_append maskTest2 512 528 544
  maskTest2_block_32
  maskTest2_block_33)
  (interval_append maskTest2 544 560 576
  maskTest2_block_34
  maskTest2_block_35))
  (interval_append maskTest2 576 608 640
  (interval_append maskTest2 576 592 608
  maskTest2_block_36
  maskTest2_block_37)
  (interval_append maskTest2 608 624 640
  maskTest2_block_38
  maskTest2_block_39)))
  (interval_append maskTest2 640 704 768
  (interval_append maskTest2 640 672 704
  (interval_append maskTest2 640 656 672
  maskTest2_block_40
  maskTest2_block_41)
  (interval_append maskTest2 672 688 704
  maskTest2_block_42
  maskTest2_block_43))
  (interval_append maskTest2 704 736 768
  (interval_append maskTest2 704 720 736
  maskTest2_block_44
  maskTest2_block_45)
  (interval_append maskTest2 736 752 768
  maskTest2_block_46
  maskTest2_block_47))))
  (interval_append maskTest2 768 896 1024
  (interval_append maskTest2 768 832 896
  (interval_append maskTest2 768 800 832
  (interval_append maskTest2 768 784 800
  maskTest2_block_48
  maskTest2_block_49)
  (interval_append maskTest2 800 816 832
  maskTest2_block_50
  maskTest2_block_51))
  (interval_append maskTest2 832 864 896
  (interval_append maskTest2 832 848 864
  maskTest2_block_52
  maskTest2_block_53)
  (interval_append maskTest2 864 880 896
  maskTest2_block_54
  maskTest2_block_55)))
  (interval_append maskTest2 896 960 1024
  (interval_append maskTest2 896 928 960
  (interval_append maskTest2 896 912 928
  maskTest2_block_56
  maskTest2_block_57)
  (interval_append maskTest2 928 944 960
  maskTest2_block_58
  maskTest2_block_59))
  (interval_append maskTest2 960 992 1024
  (interval_append maskTest2 960 976 992
  maskTest2_block_60
  maskTest2_block_61)
  (interval_append maskTest2 992 1008 1024
  maskTest2_block_62
  maskTest2_block_63))))))
def maskTest3 (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode 3) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode 3)) j)
theorem maskTest3_block_0 : Interval maskTest3 0 16 :=
  interval_of_check maskTest3 0 16 (by decide +kernel)

theorem maskTest3_block_1 : Interval maskTest3 16 32 :=
  interval_of_check maskTest3 16 16 (by decide +kernel)

theorem maskTest3_block_2 : Interval maskTest3 32 48 :=
  interval_of_check maskTest3 32 16 (by decide +kernel)

theorem maskTest3_block_3 : Interval maskTest3 48 64 :=
  interval_of_check maskTest3 48 16 (by decide +kernel)

theorem maskTest3_block_4 : Interval maskTest3 64 80 :=
  interval_of_check maskTest3 64 16 (by decide +kernel)

theorem maskTest3_block_5 : Interval maskTest3 80 96 :=
  interval_of_check maskTest3 80 16 (by decide +kernel)

theorem maskTest3_block_6 : Interval maskTest3 96 112 :=
  interval_of_check maskTest3 96 16 (by decide +kernel)

theorem maskTest3_block_7 : Interval maskTest3 112 128 :=
  interval_of_check maskTest3 112 16 (by decide +kernel)

theorem maskTest3_block_8 : Interval maskTest3 128 144 :=
  interval_of_check maskTest3 128 16 (by decide +kernel)

theorem maskTest3_block_9 : Interval maskTest3 144 160 :=
  interval_of_check maskTest3 144 16 (by decide +kernel)

theorem maskTest3_block_10 : Interval maskTest3 160 176 :=
  interval_of_check maskTest3 160 16 (by decide +kernel)

theorem maskTest3_block_11 : Interval maskTest3 176 192 :=
  interval_of_check maskTest3 176 16 (by decide +kernel)

theorem maskTest3_block_12 : Interval maskTest3 192 208 :=
  interval_of_check maskTest3 192 16 (by decide +kernel)

theorem maskTest3_block_13 : Interval maskTest3 208 224 :=
  interval_of_check maskTest3 208 16 (by decide +kernel)

theorem maskTest3_block_14 : Interval maskTest3 224 240 :=
  interval_of_check maskTest3 224 16 (by decide +kernel)

theorem maskTest3_block_15 : Interval maskTest3 240 256 :=
  interval_of_check maskTest3 240 16 (by decide +kernel)

theorem maskTest3_block_16 : Interval maskTest3 256 272 :=
  interval_of_check maskTest3 256 16 (by decide +kernel)

theorem maskTest3_block_17 : Interval maskTest3 272 288 :=
  interval_of_check maskTest3 272 16 (by decide +kernel)

theorem maskTest3_block_18 : Interval maskTest3 288 304 :=
  interval_of_check maskTest3 288 16 (by decide +kernel)

theorem maskTest3_block_19 : Interval maskTest3 304 320 :=
  interval_of_check maskTest3 304 16 (by decide +kernel)

theorem maskTest3_block_20 : Interval maskTest3 320 336 :=
  interval_of_check maskTest3 320 16 (by decide +kernel)

theorem maskTest3_block_21 : Interval maskTest3 336 352 :=
  interval_of_check maskTest3 336 16 (by decide +kernel)

theorem maskTest3_block_22 : Interval maskTest3 352 368 :=
  interval_of_check maskTest3 352 16 (by decide +kernel)

theorem maskTest3_block_23 : Interval maskTest3 368 384 :=
  interval_of_check maskTest3 368 16 (by decide +kernel)

theorem maskTest3_block_24 : Interval maskTest3 384 400 :=
  interval_of_check maskTest3 384 16 (by decide +kernel)

theorem maskTest3_block_25 : Interval maskTest3 400 416 :=
  interval_of_check maskTest3 400 16 (by decide +kernel)

theorem maskTest3_block_26 : Interval maskTest3 416 432 :=
  interval_of_check maskTest3 416 16 (by decide +kernel)

theorem maskTest3_block_27 : Interval maskTest3 432 448 :=
  interval_of_check maskTest3 432 16 (by decide +kernel)

theorem maskTest3_block_28 : Interval maskTest3 448 464 :=
  interval_of_check maskTest3 448 16 (by decide +kernel)

theorem maskTest3_block_29 : Interval maskTest3 464 480 :=
  interval_of_check maskTest3 464 16 (by decide +kernel)

theorem maskTest3_block_30 : Interval maskTest3 480 496 :=
  interval_of_check maskTest3 480 16 (by decide +kernel)

theorem maskTest3_block_31 : Interval maskTest3 496 512 :=
  interval_of_check maskTest3 496 16 (by decide +kernel)

theorem maskTest3_block_32 : Interval maskTest3 512 528 :=
  interval_of_check maskTest3 512 16 (by decide +kernel)

theorem maskTest3_block_33 : Interval maskTest3 528 544 :=
  interval_of_check maskTest3 528 16 (by decide +kernel)

theorem maskTest3_block_34 : Interval maskTest3 544 560 :=
  interval_of_check maskTest3 544 16 (by decide +kernel)

theorem maskTest3_block_35 : Interval maskTest3 560 576 :=
  interval_of_check maskTest3 560 16 (by decide +kernel)

theorem maskTest3_block_36 : Interval maskTest3 576 592 :=
  interval_of_check maskTest3 576 16 (by decide +kernel)

theorem maskTest3_block_37 : Interval maskTest3 592 608 :=
  interval_of_check maskTest3 592 16 (by decide +kernel)

theorem maskTest3_block_38 : Interval maskTest3 608 624 :=
  interval_of_check maskTest3 608 16 (by decide +kernel)

theorem maskTest3_block_39 : Interval maskTest3 624 640 :=
  interval_of_check maskTest3 624 16 (by decide +kernel)

theorem maskTest3_block_40 : Interval maskTest3 640 656 :=
  interval_of_check maskTest3 640 16 (by decide +kernel)

theorem maskTest3_block_41 : Interval maskTest3 656 672 :=
  interval_of_check maskTest3 656 16 (by decide +kernel)

theorem maskTest3_block_42 : Interval maskTest3 672 688 :=
  interval_of_check maskTest3 672 16 (by decide +kernel)

theorem maskTest3_block_43 : Interval maskTest3 688 704 :=
  interval_of_check maskTest3 688 16 (by decide +kernel)

theorem maskTest3_block_44 : Interval maskTest3 704 720 :=
  interval_of_check maskTest3 704 16 (by decide +kernel)

theorem maskTest3_block_45 : Interval maskTest3 720 736 :=
  interval_of_check maskTest3 720 16 (by decide +kernel)

theorem maskTest3_block_46 : Interval maskTest3 736 752 :=
  interval_of_check maskTest3 736 16 (by decide +kernel)

theorem maskTest3_block_47 : Interval maskTest3 752 768 :=
  interval_of_check maskTest3 752 16 (by decide +kernel)

theorem maskTest3_block_48 : Interval maskTest3 768 784 :=
  interval_of_check maskTest3 768 16 (by decide +kernel)

theorem maskTest3_block_49 : Interval maskTest3 784 800 :=
  interval_of_check maskTest3 784 16 (by decide +kernel)

theorem maskTest3_block_50 : Interval maskTest3 800 816 :=
  interval_of_check maskTest3 800 16 (by decide +kernel)

theorem maskTest3_block_51 : Interval maskTest3 816 832 :=
  interval_of_check maskTest3 816 16 (by decide +kernel)

theorem maskTest3_block_52 : Interval maskTest3 832 848 :=
  interval_of_check maskTest3 832 16 (by decide +kernel)

theorem maskTest3_block_53 : Interval maskTest3 848 864 :=
  interval_of_check maskTest3 848 16 (by decide +kernel)

theorem maskTest3_block_54 : Interval maskTest3 864 880 :=
  interval_of_check maskTest3 864 16 (by decide +kernel)

theorem maskTest3_block_55 : Interval maskTest3 880 896 :=
  interval_of_check maskTest3 880 16 (by decide +kernel)

theorem maskTest3_block_56 : Interval maskTest3 896 912 :=
  interval_of_check maskTest3 896 16 (by decide +kernel)

theorem maskTest3_block_57 : Interval maskTest3 912 928 :=
  interval_of_check maskTest3 912 16 (by decide +kernel)

theorem maskTest3_block_58 : Interval maskTest3 928 944 :=
  interval_of_check maskTest3 928 16 (by decide +kernel)

theorem maskTest3_block_59 : Interval maskTest3 944 960 :=
  interval_of_check maskTest3 944 16 (by decide +kernel)

theorem maskTest3_block_60 : Interval maskTest3 960 976 :=
  interval_of_check maskTest3 960 16 (by decide +kernel)

theorem maskTest3_block_61 : Interval maskTest3 976 992 :=
  interval_of_check maskTest3 976 16 (by decide +kernel)

theorem maskTest3_block_62 : Interval maskTest3 992 1008 :=
  interval_of_check maskTest3 992 16 (by decide +kernel)

theorem maskTest3_block_63 : Interval maskTest3 1008 1024 :=
  interval_of_check maskTest3 1008 16 (by decide +kernel)

theorem maskTest3_complete : Interval maskTest3 0 1024 :=
  (interval_append maskTest3 0 512 1024
  (interval_append maskTest3 0 256 512
  (interval_append maskTest3 0 128 256
  (interval_append maskTest3 0 64 128
  (interval_append maskTest3 0 32 64
  (interval_append maskTest3 0 16 32
  maskTest3_block_0
  maskTest3_block_1)
  (interval_append maskTest3 32 48 64
  maskTest3_block_2
  maskTest3_block_3))
  (interval_append maskTest3 64 96 128
  (interval_append maskTest3 64 80 96
  maskTest3_block_4
  maskTest3_block_5)
  (interval_append maskTest3 96 112 128
  maskTest3_block_6
  maskTest3_block_7)))
  (interval_append maskTest3 128 192 256
  (interval_append maskTest3 128 160 192
  (interval_append maskTest3 128 144 160
  maskTest3_block_8
  maskTest3_block_9)
  (interval_append maskTest3 160 176 192
  maskTest3_block_10
  maskTest3_block_11))
  (interval_append maskTest3 192 224 256
  (interval_append maskTest3 192 208 224
  maskTest3_block_12
  maskTest3_block_13)
  (interval_append maskTest3 224 240 256
  maskTest3_block_14
  maskTest3_block_15))))
  (interval_append maskTest3 256 384 512
  (interval_append maskTest3 256 320 384
  (interval_append maskTest3 256 288 320
  (interval_append maskTest3 256 272 288
  maskTest3_block_16
  maskTest3_block_17)
  (interval_append maskTest3 288 304 320
  maskTest3_block_18
  maskTest3_block_19))
  (interval_append maskTest3 320 352 384
  (interval_append maskTest3 320 336 352
  maskTest3_block_20
  maskTest3_block_21)
  (interval_append maskTest3 352 368 384
  maskTest3_block_22
  maskTest3_block_23)))
  (interval_append maskTest3 384 448 512
  (interval_append maskTest3 384 416 448
  (interval_append maskTest3 384 400 416
  maskTest3_block_24
  maskTest3_block_25)
  (interval_append maskTest3 416 432 448
  maskTest3_block_26
  maskTest3_block_27))
  (interval_append maskTest3 448 480 512
  (interval_append maskTest3 448 464 480
  maskTest3_block_28
  maskTest3_block_29)
  (interval_append maskTest3 480 496 512
  maskTest3_block_30
  maskTest3_block_31)))))
  (interval_append maskTest3 512 768 1024
  (interval_append maskTest3 512 640 768
  (interval_append maskTest3 512 576 640
  (interval_append maskTest3 512 544 576
  (interval_append maskTest3 512 528 544
  maskTest3_block_32
  maskTest3_block_33)
  (interval_append maskTest3 544 560 576
  maskTest3_block_34
  maskTest3_block_35))
  (interval_append maskTest3 576 608 640
  (interval_append maskTest3 576 592 608
  maskTest3_block_36
  maskTest3_block_37)
  (interval_append maskTest3 608 624 640
  maskTest3_block_38
  maskTest3_block_39)))
  (interval_append maskTest3 640 704 768
  (interval_append maskTest3 640 672 704
  (interval_append maskTest3 640 656 672
  maskTest3_block_40
  maskTest3_block_41)
  (interval_append maskTest3 672 688 704
  maskTest3_block_42
  maskTest3_block_43))
  (interval_append maskTest3 704 736 768
  (interval_append maskTest3 704 720 736
  maskTest3_block_44
  maskTest3_block_45)
  (interval_append maskTest3 736 752 768
  maskTest3_block_46
  maskTest3_block_47))))
  (interval_append maskTest3 768 896 1024
  (interval_append maskTest3 768 832 896
  (interval_append maskTest3 768 800 832
  (interval_append maskTest3 768 784 800
  maskTest3_block_48
  maskTest3_block_49)
  (interval_append maskTest3 800 816 832
  maskTest3_block_50
  maskTest3_block_51))
  (interval_append maskTest3 832 864 896
  (interval_append maskTest3 832 848 864
  maskTest3_block_52
  maskTest3_block_53)
  (interval_append maskTest3 864 880 896
  maskTest3_block_54
  maskTest3_block_55)))
  (interval_append maskTest3 896 960 1024
  (interval_append maskTest3 896 928 960
  (interval_append maskTest3 896 912 928
  maskTest3_block_56
  maskTest3_block_57)
  (interval_append maskTest3 928 944 960
  maskTest3_block_58
  maskTest3_block_59))
  (interval_append maskTest3 960 992 1024
  (interval_append maskTest3 960 976 992
  maskTest3_block_60
  maskTest3_block_61)
  (interval_append maskTest3 992 1008 1024
  maskTest3_block_62
  maskTest3_block_63))))))
theorem mask_checked (g : Fin generatorCount) (i : Fin 1024) :
    CachedCellRelabel.lookup (renameCode g) i.val =
      RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode g)) i.val := by
  have hg : g.val < 4 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 ∨ g.val = 2 ∨ g.val = 3 := by omega
  rcases hc with h | h | h | h
  · have hg : g = (⟨0, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest0_complete i.val (Nat.zero_le _) i.isLt)
  · have hg : g = (⟨1, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest1_complete i.val (Nat.zero_le _) i.isLt)
  · have hg : g = (⟨2, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest2_complete i.val (Nat.zero_le _) i.isLt)
  · have hg : g = (⟨3, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest3_complete i.val (Nat.zero_le _) i.isLt)
def fastCellTest (g i : Nat) : Bool :=
  let gen := Fin.ofNat generatorCount g
  let cell := Fin.ofNat 15246 i
  inverseCheckAt (forward gen) (inverse gen) cell &&
    CachedCellRelabel.bitsetCellCheck (CachedCellRelabel.lookup (renameCode gen))
      (cells cell) (cells (forward gen cell))
theorem fastCellTest_eq (g i : Nat) : fastCellTest g i = cellTest g i := by
  simp only [fastCellTest, cellTest,
    CachedCellRelabel.cached_bitsetCellCheck_eq _ _ (mask_checked _)]
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Verified
