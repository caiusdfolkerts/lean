module
public import verification_bundle.PalomarPart018
import all verification_bundle.PalomarPart018
public import foundation_bundle
public import incidence_bundle
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See VerificationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/FaceDataChecks/LowerFacets.lean -/
section VerificationSource011


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 49.3, recovered from skew spokes on cycle 5. -/
theorem value_199 (h : Assignment) (H : Constraints h) :
    h 49 3 = ((-2426322943114626526678742106 : ℝ) / 8971371669482483594692034863) * (h 1 0) + ((297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (h 1 1) + h 1 3 + ((2426322943114626526678742106 : ℝ) / 8971371669482483594692034863) * (h 3 0) + ((-297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (h 5 1) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 41 3
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 3 - h 8 3) - ((-529767551903157376559408544 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-11311528250090727670709154778126512014635981405964898551734024379 : ℝ) / 1794864300951399695831192167496145713152631976225639513007613208) * r0 + ((75853659905712005905582150656068742751027427474442769 : ℝ) / 19862340126669629151451224189224724232845911863373412) * r1 + ((8764536704280177185725509 : ℝ) / 1406454857523895487521505370515786415408745026862507984) * r2 + ((-4461979994453647406210714744474631926531025145555457 : ℝ) / 6227695336260158034521420078029352065534515282796599625579078929540694736514432) * r3 + ((1 : ℝ) / 5330228968049311405994223712) * r4 + ((-148997123972763012157333653 : ℝ) / 405349889223269495638375140553315272821) * r5 + ((-8764536704280177185725509 : ℝ) / 6724747171953118056688208911266696752807828216917688) * r6 + ((4461979994453647406210714744474631926531025145555457 : ℝ) / 29776765586370474751411235639553103580951663991975110161295121673018568207424) * r7 + ((-324612470528895451323167 : ℝ) / 110503321164829735063530166068804158369943874719046610320) * r8 + ((4461979994453647406210714744474631926531025145555457 : ℝ) / 13211150989174186200246742099694985726956955622374237169286933712265241431518126720) * r9 + ((11819073567744266577307007134560483825 : ℝ) / 405349889223269495638375140553315272821) * (value_032 h H) + ((297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (value_033 h H) + (1 : ℝ) * (value_035 h H) + ((-297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (value_053 h H) + ((-11819073567744266577307007134560483825 : ℝ) / 405349889223269495638375140553315272821) * (value_052 h H)

/-- Coordinate 53.0, recovered from skew spokes on cycle 5. -/
theorem value_212 (h : Assignment) (H : Constraints h) :
    h 53 0 = ((149302932363421640305550014 : ℝ) / 174439137112328495842535639) * (h 1 0) + ((-57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (h 1 1) + ((25136204748906855536985625 : ℝ) / 174439137112328495842535639) * (h 3 0) + ((57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (h 5 1) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((6096790668967437779697306810405810950684001980456330580041389309 : ℝ) / 52348948091749130823088635389233490102712571658498723449989636) * r0 + ((-40937330339900113224069070961328780763007853164799599 : ℝ) / 579304302682127186438340924196235438563605237615654) * r1 + ((-64867368774335133109221 : ℝ) / 1051810567644410698623505788393233983282358761876552) * r2 + ((242232723904734397775556632907270892088803864880471 : ℝ) / 18271151334153140441880121740549312635372018852175956043502451456678979580992) * r3 + ((28671376998256128834275682 : ℝ) / 7881613593739778570452464141595648813) * r4 + ((9 : ℝ) / 697756548449313983370142556) * r5 + ((-436910410154745972362568511367 : ℝ) / 157570770329538594711228731381376039289300624631457888) * r6 + ((93697310451817414491097 : ℝ) / 3222935918084311247086156974372921898445946633741004440) * r7 + ((-40937330339900113224069070961328780763007853164799599 : ℝ) / 6550371283759531524534649210349552831825880373927469794599278785891610307252550080) * r8 + ((5607280338200792782663752809215611763 : ℝ) / 7881613593739778570452464141595648813) * (value_032 h H) + ((-57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (value_033 h H) + ((57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (value_053 h H) + ((2274333255538985787788711332380037050 : ℝ) / 7881613593739778570452464141595648813) * (value_052 h H)

/-- Coordinate 53.1, recovered from skew spokes on cycle 5. -/
theorem value_213 (h : Assignment) (H : Constraints h) :
    h 53 1 = ((734066461754127170845303 : ℝ) / 199359013842661138105755016) * (h 1 0) + ((46077754888497773053609785 : ℝ) / 99679506921330569052877508) * (h 1 1) + ((-734066461754127170845303 : ℝ) / 199359013842661138105755016) * (h 3 0) + ((53601752032832795999267723 : ℝ) / 99679506921330569052877508) * (h 5 1) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-110687415190230211852373516388487015249348527657275715750661196795 : ℝ) / 678043518140750646851433753612929014663705690052935846590341952) * r0 + ((745624103234941233090529098238305516128812060487219485 : ℝ) / 7503370015692314033868034827684573299490505934831328) * r1 + ((46077754888497773053609785 : ℝ) / 531314595312948032904673781108353623555202940285069696) * r2 + ((-57355700248841633314656084479869655086831696960555345 : ℝ) / 3076513862741214504880386213075350927555974221966389550944031826229374847542272) * r3 + ((53601752032832795999267723 : ℝ) / 9007558392845461223374244733252170072) * r4 + ((242541864401958352937863 : ℝ) / 11495017483928606813497669191714096484289596980032) * r5 + ((57355700248841633314656084479869655086831696960555345 : ℝ) / 14709876955714553234276577427340917147776280699873996529538592388679502370304) * r6 + ((-341316702877761281878591 : ℝ) / 8348938759227930087689854257423188155974261755976697216) * r7 + ((149124820646988246618105819647661103225762412097443897 : ℝ) / 16968580849358024520699281763953127335777518682935921753628607902500171462597082112) * r8 + ((-4251914625894698174324042632915910575 : ℝ) / 9007558392845461223374244733252170072) * (value_032 h H) + ((46077754888497773053609785 : ℝ) / 99679506921330569052877508) * (value_033 h H) + ((53601752032832795999267723 : ℝ) / 99679506921330569052877508) * (value_053 h H) + ((4251914625894698174324042632915910575 : ℝ) / 9007558392845461223374244733252170072) * (value_052 h H)

/-- Coordinate 53.2, recovered from skew spokes on cycle 5. -/
theorem value_214 (h : Assignment) (H : Constraints h) :
    h 53 2 = ((18914006173254357364399801 : ℝ) / 24919876730332642263219377) * (h 1 0) + ((-13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (h 1 1) + ((-18914006173254357364399801 : ℝ) / 24919876730332642263219377) * (h 3 0) + ((13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (h 5 1) + h 9 2 := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((30891051111043265972623958996084316549881249872263567965191211 : ℝ) / 162574372955742642307728681333023261188548359187884234316738) * r0 + ((-4770601468201951822443083850263770846122178510358678 : ℝ) / 41378878763009084745595780299731102754543231258261) * r1 + ((-99122891366552195350053 : ℝ) / 976681241384095648721826803508002984476475993171084) * r2 + ((370152334381920069783744586966423226836670903201303 : ℝ) / 16966069095999344696031541616224361732845446077020530611823704924059052468064) * r3 + ((293058983170676055817548 : ℝ) / 48954121700247071866164373550283533) * r4 + ((99122891366552195350053 : ℝ) / 4669850852845996517983428109133851696742648773138) * r5 + ((-2385300734100975911221541925131885423061089255179339 : ℝ) / 527284192346385639831605257046227728642715944205042155011034102167739515112) * r6 + ((11013654596283577261117 : ℝ) / 230209708434593660506154069598065849888996188124357460) * r7 + ((-4811980346964960907188679630563501948876721741616939 : ℝ) / 467883663125680823181046372167825202273277169566247842471377056135115021946610720) * r8 + ((-23246661341031778972557707474468700 : ℝ) / 48954121700247071866164373550283533) * (value_032 h H) + (1 : ℝ) * (value_034 h H) + ((-13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (value_033 h H) + ((13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (value_053 h H) + ((23246661341031778972557707474468700 : ℝ) / 48954121700247071866164373550283533) * (value_052 h H)

/-- Coordinate 53.3, recovered from skew spokes on cycle 5. -/
theorem value_215 (h : Assignment) (H : Constraints h) :
    h 53 3 = ((-47102140364334606424138497 : ℝ) / 174439137112328495842535639) * (h 1 0) + ((5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (h 1 1) + h 1 3 + ((47102140364334606424138497 : ℝ) / 174439137112328495842535639) * (h 3 0) + ((-5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (h 5 1) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 38 3
  change ((1 : ℤ) : ℝ) * (h 12 3 - h 8 3) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 60 3
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 3 - h 12 3) - ((-2527909764593526516805248 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-49962077320552278117408599750870413844297744523195099265572638 : ℝ) / 4362412340979094235257386282436124175226047638208226954165803) * r0 + ((676758634854623166893449583211556831803906541674788 : ℝ) / 96550717113687864406390154032705906427267539602609) * r1 + (1 : ℝ) * r2 + ((10455509136646019600757 : ℝ) / 1709192172422167385263196906139005222833832988049397) * r3 + ((-765564066577628016847793646166919492990844504157 : ℝ) / 582169037607820651334415643693973196715284914407567226876303600335359643512) * r4 + ((-2843898485167717331405904 : ℝ) / 7881613593739778570452464141595648813) * r5 + ((-20911018273292039201514 : ℝ) / 16344477984960987812941998381968480938599270705983) * r6 + ((765564066577628016847793646166919492990844504157 : ℝ) / 2783551543306711522489620512310402790723236507869754966121597824414914484) * r7 + ((1 : ℝ) / 25485668442894336741578384) * r8 + ((-387241079135037762991 : ℝ) / 134288996586846301961923207265538412435247776405875185) * r9 + ((9952332865509164219021317400169953408880978554041 : ℝ) / 16054831577841989030722179437131256940749706798841837731860977416401005655030760) * r10 + ((225589894081030163156874529699587600 : ℝ) / 7881613593739778570452464141595648813) * (value_032 h H) + (1 : ℝ) * (value_035 h H) + ((5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (value_033 h H) + ((-5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (value_053 h H) + ((-225589894081030163156874529699587600 : ℝ) / 7881613593739778570452464141595648813) * (value_052 h H)

/-- Coordinate 78.0, recovered from nonplanar cycle 6. -/
theorem value_312 (h : Assignment) (H : Constraints h) :
    h 78 0 = h 1 0 + ((-45182599067 : ℝ) / 120001635295) * (h 1 1) + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1 : ℝ) / 240003270590) * r0 + ((-233686076288 : ℝ) / 2048522323252184000055) * r1 + ((45182599067 : ℝ) / 84380825116268455517910) * r2 + ((10558544292461079623296 : ℝ) / 720223534788432716228232424908195) * r3 + ((45182599067 : ℝ) / 72176671146295109632170) * r4 + ((10558544292461079623296 : ℝ) / 616056279973785887513223853735965) * r5 + ((-45182599067 : ℝ) / 120001635295) * (value_037 h H) + ((-17765652119624952205357 : ℝ) / 2048522323252184000055) * (value_036 h H) + ((45182599067 : ℝ) / 120001635295) * (value_053 h H) + ((19814174442877136205412 : ℝ) / 2048522323252184000055) * (value_052 h H) + ((21117088584922159246592 : ℝ) / 2048522323252184000055) * (value_054 h H)

/-- Coordinate 78.1, recovered from nonplanar cycle 6. -/
theorem value_313 (h : Assignment) (H : Constraints h) :
    h 78 1 = ((74819036228 : ℝ) / 120001635295) * (h 1 1) + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((37409518114 : ℝ) / 5421985774918341269765) * r0 + ((-233686076288 : ℝ) / 2048522323252184000055) * r1 + ((45182599067 : ℝ) / 84380825116268455517910) * r2 + ((10558544292461079623296 : ℝ) / 720223534788432716228232424908195) * r3 + ((45182599067 : ℝ) / 72176671146295109632170) * r4 + ((10558544292461079623296 : ℝ) / 616056279973785887513223853735965) * r5 + ((74819036228 : ℝ) / 120001635295) * (value_037 h H) + ((-19814174442877136205412 : ℝ) / 2048522323252184000055) * (value_036 h H) + ((45182599067 : ℝ) / 120001635295) * (value_053 h H) + ((19814174442877136205412 : ℝ) / 2048522323252184000055) * (value_052 h H) + ((21117088584922159246592 : ℝ) / 2048522323252184000055) * (value_054 h H)

/-- Coordinate 78.2, recovered from nonplanar cycle 6. -/
theorem value_314 (h : Assignment) (H : Constraints h) :
    h 78 2 = ((15864834505 : ℝ) / 48000654118) * (h 1 1) + ((-15864834505 : ℝ) / 48000654118) * (h 5 1) + h 9 2 := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((15864834505 : ℝ) / 4337588619934673015812) * r0 + ((91121260753 : ℝ) / 819408929300873600022) * r1 + ((-15864834505 : ℝ) / 33752330046507382207164) * r2 + ((-1853695463215962358720 : ℝ) / 144044706957686543245646484981639) * r3 + ((-15864834505 : ℝ) / 28870668458518043852868) * r4 + ((-1853695463215962358720 : ℝ) / 123211255994757177502644770747193) * r5 + ((15864834505 : ℝ) / 48000654118) * (value_037 h H) + ((3478646701170374063590 : ℝ) / 409704464650436800011) * (value_036 h H) + ((-15864834505 : ℝ) / 48000654118) * (value_053 h H) + ((-3478646701170374063590 : ℝ) / 409704464650436800011) * (value_052 h H) + ((-3707390926431924717440 : ℝ) / 409704464650436800011) * (value_054 h H)

/-- Coordinate 78.3, recovered from nonplanar cycle 6. -/
theorem value_315 (h : Assignment) (H : Constraints h) :
    h 78 3 = ((29636437161 : ℝ) / 120001635295) * (h 1 1) + h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 45 3
  change ((90365198134 : ℤ) : ℝ) * (h 78 3 - h 9 3) - ((-59272874322 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((29636437161 : ℝ) / 10843971549836682539530) * r0 + ((2308540905103321379456 : ℝ) / 30852520937100933735532456982895) * r1 + ((1 : ℝ) / 90365198134) * r2 + ((-9878812387 : ℝ) / 28126941705422818505970) * r3 + ((-2308540905103321379456 : ℝ) / 240074511596144238742744141636065) * r4 + ((-9878812387 : ℝ) / 24058890382098369877390) * r5 + ((-2308540905103321379456 : ℝ) / 205352093324595295837741284578655) * r6 + ((29636437161 : ℝ) / 120001635295) * (value_037 h H) + ((4332210097834686324932 : ℝ) / 682840774417394666685) * (value_036 h H) + (1 : ℝ) * (value_039 h H) + ((-29636437161 : ℝ) / 120001635295) * (value_053 h H) + ((-4332210097834686324932 : ℝ) / 682840774417394666685) * (value_052 h H) + ((-4617081810206642758912 : ℝ) / 682840774417394666685) * (value_054 h H)

/-- Coordinate 79.0, recovered from nonplanar cycle 6. -/
theorem value_316 (h : Assignment) (H : Constraints h) :
    h 79 0 = h 1 0 + ((-117193993383 : ℝ) / 333176110636) * (h 1 1) + ((117193993383 : ℝ) / 333176110636) * (h 5 1) := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-117193993383 : ℝ) / 30107525251137644753224) * r0 + ((-664099295837 : ℝ) / 3791718885243243033096) * r1 + ((1 : ℝ) / 1999056663816) * r2 + ((768104184139 : ℝ) / 34125469967189187297864) * r3 + ((39064664461 : ℝ) / 66797819079882088002712) * r4 + ((30005732224480193184079 : ℝ) / 1140291323474994138761506125609048) * r5 + ((-117193993383 : ℝ) / 333176110636) * (value_037 h H) + ((-51345398005397848802287 : ℝ) / 3791718885243243033096) * (value_036 h H) + ((117193993383 : ℝ) / 333176110636) * (value_053 h H) + ((55137116890641091835383 : ℝ) / 3791718885243243033096) * (value_052 h H) + ((30005732224480193184079 : ℝ) / 1895859442621621516548) * (value_054 h H)

/-- Coordinate 79.1, recovered from nonplanar cycle 6. -/
theorem value_317 (h : Assignment) (H : Constraints h) :
    h 79 1 = ((120001635295 : ℝ) / 249882082977) * (h 1 1) + ((129880447682 : ℝ) / 249882082977) * (h 5 1) := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((120001635295 : ℝ) / 22580643938353233564918) * r0 + ((2040027800015 : ℝ) / 8531367491797296824466) * r1 + ((64940223841 : ℝ) / 87854037536810384823573) * r2 + ((-92173758173611801586005 : ℝ) / 2999475076144901132471265949525434) * r3 + ((-120001635295 : ℝ) / 150295092929734698006102) * r4 + ((-92173758173611801586005 : ℝ) / 2565655477818736812213388782620358) * r5 + ((120001635295 : ℝ) / 249882082977) * (value_037 h H) + ((157726472517681689587765 : ℝ) / 8531367491797296824466) * (value_036 h H) + ((129880447682 : ℝ) / 249882082977) * (value_053 h H) + ((-157726472517681689587765 : ℝ) / 8531367491797296824466) * (value_052 h H) + ((-92173758173611801586005 : ℝ) / 4265683745898648412233) * (value_054 h H)

/-- Coordinate 79.2, recovered from nonplanar cycle 6. -/
theorem value_318 (h : Assignment) (H : Constraints h) :
    h 79 2 = ((208238189271 : ℝ) / 666352221272) * (h 1 1) + ((-208238189271 : ℝ) / 666352221272) * (h 5 1) + h 9 2 := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((208238189271 : ℝ) / 60215050502275289506448) * r0 + ((1180016405869 : ℝ) / 7583437770486486066192) * r1 + ((-69412729757 : ℝ) / 156184955620996239686352) * r2 + ((-49524489273618129691127 : ℝ) / 2666200067684356562196680844022608) * r3 + ((-69412729757 : ℝ) / 133595638159764176005424) * r4 + ((-53316208158861372724223 : ℝ) / 2280582646949988277523012251218096) * r5 + ((208238189271 : ℝ) / 666352221272) * (value_037 h H) + ((91233965149564060559519 : ℝ) / 7583437770486486066192) * (value_036 h H) + ((-208238189271 : ℝ) / 666352221272) * (value_053 h H) + ((-91233965149564060559519 : ℝ) / 7583437770486486066192) * (value_052 h H) + ((-49524489273618129691127 : ℝ) / 3791718885243243033096) * (value_054 h H)

/-- Coordinate 79.3, recovered from nonplanar cycle 6. -/
theorem value_319 (h : Assignment) (H : Constraints h) :
    h 79 3 = ((19757624774 : ℝ) / 83294027659) * (h 1 1) + h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 5 1) := by
  have r0 := H 45 1
  change ((90365198134 : ℤ) : ℝ) * (h 78 1 - h 9 1) - ((90365198134 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 45 2
  change ((90365198134 : ℤ) : ℝ) * (h 78 2 - h 9 2) - ((-79324172525 : ℤ) : ℝ) * (h 78 0 - h 9 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 63 1
  change ((703163960298 : ℤ) : ℝ) * (h 79 1 - h 13 1) - ((-960013082360 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 63 2
  change ((703163960298 : ℤ) : ℝ) * (h 79 2 - h 13 2) - ((-624714567813 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 63 3
  change ((703163960298 : ℤ) : ℝ) * (h 79 3 - h 13 3) - ((-474182994576 : ℤ) : ℝ) * (h 79 0 - h 13 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 231 1
  change ((-601464063126 : ℤ) : ℝ) * (h 79 1 - h 78 1) - ((3478591536904 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 231 2
  change ((-601464063126 : ℤ) : ℝ) * (h 79 2 - h 78 2) - ((437298325395 : ℤ) : ℝ) * (h 79 0 - h 78 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((9878812387 : ℝ) / 3763440656392205594153) * r0 + ((167939810579 : ℝ) / 1421894581966216137411) * r1 + ((-9878812387 : ℝ) / 29284679178936794941191) * r2 + ((-7587957128778882129793 : ℝ) / 499912512690816855411877658254239) * r3 + ((1 : ℝ) / 703163960298) * r4 + ((-9878812387 : ℝ) / 25049182154955783001017) * r5 + ((-7587957128778882129793 : ℝ) / 427609246303122802035564797103393) * r6 + ((19757624774 : ℝ) / 83294027659) * (value_037 h H) + ((12984408309395855317729 : ℝ) / 1421894581966216137411) * (value_036 h H) + ((-19757624774 : ℝ) / 83294027659) * (value_053 h H) + ((-12984408309395855317729 : ℝ) / 1421894581966216137411) * (value_052 h H) + ((-15175914257557764259586 : ℝ) / 1421894581966216137411) * (value_054 h H) + (1 : ℝ) * (value_055 h H)

/-- Coordinate 14.0, recovered from skew spokes on cycle 7. -/
theorem value_056 (h : Assignment) (H : Constraints h) :
    h 14 0 = ((120001635295 : ℝ) / 249882082977) * (h 1 0) + ((129880447682 : ℝ) / 249882082977) * (h 3 0) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_040 h H)

/-- Coordinate 14.1, recovered from skew spokes on cycle 7. -/
theorem value_057 (h : Assignment) (H : Constraints h) :
    h 14 1 = ((208238189271 : ℝ) / 666352221272) * (h 1 0) + ((-208238189271 : ℝ) / 666352221272) * (h 3 0) + h 5 1 := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((437298325395 : ℝ) / 3478591536904) * r0 + ((1 : ℝ) / 3478591536904) * r1 + ((437298325395 : ℝ) / 3478591536904) * (value_040 h H) + (1 : ℝ) * (value_049 h H) + ((-437298325395 : ℝ) / 3478591536904) * (value_048 h H)

/-- Coordinate 14.2, recovered from skew spokes on cycle 7. -/
theorem value_058 (h : Assignment) (H : Constraints h) :
    h 14 2 = ((170851583881 : ℝ) / 499764165954) * (h 1 0) + ((-170851583881 : ℝ) / 499764165954) * (h 3 0) + h 9 2 := by
  have r0 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_042 h H)

/-- Coordinate 14.3, recovered from skew spokes on cycle 7. -/
theorem value_059 (h : Assignment) (H : Constraints h) :
    h 14 3 = ((-19757624774 : ℝ) / 83294027659) * (h 1 0) + h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0) := by
  have r0 := H 48 3
  change ((1 : ℤ) : ℝ) * (h 14 3 - h 10 3) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_043 h H)

/-- Coordinate 51.0, recovered from skew spokes on cycle 7. -/
theorem value_204 (h : Assignment) (H : Constraints h) :
    h 51 0 = ((9599590205553679886220594602 : ℝ) / 24441996955307478186442031817) * (h 1 0) + ((1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (h 1 1) + ((14842406749753798300221437215 : ℝ) / 24441996955307478186442031817) * (h 3 0) + ((-1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (h 5 1) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((25604571543574519013741822552638404903534822724843313370788232401 : ℝ) / 5842844663956316056926723939635518732222849820972013376299551514) * r0 + ((64242933190513867602281216569287171714679266512866472 : ℝ) / 47030428509690176576451127973043715476518159445220923) * r1 + ((-9 : ℝ) / 1254689177039117213570690966606) * r2 + ((9160303189334886005552033581 : ℝ) / 123125661838368882277149053033428447117524541427588376414) * r3 + ((-134127230493752643566328417 : ℝ) / 3542655156406913714352493421408437403107) * r4 + ((7889837087867802562725201 : ℝ) / 1048423833517568265887618382743565677511045506235302) * r5 + ((-8030366648814233450285152071160896464334908314108309 : ℝ) / 102884348371920256295108295218437839172815676913064238606414883052776919106038) * r6 + ((876648565318644729191689 : ℝ) / 125816642305484045500024452183918231933166618170215901474) * r7 + ((-8030366648814233450285152071160896464334908314108309 : ℝ) / 111120203105848334388720062617857545038347484683449605319592288787790167798253361954) * r8 + ((3484001543122126504311583684045736153392 : ℝ) / 3542655156406913714352493421408437403107) * (value_040 h H) + ((1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (value_041 h H) + ((-1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (value_049 h H) + ((58653613284787210040909737362701249715 : ℝ) / 3542655156406913714352493421408437403107) * (value_048 h H)

/-- Coordinate 51.1, recovered from skew spokes on cycle 7. -/
theorem value_205 (h : Assignment) (H : Constraints h) :
    h 51 1 = ((-66893936986311160142107637049 : ℝ) / 10037513416312937708565527732848) * (h 1 0) + ((602870056514230939827016065041 : ℝ) / 1254689177039117213570690966606) * (h 1 1) + ((66893936986311160142107637049 : ℝ) / 10037513416312937708565527732848) * (h 3 0) + ((651819120524886273743674901565 : ℝ) / 1254689177039117213570690966606) * (h 5 1) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-705107474298076532924358148258110586554811141193262906002663346689855 : ℝ) / 40790846213967027832091102063908768109225122216812616051072602303072) * r0 + ((-221142991430132451438945588146152216366716230734657387195 : ℝ) / 41041887279456294092383017677809482372508180475862792138) * r1 + ((-602870056514230939827016065041 : ℝ) / 23036755204265194394557134078138696414221463240280070912096) * r2 + ((-221142991430132451438945588146152216366716230734657387195 : ℝ) / 753550702181918526199435163768461002154851167390475930423816364194836966458570821408) * r3 + ((651819120524886273743674901565 : ℝ) / 4364551152693317696082271895175194880627824) * r4 + ((-651819120524886273743674901565 : ℝ) / 21958188769191949760750279408181239549791337082592165088) * r5 + ((221142991430132451438945588146152216366716230734657387195 : ℝ) / 718269930767165949281582711684987367878483845755739137790917770219119931252286624) * r6 + ((-24141448908329121249765737095 : ℝ) / 878367918815352616317504042179994483202747216985667280157152) * r7 + ((221142991430132451438945588146152216366716230734657387195 : ℝ) / 775767177949629171812450997156136141094383239736722844604513632123825758122206137588192) * r8 + ((285039409865974440930930591927665964743175 : ℝ) / 4364551152693317696082271895175194880627824) * (value_040 h H) + ((602870056514230939827016065041 : ℝ) / 1254689177039117213570690966606) * (value_041 h H) + ((651819120524886273743674901565 : ℝ) / 1254689177039117213570690966606) * (value_049 h H) + ((-285039409865974440930930591927665964743175 : ℝ) / 4364551152693317696082271895175194880627824) * (value_048 h H)

/-- Coordinate 51.2, recovered from skew spokes on cycle 7. -/
theorem value_206 (h : Assignment) (H : Constraints h) :
    h 51 2 = ((2231362585778583771038978354791 : ℝ) / 3764067531117351640712072899818) * (h 1 0) + ((-236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (h 1 1) + ((-2231362585778583771038978354791 : ℝ) / 3764067531117351640712072899818) * (h 3 0) + ((236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (h 5 1) + h 9 2 := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-5655310733999988566745810638378764098695888447526684984301901135449 : ℝ) / 449899039124636336383357743351934942381159436214845029975065466578) * r0 + ((-14189409459074935725951200296473293469865017818042378728 : ℝ) / 3621342995246143596386736853924366091691898277282011071) * r1 + ((1742637258998668047351122649 : ℝ) / 84693952956857332332930639993156972111108320736323790118) * r2 + ((-17810752454321079322337937150397659561556916095324389799 : ℝ) / 66489767839581046429361926214864206072486867710924346802101443899544438216932719536) * r3 + ((29624833402977356804969085033 : ℝ) / 272784447043332356005141993448449680039239) * r4 + ((-1742637258998668047351122649 : ℝ) / 80728635180852756473346615471254557168350503980118254) * r5 + ((1773676182384366965743900037059161683733127227255297341 : ℝ) / 7922094824637859734723338731819713616306807122305946372693945995063822771164926) * r6 + ((-193626362110963116372346961 : ℝ) / 9687881457522271503501882818161703858853829599106624413498) * r7 + ((1773676182384366965743900037059161683733127227255297341 : ℝ) / 8556255639150321747931444821575030967952756320625619609608606236659842920465508870458) * r8 + ((12954890037227857337916388499676258313035 : ℝ) / 272784447043332356005141993448449680039239) * (value_040 h H) + (1 : ℝ) * (value_042 h H) + ((-236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (value_041 h H) + ((236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (value_049 h H) + ((-12954890037227857337916388499676258313035 : ℝ) / 272784447043332356005141993448449680039239) * (value_048 h H)

/-- Coordinate 51.3, recovered from skew spokes on cycle 7. -/
theorem value_207 (h : Assignment) (H : Constraints h) :
    h 51 3 = ((-148866993062121542009973162791 : ℝ) / 627344588519558606785345483303) * (h 1 0) + ((88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (h 1 1) + h 1 3 + ((148866993062121542009973162791 : ℝ) / 627344588519558606785345483303) * (h 3 0) + ((-88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (h 5 1) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 51 3
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 3 - h 10 3) - ((-19650205671972399073020144 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((703345848082754778331899775630536533466157253731799840386117981 : ℝ) / 149966346374878778794452581117311647460386478738281676658355155526) * r0 + ((1764723938118188568964017838674059510805148142916232 : ℝ) / 1207114331748714532128912284641455363897299425760670357) * r1 + ((-650190628852027910504343 : ℝ) / 84693952956857332332930639993156972111108320736323790118) * r2 + ((12975911309692563007088366460838672873567265756737 : ℝ) / 162965117253875113797455701507020112922761930664030261769856480145942250531697842) * r3 + ((-1 : ℝ) / 18360527552033695208190734416) * r4 + ((-11053240690484474478573831 : ℝ) / 272784447043332356005141993448449680039239) * r5 + ((650190628852027910504343 : ℝ) / 80728635180852756473346615471254557168350503980118254) * r6 + ((-12975911309692563007088366460838672873567265756737 : ℝ) / 155335192639958034014183112388621835613858963182469536719489137158114171983626) * r7 + ((24081134401926959648309 : ℝ) / 3229293819174090501167294272720567952951276533035541471166) * r8 + ((-12975911309692563007088366460838672873567265756737 : ℝ) / 167769718414712191135910682775980999371622672953443521757031494836467508244421742558) * r9 + ((-4833563644136734200726952104169738245 : ℝ) / 272784447043332356005141993448449680039239) * (value_040 h H) + ((88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (value_041 h H) + (1 : ℝ) * (value_043 h H) + ((-88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (value_049 h H) + ((4833563644136734200726952104169738245 : ℝ) / 272784447043332356005141993448449680039239) * (value_048 h H)

/-- Coordinate 55.0, recovered from skew spokes on cycle 7. -/
theorem value_220 (h : Assignment) (H : Constraints h) :
    h 55 0 = ((65438079437624354349170147 : ℝ) / 165971804271352017315051390) * (h 1 0) + ((3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (h 1 1) + ((100533724833727662965881243 : ℝ) / 165971804271352017315051390) * (h 3 0) + ((-3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (h 5 1) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((221819512400579453874596029849809268612782076453620380107462183 : ℝ) / 25248019959218974201878190436621618842090783656000752638836060) * r0 + ((925448735896009583047709361687325207722837788649059 : ℝ) / 319357092208176997509502470502981467530742371764410) * r1 + ((-4785734457754620752961 : ℝ) / 678995072456529067001447669388527221628731580855980) * r2 + ((84131703263273598458882669244302291611167071695369 : ℝ) / 533051335493236280561363416653794680955300814284073969554875839115656330084960) * r3 + ((-81357485781828552800337 : ℝ) / 2186924673117470779431687251181217790) * r4 + ((9 : ℝ) / 1217126564656581460310376860) * r5 + ((-158217163123739197333855455761 : ℝ) / 955516419886865576548431391744920550851981176319114720) * r6 + ((5849231003922314253619 : ℝ) / 854349796744822149912024564023490066614708190389135580) * r7 + ((-925448735896009583047709361687325207722837788649059 : ℝ) / 6036436592050866889287451208914162205655710306263393226002994484750240746820937440) * r8 + ((430269436165345926194220708657911935 : ℝ) / 437384934623494155886337450236243558) * (value_040 h H) + ((3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (value_041 h H) + ((-3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (value_049 h H) + ((7115498458148229692116741578331623 : ℝ) / 437384934623494155886337450236243558) * (value_048 h H)

/-- Coordinate 55.1, recovered from skew spokes on cycle 7. -/
theorem value_221 (h : Assignment) (H : Constraints h) :
    h 55 1 = ((86306860777438791550635177 : ℝ) / 9737012517252651682483014880) * (h 1 0) + ((556368780748240554606645741 : ℝ) / 1217126564656581460310376860) * (h 1 1) + ((-86306860777438791550635177 : ℝ) / 9737012517252651682483014880) * (h 3 0) + ((660757783908340905703731119 : ℝ) / 1217126564656581460310376860) * (h 5 1) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((7652337534024278104803214822807396616754397473629303421376160739421 : ℝ) / 276987610965938292977405001216696906443630623895432256949790802240) * r0 + ((3260262597800009783067154383141092993032411071889798663 : ℝ) / 318505473295621858849477130581640183617327058773038240) * r1 + ((-556368780748240554606645741 : ℝ) / 22347085824689284653151645694915207918244813789132013760) * r2 + ((3260262597800009783067154383141092993032411071889798663 : ℝ) / 5847928517917797488611864256303230179866953466572480828663357872324827045252067840) * r3 + ((660757783908340905703731119 : ℝ) / 4233886167155423428979746518286837641440) * r4 + ((-38868104935784759159043007 : ℝ) / 1252988781032865096824307053987653083885225558715840) * r5 + ((-3260262597800009783067154383141092993032411071889798663 : ℝ) / 5574132171244548679678623505441095554662764977307963462668741114497663808555520) * r6 + ((20606251138823724244690583 : ℝ) / 852071530620169290845592498519427426437068968548097885120) * r7 + ((-3260262597800009783067154383141092993032411071889798663 : ℝ) / 6020339427805397910916018005690391106440628412113357510733653166124240104829414940160) * r8 + ((57789654478965751247403844468409893401 : ℝ) / 846777233431084685795949303657367528288) * (value_040 h H) + ((556368780748240554606645741 : ℝ) / 1217126564656581460310376860) * (value_041 h H) + ((660757783908340905703731119 : ℝ) / 1217126564656581460310376860) * (value_049 h H) + ((-57789654478965751247403844468409893401 : ℝ) / 846777233431084685795949303657367528288) * (value_048 h H)

/-- Coordinate 55.2, recovered from skew spokes on cycle 7. -/
theorem value_222 (h : Assignment) (H : Constraints h) :
    h 55 2 = ((1076063047865449966450768109 : ℝ) / 1825689846984872190465565290) * (h 1 0) + ((-113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (h 1 1) + ((-1076063047865449966450768109 : ℝ) / 1825689846984872190465565290) * (h 3 0) + ((113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (h 5 1) + h 9 2 := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-17123186101006999731995727708672654219549291047447171166335493556 : ℝ) / 763752603766373969606815260707803969973246205594022767324790815) * r0 + ((-12900827282450133897095517491190666752174618632505081 : ℝ) / 1756464007144973486302263587766398071419083044704255) * r1 + ((416881515892137435592092 : ℝ) / 20539600941810004276793791999002948454269130320893395) * r2 + ((-1832161411199388422924722634869633102949212709651167 : ℝ) / 4031200724667599371745310838444322274724462408023309394758748533312150996267510) * r3 + ((14173971540332672810131128 : ℝ) / 132308942723606982155617078696463676295) * r4 + ((-416881515892137435592092 : ℝ) / 19577949703638517137879797718557079435706649354935) * r5 + ((12900827282450133897095517491190666752174618632505081 : ℝ) / 30739699473775084630580644331476629897037306860154210272070263499067998944240) * r6 + ((-46320168432459715065788 : ℝ) / 2349461941048260912258067551064597683190447523570122845) * r7 + ((1832161411199388422924722634869633102949212709651167 : ℝ) / 4150050157034970986385122706128486516388300835556082842877058708265790513439394490) * r8 + ((1239650803756773304214958212952479112 : ℝ) / 26461788544721396431123415739292735259) * (value_040 h H) + (1 : ℝ) * (value_042 h H) + ((-113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (value_041 h H) + ((113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (value_049 h H) + ((-1239650803756773304214958212952479112 : ℝ) / 26461788544721396431123415739292735259) * (value_048 h H)

/-- Coordinate 55.3, recovered from skew spokes on cycle 7. -/
theorem value_223 (h : Assignment) (H : Constraints h) :
    h 55 3 = ((-14439774503848767519240428 : ℝ) / 60856328232829073015518843) * (h 1 0) + ((6696008247861808220880 : ℝ) / 60856328232829073015518843) * (h 1 1) + h 1 3 + ((14439774503848767519240428 : ℝ) / 60856328232829073015518843) * (h 3 0) + ((-6696008247861808220880 : ℝ) / 60856328232829073015518843) * (h 5 1) := by
  have r0 := H 48 0
  change ((1 : ℤ) : ℝ) * (h 14 0 - h 10 0) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 48 2
  change ((1 : ℤ) : ℝ) * (h 14 2 - h 10 2) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 48 3
  change ((1 : ℤ) : ℝ) * (h 14 3 - h 10 3) - ((0 : ℤ) : ℝ) * (h 14 1 - h 10 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 51 1
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 1 - h 10 1) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 51 2
  change ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 51 2 - h 10 2) - ((52666370494181967653278373392 : ℤ) : ℝ) * (h 51 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 57 1
  change ((3478591536904 : ℤ) : ℝ) * (h 14 1 - h 12 1) - ((437298325395 : ℤ) : ℝ) * (h 14 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 68 1
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 1 - h 14 1) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 68 2
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 2 - h 14 2) - ((50396343254516169991577344 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 68 3
  change ((-17500899163735564246828048 : ℤ) : ℝ) * (h 55 3 - h 14 3) - ((-14880018328581796046400 : ℤ) : ℝ) * (h 55 0 - h 14 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 179 1
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 1 - h 51 1) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 179 2
  change ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 55 2 - h 51 2) - ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 55 0 - h 51 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((337052659740173259007538971155695620550438027996941231569365 : ℝ) / 50916840251091597973787684047186931331549747039601517821652721) * r0 + ((288514005781550871102670742110296533411620086190 : ℝ) / 117097600476331565753484239184426538094605536313617) * r1 + (1 : ℝ) * r2 + ((-24617677381844883165 : ℝ) / 4107920188362000855358758399800589690853826064178679) * r3 + ((8485706052398555032431492415008721570930002535 : ℝ) / 63234521171256460733259777857950153329011175027816617956999976993131780333608) * r4 + ((-837001030982726027610 : ℝ) / 26461788544721396431123415739292735259) * r5 + ((24617677381844883165 : ℝ) / 3915589940727703427575959543711415887141329870987) * r6 + ((-8485706052398555032431492415008721570930002535 : ℝ) / 60273920536813891432511067316620842935367268353243549553078948037388233224) * r7 + ((-1 : ℝ) / 17500899163735564246828048) * r8 + ((911765828957217895 : ℝ) / 156630796069884060817204503404306512212696501571341523) * r9 + ((-8485706052398555032431492415008721570930002535 : ℝ) / 65098825992705427237413689507897827708051777812644436751012685619855537465715992) * r10 + ((-366019149202634603045933534155950 : ℝ) / 26461788544721396431123415739292735259) * (value_040 h H) + (1 : ℝ) * (value_043 h H) + ((6696008247861808220880 : ℝ) / 60856328232829073015518843) * (value_041 h H) + ((-6696008247861808220880 : ℝ) / 60856328232829073015518843) * (value_049 h H) + ((366019149202634603045933534155950 : ℝ) / 26461788544721396431123415739292735259) * (value_048 h H)

/-- Coordinate 82.0, recovered from nonplanar cycle 8. -/
theorem value_328 (h : Assignment) (H : Constraints h) :
    h 82 0 = ((45182599067 : ℝ) / 120001635295) * (h 1 1) + h 3 0 + ((-45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1 : ℝ) / 240003270590) * r0 + ((-392553116348 : ℝ) / 13616075067927077269985) * r1 + ((45182599067 : ℝ) / 82009877833843450719580) * r2 + ((8868285034226543623658 : ℝ) / 2326327991597935814984010711111785) * r3 + ((45182599067 : ℝ) / 100977456093243489106220) * r4 + ((8868285034226543623658 : ℝ) / 2864370595771375324373746556328565) * r5 + ((45182599067 : ℝ) / 120001635295) * (value_045 h H) + ((-26012273817827195140839 : ℝ) / 13616075067927077269985) * (value_044 h H) + ((35473140136906174494632 : ℝ) / 13616075067927077269985) * (value_046 h H) + ((-45182599067 : ℝ) / 120001635295) * (value_061 h H) + ((39628348885754272410824 : ℝ) / 13616075067927077269985) * (value_060 h H) + ((-35473140136906174494632 : ℝ) / 13616075067927077269985) * (value_062 h H)

/-- Coordinate 82.1, recovered from nonplanar cycle 8. -/
theorem value_329 (h : Assignment) (H : Constraints h) :
    h 82 1 = ((74819036228 : ℝ) / 120001635295) * (h 1 1) + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-37409518114 : ℝ) / 5421985774918341269765) * r0 + ((392553116348 : ℝ) / 13616075067927077269985) * r1 + ((-45182599067 : ℝ) / 82009877833843450719580) * r2 + ((-8868285034226543623658 : ℝ) / 2326327991597935814984010711111785) * r3 + ((-45182599067 : ℝ) / 100977456093243489106220) * r4 + ((-8868285034226543623658 : ℝ) / 2864370595771375324373746556328565) * r5 + ((74819036228 : ℝ) / 120001635295) * (value_045 h H) + ((39628348885754272410824 : ℝ) / 13616075067927077269985) * (value_044 h H) + ((-35473140136906174494632 : ℝ) / 13616075067927077269985) * (value_046 h H) + ((45182599067 : ℝ) / 120001635295) * (value_061 h H) + ((-39628348885754272410824 : ℝ) / 13616075067927077269985) * (value_060 h H) + ((35473140136906174494632 : ℝ) / 13616075067927077269985) * (value_062 h H)

/-- Coordinate 82.2, recovered from nonplanar cycle 8. -/
theorem value_330 (h : Assignment) (H : Constraints h) :
    h 82 2 = ((15864834505 : ℝ) / 48000654118) * (h 1 1) + ((-15864834505 : ℝ) / 48000654118) * (h 5 1) + h 9 2 := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-15864834505 : ℝ) / 4337588619934673015812) * r0 + ((-198107356011 : ℝ) / 5446430027170830907994) * r1 + ((15864834505 : ℝ) / 32803951133537380287832) * r2 + ((1556947556320757496935 : ℝ) / 465265598319587162996802142222357) * r3 + ((15864834505 : ℝ) / 40390982437297395642488) * r4 + ((1556947556320757496935 : ℝ) / 572874119154275064874749311265713) * r5 + ((15864834505 : ℝ) / 48000654118) * (value_045 h H) + ((-6957293402340748127180 : ℝ) / 2723215013585415453997) * (value_044 h H) + ((8951005238868445441737 : ℝ) / 2723215013585415453997) * (value_046 h H) + ((-15864834505 : ℝ) / 48000654118) * (value_061 h H) + ((6957293402340748127180 : ℝ) / 2723215013585415453997) * (value_060 h H) + ((-6227790225283029987740 : ℝ) / 2723215013585415453997) * (value_062 h H)

/-- Coordinate 82.3, recovered from nonplanar cycle 8. -/
theorem value_331 (h : Assignment) (H : Constraints h) :
    h 82 3 = ((29636437161 : ℝ) / 120001635295) * (h 1 1) + h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 54 3
  change ((-90365198134 : ℤ) : ℝ) * (h 82 3 - h 11 3) - ((-59272874322 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-29636437161 : ℝ) / 10843971549836682539530) * r0 + ((-11633875765002223808028 : ℝ) / 615209660660323923082861168103995) * r1 + ((-1 : ℝ) / 90365198134) * r2 + ((29636437161 : ℝ) / 82009877833843450719580) * r3 + ((5816937882501111904014 : ℝ) / 2326327991597935814984010711111785) * r4 + ((29636437161 : ℝ) / 100977456093243489106220) * r5 + ((5816937882501111904014 : ℝ) / 2864370595771375324373746556328565) * r6 + ((29636437161 : ℝ) / 120001635295) * (value_045 h H) + ((-25993260587008117949592 : ℝ) / 13616075067927077269985) * (value_044 h H) + ((23267751530004447616056 : ℝ) / 13616075067927077269985) * (value_046 h H) + (1 : ℝ) * (value_047 h H) + ((-29636437161 : ℝ) / 120001635295) * (value_061 h H) + ((25993260587008117949592 : ℝ) / 13616075067927077269985) * (value_060 h H) + ((-23267751530004447616056 : ℝ) / 13616075067927077269985) * (value_062 h H)

/-- Coordinate 83.0, recovered from nonplanar cycle 8. -/
theorem value_332 (h : Assignment) (H : Constraints h) :
    h 83 0 = ((170851583881 : ℝ) / 499764165954) * (h 1 1) + h 3 0 + ((-170851583881 : ℝ) / 499764165954) * (h 5 1) := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-170851583881 : ℝ) / 45161287876706467129836) * r0 + ((-512554751643 : ℝ) / 9451018984257070143797) * r1 + ((1 : ℝ) / 1999056663816) * r2 + ((135547797201 : ℝ) / 18902037968514140287594) * r3 + ((170851583881 : ℝ) / 420535220212112923505064) * r4 + ((23158555843371428517081 : ℝ) / 3976361872791047696511425153179826) * r5 + ((170851583881 : ℝ) / 499764165954) * (value_045 h H) + ((-224562086869592391951427 : ℝ) / 56706113905542420862782) * (value_044 h H) + ((46317111686742857034162 : ℝ) / 9451018984257070143797) * (value_046 h H) + ((-170851583881 : ℝ) / 499764165954) * (value_061 h H) + ((281268200775134812814209 : ℝ) / 56706113905542420862782) * (value_060 h H) + ((-46317111686742857034162 : ℝ) / 9451018984257070143797) * (value_062 h H)

/-- Coordinate 83.1, recovered from nonplanar cycle 8. -/
theorem value_333 (h : Assignment) (H : Constraints h) :
    h 83 1 = ((120001635295 : ℝ) / 249882082977) * (h 1 1) + ((129880447682 : ℝ) / 249882082977) * (h 5 1) := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-120001635295 : ℝ) / 22580643938353233564918) * r0 + ((-720009811770 : ℝ) / 9451018984257070143797) * r1 + ((-64940223841 : ℝ) / 85385499320207835387474) * r2 + ((16265957324755023809295 : ℝ) / 1614721562749720238140233877336157) * r3 + ((120001635295 : ℝ) / 210267610106056461752532) * r4 + ((16265957324755023809295 : ℝ) / 1988180936395523848255712576589913) * r5 + ((120001635295 : ℝ) / 249882082977) * (value_045 h H) + ((-157726472517681689587765 : ℝ) / 28353056952771210431391) * (value_044 h H) + ((65063829299020095237180 : ℝ) / 9451018984257070143797) * (value_046 h H) + ((129880447682 : ℝ) / 249882082977) * (value_061 h H) + ((157726472517681689587765 : ℝ) / 28353056952771210431391) * (value_060 h H) + ((-65063829299020095237180 : ℝ) / 9451018984257070143797) * (value_062 h H)

/-- Coordinate 83.2, recovered from nonplanar cycle 8. -/
theorem value_334 (h : Assignment) (H : Constraints h) :
    h 83 2 = ((208238189271 : ℝ) / 666352221272) * (h 1 1) + ((-208238189271 : ℝ) / 666352221272) * (h 5 1) + h 9 2 := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-208238189271 : ℝ) / 60215050502275289506448) * r0 + ((-1874143703439 : ℝ) / 37804075937028280575188) * r1 + ((208238189271 : ℝ) / 455389329707775122066528) * r2 + ((65776645577912745803819 : ℝ) / 12917772501997761905121871018689256) * r3 + ((208238189271 : ℝ) / 560713626949483898006752) * r4 + ((84678683546426886091413 : ℝ) / 15905447491164190786045700612719304) * r5 + ((208238189271 : ℝ) / 666352221272) * (value_045 h H) + ((-273701895448692181678557 : ℝ) / 75608151874056561150376) * (value_044 h H) + ((84678683546426886091413 : ℝ) / 18902037968514140287594) * (value_046 h H) + ((-208238189271 : ℝ) / 666352221272) * (value_061 h H) + ((273701895448692181678557 : ℝ) / 75608151874056561150376) * (value_060 h H) + ((-65776645577912745803819 : ℝ) / 18902037968514140287594) * (value_062 h H)

/-- Coordinate 83.3, recovered from nonplanar cycle 8. -/
theorem value_335 (h : Assignment) (H : Constraints h) :
    h 83 3 = ((19757624774 : ℝ) / 83294027659) * (h 1 1) + h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 5 1) := by
  have r0 := H 54 1
  change ((-90365198134 : ℤ) : ℝ) * (h 82 1 - h 11 1) - ((90365198134 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 54 2
  change ((-90365198134 : ℤ) : ℝ) * (h 82 2 - h 11 2) - ((-79324172525 : ℤ) : ℝ) * (h 82 0 - h 11 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 70 1
  change ((-683406335524 : ℤ) : ℝ) * (h 83 1 - h 15 1) - ((-960013082360 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 70 2
  change ((-683406335524 : ℤ) : ℝ) * (h 83 2 - h 15 2) - ((-624714567813 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 70 3
  change ((-683406335524 : ℤ) : ℝ) * (h 83 3 - h 15 3) - ((-474182994576 : ℤ) : ℝ) * (h 83 0 - h 15 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 245 1
  change ((841467333716 : ℤ) : ℝ) * (h 83 1 - h 82 1) - ((3478591536904 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 245 2
  change ((841467333716 : ℤ) : ℝ) * (h 83 2 - h 82 2) - ((437298325395 : ℤ) : ℝ) * (h 83 0 - h 82 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-9878812387 : ℝ) / 3763440656392205594153) * r0 + ((-355637245932 : ℝ) / 9451018984257070143797) * r1 + ((9878812387 : ℝ) / 28461833106735945129158) * r2 + ((8034307548118816372722 : ℝ) / 1614721562749720238140233877336157) * r3 + ((-1 : ℝ) / 683406335524) * r4 + ((9878812387 : ℝ) / 35044601684342743625422) * r5 + ((8034307548118816372722 : ℝ) / 1988180936395523848255712576589913) * r6 + ((19757624774 : ℝ) / 83294027659) * (value_045 h H) + ((-25968816618791710635458 : ℝ) / 9451018984257070143797) * (value_044 h H) + ((32137230192475265490888 : ℝ) / 9451018984257070143797) * (value_046 h H) + ((-19757624774 : ℝ) / 83294027659) * (value_061 h H) + ((25968816618791710635458 : ℝ) / 9451018984257070143797) * (value_060 h H) + ((-32137230192475265490888 : ℝ) / 9451018984257070143797) * (value_062 h H) + (1 : ℝ) * (value_063 h H)

/-- Coordinate 16.0, recovered from skew spokes on cycle 10. -/
theorem value_064 (h : Assignment) (H : Constraints h) :
    h 16 0 = ((434743100796814 : ℝ) / 617857941263449) * (h 1 0) + ((-546216952893660 : ℝ) / 617857941263449) * (h 1 1) + ((447088691072218 : ℝ) / 617857941263449) * (h 1 2) + ((183114840466635 : ℝ) / 617857941263449) * (h 3 0) + ((546216952893660 : ℝ) / 617857941263449) * (h 5 1) + ((-447088691072218 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-270 : ℝ) / 617857941263449) * r0 + ((221 : ℝ) / 617857941263449) * r1 + ((270 : ℝ) / 617857941263449) * r2 + ((-221 : ℝ) / 617857941263449) * r3 + ((5 : ℝ) / 159407348845969842) * r4 + ((-221 : ℝ) / 159407348845969842) * r5 + ((-2690866844741470855 : ℝ) / 159407348845969842) * r6 + ((-546216952893660 : ℝ) / 617857941263449) * r7 + ((2493318039162658669 : ℝ) / 159407348845969842) * r8 + ((447088691072218 : ℝ) / 617857941263449) * r9 + ((-546216952893660 : ℝ) / 617857941263449) * (value_001 h H) + ((-147835103615668 : ℝ) / 617857941263449) * (value_000 h H) + ((447088691072218 : ℝ) / 617857941263449) * (value_002 h H) + ((546216952893660 : ℝ) / 617857941263449) * (value_049 h H) + ((765693044879117 : ℝ) / 617857941263449) * (value_048 h H) + ((-447088691072218 : ℝ) / 617857941263449) * (value_050 h H)

/-- Coordinate 16.1, recovered from skew spokes on cycle 10. -/
theorem value_065 (h : Assignment) (H : Constraints h) :
    h 16 1 = ((-306483803023377 : ℝ) / 617857941263449) * (h 1 0) + ((1432459532615089 : ℝ) / 617857941263449) * (h 1 1) + ((-666766487735972 : ℝ) / 617857941263449) * (h 1 2) + ((306483803023377 : ℝ) / 617857941263449) * (h 3 0) + ((-814601591351640 : ℝ) / 617857941263449) * (h 5 1) + ((666766487735972 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((1432459532615089 : ℝ) / 1249942525918781739173858642) * r0 + ((-333383243867986 : ℝ) / 624971262959390869586929321) * r1 + ((-407300795675820 : ℝ) / 624971262959390869586929321) * r2 + ((333383243867986 : ℝ) / 624971262959390869586929321) * r3 + ((-3771303663665 : ℝ) / 80621292921761422176713882409) * r4 + ((166691621933993 : ℝ) / 80621292921761422176713882409) * r5 + ((2029615198001637555044463996715 : ℝ) / 80621292921761422176713882409) * r6 + ((814601591351640 : ℝ) / 617857941263449) * r7 + ((-1880611891155233717452314512377 : ℝ) / 80621292921761422176713882409) * r8 + ((-666766487735972 : ℝ) / 617857941263449) * r9 + ((1432459532615089 : ℝ) / 617857941263449) * (value_001 h H) + ((1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_000 h H) + ((-666766487735972 : ℝ) / 617857941263449) * (value_002 h H) + ((-814601591351640 : ℝ) / 617857941263449) * (value_049 h H) + ((-1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_048 h H) + ((666766487735972 : ℝ) / 617857941263449) * (value_050 h H)

/-- Coordinate 16.2, recovered from skew spokes on cycle 10. -/
theorem value_066 (h : Assignment) (H : Constraints h) :
    h 16 2 = ((-306483803023377 : ℝ) / 617857941263449) * (h 1 0) + ((814601591351640 : ℝ) / 617857941263449) * (h 1 1) + ((-48908546472523 : ℝ) / 617857941263449) * (h 1 2) + ((306483803023377 : ℝ) / 617857941263449) * (h 3 0) + ((-814601591351640 : ℝ) / 617857941263449) * (h 5 1) + ((666766487735972 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((407300795675820 : ℝ) / 624971262959390869586929321) * r0 + ((-48908546472523 : ℝ) / 1249942525918781739173858642) * r1 + ((-407300795675820 : ℝ) / 624971262959390869586929321) * r2 + ((333383243867986 : ℝ) / 624971262959390869586929321) * r3 + ((-3771303663665 : ℝ) / 80621292921761422176713882409) * r4 + ((166691621933993 : ℝ) / 80621292921761422176713882409) * r5 + ((2029615198001637555044463996715 : ℝ) / 80621292921761422176713882409) * r6 + ((814601591351640 : ℝ) / 617857941263449) * r7 + ((-1880611891155233717452314512377 : ℝ) / 80621292921761422176713882409) * r8 + ((-666766487735972 : ℝ) / 617857941263449) * r9 + ((814601591351640 : ℝ) / 617857941263449) * (value_001 h H) + ((1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_000 h H) + ((-48908546472523 : ℝ) / 617857941263449) * (value_002 h H) + ((-814601591351640 : ℝ) / 617857941263449) * (value_049 h H) + ((-1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_048 h H) + ((666766487735972 : ℝ) / 617857941263449) * (value_050 h H)

/-- Coordinate 16.3, recovered from skew spokes on cycle 10. -/
theorem value_067 (h : Assignment) (H : Constraints h) :
    h 16 3 = ((-160570216538298 : ℝ) / 617857941263449) * (h 1 0) + ((88020218368170 : ℝ) / 617857941263449) * (h 1 1) + ((-72046178738391 : ℝ) / 617857941263449) * (h 1 2) + h 1 3 + ((160570216538298 : ℝ) / 617857941263449) * (h 3 0) + ((-88020218368170 : ℝ) / 617857941263449) * (h 5 1) + ((72046178738391 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 4 3
  change ((2023025751458 : ℤ) : ℝ) * (h 16 3 - h 0 3) - ((-326000808771 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((44010109184085 : ℝ) / 624971262959390869586929321) * r0 + ((-72046178738391 : ℝ) / 1249942525918781739173858642) * r1 + ((1 : ℝ) / 2023025751458) * r2 + ((-44010109184085 : ℝ) / 624971262959390869586929321) * r3 + ((72046178738391 : ℝ) / 1249942525918781739173858642) * r4 + ((-543334681285 : ℝ) / 107495057229015229568951843212) * r5 + ((24015392912797 : ℝ) / 107495057229015229568951843212) * r6 + ((292408255893596129044708289735 : ℝ) / 107495057229015229568951843212) * r7 + ((88020218368170 : ℝ) / 617857941263449) * r8 + ((-270941232430116859238871461933 : ℝ) / 107495057229015229568951843212) * r9 + ((-72046178738391 : ℝ) / 617857941263449) * r10 + ((88020218368170 : ℝ) / 617857941263449) * (value_001 h H) + ((249616551900921741928335207 : ℝ) / 1249942525918781739173858642) * (value_000 h H) + ((-72046178738391 : ℝ) / 617857941263449) * (value_002 h H) + (1 : ℝ) * (value_003 h H) + ((-88020218368170 : ℝ) / 617857941263449) * (value_049 h H) + ((-249616551900921741928335207 : ℝ) / 1249942525918781739173858642) * (value_048 h H) + ((72046178738391 : ℝ) / 617857941263449) * (value_050 h H)

/-- Coordinate 20.0, recovered from skew spokes on cycle 10. -/
theorem value_080 (h : Assignment) (H : Constraints h) :
    h 20 0 = ((1674719823442006 : ℝ) / 2542109602773571) * (h 1 0) + ((-1857137639838444 : ℝ) / 2542109602773571) * (h 1 1) + ((1624489678420774 : ℝ) / 2542109602773571) * (h 1 2) + ((867389779331565 : ℝ) / 2542109602773571) * (h 3 0) + ((1857137639838444 : ℝ) / 2542109602773571) * (h 5 1) + ((-1624489678420774 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-918 : ℝ) / 2542109602773571) * r0 + ((803 : ℝ) / 2542109602773571) * r1 + ((918 : ℝ) / 2542109602773571) * r2 + ((-803 : ℝ) / 2542109602773571) * r3 + ((17 : ℝ) / 655864277515581318) * r4 + ((-803 : ℝ) / 655864277515581318) * r5 + ((-9804811549636582225 : ℝ) / 655864277515581318) * r6 + ((-1857137639838444 : ℝ) / 2542109602773571) * r7 + ((9059431608360248467 : ℝ) / 655864277515581318) * r8 + ((1624489678420774 : ℝ) / 2542109602773571) * r9 + ((-1857137639838444 : ℝ) / 2542109602773571) * (value_001 h H) + ((-346959937057180 : ℝ) / 2542109602773571) * (value_000 h H) + ((1624489678420774 : ℝ) / 2542109602773571) * (value_002 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (value_049 h H) + ((2889069539830751 : ℝ) / 2542109602773571) * (value_048 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 20.1, recovered from skew spokes on cycle 10. -/
theorem value_081 (h : Assignment) (H : Constraints h) :
    h 20 1 = ((1830920974610259 : ℝ) / 5084219205547142) * (h 1 0) + ((-1557203509687230 : ℝ) / 2542109602773571) * (h 1 1) + ((1362128995946455 : ℝ) / 2542109602773571) * (h 1 2) + ((-1830920974610259 : ℝ) / 5084219205547142) * (h 3 0) + ((4099313112460801 : ℝ) / 2542109602773571) * (h 5 1) + ((-1362128995946455 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-778601754843615 : ℝ) / 2571376594719800676648558259) * r0 + ((1362128995946455 : ℝ) / 5142753189439601353297116518) * r1 + ((4099313112460801 : ℝ) / 5142753189439601353297116518) * r2 + ((-1362128995946455 : ℝ) / 5142753189439601353297116518) * r3 + ((28837102031245 : ℝ) / 1326830322875417149150656061644) * r4 + ((-1362128995946455 : ℝ) / 1326830322875417149150656061644) * r5 + ((-15519360350860818647921893372895 : ℝ) / 1326830322875417149150656061644) * r6 + ((-4099313112460801 : ℝ) / 2542109602773571) * r7 + ((15367514919727675199496388079495 : ℝ) / 1326830322875417149150656061644) * r8 + ((1362128995946455 : ℝ) / 2542109602773571) * r9 + ((-1557203509687230 : ℝ) / 2542109602773571) * (value_001 h H) + ((-294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((1362128995946455 : ℝ) / 2542109602773571) * (value_002 h H) + ((4099313112460801 : ℝ) / 2542109602773571) * (value_049 h H) + ((294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((-1362128995946455 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 20.2, recovered from skew spokes on cycle 10. -/
theorem value_082 (h : Assignment) (H : Constraints h) :
    h 20 2 = ((-1091004794628483 : ℝ) / 2542109602773571) * (h 1 0) + ((2769645410595576 : ℝ) / 2542109602773571) * (h 1 1) + ((119424129235175 : ℝ) / 2542109602773571) * (h 1 2) + ((1091004794628483 : ℝ) / 2542109602773571) * (h 3 0) + ((-2769645410595576 : ℝ) / 2542109602773571) * (h 5 1) + ((2422685473538396 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 74 2
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 2 - h 16 2) - ((42033442113744624 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((1384822705297788 : ℝ) / 2571376594719800676648558259) * r0 + ((119424129235175 : ℝ) / 5142753189439601353297116518) * r1 + ((-1384822705297788 : ℝ) / 2571376594719800676648558259) * r2 + ((1211342736769198 : ℝ) / 2571376594719800676648558259) * r3 + ((-12822432456461 : ℝ) / 331707580718854287287664015411) * r4 + ((-1 : ℝ) / 28184794769312856) * r5 + ((605671368384599 : ℝ) / 331707580718854287287664015411) * r6 + ((7395384343737869708890303470925 : ℝ) / 331707580718854287287664015411) * r7 + ((2769645410595576 : ℝ) / 2542109602773571) * r8 + ((-6833173523066301697349359970311 : ℝ) / 331707580718854287287664015411) * r9 + ((-2422685473538396 : ℝ) / 2542109602773571) * r10 + ((2769645410595576 : ℝ) / 2542109602773571) * (value_001 h H) + ((4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((119424129235175 : ℝ) / 2542109602773571) * (value_002 h H) + ((-2769645410595576 : ℝ) / 2542109602773571) * (value_049 h H) + ((-4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((2422685473538396 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 20.3, recovered from skew spokes on cycle 10. -/
theorem value_083 (h : Assignment) (H : Constraints h) :
    h 20 3 = ((-642280866153192 : ℝ) / 2542109602773571) * (h 1 0) + ((299268742451778 : ℝ) / 2542109602773571) * (h 1 1) + ((-261778649443113 : ℝ) / 2542109602773571) * (h 1 2) + h 1 3 + ((642280866153192 : ℝ) / 2542109602773571) * (h 3 0) + ((-299268742451778 : ℝ) / 2542109602773571) * (h 5 1) + ((261778649443113 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 4 3
  change ((2023025751458 : ℤ) : ℝ) * (h 16 3 - h 0 3) - ((-326000808771 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 74 3
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 3 - h 16 3) - ((4541843267797572 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((149634371225889 : ℝ) / 2571376594719800676648558259) * r0 + ((-261778649443113 : ℝ) / 5142753189439601353297116518) * r1 + ((1 : ℝ) / 2023025751458) * r2 + ((-149634371225889 : ℝ) / 2571376594719800676648558259) * r3 + ((261778649443113 : ℝ) / 5142753189439601353297116518) * r4 + ((-1847337916369 : ℝ) / 442276774291805716383552020548) * r5 + ((-1 : ℝ) / 28184794769312856) * r6 + ((87259549814371 : ℝ) / 442276774291805716383552020548) * r7 + ((1065458831676255872159414231825 : ℝ) / 442276774291805716383552020548) * r8 + ((299268742451778 : ℝ) / 2542109602773571) * r9 + ((-984460677110334108456170968019 : ℝ) / 442276774291805716383552020548) * r10 + ((-261778649443113 : ℝ) / 2542109602773571) * r11 + ((299268742451778 : ℝ) / 2542109602773571) * (value_001 h H) + ((941839006580485624456317021 : ℝ) / 5142753189439601353297116518) * (value_000 h H) + ((-261778649443113 : ℝ) / 2542109602773571) * (value_002 h H) + (1 : ℝ) * (value_003 h H) + ((-299268742451778 : ℝ) / 2542109602773571) * (value_049 h H) + ((-941839006580485624456317021 : ℝ) / 5142753189439601353297116518) * (value_048 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 24.0, recovered from skew spokes on cycle 10. -/
theorem value_096 (h : Assignment) (H : Constraints h) :
    h 24 0 = ((1674719823442006 : ℝ) / 2542109602773571) * (h 1 0) + ((-1857137639838444 : ℝ) / 2542109602773571) * (h 1 1) + ((1624489678420774 : ℝ) / 2542109602773571) * (h 1 2) + ((867389779331565 : ℝ) / 2542109602773571) * (h 3 0) + ((1857137639838444 : ℝ) / 2542109602773571) * (h 5 1) + ((-1624489678420774 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-918 : ℝ) / 2542109602773571) * r0 + ((803 : ℝ) / 2542109602773571) * r1 + ((918 : ℝ) / 2542109602773571) * r2 + ((-803 : ℝ) / 2542109602773571) * r3 + ((17 : ℝ) / 655864277515581318) * r4 + ((-803 : ℝ) / 655864277515581318) * r5 + ((-9148947272121000907 : ℝ) / 655864277515581318) * r6 + ((-1857137639838444 : ℝ) / 2542109602773571) * r7 + ((8403567330844667149 : ℝ) / 655864277515581318) * r8 + ((1624489678420774 : ℝ) / 2542109602773571) * r9 + ((-1857137639838444 : ℝ) / 2542109602773571) * (value_001 h H) + ((-346959937057180 : ℝ) / 2542109602773571) * (value_000 h H) + ((1624489678420774 : ℝ) / 2542109602773571) * (value_002 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (value_049 h H) + ((2889069539830751 : ℝ) / 2542109602773571) * (value_048 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 24.1, recovered from skew spokes on cycle 10. -/
theorem value_097 (h : Assignment) (H : Constraints h) :
    h 24 1 = ((-1091004794628483 : ℝ) / 2542109602773571) * (h 1 0) + ((5311755013369147 : ℝ) / 2542109602773571) * (h 1 1) + ((-2422685473538396 : ℝ) / 2542109602773571) * (h 1 2) + ((1091004794628483 : ℝ) / 2542109602773571) * (h 3 0) + ((-2769645410595576 : ℝ) / 2542109602773571) * (h 5 1) + ((2422685473538396 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 1
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 1 - h 16 1) - ((778397076180456 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((5311755013369147 : ℝ) / 5142753189439601353297116518) * r0 + ((-1211342736769198 : ℝ) / 2571376594719800676648558259) * r1 + ((-1384822705297788 : ℝ) / 2571376594719800676648558259) * r2 + ((1211342736769198 : ℝ) / 2571376594719800676648558259) * r3 + ((-12822432456461 : ℝ) / 331707580718854287287664015411) * r4 + ((-1 : ℝ) / 521940643876164) * r5 + ((605671368384599 : ℝ) / 331707580718854287287664015411) * r6 + ((6900691673205567687151177588831 : ℝ) / 331707580718854287287664015411) * r7 + ((2769645410595576 : ℝ) / 2542109602773571) * r8 + ((-6338480852533999675610234088217 : ℝ) / 331707580718854287287664015411) * r9 + ((-2422685473538396 : ℝ) / 2542109602773571) * r10 + ((5311755013369147 : ℝ) / 2542109602773571) * (value_001 h H) + ((4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((-2422685473538396 : ℝ) / 2542109602773571) * (value_002 h H) + ((-2769645410595576 : ℝ) / 2542109602773571) * (value_049 h H) + ((-4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((2422685473538396 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 24.2, recovered from skew spokes on cycle 10. -/
theorem value_098 (h : Assignment) (H : Constraints h) :
    h 24 2 = ((1202812302276942 : ℝ) / 2542109602773571) * (h 1 0) + ((-5083036935812586 : ℝ) / 2542109602773571) * (h 1 1) + ((4446273049517981 : ℝ) / 2542109602773571) * (h 1 2) + ((-1202812302276942 : ℝ) / 2542109602773571) * (h 3 0) + ((5083036935812586 : ℝ) / 2542109602773571) * (h 5 1) + ((-1904163446744410 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-2541518467906293 : ℝ) / 2571376594719800676648558259) * r0 + ((4446273049517981 : ℝ) / 5142753189439601353297116518) * r1 + ((2541518467906293 : ℝ) / 2571376594719800676648558259) * r2 + ((-952081723372205 : ℝ) / 2571376594719800676648558259) * r3 + ((94130313626159 : ℝ) / 1326830322875417149150656061644) * r4 + ((-4446273049517981 : ℝ) / 1326830322875417149150656061644) * r5 + ((-50658428004349509659600452819189 : ℝ) / 1326830322875417149150656061644) * r6 + ((-5083036935812586 : ℝ) / 2542109602773571) * r7 + ((50162772857040484789160293579309 : ℝ) / 1326830322875417149150656061644) * r8 + ((1904163446744410 : ℝ) / 2542109602773571) * r9 + ((-5083036935812586 : ℝ) / 2542109602773571) * (value_001 h H) + ((-960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((4446273049517981 : ℝ) / 2542109602773571) * (value_002 h H) + ((5083036935812586 : ℝ) / 2542109602773571) * (value_049 h H) + ((960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((-1904163446744410 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 24.3, recovered from skew spokes on cycle 10. -/
theorem value_099 (h : Assignment) (H : Constraints h) :
    h 24 3 = ((-642280866153192 : ℝ) / 2542109602773571) * (h 1 0) + ((299268742451778 : ℝ) / 2542109602773571) * (h 1 1) + ((-261778649443113 : ℝ) / 2542109602773571) * (h 1 2) + h 1 3 + ((642280866153192 : ℝ) / 2542109602773571) * (h 3 0) + ((-299268742451778 : ℝ) / 2542109602773571) * (h 5 1) + ((261778649443113 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 4 3
  change ((2023025751458 : ℤ) : ℝ) * (h 16 3 - h 0 3) - ((-326000808771 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 75 3
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 3 - h 16 3) - ((84108208662918 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((149634371225889 : ℝ) / 2571376594719800676648558259) * r0 + ((-261778649443113 : ℝ) / 5142753189439601353297116518) * r1 + ((1 : ℝ) / 2023025751458) * r2 + ((-149634371225889 : ℝ) / 2571376594719800676648558259) * r3 + ((261778649443113 : ℝ) / 5142753189439601353297116518) * r4 + ((-1847337916369 : ℝ) / 442276774291805716383552020548) * r5 + ((87259549814371 : ℝ) / 442276774291805716383552020548) * r6 + ((-1 : ℝ) / 521940643876164) * r7 + ((994188070038226838752008185099 : ℝ) / 442276774291805716383552020548) * r8 + ((299268742451778 : ℝ) / 2542109602773571) * r9 + ((-913189915472305075048764921293 : ℝ) / 442276774291805716383552020548) * r10 + ((-261778649443113 : ℝ) / 2542109602773571) * r11 + ((299268742451778 : ℝ) / 2542109602773571) * (value_001 h H) + ((941839006580485624456317021 : ℝ) / 5142753189439601353297116518) * (value_000 h H) + ((-261778649443113 : ℝ) / 2542109602773571) * (value_002 h H) + (1 : ℝ) * (value_003 h H) + ((-299268742451778 : ℝ) / 2542109602773571) * (value_049 h H) + ((-941839006580485624456317021 : ℝ) / 5142753189439601353297116518) * (value_048 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 28.0, recovered from skew spokes on cycle 10. -/
theorem value_112 (h : Assignment) (H : Constraints h) :
    h 28 0 = ((1674719823442006 : ℝ) / 2542109602773571) * (h 1 0) + ((-1857137639838444 : ℝ) / 2542109602773571) * (h 1 1) + ((1624489678420774 : ℝ) / 2542109602773571) * (h 1 2) + ((867389779331565 : ℝ) / 2542109602773571) * (h 3 0) + ((1857137639838444 : ℝ) / 2542109602773571) * (h 5 1) + ((-1624489678420774 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-918 : ℝ) / 2542109602773571) * r0 + ((803 : ℝ) / 2542109602773571) * r1 + ((918 : ℝ) / 2542109602773571) * r2 + ((-803 : ℝ) / 2542109602773571) * r3 + ((17 : ℝ) / 655864277515581318) * r4 + ((-803 : ℝ) / 655864277515581318) * r5 + ((-9148947272121000907 : ℝ) / 655864277515581318) * r6 + ((-1857137639838444 : ℝ) / 2542109602773571) * r7 + ((9059431608360248467 : ℝ) / 655864277515581318) * r8 + ((1624489678420774 : ℝ) / 2542109602773571) * r9 + ((-1857137639838444 : ℝ) / 2542109602773571) * (value_001 h H) + ((-346959937057180 : ℝ) / 2542109602773571) * (value_000 h H) + ((1624489678420774 : ℝ) / 2542109602773571) * (value_002 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (value_049 h H) + ((2889069539830751 : ℝ) / 2542109602773571) * (value_048 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 28.1, recovered from skew spokes on cycle 10. -/
theorem value_113 (h : Assignment) (H : Constraints h) :
    h 28 1 = ((1830920974610259 : ℝ) / 5084219205547142) * (h 1 0) + ((-1557203509687230 : ℝ) / 2542109602773571) * (h 1 1) + ((1362128995946455 : ℝ) / 2542109602773571) * (h 1 2) + ((-1830920974610259 : ℝ) / 5084219205547142) * (h 3 0) + ((4099313112460801 : ℝ) / 2542109602773571) * (h 5 1) + ((-1362128995946455 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-778601754843615 : ℝ) / 2571376594719800676648558259) * r0 + ((1362128995946455 : ℝ) / 5142753189439601353297116518) * r1 + ((4099313112460801 : ℝ) / 5142753189439601353297116518) * r2 + ((-1362128995946455 : ℝ) / 5142753189439601353297116518) * r3 + ((28837102031245 : ℝ) / 1326830322875417149150656061644) * r4 + ((-1362128995946455 : ℝ) / 1326830322875417149150656061644) * r5 + ((-15519360350860818647921893372895 : ℝ) / 1326830322875417149150656061644) * r6 + ((-1557203509687230 : ℝ) / 2542109602773571) * r7 + ((15367514919727675199496388079495 : ℝ) / 1326830322875417149150656061644) * r8 + ((1362128995946455 : ℝ) / 2542109602773571) * r9 + ((-1557203509687230 : ℝ) / 2542109602773571) * (value_001 h H) + ((-294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((1362128995946455 : ℝ) / 2542109602773571) * (value_002 h H) + ((4099313112460801 : ℝ) / 2542109602773571) * (value_049 h H) + ((294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((-1362128995946455 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 28.2, recovered from skew spokes on cycle 10. -/
theorem value_114 (h : Assignment) (H : Constraints h) :
    h 28 2 = ((1202812302276942 : ℝ) / 2542109602773571) * (h 1 0) + ((-5083036935812586 : ℝ) / 2542109602773571) * (h 1 1) + ((4446273049517981 : ℝ) / 2542109602773571) * (h 1 2) + ((-1202812302276942 : ℝ) / 2542109602773571) * (h 3 0) + ((5083036935812586 : ℝ) / 2542109602773571) * (h 5 1) + ((-1904163446744410 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-2541518467906293 : ℝ) / 2571376594719800676648558259) * r0 + ((4446273049517981 : ℝ) / 5142753189439601353297116518) * r1 + ((2541518467906293 : ℝ) / 2571376594719800676648558259) * r2 + ((-952081723372205 : ℝ) / 2571376594719800676648558259) * r3 + ((94130313626159 : ℝ) / 1326830322875417149150656061644) * r4 + ((-4446273049517981 : ℝ) / 1326830322875417149150656061644) * r5 + ((-50658428004349509659600452819189 : ℝ) / 1326830322875417149150656061644) * r6 + ((-5083036935812586 : ℝ) / 2542109602773571) * r7 + ((50162772857040484789160293579309 : ℝ) / 1326830322875417149150656061644) * r8 + ((4446273049517981 : ℝ) / 2542109602773571) * r9 + ((-5083036935812586 : ℝ) / 2542109602773571) * (value_001 h H) + ((-960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((4446273049517981 : ℝ) / 2542109602773571) * (value_002 h H) + ((5083036935812586 : ℝ) / 2542109602773571) * (value_049 h H) + ((960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((-1904163446744410 : ℝ) / 2542109602773571) * (value_050 h H)

/-- Coordinate 28.3, recovered from skew spokes on cycle 10. -/
theorem value_115 (h : Assignment) (H : Constraints h) :
    h 28 3 = ((-642280866153192 : ℝ) / 2542109602773571) * (h 1 0) + ((299268742451778 : ℝ) / 2542109602773571) * (h 1 1) + ((-261778649443113 : ℝ) / 2542109602773571) * (h 1 2) + h 1 3 + ((642280866153192 : ℝ) / 2542109602773571) * (h 3 0) + ((-299268742451778 : ℝ) / 2542109602773571) * (h 5 1) + ((261778649443113 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 4 1
  change ((2023025751458 : ℤ) : ℝ) * (h 16 1 - h 0 1) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 4 2
  change ((2023025751458 : ℤ) : ℝ) * (h 16 2 - h 0 2) - ((-3017042930932 : ℤ) : ℝ) * (h 16 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 58 1
  change ((2023025751458 : ℤ) : ℝ) * (h 28 1 - h 12 1) - ((1696300119485 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 58 2
  change ((2023025751458 : ℤ) : ℝ) * (h 28 2 - h 12 2) - ((5537077272127 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 58 3
  change ((2023025751458 : ℤ) : ℝ) * (h 28 3 - h 12 3) - ((-326000808771 : ℤ) : ℝ) * (h 28 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 74 1
  change ((-28184794769312856 : ℤ) : ℝ) * (h 20 1 - h 16 1) - ((538173368948294171 : ℤ) : ℝ) * (h 20 0 - h 16 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 75 2
  change ((-521940643876164 : ℤ) : ℝ) * (h 24 2 - h 16 2) - ((11281982077659089 : ℤ) : ℝ) * (h 24 0 - h 16 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 86 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 20 0) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 86 1
  change ((1 : ℤ) : ℝ) * (h 28 1 - h 20 1) - ((0 : ℤ) : ℝ) * (h 28 2 - h 20 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 94 0
  change ((1 : ℤ) : ℝ) * (h 28 0 - h 24 0) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 94 2
  change ((1 : ℤ) : ℝ) * (h 28 2 - h 24 2) - ((0 : ℤ) : ℝ) * (h 28 1 - h 24 1) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((149634371225889 : ℝ) / 2571376594719800676648558259) * r0 + ((-261778649443113 : ℝ) / 5142753189439601353297116518) * r1 + ((-149634371225889 : ℝ) / 2571376594719800676648558259) * r2 + ((261778649443113 : ℝ) / 5142753189439601353297116518) * r3 + ((1 : ℝ) / 2023025751458) * r4 + ((-1847337916369 : ℝ) / 442276774291805716383552020548) * r5 + ((87259549814371 : ℝ) / 442276774291805716383552020548) * r6 + ((994188070038226838752008185099 : ℝ) / 442276774291805716383552020548) * r7 + ((299268742451778 : ℝ) / 2542109602773571) * r8 + ((-984460677110334108456170968019 : ℝ) / 442276774291805716383552020548) * r9 + ((-261778649443113 : ℝ) / 2542109602773571) * r10 + ((299268742451778 : ℝ) / 2542109602773571) * (value_001 h H) + ((56554610045887966836262890 : ℝ) / 2571376594719800676648558259) * (value_000 h H) + ((-261778649443113 : ℝ) / 2542109602773571) * (value_002 h H) + ((-299268742451778 : ℝ) / 2542109602773571) * (value_049 h H) + ((-56554610045887966836262890 : ℝ) / 2571376594719800676648558259) * (value_048 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (value_050 h H) + (1 : ℝ) * (value_051 h H)

/-- Coordinate 17.0, recovered from skew spokes on cycle 11. -/
theorem value_068 (h : Assignment) (H : Constraints h) :
    h 17 0 = h 1 0 + ((-3240044152965 : ℝ) / 1352091329024) * (h 1 1) + ((5304072280039 : ℝ) / 2704182658048) * (h 1 2) + ((3240044152965 : ℝ) / 1352091329024) * (h 5 1) + ((-5304072280039 : ℝ) / 2704182658048) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 1
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 1 - h 17 1) - ((2502805068546721 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-3483 : ℝ) / 2714323343015680) * r0 + ((8260930649674693 : ℝ) / 981121466765412673074964480) * r1 + ((1 : ℝ) / 2714323343015680) * r2 + ((-8260930649674693 : ℝ) / 3417246068743932340320101283840) * r3 + ((-83593139146497 : ℝ) / 44845263343483552151651694080) * r4 + ((198265037403909983955417887 : ℝ) / 16209804429621193951816509403583819386880) * r5 + ((83593139146497 : ℝ) / 542864668603136) * (value_081 h H) + ((350271976707008620126583 : ℝ) / 244364001685034289682432) * (value_080 h H) + ((-198265037403909983955417887 : ℝ) / 196224293353082534614992896) * (value_082 h H)

/-- Coordinate 17.1, recovered from skew spokes on cycle 11. -/
theorem value_069 (h : Assignment) (H : Constraints h) :
    h 17 1 = ((-287585217247 : ℝ) / 1352091329024) * (h 1 1) + ((13421056175033 : ℝ) / 13520913290240) * (h 1 2) + ((1639676546271 : ℝ) / 1352091329024) * (h 5 1) + ((-13421056175033 : ℝ) / 13520913290240) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 1
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 1 - h 17 1) - ((2502805068546721 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2502805068546721 : ℝ) / 325723239881272816826425600) * r0 + ((501676082838624031404156289 : ℝ) / 117736180434878514914512953724039321600) * r1 + ((60728760973 : ℝ) / 325723239881272816826425600) * r2 + ((-501676082838624031404156289 : ℝ) / 410075116454681867447248617820828957132800) * r3 + ((-211518274468959 : ℝ) / 224226316717417760758258470400) * r4 + ((501676082838624031404156289 : ℝ) / 81049022148105969759082547017919096934400) * r5 + ((211518274468959 : ℝ) / 2714323343015680) * (value_081 h H) + ((886303886471556026869801 : ℝ) / 1221820008425171448412160) * (value_080 h H) + ((-501676082838624031404156289 : ℝ) / 981121466765412673074964480) * (value_082 h H)

/-- Coordinate 17.2, recovered from skew spokes on cycle 11. -/
theorem value_070 (h : Assignment) (H : Constraints h) :
    h 17 2 = ((-1639676546271 : ℝ) / 1352091329024) * (h 1 1) + ((26941969465273 : ℝ) / 13520913290240) * (h 1 2) + ((1639676546271 : ℝ) / 1352091329024) * (h 5 1) + ((-13421056175033 : ℝ) / 13520913290240) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 1
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 1 - h 17 1) - ((2502805068546721 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-211518274468959 : ℝ) / 325723239881272816826425600) * r0 + ((1482797549604036704479120769 : ℝ) / 117736180434878514914512953724039321600) * r1 + ((60728760973 : ℝ) / 325723239881272816826425600) * r2 + ((-501676082838624031404156289 : ℝ) / 410075116454681867447248617820828957132800) * r3 + ((-211518274468959 : ℝ) / 224226316717417760758258470400) * r4 + ((501676082838624031404156289 : ℝ) / 81049022148105969759082547017919096934400) * r5 + ((211518274468959 : ℝ) / 2714323343015680) * (value_081 h H) + ((886303886471556026869801 : ℝ) / 1221820008425171448412160) * (value_080 h H) + ((-501676082838624031404156289 : ℝ) / 981121466765412673074964480) * (value_082 h H)

/-- Coordinate 17.3, recovered from skew spokes on cycle 11. -/
theorem value_071 (h : Assignment) (H : Constraints h) :
    h 17 3 = ((-800183803347 : ℝ) / 676045664512) * (h 1 1) + ((6549652612581 : ℝ) / 6760456645120) * (h 1 2) + h 1 3 + ((800183803347 : ℝ) / 676045664512) * (h 5 1) + ((-6549652612581 : ℝ) / 6760456645120) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 8 3
  change ((120001635295 : ℤ) : ℝ) * (h 17 3 - h 1 3) - ((59272874322 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 1
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 1 - h 17 1) - ((2502805068546721 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-103223710631763 : ℝ) / 162861619940636408413212800) * r0 + ((244824552090462944186466573 : ℝ) / 58868090217439257457256476862019660800) * r1 + ((1 : ℝ) / 120001635295) * r2 + ((29636437161 : ℝ) / 162861619940636408413212800) * r3 + ((-81608184030154314728822191 : ℝ) / 68345852742446977907874769636804826188800) * r4 + ((-103223710631763 : ℝ) / 112113158358708880379129235200) * r5 + ((244824552090462944186466573 : ℝ) / 40524511074052984879541273508959548467200) * r6 + ((103223710631763 : ℝ) / 1357161671507840) * (value_081 h H) + ((432527998531743536881557 : ℝ) / 610910004212585724206080) * (value_080 h H) + ((-244824552090462944186466573 : ℝ) / 490560733382706336537482240) * (value_082 h H)

/-- Coordinate 21.0, recovered from skew spokes on cycle 11. -/
theorem value_084 (h : Assignment) (H : Constraints h) :
    h 21 0 = h 1 0 + ((-11016150120081 : ℝ) / 4123313721191) * (h 1 1) + ((19272262628377 : ℝ) / 8246627442382) * (h 1 2) + ((11016150120081 : ℝ) / 4123313721191) * (h 5 1) + ((-19272262628377 : ℝ) / 8246627442382) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((8260855041253 : ℝ) / 745208122768131098915188) * r0 + ((-8260855041253 : ℝ) / 2595559891601400617521599804) * r1 + ((24000327059 : ℝ) / 1490416245536262197830376) * r2 + ((-991316113885304685824635 : ℝ) / 745208122768131098915188) * (value_082 h H) + ((1246879614000986590334357 : ℝ) / 745208122768131098915188) * (value_080 h H)

/-- Coordinate 21.1, recovered from skew spokes on cycle 11. -/
theorem value_085 (h : Assignment) (H : Constraints h) :
    h 21 1 = ((59216465721051 : ℝ) / 41233137211910) * (h 1 1) + ((-103596562034867 : ℝ) / 82466274423820) * (h 1 2) + ((-17983328509141 : ℝ) / 41233137211910) * (h 5 1) + ((103596562034867 : ℝ) / 82466274423820) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-87186713076679 : ℝ) / 7452081227681310989151880) * r0 + ((87186713076679 : ℝ) / 25955598916014006175215998040) * r1 + ((-1 : ℝ) / 82608550412530) * r2 + ((-2092509629039488145557061 : ℝ) / 123121125555036006353654751785765011280) * r3 + (1 : ℝ) * (value_081 h H) + ((-5294741058455172411648667 : ℝ) / 7452081227681310989151880) * (value_080 h H) + ((2092509629039488145557061 : ℝ) / 1490416245536262197830376) * (value_082 h H)

/-- Coordinate 21.2, recovered from skew spokes on cycle 11. -/
theorem value_086 (h : Assignment) (H : Constraints h) :
    h 21 2 = ((-27874501286607 : ℝ) / 20616568605955) * (h 1 1) + ((89998332273229 : ℝ) / 41233137211910) * (h 1 2) + ((27874501286607 : ℝ) / 20616568605955) * (h 5 1) + ((-48765195061319 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((51952609268023 : ℝ) / 3726040613840655494575940) * r0 + ((-51952609268023 : ℝ) / 12977799458007003087607999020) * r1 + ((60728760973 : ℝ) / 7452081227681310989151880) * r2 + ((-501671491232855491419169 : ℝ) / 745208122768131098915188) * (value_082 h H) + ((3155017590161433259266379 : ℝ) / 3726040613840655494575940) * (value_080 h H)

/-- Coordinate 21.3, recovered from skew spokes on cycle 11. -/
theorem value_087 (h : Assignment) (H : Constraints h) :
    h 21 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 3
  change ((120001635295 : ℤ) : ℝ) * (h 17 3 - h 1 3) - ((59272874322 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 3
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 3 - h 17 3) - ((-206447421263526 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((244822311326224597202733 : ℝ) / 44713096683646426990383980256180230) * r0 + ((1 : ℝ) / 120001635295) * r1 + ((-81607437108741532400911 : ℝ) / 51911905249713501735835801077425247030) * r2 + ((-1 : ℝ) / 417965695732485) * r3 + ((29636437161 : ℝ) / 3726040613840655494575940) * r4 + ((-244822311326224597202733 : ℝ) / 372604061384065549457594) * (value_082 h H) + ((1539690239921749846202703 : ℝ) / 1863020306920327747287970) * (value_080 h H)

/-- Coordinate 25.0, recovered from skew spokes on cycle 11. -/
theorem value_100 (h : Assignment) (H : Constraints h) :
    h 25 0 = h 1 0 + ((-11016150120081 : ℝ) / 4123313721191) * (h 1 1) + ((19272262628377 : ℝ) / 8246627442382) * (h 1 2) + ((11016150120081 : ℝ) / 4123313721191) * (h 5 1) + ((-19272262628377 : ℝ) / 8246627442382) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 88 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 21 0) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 99 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 25 0) - ((0 : ℤ) : ℝ) * (h 29 1 - h 25 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((8260855041253 : ℝ) / 745208122768131098915188) * r0 + ((-8260855041253 : ℝ) / 2595559891601400617521599804) * r1 + ((24000327059 : ℝ) / 1490416245536262197830376) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((-991316113885304685824635 : ℝ) / 745208122768131098915188) * (value_082 h H) + ((1246879614000986590334357 : ℝ) / 745208122768131098915188) * (value_080 h H)

/-- Coordinate 25.1, recovered from skew spokes on cycle 11. -/
theorem value_101 (h : Assignment) (H : Constraints h) :
    h 25 1 = ((-7257932680652 : ℝ) / 20616568605955) * (h 1 1) + ((48765195061319 : ℝ) / 41233137211910) * (h 1 2) + ((27874501286607 : ℝ) / 20616568605955) * (h 5 1) + ((-48765195061319 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 78 1
  change ((-15480210953055 : ℤ) : ℝ) * (h 25 1 - h 17 1) - ((-7834010165517 : ℤ) : ℝ) * (h 25 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 88 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 21 0) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 99 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 25 0) - ((0 : ℤ) : ℝ) * (h 29 1 - h 25 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1 : ℝ) / 120001635295) * r0 + ((501671491232855491419169 : ℝ) / 89426193367292853980767960512360460) * r1 + ((-501671491232855491419169 : ℝ) / 311471431498281010415014806464551482180) * r2 + ((-1 : ℝ) / 15480210953055) * r3 + ((60728760973 : ℝ) / 7452081227681310989151880) * r4 + ((60728760973 : ℝ) / 120001635295) * r5 + ((-60728760973 : ℝ) / 120001635295) * r6 + ((-501671491232855491419169 : ℝ) / 745208122768131098915188) * (value_082 h H) + ((3155017590161433259266379 : ℝ) / 3726040613840655494575940) * (value_080 h H)

/-- Coordinate 25.2, recovered from skew spokes on cycle 11. -/
theorem value_102 (h : Assignment) (H : Constraints h) :
    h 25 2 = ((14271376629708 : ℝ) / 20616568605955) * (h 1 1) + ((-12483568010518 : ℝ) / 20616568605955) * (h 1 2) + ((-14271376629708 : ℝ) / 20616568605955) * (h 5 1) + ((33100136616473 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 1
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 1 - h 17 1) - ((2502805068546721 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 78 2
  change ((-15480210953055 : ℤ) : ℝ) * (h 25 2 - h 17 2) - ((107093752801523 : ℤ) : ℝ) * (h 25 0 - h 17 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 88 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 21 0) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 99 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 25 0) - ((0 : ℤ) : ℝ) * (h 29 1 - h 25 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-918 : ℝ) / 96361313141885) * r0 + ((-41975201863809416789499947 : ℝ) / 7180923327393616174655667229142544938) * r1 + ((34 : ℝ) / 12430609395303165) * r2 + ((509077070610451720161947717 : ℝ) / 125055779746559825681628444795517420095270) * r3 + ((-1 : ℝ) / 15480210953055) * r4 + ((-459 : ℝ) / 33167332990630795) * r5 + ((-509077070610451720161947717 : ℝ) / 24716565955173478275496191420992326014460) * r6 + ((-107093752801523 : ℝ) / 15480210953055) * r7 + ((107093752801523 : ℝ) / 15480210953055) * r8 + ((918 : ℝ) / 803) * (value_081 h H) + ((-1739173828580005580175823 : ℝ) / 1863020306920327747287970) * (value_080 h H) + ((509077070610451720161947717 : ℝ) / 299201061291404636214447982) * (value_082 h H)

/-- Coordinate 25.3, recovered from skew spokes on cycle 11. -/
theorem value_103 (h : Assignment) (H : Constraints h) :
    h 25 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 3
  change ((120001635295 : ℤ) : ℝ) * (h 17 3 - h 1 3) - ((59272874322 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 78 3
  change ((-15480210953055 : ℤ) : ℝ) * (h 25 3 - h 17 3) - ((-7646200787538 : ℤ) : ℝ) * (h 25 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 88 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 21 0) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 99 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 25 0) - ((0 : ℤ) : ℝ) * (h 29 1 - h 25 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((244822311326224597202733 : ℝ) / 44713096683646426990383980256180230) * r0 + ((1 : ℝ) / 120001635295) * r1 + ((-81607437108741532400911 : ℝ) / 51911905249713501735835801077425247030) * r2 + ((-1 : ℝ) / 15480210953055) * r3 + ((29636437161 : ℝ) / 3726040613840655494575940) * r4 + ((59272874322 : ℝ) / 120001635295) * r5 + ((-59272874322 : ℝ) / 120001635295) * r6 + ((-244822311326224597202733 : ℝ) / 372604061384065549457594) * (value_082 h H) + ((1539690239921749846202703 : ℝ) / 1863020306920327747287970) * (value_080 h H)

/-- Coordinate 29.0, recovered from skew spokes on cycle 11. -/
theorem value_116 (h : Assignment) (H : Constraints h) :
    h 29 0 = h 1 0 + ((-11016150120081 : ℝ) / 4123313721191) * (h 1 1) + ((19272262628377 : ℝ) / 8246627442382) * (h 1 2) + ((11016150120081 : ℝ) / 4123313721191) * (h 5 1) + ((-19272262628377 : ℝ) / 8246627442382) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 88 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 21 0) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((8260855041253 : ℝ) / 745208122768131098915188) * r0 + ((-8260855041253 : ℝ) / 2595559891601400617521599804) * r1 + ((24000327059 : ℝ) / 1490416245536262197830376) * r2 + (1 : ℝ) * r3 + ((-991316113885304685824635 : ℝ) / 745208122768131098915188) * (value_082 h H) + ((1246879614000986590334357 : ℝ) / 745208122768131098915188) * (value_080 h H)

/-- Coordinate 29.1, recovered from skew spokes on cycle 11. -/
theorem value_117 (h : Assignment) (H : Constraints h) :
    h 29 1 = ((59216465721051 : ℝ) / 41233137211910) * (h 1 1) + ((-103596562034867 : ℝ) / 82466274423820) * (h 1 2) + ((-17983328509141 : ℝ) / 41233137211910) * (h 5 1) + ((103596562034867 : ℝ) / 82466274423820) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 88 1
  change ((1 : ℤ) : ℝ) * (h 29 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-87186713076679 : ℝ) / 7452081227681310989151880) * r0 + ((87186713076679 : ℝ) / 25955598916014006175215998040) * r1 + ((-1 : ℝ) / 82608550412530) * r2 + ((-2092509629039488145557061 : ℝ) / 123121125555036006353654751785765011280) * r3 + (1 : ℝ) * r4 + (1 : ℝ) * (value_081 h H) + ((-5294741058455172411648667 : ℝ) / 7452081227681310989151880) * (value_080 h H) + ((2092509629039488145557061 : ℝ) / 1490416245536262197830376) * (value_082 h H)

/-- Coordinate 29.2, recovered from skew spokes on cycle 11. -/
theorem value_118 (h : Assignment) (H : Constraints h) :
    h 29 2 = ((14271376629708 : ℝ) / 20616568605955) * (h 1 1) + ((-12483568010518 : ℝ) / 20616568605955) * (h 1 2) + ((-14271376629708 : ℝ) / 20616568605955) * (h 5 1) + ((33100136616473 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 8 1
  change ((120001635295 : ℤ) : ℝ) * (h 17 1 - h 1 1) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 1
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 1 - h 17 1) - ((2502805068546721 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 78 2
  change ((-15480210953055 : ℤ) : ℝ) * (h 25 2 - h 17 2) - ((107093752801523 : ℤ) : ℝ) * (h 25 0 - h 17 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 84 1
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 1 - h 20 1) - ((87186713076679 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 88 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 21 0) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 99 0
  change ((1 : ℤ) : ℝ) * (h 29 0 - h 25 0) - ((0 : ℤ) : ℝ) * (h 29 1 - h 25 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 99 2
  change ((1 : ℤ) : ℝ) * (h 29 2 - h 25 2) - ((0 : ℤ) : ℝ) * (h 29 1 - h 25 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-918 : ℝ) / 96361313141885) * r0 + ((-41975201863809416789499947 : ℝ) / 7180923327393616174655667229142544938) * r1 + ((34 : ℝ) / 12430609395303165) * r2 + ((509077070610451720161947717 : ℝ) / 125055779746559825681628444795517420095270) * r3 + ((-1 : ℝ) / 15480210953055) * r4 + ((-459 : ℝ) / 33167332990630795) * r5 + ((-509077070610451720161947717 : ℝ) / 24716565955173478275496191420992326014460) * r6 + ((-107093752801523 : ℝ) / 15480210953055) * r7 + ((107093752801523 : ℝ) / 15480210953055) * r8 + (1 : ℝ) * r9 + ((918 : ℝ) / 803) * (value_081 h H) + ((-1739173828580005580175823 : ℝ) / 1863020306920327747287970) * (value_080 h H) + ((509077070610451720161947717 : ℝ) / 299201061291404636214447982) * (value_082 h H)

/-- Coordinate 29.3, recovered from skew spokes on cycle 11. -/
theorem value_119 (h : Assignment) (H : Constraints h) :
    h 29 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 8 2
  change ((120001635295 : ℤ) : ℝ) * (h 17 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 8 3
  change ((120001635295 : ℤ) : ℝ) * (h 17 3 - h 1 3) - ((59272874322 : ℤ) : ℝ) * (h 17 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 77 2
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 2 - h 17 2) - ((-211518274468959 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 77 3
  change ((-417965695732485 : ℤ) : ℝ) * (h 21 3 - h 17 3) - ((-206447421263526 : ℤ) : ℝ) * (h 21 0 - h 17 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 84 2
  change ((-82608550412530 : ℤ) : ℝ) * (h 21 2 - h 20 2) - ((-103905218536046 : ℤ) : ℝ) * (h 21 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 88 3
  change ((1 : ℤ) : ℝ) * (h 29 3 - h 21 3) - ((0 : ℤ) : ℝ) * (h 29 2 - h 21 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((244822311326224597202733 : ℝ) / 44713096683646426990383980256180230) * r0 + ((1 : ℝ) / 120001635295) * r1 + ((-81607437108741532400911 : ℝ) / 51911905249713501735835801077425247030) * r2 + ((-1 : ℝ) / 417965695732485) * r3 + ((29636437161 : ℝ) / 3726040613840655494575940) * r4 + (1 : ℝ) * r5 + ((-244822311326224597202733 : ℝ) / 372604061384065549457594) * (value_082 h H) + ((1539690239921749846202703 : ℝ) / 1863020306920327747287970) * (value_080 h H)

/-- Coordinate 18.0, recovered from skew spokes on cycle 12. -/
theorem value_072 (h : Assignment) (H : Constraints h) :
    h 18 0 = ((1048714533548638 : ℝ) / 2429983562997233) * (h 1 0) + ((1225096040646180 : ℝ) / 2429983562997233) * (h 1 1) + ((-1002763796232614 : ℝ) / 2429983562997233) * (h 1 2) + ((1381269029448595 : ℝ) / 2429983562997233) * (h 3 0) + ((-1225096040646180 : ℝ) / 2429983562997233) * (h 5 1) + ((1002763796232614 : ℝ) / 2429983562997233) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-6966 : ℝ) / 1951276801086778099) * r0 + ((1867388149199539994 : ℝ) / 37717189804404845245397823781801) * r1 + ((1 : ℝ) / 1951276801086778099) * r2 + ((-933694074599769997 : ℝ) / 131368972088742075989720620232012883) * r3 + ((-7901869462167861 : ℝ) / 17130469750998658093415065270558945) * r4 + ((2118268359198106009926650475299 : ℝ) / 331123282292483907882415147331761372007461585555) * r5 + ((63214955697342888 : ℝ) / 1951276801086778099) * (value_009 h H) + ((44553288234250927096744029000 : ℝ) / 46970348448822970417680976067) * (value_008 h H) + ((-16946146873584848079413203802392 : ℝ) / 37717189804404845245397823781801) * (value_010 h H) + ((-63214955697342888 : ℝ) / 1951276801086778099) * (value_081 h H) + ((2417060214572043320936947067 : ℝ) / 46970348448822970417680976067) * (value_080 h H) + ((16946146873584848079413203802392 : ℝ) / 37717189804404845245397823781801) * (value_082 h H)

/-- Coordinate 18.1, recovered from skew spokes on cycle 12. -/
theorem value_073 (h : Assignment) (H : Constraints h) :
    h 18 1 = ((-1123773944419049 : ℝ) / 2429983562997233) * (h 1 0) + ((5217362084823608 : ℝ) / 2429983562997233) * (h 1 1) + ((-4563041876471325 : ℝ) / 4859967125994466) * (h 1 2) + ((1123773944419049 : ℝ) / 2429983562997233) * (h 3 0) + ((-2787378521826375 : ℝ) / 2429983562997233) * (h 5 1) + ((4563041876471325 : ℝ) / 4859967125994466) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2095105532813019049 : ℝ) / 17707418394193745101999127644532) * r0 + ((19278213403673718533891995320525 : ℝ) / 171137703309914237684296389038419981256904334) * r1 + ((20647248309825 : ℝ) / 17707418394193745101999127644532) * r2 + ((-6426071134557906177963998440175 : ℝ) / 397381747085620859902936215347211196478531863548) * r3 + ((-14382873172624095 : ℝ) / 13704375800798926474732052216447156) * r4 + ((3855642680734743706778399064105 : ℝ) / 264898625833987126305932117865409097605969268444) * r5 + ((2095105532813019049 : ℝ) / 1951276801086778099) * (value_009 h H) + ((-21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_008 h H) + ((-38556426807347437067783990641050 : ℝ) / 37717189804404845245397823781801) * (value_010 h H) + ((-143828731726240950 : ℝ) / 1951276801086778099) * (value_081 h H) + ((21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_080 h H) + ((38556426807347437067783990641050 : ℝ) / 37717189804404845245397823781801) * (value_082 h H)

/-- Coordinate 18.2, recovered from skew spokes on cycle 12. -/
theorem value_074 (h : Assignment) (H : Constraints h) :
    h 18 2 = ((-1123773944419049 : ℝ) / 2429983562997233) * (h 1 0) + ((2787378521826375 : ℝ) / 2429983562997233) * (h 1 1) + ((296925249523141 : ℝ) / 4859967125994466) * (h 1 2) + ((1123773944419049 : ℝ) / 2429983562997233) * (h 3 0) + ((-2787378521826375 : ℝ) / 2429983562997233) * (h 5 1) + ((4563041876471325 : ℝ) / 4859967125994466) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-71914365863120475 : ℝ) / 8853709197096872550999563822266) * r0 + ((839237002942591822386166859249 : ℝ) / 342275406619828475368592778076839962513808668) * r1 + ((20647248309825 : ℝ) / 17707418394193745101999127644532) * r2 + ((-6426071134557906177963998440175 : ℝ) / 397381747085620859902936215347211196478531863548) * r3 + ((-14382873172624095 : ℝ) / 13704375800798926474732052216447156) * r4 + ((3855642680734743706778399064105 : ℝ) / 264898625833987126305932117865409097605969268444) * r5 + ((143828731726240950 : ℝ) / 1951276801086778099) * (value_009 h H) + ((-21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_008 h H) + ((-839237002942591822386166859249 : ℝ) / 37717189804404845245397823781801) * (value_010 h H) + ((-143828731726240950 : ℝ) / 1951276801086778099) * (value_081 h H) + ((21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_080 h H) + ((38556426807347437067783990641050 : ℝ) / 37717189804404845245397823781801) * (value_082 h H)

/-- Coordinate 18.3, recovered from skew spokes on cycle 12. -/
theorem value_075 (h : Assignment) (H : Constraints h) :
    h 18 3 = ((-20301981401394 : ℝ) / 83792536655077) * (h 1 0) + ((4414807190880 : ℝ) / 83792536655077) * (h 1 1) + ((-3613601441424 : ℝ) / 83792536655077) * (h 1 2) + h 1 3 + ((20301981401394 : ℝ) / 83792536655077) * (h 3 0) + ((-4414807190880 : ℝ) / 83792536655077) * (h 5 1) + ((3613601441424 : ℝ) / 83792536655077) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-56951012762352 : ℝ) / 152650158570635733637923514177) * r0 + ((15266960424537450891665466768 : ℝ) / 2950650057067486856625799811007241056153523) * r1 + ((-1 : ℝ) / 9074785486268) * r2 + ((8175568872 : ℝ) / 152650158570635733637923514177) * r3 + ((-2544493404089575148610911128 : ℝ) / 3425704716255352240542553580579406866194240203) * r4 + ((-28475506381176 : ℝ) / 590705853482712348048795354157205) * r5 + ((7633480212268725445832733384 : ℝ) / 11418044216982203720083280942474530069222813295) * r6 + ((227804051049408 : ℝ) / 67285406934026831) * (value_009 h H) + ((-8710219004915111225476872 : ℝ) / 1619667187890447255782102623) * (value_008 h H) + ((-61067841698149803566661867072 : ℝ) / 1300592751876029146393028406269) * (value_010 h H) + (1 : ℝ) * (value_011 h H) + ((-227804051049408 : ℝ) / 67285406934026831) * (value_081 h H) + ((8710219004915111225476872 : ℝ) / 1619667187890447255782102623) * (value_080 h H) + ((61067841698149803566661867072 : ℝ) / 1300592751876029146393028406269) * (value_082 h H)

/-- Coordinate 22.0, recovered from skew spokes on cycle 12. -/
theorem value_088 (h : Assignment) (H : Constraints h) :
    h 22 0 = ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 0) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 1) + ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 2) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 3 0) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 5 1) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((-8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_008 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_080 h H)

/-- Coordinate 22.1, recovered from skew spokes on cycle 12. -/
theorem value_089 (h : Assignment) (H : Constraints h) :
    h 22 1 = ((6713376906904283 : ℝ) / 19645476759162664) * (h 1 0) + ((-9978558405160779 : ℝ) / 19645476759162664) * (h 1 1) + ((17457042264366243 : ℝ) / 39290953518325328) * (h 1 2) + ((-6713376906904283 : ℝ) / 19645476759162664) * (h 3 0) + ((29624035164323443 : ℝ) / 19645476759162664) * (h 5 1) + ((-17457042264366243 : ℝ) / 39290953518325328) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((6364630054597567 : ℝ) / 1518948363062938929906044414944) * r0 + ((-6364630054597567 : ℝ) / 10580994297096432585725505394499904) * r1 + ((1 : ℝ) / 70232863903092440) * r2 + ((14439413111231777359286177489 : ℝ) / 26670023414706108418493303011628931528037355840) * r3 + ((-14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_010 h H) + ((131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_008 h H) + (1 : ℝ) * (value_081 h H) + ((-131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_080 h H) + ((14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_082 h H)

/-- Coordinate 22.2, recovered from skew spokes on cycle 12. -/
theorem value_090 (h : Assignment) (H : Constraints h) :
    h 22 2 = ((-4000350913637771 : ℝ) / 9822738379581332) * (h 1 0) + ((9477086974209675 : ℝ) / 9822738379581332) * (h 1 1) + ((3065736366373189 : ℝ) / 19645476759162664) * (h 1 2) + ((4000350913637771 : ℝ) / 9822738379581332) * (h 3 0) + ((-9477086974209675 : ℝ) / 9822738379581332) * (h 5 1) + ((16579740392789475 : ℝ) / 19645476759162664) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-3792540476565679 : ℝ) / 759474181531469464953022207472) * r0 + ((3792540476565679 : ℝ) / 5290497148548216292862752697249952) * r1 + ((20647248309825 : ℝ) / 1518948363062938929906044414944) * r2 + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_010 h H) + ((-78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_008 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_082 h H) + ((78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_080 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource011

/- Original source: CubicalIndecomposability/Rigidity/Values02.lean -/
section VerificationSource012


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 22.3, recovered from skew spokes on cycle 12. -/
theorem value_091 (h : Assignment) (H : Constraints h) :
    h 22 3 = ((-588757460640426 : ℝ) / 2455684594895333) * (h 1 0) + ((108824997255192 : ℝ) / 2455684594895333) * (h 1 1) + ((-95192236161132 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((588757460640426 : ℝ) / 2455684594895333) * (h 3 0) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 5 1) + ((95192236161132 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 3
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 3 - h 18 3) - ((6606317480432832 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((520362964425266072908540710 : ℝ) / 107688519996203866147786022137656192234289) * r0 + ((-1 : ℝ) / 9074785486268) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((1 : ℝ) / 63214955697342888) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_008 h H) + (1 : ℝ) * (value_011 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_080 h H)

/-- Coordinate 26.0, recovered from skew spokes on cycle 12. -/
theorem value_104 (h : Assignment) (H : Constraints h) :
    h 26 0 = ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 0) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 1) + ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 2) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 3 0) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 5 1) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((-8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_008 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_080 h H)

/-- Coordinate 26.1, recovered from skew spokes on cycle 12. -/
theorem value_105 (h : Assignment) (H : Constraints h) :
    h 26 1 = ((-4000350913637771 : ℝ) / 9822738379581332) * (h 1 0) + ((19299825353791007 : ℝ) / 9822738379581332) * (h 1 1) + ((-16579740392789475 : ℝ) / 19645476759162664) * (h 1 2) + ((4000350913637771 : ℝ) / 9822738379581332) * (h 3 0) + ((-9477086974209675 : ℝ) / 9822738379581332) * (h 5 1) + ((16579740392789475 : ℝ) / 19645476759162664) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 81 1
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 1 - h 18 1) - ((2663495031967425 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1 : ℝ) / 9074785486268) * r0 + ((181264422564661829297591902875 : ℝ) / 1723016319939261858364576354202499075748624) * r1 + ((-60421474188220609765863967625 : ℝ) / 4000843894898966035122546294458202853888304928) * r2 + ((1 : ℝ) / 1170647327728572) * r3 + ((20647248309825 : ℝ) / 1518948363062938929906044414944) * r4 + ((20647248309825 : ℝ) / 9074785486268) * r5 + ((-20647248309825 : ℝ) / 9074785486268) * r6 + (1 : ℝ) * (value_009 h H) + ((-78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_008 h H) + ((-181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_082 h H) + ((78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_080 h H)

/-- Coordinate 26.2, recovered from skew spokes on cycle 12. -/
theorem value_106 (h : Assignment) (H : Constraints h) :
    h 26 2 = ((2205155887507727 : ℝ) / 4911369189790666) * (h 1 0) + ((-9145265966661627 : ℝ) / 4911369189790666) * (h 1 1) + ((15999234359976659 : ℝ) / 9822738379581332) * (h 1 2) + ((-2205155887507727 : ℝ) / 4911369189790666) * (h 3 0) + ((9145265966661627 : ℝ) / 4911369189790666) * (h 5 1) + ((-6176495980395327 : ℝ) / 9822738379581332) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 81 2
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 2 - h 18 2) - ((43973215602920386 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((459 : ℝ) / 3643526372736602) * r0 + ((-83341079959661609825314960756589 : ℝ) / 691791052455613636133377406212303378913072536) * r1 + ((-17 : ℝ) / 940029804166043316) * r2 + ((2369619662813454093551785560529 : ℝ) / 1606338823801934863101702337224968445836154428592) * r3 + ((1 : ℝ) / 1170647327728572) * r4 + ((459 : ℝ) / 28198494857091614660) * r5 + ((-7108858988440362280655356681587 : ℝ) / 5354007200502251265012530579584508004253499184880) * r6 + ((21986607801460193 : ℝ) / 585323663864286) * r7 + ((-21986607801460193 : ℝ) / 585323663864286) * r8 + ((-918 : ℝ) / 803) * (value_009 h H) + ((43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_008 h H) + ((83341079959661609825314960756589 : ℝ) / 76232220971221247544659604075002) * (value_010 h H) + ((918 : ℝ) / 803) * (value_081 h H) + ((-43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_080 h H) + ((-7108858988440362280655356681587 : ℝ) / 76232220971221247544659604075002) * (value_082 h H)

/-- Coordinate 26.3, recovered from skew spokes on cycle 12. -/
theorem value_107 (h : Assignment) (H : Constraints h) :
    h 26 3 = ((-588757460640426 : ℝ) / 2455684594895333) * (h 1 0) + ((108824997255192 : ℝ) / 2455684594895333) * (h 1 1) + ((-95192236161132 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((588757460640426 : ℝ) / 2455684594895333) * (h 3 0) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 5 1) + ((95192236161132 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 81 3
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 3 - h 18 3) - ((122339212600608 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((520362964425266072908540710 : ℝ) / 107688519996203866147786022137656192234289) * r0 + ((-1 : ℝ) / 9074785486268) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((1 : ℝ) / 1170647327728572) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + ((237091497288 : ℝ) / 2268696371567) * r5 + ((-237091497288 : ℝ) / 2268696371567) * r6 + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_008 h H) + (1 : ℝ) * (value_011 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_080 h H)

/-- Coordinate 30.0, recovered from skew spokes on cycle 12. -/
theorem value_120 (h : Assignment) (H : Constraints h) :
    h 30 0 = ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 0) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 1) + ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 2) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 3 0) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 5 1) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((-8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + (1 : ℝ) * r3 + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_008 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_080 h H)

/-- Coordinate 30.1, recovered from skew spokes on cycle 12. -/
theorem value_121 (h : Assignment) (H : Constraints h) :
    h 30 1 = ((6713376906904283 : ℝ) / 19645476759162664) * (h 1 0) + ((-9978558405160779 : ℝ) / 19645476759162664) * (h 1 1) + ((17457042264366243 : ℝ) / 39290953518325328) * (h 1 2) + ((-6713376906904283 : ℝ) / 19645476759162664) * (h 3 0) + ((29624035164323443 : ℝ) / 19645476759162664) * (h 5 1) + ((-17457042264366243 : ℝ) / 39290953518325328) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 90 1
  change ((1 : ℤ) : ℝ) * (h 30 1 - h 22 1) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((6364630054597567 : ℝ) / 1518948363062938929906044414944) * r0 + ((-6364630054597567 : ℝ) / 10580994297096432585725505394499904) * r1 + ((1 : ℝ) / 70232863903092440) * r2 + ((14439413111231777359286177489 : ℝ) / 26670023414706108418493303011628931528037355840) * r3 + (1 : ℝ) * r4 + ((-14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_010 h H) + ((131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_008 h H) + (1 : ℝ) * (value_081 h H) + ((-131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_080 h H) + ((14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_082 h H)

/-- Coordinate 30.2, recovered from skew spokes on cycle 12. -/
theorem value_122 (h : Assignment) (H : Constraints h) :
    h 30 2 = ((2205155887507727 : ℝ) / 4911369189790666) * (h 1 0) + ((-9145265966661627 : ℝ) / 4911369189790666) * (h 1 1) + ((15999234359976659 : ℝ) / 9822738379581332) * (h 1 2) + ((-2205155887507727 : ℝ) / 4911369189790666) * (h 3 0) + ((9145265966661627 : ℝ) / 4911369189790666) * (h 5 1) + ((-6176495980395327 : ℝ) / 9822738379581332) * (h 9 2) := by
  have r0 := H 14 1
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 1 - h 2 1) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 1
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 1 - h 18 1) - ((2095105532813019049 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 81 2
  change ((1170647327728572 : ℤ) : ℝ) * (h 26 2 - h 18 2) - ((43973215602920386 : ℤ) : ℝ) * (h 26 0 - h 18 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 85 1
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 1 - h 20 1) - ((6364630054597567 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 90 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 22 0) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 103 0
  change ((1 : ℤ) : ℝ) * (h 30 0 - h 26 0) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 103 2
  change ((1 : ℤ) : ℝ) * (h 30 2 - h 26 2) - ((0 : ℤ) : ℝ) * (h 30 1 - h 26 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((459 : ℝ) / 3643526372736602) * r0 + ((-83341079959661609825314960756589 : ℝ) / 691791052455613636133377406212303378913072536) * r1 + ((-17 : ℝ) / 940029804166043316) * r2 + ((2369619662813454093551785560529 : ℝ) / 1606338823801934863101702337224968445836154428592) * r3 + ((1 : ℝ) / 1170647327728572) * r4 + ((459 : ℝ) / 28198494857091614660) * r5 + ((-7108858988440362280655356681587 : ℝ) / 5354007200502251265012530579584508004253499184880) * r6 + ((21986607801460193 : ℝ) / 585323663864286) * r7 + ((-21986607801460193 : ℝ) / 585323663864286) * r8 + (1 : ℝ) * r9 + ((-918 : ℝ) / 803) * (value_009 h H) + ((43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_008 h H) + ((83341079959661609825314960756589 : ℝ) / 76232220971221247544659604075002) * (value_010 h H) + ((918 : ℝ) / 803) * (value_081 h H) + ((-43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_080 h H) + ((-7108858988440362280655356681587 : ℝ) / 76232220971221247544659604075002) * (value_082 h H)

/-- Coordinate 30.3, recovered from skew spokes on cycle 12. -/
theorem value_123 (h : Assignment) (H : Constraints h) :
    h 30 3 = ((-588757460640426 : ℝ) / 2455684594895333) * (h 1 0) + ((108824997255192 : ℝ) / 2455684594895333) * (h 1 1) + ((-95192236161132 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((588757460640426 : ℝ) / 2455684594895333) * (h 3 0) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 5 1) + ((95192236161132 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 14 2
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 2 - h 2 2) - ((-20647248309825 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 14 3
  change ((-9074785486268 : ℤ) : ℝ) * (h 18 3 - h 2 3) - ((-948365989152 : ℤ) : ℝ) * (h 18 0 - h 2 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 80 2
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 2 - h 18 2) - ((143828731726240950 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 80 3
  change ((63214955697342888 : ℤ) : ℝ) * (h 22 3 - h 18 3) - ((6606317480432832 : ℤ) : ℝ) * (h 22 0 - h 18 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 85 2
  change ((70232863903092440 : ℤ) : ℝ) * (h 22 2 - h 20 2) - ((-7585080953131358 : ℤ) : ℝ) * (h 22 0 - h 20 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 90 3
  change ((1 : ℤ) : ℝ) * (h 30 3 - h 22 3) - ((0 : ℤ) : ℝ) * (h 30 2 - h 22 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((520362964425266072908540710 : ℝ) / 107688519996203866147786022137656192234289) * r0 + ((-1 : ℝ) / 9074785486268) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((1 : ℝ) / 63214955697342888) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + (1 : ℝ) * r5 + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_010 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_008 h H) + (1 : ℝ) * (value_011 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_082 h H) + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_080 h H)

/-- Coordinate 19.0, recovered from skew spokes on cycle 13. -/
theorem value_076 (h : Assignment) (H : Constraints h) :
    h 19 0 = ((12807158174847 : ℝ) / 4732319651584) * (h 1 1) + ((-104828961357081 : ℝ) / 47323196515840) * (h 1 2) + h 3 0 + ((-12807158174847 : ℝ) / 4732319651584) * (h 5 1) + ((104828961357081 : ℝ) / 47323196515840) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-3483 : ℝ) / 19000263401109760) * r0 + ((-2502805068546721 : ℝ) / 1153862454510034637977396480) * r1 + ((1 : ℝ) / 19000263401109760) * r2 + ((2502805068546721 : ℝ) / 4018902929058450644075271939840) * r3 + ((-1652123404555263 : ℝ) / 9500131700554880) * r4 + ((-1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * r5 + ((1652123404555263 : ℝ) / 9500131700554880) * (value_013 h H) + ((1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * (value_014 h H) + ((-1652123404555263 : ℝ) / 9500131700554880) * (value_085 h H) + ((-1187178533099505335152093581 : ℝ) / 576931227255017318988698240) * (value_086 h H)

/-- Coordinate 19.1, recovered from skew spokes on cycle 13. -/
theorem value_077 (h : Assignment) (H : Constraints h) :
    h 19 1 = ((-287585217247 : ℝ) / 1352091329024) * (h 1 1) + ((13421056175033 : ℝ) / 13520913290240) * (h 1 2) + ((1639676546271 : ℝ) / 1352091329024) * (h 5 1) + ((-13421056175033 : ℝ) / 13520913290240) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2502805068546721 : ℝ) / 2575019880865281762496488960) * r0 + ((2502805068546721 : ℝ) / 2575019880865281762496488960) * r1 + ((-60728760973 : ℝ) / 2575019880865281762496488960) * r2 + ((-2502805068546721 : ℝ) / 8968794245053776378775271047680) * r3 + ((211518274468959 : ℝ) / 2714323343015680) * r4 + ((2502805068546721 : ℝ) / 2714323343015680) * r5 + ((2502805068546721 : ℝ) / 2714323343015680) * (value_013 h H) + ((-2502805068546721 : ℝ) / 2714323343015680) * (value_014 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_085 h H) + ((2502805068546721 : ℝ) / 2714323343015680) * (value_086 h H)

/-- Coordinate 19.2, recovered from skew spokes on cycle 13. -/
theorem value_078 (h : Assignment) (H : Constraints h) :
    h 19 2 = ((-1639676546271 : ℝ) / 1352091329024) * (h 1 1) + ((26941969465273 : ℝ) / 13520913290240) * (h 1 2) + ((1639676546271 : ℝ) / 1352091329024) * (h 5 1) + ((-13421056175033 : ℝ) / 13520913290240) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((23502030496551 : ℝ) / 286113320096142418055165440) * r0 + ((-23502030496551 : ℝ) / 286113320096142418055165440) * r1 + ((-60728760973 : ℝ) / 2575019880865281762496488960) * r2 + ((-2502805068546721 : ℝ) / 8968794245053776378775271047680) * r3 + ((211518274468959 : ℝ) / 2714323343015680) * r4 + ((2502805068546721 : ℝ) / 2714323343015680) * r5 + ((-211518274468959 : ℝ) / 2714323343015680) * (value_013 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_014 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_085 h H) + ((2502805068546721 : ℝ) / 2714323343015680) * (value_086 h H)

/-- Coordinate 19.3, recovered from skew spokes on cycle 13. -/
theorem value_079 (h : Assignment) (H : Constraints h) :
    h 19 3 = ((-800183803347 : ℝ) / 676045664512) * (h 1 1) + ((6549652612581 : ℝ) / 6760456645120) * (h 1 2) + h 1 3 + ((800183803347 : ℝ) / 676045664512) * (h 5 1) + ((-6549652612581 : ℝ) / 6760456645120) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((11469301181307 : ℝ) / 143056660048071209027582720) * r0 + ((24724741713405731503033027 : ℝ) / 26062961140965105428157572300595559680) * r1 + ((-1 : ℝ) / 948678383322) * r2 + ((-9878812387 : ℝ) / 429169980144213627082748160) * r3 + ((-24724741713405731503033027 : ℝ) / 90777293653981462206272824322974334365440) * r4 + ((103223710631763 : ℝ) / 1357161671507840) * r5 + ((74174225140217194509099081 : ℝ) / 82418746750716759855528320) * r6 + ((-103223710631763 : ℝ) / 1357161671507840) * (value_013 h H) + ((-74174225140217194509099081 : ℝ) / 82418746750716759855528320) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((103223710631763 : ℝ) / 1357161671507840) * (value_085 h H) + ((74174225140217194509099081 : ℝ) / 82418746750716759855528320) * (value_086 h H)

/-- Coordinate 23.0, recovered from skew spokes on cycle 13. -/
theorem value_092 (h : Assignment) (H : Constraints h) :
    h 23 0 = ((435443377944798 : ℝ) / 144315980241685) * (h 1 1) + ((-380894370903783 : ℝ) / 144315980241685) * (h 1 2) + h 3 0 + ((-435443377944798 : ℝ) / 144315980241685) * (h 5 1) + ((380894370903783 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + ((948678383322 : ℝ) / 425101326811) * (value_014 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_086 h H)

/-- Coordinate 23.1, recovered from skew spokes on cycle 13. -/
theorem value_093 (h : Assignment) (H : Constraints h) :
    h 23 1 = ((59216465721051 : ℝ) / 41233137211910) * (h 1 1) + ((-103596562034867 : ℝ) / 82466274423820) * (h 1 2) + ((-17983328509141 : ℝ) / 41233137211910) * (h 5 1) + ((103596562034867 : ℝ) / 82466274423820) * (h 9 2) := by
  have r0 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_085 h H)

/-- Coordinate 23.2, recovered from skew spokes on cycle 13. -/
theorem value_094 (h : Assignment) (H : Constraints h) :
    h 23 2 = ((-27874501286607 : ℝ) / 20616568605955) * (h 1 1) + ((89998332273229 : ℝ) / 41233137211910) * (h 1 2) + ((27874501286607 : ℝ) / 20616568605955) * (h 5 1) + ((-48765195061319 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_086 h H)

/-- Coordinate 23.3, recovered from skew spokes on cycle 13. -/
theorem value_095 (h : Assignment) (H : Constraints h) :
    h 23 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 3
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 3 - h 19 3) - ((-1445131948844682 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((9878812387 : ℝ) / 9602010463502301282051) * r0 + ((-1 : ℝ) / 948678383322) * r1 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r2 + ((1 : ℝ) / 3304246809110526) * r3 + ((59272874322 : ℝ) / 60728760973) * r4 + ((-59272874322 : ℝ) / 60728760973) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((59272874322 : ℝ) / 60728760973) * (value_086 h H)

/-- Coordinate 27.0, recovered from skew spokes on cycle 13. -/
theorem value_108 (h : Assignment) (H : Constraints h) :
    h 27 0 = ((435443377944798 : ℝ) / 144315980241685) * (h 1 1) + ((-380894370903783 : ℝ) / 144315980241685) * (h 1 2) + h 3 0 + ((-435443377944798 : ℝ) / 144315980241685) * (h 5 1) + ((380894370903783 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((948678383322 : ℝ) / 425101326811) * (value_014 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_086 h H)

/-- Coordinate 27.1, recovered from skew spokes on cycle 13. -/
theorem value_109 (h : Assignment) (H : Constraints h) :
    h 27 1 = ((-7257932680652 : ℝ) / 20616568605955) * (h 1 1) + ((48765195061319 : ℝ) / 41233137211910) * (h 1 2) + ((27874501286607 : ℝ) / 20616568605955) * (h 5 1) + ((-48765195061319 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 83 1
  change ((122379511448538 : ℤ) : ℝ) * (h 27 1 - h 19 1) - ((-54838071158619 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1 : ℝ) / 948678383322) * r0 + ((1 : ℝ) / 948678383322) * r1 + ((-1 : ℝ) / 3304246809110526) * r2 + ((1 : ℝ) / 122379511448538) * r3 + (1 : ℝ) * r4 + ((-425101326811 : ℝ) / 948678383322) * r5 + ((425101326811 : ℝ) / 948678383322) * r6 + (1 : ℝ) * (value_013 h H) + (-1 : ℝ) * (value_014 h H) + (1 : ℝ) * (value_086 h H)

/-- Coordinate 27.2, recovered from skew spokes on cycle 13. -/
theorem value_110 (h : Assignment) (H : Constraints h) :
    h 27 2 = ((14271376629708 : ℝ) / 20616568605955) * (h 1 1) + ((-12483568010518 : ℝ) / 20616568605955) * (h 1 2) + ((-14271376629708 : ℝ) / 20616568605955) * (h 5 1) + ((33100136616473 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 83 2
  change ((122379511448538 : ℤ) : ℝ) * (h 27 2 - h 19 2) - ((749656269610661 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((51 : ℝ) / 42321596767087) * r0 + ((-51 : ℝ) / 42321596767087) * r1 + ((-17 : ℝ) / 49135373846588007) * r2 + ((115 : ℝ) / 2653310187715752378) * r3 + ((1 : ℝ) / 122379511448538) * r4 + ((918 : ℝ) / 803) * r5 + ((-115 : ℝ) / 803) * r6 + ((749656269610661 : ℝ) / 122379511448538) * r7 + ((-749656269610661 : ℝ) / 122379511448538) * r8 + ((-918 : ℝ) / 803) * (value_013 h H) + ((918 : ℝ) / 803) * (value_014 h H) + ((918 : ℝ) / 803) * (value_085 h H) + ((-115 : ℝ) / 803) * (value_086 h H)

/-- Coordinate 27.3, recovered from skew spokes on cycle 13. -/
theorem value_111 (h : Assignment) (H : Constraints h) :
    h 27 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 83 3
  change ((122379511448538 : ℤ) : ℝ) * (h 27 3 - h 19 3) - ((-53523405512766 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((9878812387 : ℝ) / 9602010463502301282051) * r0 + ((-1 : ℝ) / 948678383322) * r1 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r2 + ((1 : ℝ) / 122379511448538) * r3 + ((59272874322 : ℝ) / 60728760973) * r4 + ((-69151686709 : ℝ) / 158113063887) * r5 + ((69151686709 : ℝ) / 158113063887) * r6 + ((-59272874322 : ℝ) / 60728760973) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((59272874322 : ℝ) / 60728760973) * (value_086 h H)

/-- Coordinate 31.0, recovered from skew spokes on cycle 13. -/
theorem value_124 (h : Assignment) (H : Constraints h) :
    h 31 0 = ((435443377944798 : ℝ) / 144315980241685) * (h 1 1) + ((-380894370903783 : ℝ) / 144315980241685) * (h 1 2) + h 3 0 + ((-435443377944798 : ℝ) / 144315980241685) * (h 5 1) + ((380894370903783 : ℝ) / 144315980241685) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-1 : ℝ) / 425101326811) * r0 + ((1 : ℝ) / 1480627921282713) * r1 + ((-948678383322 : ℝ) / 425101326811) * r2 + (1 : ℝ) * r3 + ((948678383322 : ℝ) / 425101326811) * (value_014 h H) + ((-948678383322 : ℝ) / 425101326811) * (value_086 h H)

/-- Coordinate 31.1, recovered from skew spokes on cycle 13. -/
theorem value_125 (h : Assignment) (H : Constraints h) :
    h 31 1 = ((59216465721051 : ℝ) / 41233137211910) * (h 1 1) + ((-103596562034867 : ℝ) / 82466274423820) * (h 1 2) + ((-17983328509141 : ℝ) / 41233137211910) * (h 5 1) + ((103596562034867 : ℝ) / 82466274423820) * (h 9 2) := by
  have r0 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 91 1
  change ((1 : ℤ) : ℝ) * (h 31 1 - h 23 1) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1 + (1 : ℝ) * (value_085 h H)

/-- Coordinate 31.2, recovered from skew spokes on cycle 13. -/
theorem value_126 (h : Assignment) (H : Constraints h) :
    h 31 2 = ((14271376629708 : ℝ) / 20616568605955) * (h 1 1) + ((-12483568010518 : ℝ) / 20616568605955) * (h 1 2) + ((-14271376629708 : ℝ) / 20616568605955) * (h 5 1) + ((33100136616473 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 1
  change ((-948678383322 : ℤ) : ℝ) * (h 19 1 - h 3 1) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 1
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 1 - h 19 1) - ((17519635479827047 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 83 2
  change ((122379511448538 : ℤ) : ℝ) * (h 27 2 - h 19 2) - ((749656269610661 : ℤ) : ℝ) * (h 27 0 - h 19 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 87 1
  change ((1 : ℤ) : ℝ) * (h 23 1 - h 21 1) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 91 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 23 0) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 107 0
  change ((1 : ℤ) : ℝ) * (h 31 0 - h 27 0) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 107 2
  change ((1 : ℤ) : ℝ) * (h 31 2 - h 27 2) - ((0 : ℤ) : ℝ) * (h 31 1 - h 27 1) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((51 : ℝ) / 42321596767087) * r0 + ((-51 : ℝ) / 42321596767087) * r1 + ((-17 : ℝ) / 49135373846588007) * r2 + ((115 : ℝ) / 2653310187715752378) * r3 + ((1 : ℝ) / 122379511448538) * r4 + ((918 : ℝ) / 803) * r5 + ((-115 : ℝ) / 803) * r6 + ((749656269610661 : ℝ) / 122379511448538) * r7 + ((-749656269610661 : ℝ) / 122379511448538) * r8 + (1 : ℝ) * r9 + ((-918 : ℝ) / 803) * (value_013 h H) + ((918 : ℝ) / 803) * (value_014 h H) + ((918 : ℝ) / 803) * (value_085 h H) + ((-115 : ℝ) / 803) * (value_086 h H)

/-- Coordinate 31.3, recovered from skew spokes on cycle 13. -/
theorem value_127 (h : Assignment) (H : Constraints h) :
    h 31 3 = ((-27206249313798 : ℝ) / 20616568605955) * (h 1 1) + ((23798059040283 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((27206249313798 : ℝ) / 20616568605955) * (h 5 1) + ((-23798059040283 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 17 2
  change ((-948678383322 : ℤ) : ℝ) * (h 19 2 - h 3 2) - ((425101326811 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 17 3
  change ((-948678383322 : ℤ) : ℝ) * (h 19 3 - h 3 3) - ((414910120254 : ℤ) : ℝ) * (h 19 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 82 2
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 2 - h 19 2) - ((-1480627921282713 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 82 3
  change ((3304246809110526 : ℤ) : ℝ) * (h 23 3 - h 19 3) - ((-1445131948844682 : ℤ) : ℝ) * (h 23 0 - h 19 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 87 2
  change ((1 : ℤ) : ℝ) * (h 23 2 - h 21 2) - ((0 : ℤ) : ℝ) * (h 23 0 - h 21 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 91 3
  change ((1 : ℤ) : ℝ) * (h 31 3 - h 23 3) - ((0 : ℤ) : ℝ) * (h 31 2 - h 23 2) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((9878812387 : ℝ) / 9602010463502301282051) * r0 + ((-1 : ℝ) / 948678383322) * r1 + ((-9878812387 : ℝ) / 33443802444378515365383633) * r2 + ((1 : ℝ) / 3304246809110526) * r3 + ((59272874322 : ℝ) / 60728760973) * r4 + (1 : ℝ) * r5 + ((-59272874322 : ℝ) / 60728760973) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((59272874322 : ℝ) / 60728760973) * (value_086 h H)

/-- Coordinate 48.0, recovered from nonplanar cycle 14. -/
theorem value_192 (h : Assignment) (H : Constraints h) :
    h 48 0 = ((777343598631346184615358841 : ℝ) / 1054049275990752831481248181) * (h 1 0) + ((-32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (h 1 1) + ((25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (h 1 2) + ((276705677359406646865889340 : ℝ) / 1054049275990752831481248181) * (h 3 0) + ((32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (h 5 1) + ((-25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-9 : ℝ) / 522808440891413404414699097776) * r0 + ((267439343514741224767662154085 : ℝ) / 501412970893659741630471408892960087425827898672277981824) * r1 + ((11184256210993020617805 : ℝ) / 11539043138164279103797546460233995068179864280632) * r2 + ((-332345570974293394641455911683402706409444867164825 : ℝ) / 11066818070710449644632182349654680334373993382286172124277612784854030421568) * r3 + ((10646169217730800848081715 : ℝ) / 12385064011883937207218790974912140348853335290175364478288) * r4 + ((-4320492422665814130338926851884235183322783273142725 : ℝ) / 162221466829005846075564634489692492763163736289417250659005536461023638980163037312) * r5 + ((-3257727780625625059513004790 : ℝ) / 32675527555713337775918693611) * (value_097 h H) + ((-198352154553638402281892030013241633118676490791757 : ℝ) / 2797314173065583669722794167259663078114276860396088) * (value_096 h H) + ((4320492422665814130338926851884235183322783273142725 : ℝ) / 1398657086532791834861397083629831539057138430198044) * (value_098 h H) + ((3257727780625625059513004790 : ℝ) / 32675527555713337775918693611) * (value_113 h H) + ((2995666327619222072004686197272904711232953351187845 : ℝ) / 2797314173065583669722794167259663078114276860396088) * (value_112 h H) + ((-4320492422665814130338926851884235183322783273142725 : ℝ) / 1398657086532791834861397083629831539057138430198044) * (value_114 h H)

/-- Coordinate 48.1, recovered from nonplanar cycle 14. -/
theorem value_193 (h : Assignment) (H : Constraints h) :
    h 48 1 = ((181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (h 1 0) + ((314625604589592308369047275445 : ℝ) / 522808440891413404414699097776) * (h 1 1) + ((-69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (h 1 2) + ((-181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (h 3 0) + ((208182836301821096045651822331 : ℝ) / 522808440891413404414699097776) * (h 5 1) + ((69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((46992041205039445673799552395 : ℝ) / 605570695764454212612526808649200123423397174169516923392) * r0 + ((6266336423646552704914976797246244669772602789544777281 : ℝ) / 2127429502445327844927176384425105846429191706444308938222988407322821877090103296) * r1 + ((22142171912785859695823179677 : ℝ) / 4136700808859341401595005215808046295962208625149449472) * r2 + ((-219321774827629344672024187903618563442041097634067204835 : ℝ) / 1322470003692471118600686281207268093717246377192021187288342357639676830003480576) * r3 + ((10661045735785784297988938363 : ℝ) / 2245824940821620613575674096784068116592071465951799425396224) * r4 + ((-2851183072759181480736314442747041324746534269242873662855 : ℝ) / 19385248990777093264901873068672266628541048934936975564083616266377043493277509408067584) * r5 + ((234960206025197228368997761975 : ℝ) / 522808440891413404414699097776) * (value_097 h H) + ((-1976902697510699784209606353945204353703043213119051571911 : ℝ) / 334275313929106494420314272595306724950551932448185321216) * (value_096 h H) + ((2851183072759181480736314442747041324746534269242873662855 : ℝ) / 167137656964553247210157136297653362475275966224092660608) * (value_098 h H) + ((287848234866216176045701335801 : ℝ) / 522808440891413404414699097776) * (value_113 h H) + ((1976902697510699784209606353945204353703043213119051571911 : ℝ) / 334275313929106494420314272595306724950551932448185321216) * (value_112 h H) + ((-2851183072759181480736314442747041324746534269242873662855 : ℝ) / 167137656964553247210157136297653362475275966224092660608) * (value_114 h H)

/-- Coordinate 48.2, recovered from nonplanar cycle 14. -/
theorem value_194 (h : Assignment) (H : Constraints h) :
    h 48 2 = ((2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (h 1 0) + ((-134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (h 1 1) + ((116253836556504342053382163315 : ℝ) / 65351055111426675551837387222) * (h 1 2) + ((-2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (h 3 0) + ((134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (h 5 1) + ((-50902781445077666501544776093 : ℝ) / 65351055111426675551837387222) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-117009665260111260838611 : ℝ) / 33783958301596347664271110899379637341749820035343040) * r0 + ((99688209007599858566830146942415910046464477761301 : ℝ) / 356059119618404865593006848236818125685506957920474806673935844303337589890560) * r1 + ((117009665260111260838611 : ℝ) / 600030243184542513397472415932167743545352942592864) * r2 + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 575474539676943381520873482182043377387447655878880950462435864812409581921536) * r3 + ((8567707711823702321404961 : ℝ) / 49540256047535748828875163899648561395413341160701457913152) * r4 + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 648885867316023384302258537958769971052654945157669002636022145844094555920652149248) * r5 + ((-1310859279909026455174959033 : ℝ) / 65351055111426675551837387222) * (value_097 h H) + ((-2410819607718430417322749417151299737186306259291463 : ℝ) / 11189256692262334678891176669038652312457107441584352) * (value_096 h H) + ((9071627019691587129581543371759847814228267476278391 : ℝ) / 5594628346131167339445588334519326156228553720792176) * (value_098 h H) + ((1310859279909026455174959033 : ℝ) / 65351055111426675551837387222) * (value_113 h H) + ((2410819607718430417322749417151299737186306259291463 : ℝ) / 11189256692262334678891176669038652312457107441584352) * (value_112 h H) + ((-3476998673560419790135955037240521657999713755486215 : ℝ) / 5594628346131167339445588334519326156228553720792176) * (value_114 h H)

/-- Coordinate 48.3, recovered from nonplanar cycle 14. -/
theorem value_195 (h : Assignment) (H : Constraints h) :
    h 48 3 = ((-267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (h 1 0) + ((4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (h 1 1) + ((-3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (h 1 2) + h 1 3 + ((267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (h 3 0) + ((-4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (h 5 1) + ((3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 96 3
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 3 - h 24 3) - ((-102638922139772590676165376 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((46013180225658690159 : ℝ) / 150821242417840837786924602229373380989954553729210) * r0 + ((-5361975909619012018812310659699734680373651917 : ℝ) / 567251048411674418224153067043950445332302751588991726318770340189140768208) * r1 + ((1 : ℝ) / 5791516054445555661356452960) * r2 + ((-322092261579610831113 : ℝ) / 18750945099516953543671012997880241985792279456027) * r3 + ((187669156836665420658430873089490713813077817095 : ℝ) / 352619203233421189657397967023310893007014495023824111802963152458584302648) * r4 + ((-7861437051146797692721 : ℝ) / 516044333828497383634116290621339181202222303757306853262) * r5 + ((187669156836665420658430873089490713813077817095 : ℝ) / 397601634384818250185207437474736501870499353650532477105405726620155977892556464) * r6 + ((57734393703622082255343024 : ℝ) / 32675527555713337775918693611) * (value_097 h H) + ((2212086035754208843771774536230306998597443727543 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_096 h H) + ((-6380751332446624302386649685042684269644645781230 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_098 h H) + (1 : ℝ) * (value_099 h H) + ((-57734393703622082255343024 : ℝ) / 32675527555713337775918693611) * (value_113 h H) + ((-2212086035754208843771774536230306998597443727543 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_112 h H) + ((6380751332446624302386649685042684269644645781230 : ℝ) / 116554757211065986238449756969152628254761535849837) * (value_114 h H)

/-- Coordinate 52.0, recovered from nonplanar cycle 14. -/
theorem value_208 (h : Assignment) (H : Constraints h) :
    h 52 0 = ((53540161796728255588055464436 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((-72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (h 1 2) + ((19134279502130384499223111215 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((-57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-397282752613584151101 : ℝ) / 23306367640923510534925481437863313348361188532360) * r0 + ((2881594236232237583160954498735011292965636516503 : ℝ) / 3193225042057723093664543934838762696429799470233973351668959639509796435520) * r1 + ((9 : ℝ) / 9377347264368856785455300084) * r2 + ((-456955243308046941546612221789 : ℝ) / 8993587676036210856805132296664826142766790131953438816) * r3 + ((378169037960063935831363 : ℝ) / 444289101120289438585768456621287728747991486724359221784) * r4 + ((-262225075497133620067646859384886027659872923001773 : ℝ) / 5819366747779169185697650401617087170798893366554321428601425899777186130307054016) * r5 + ((-231439451231559128728794156 : ℝ) / 2344336816092214196363825021) * (value_097 h H) + ((-50806812432100068774808749244587847252382269177873 : ℝ) / 100347983531601031607662370533169978384883403239684) * (value_096 h H) + ((262225075497133620067646859384886027659872923001773 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_098 h H) + ((231439451231559128728794156 : ℝ) / 2344336816092214196363825021) * (value_113 h H) + ((151154795963701100382471119777757825637265672417557 : ℝ) / 100347983531601031607662370533169978384883403239684) * (value_112 h H) + ((-262225075497133620067646859384886027659872923001773 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_114 h H)

/-- Coordinate 52.1, recovered from nonplanar cycle 14. -/
theorem value_209 (h : Assignment) (H : Constraints h) :
    h 52 1 = ((11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (h 1 0) + ((160626840066267720921754585353 : ℝ) / 290697765195434560349114302604) * (h 1 1) + ((-30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (h 1 2) + ((-11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (h 3 0) + ((130070925129166839427359717251 : ℝ) / 290697765195434560349114302604) * (h 5 1) + ((30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((4043466963996211447571115909 : ℝ) / 54309057229703346412736195058063601483871602186630048640) * r0 + ((-752007908156670201305673407778639247968810713716131193 : ℝ) / 190793067446254249697727390410659511936549565146833085113319225820950663824696320) * r1 + ((24135204979061743610335675 : ℝ) / 4364581407487763576164893452252862962433655610750144) * r2 + ((5264055357096691409139713854450474735781674996012918351 : ℝ) / 23720467194811781461289858175694786448502236212859104855335972237953817905462784) * r3 + ((-149758035703563386947078367 : ℝ) / 40282211834906242431776340066996754073151228129675236108416) * r4 + ((68432719642256988318816280107856171565161774948167938563 : ℝ) / 347703283601973506065977479729686547063786679389376335811316129894420353161759606086656) * r5 + ((4043466963996211447571115909 : ℝ) / 9377347264368856785455300084) * (value_097 h H) + ((13259023167373046758818870178652679467588702490059917663 : ℝ) / 5995725117357473904536754864443217428511193421302292544) * (value_096 h H) + ((-68432719642256988318816280107856171565161774948167938563 : ℝ) / 2997862558678736952268377432221608714255596710651146272) * (value_098 h H) + ((5333880300372645337884184175 : ℝ) / 9377347264368856785455300084) * (value_113 h H) + ((-13259023167373046758818870178652679467588702490059917663 : ℝ) / 5995725117357473904536754864443217428511193421302292544) * (value_112 h H) + ((68432719642256988318816280107856171565161774948167938563 : ℝ) / 2997862558678736952268377432221608714255596710651146272) * (value_114 h H)

/-- Coordinate 52.2, recovered from nonplanar cycle 14. -/
theorem value_210 (h : Assignment) (H : Constraints h) :
    h 52 2 = ((35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((-149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((129308514503944045342629379669 : ℝ) / 72674441298858640087278575651) * (h 1 2) + ((-35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((-56634073205085405255350804018 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-531215624692007731647 : ℝ) / 151491389666002818477015629346111536764347725460340) * r0 + ((296387991489832163199975185549618018136425834257 : ℝ) / 1596612521028861546832271967419381348214899735116986675834479819754898217760) * r1 + ((531215624692007731647 : ℝ) / 2690608796345833008826992359602011499982811216794) * r2 + ((-55420921843366733802416154462433678064526473749 : ℝ) / 75897000786755802426731848747520414658132801572115751669565179928186818584) * r3 + ((38896788519114788350597 : ℝ) / 222144550560144719292884228310643864373995743362179610892) * r4 + ((-26971307225574726851197741885015239650414750917387 : ℝ) / 2909683373889584592848825200808543585399446683277160714300712949888593065153527008) * r5 + ((-47609669147396500941130728 : ℝ) / 2344336816092214196363825021) * (value_097 h H) + ((-5225763190878743665149810666045011232913848353287 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_096 h H) + ((26971307225574726851197741885015239650414750917387 : ℝ) / 25086995882900257901915592633292494596220850809921) * (value_098 h H) + ((47609669147396500941130728 : ℝ) / 2344336816092214196363825021) * (value_113 h H) + ((5225763190878743665149810666045011232913848353287 : ℝ) / 50173991765800515803831185266584989192441701619842) * (value_112 h H) + ((-1884311342674468949282149251722745054193900107466 : ℝ) / 25086995882900257901915592633292494596220850809921) * (value_114 h H)

/-- Coordinate 52.3, recovered from nonplanar cycle 14. -/
theorem value_211 (h : Assignment) (H : Constraints h) :
    h 52 3 = ((-18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (h 1 0) + ((8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (h 1 1) + ((-7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (h 1 2) + h 1 3 + ((18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (h 3 0) + ((-8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (h 5 1) + ((7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (h 9 2) := by
  have r0 := H 96 1
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 1 - h 24 1) - ((31983137207357352893966815089 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 96 2
  change ((5791516054445555661356452960 : ℤ) : ℝ) * (h 48 2 - h 24 2) - ((1165208248808023515711074696 : ℤ) : ℝ) * (h 48 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 113 1
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 1 - h 28 1) - ((-449274107110690160841235101 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 113 2
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 2 - h 28 2) - ((21159852954398444862724768 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 113 3
  change ((102861978325137390546130736 : ℤ) : ℝ) * (h 52 3 - h 28 3) - ((-1794845640955164300638976 : ℤ) : ℝ) * (h 52 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 174 1
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 1 - h 48 1) - ((2164490312269148924570614520397613 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 174 2
  change ((-115983730673503098668717441434848 : ℤ) : ℝ) * (h 52 2 - h 48 2) - ((29650187768505659988086977891848 : ℤ) : ℝ) * (h 52 0 - h 48 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((212544288389161242 : ℝ) / 714582026726428389042526553519394041341262855945) * r0 + ((-1162623321298150205724030379693338413126801 : ℝ) / 73835207224790119627833516806297694608532174209997534028601545493659740) * r1 + ((-22529694569251091652 : ℝ) / 1345304398172916504413496179801005749991405608397) * r2 + ((431333252201613726323615270866228551270043171 : ℝ) / 486519235812537195043152876586669324731620522898177895317725512360171914) * r3 + ((1 : ℝ) / 102861978325137390546130736) * r4 + ((-274945717058082766642 : ℝ) / 18512045880012059941073685692553655364499645280181634241) * r5 + ((5607332278620978442206998521260971166510561223 : ℝ) / 7131576896788197531492218629432704866175114419796962535050767034040669277337076) * r6 + ((4038402692149119676437696 : ℝ) / 2344336816092214196363825021) * (value_097 h H) + ((73877626528771814852787874377545267459434957964 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_096 h H) + ((-762597189892453068140151798891492078645436326328 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_098 h H) + ((-4038402692149119676437696 : ℝ) / 2344336816092214196363825021) * (value_113 h H) + ((-73877626528771814852787874377545267459434957964 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_112 h H) + ((762597189892453068140151798891492078645436326328 : ℝ) / 8362331960966752633971864211097498198740283603307) * (value_114 h H) + (1 : ℝ) * (value_115 h H)

/-- Coordinate 68.0, recovered from nonplanar cycle 15. -/
theorem value_272 (h : Assignment) (H : Constraints h) :
    h 68 0 = ((592360119142457741376988247 : ℝ) / 782252171153441540641802252) * (h 1 0) + ((-5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (h 1 1) + ((4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (h 1 2) + ((189892052010983799264814005 : ℝ) / 782252171153441540641802252) * (h 3 0) + ((5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (h 5 1) + ((-4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-27 : ℝ) / 40677112899978960113373717104) * r0 + ((6087793873111237828341919525 : ℝ) / 869769183161367153610622770561335594988148116503599104) * r1 + ((18872052133739110457913 : ℝ) / 27370652954866520312911971639344348244341579126656) * r2 + ((-4255154198252326641550578260532690394616894275975 : ℝ) / 585246807502895003467259267114234357508686894825473556632216135987397574656) * r3 + ((460617865042002733028321 : ℝ) / 20650386866775547166195602454984750793380867468338957232) * r4 + ((-4255154198252326641550578260532690394616894275975 : ℝ) / 18090910996698616947368282418177661958544807042412458222981809939761628410116096) * r5 + ((-634270800162837763379998017 : ℝ) / 5084639112497370014171714638) * (value_097 h H) + ((-176920156218807693408441883987636073522688366373 : ℝ) / 373255611117801187186563510873347624515131642496) * (value_096 h H) + ((12765462594756979924651734781598071183850682827925 : ℝ) / 9704645889062830866850651282707038237393422704896) * (value_098 h H) + ((634270800162837763379998017 : ℝ) / 5084639112497370014171714638) * (value_113 h H) + ((550175767336608880595005394860983698037820008869 : ℝ) / 373255611117801187186563510873347624515131642496) * (value_112 h H) + ((-12765462594756979924651734781598071183850682827925 : ℝ) / 9704645889062830866850651282707038237393422704896) * (value_114 h H)

/-- Coordinate 68.1, recovered from nonplanar cycle 15. -/
theorem value_273 (h : Assignment) (H : Constraints h) :
    h 68 1 = ((-281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (h 1 0) + ((31503118265292785232231262877 : ℝ) / 40677112899978960113373717104) * (h 1 1) + ((-9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (h 1 2) + ((281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (h 3 0) + ((9173994634686174881142454227 : ℝ) / 40677112899978960113373717104) * (h 5 1) + ((9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((20880446715448310685376954031 : ℝ) / 7644534799224813362863963584513448847707942527833772672) * r0 + ((4463630485415337523083213045920005038690122236128062975 : ℝ) / 163457539484663153202126652843500821119303668711623277139106394760834662187548672) * r1 + ((6598888728176883142665587691 : ℝ) / 2453067400426957016524422546204597867050869687647417344) * r2 + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 157356479626918385372248933667538420172075662785514726118817216915203560692908032) * r3 + ((733209858686320349185065299 : ℝ) / 8425357841644423243807805801633778323699393927082294550656) * r4 + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 4864139421504350535872804830340264326117859359107522467329565202123588553884734963712) * r5 + ((20880446715448310685376954031 : ℝ) / 40677112899978960113373717104) * (value_097 h H) + ((-577130983509152204314062725969921177174050064615895949 : ℝ) / 100357982672465440801225704295538722498632474981184512) * (value_096 h H) + ((4463630485415337523083213045920005038690122236128062975 : ℝ) / 869769183161367153610622770561335594988148116503599104) * (value_098 h H) + ((19796666184530649427996763073 : ℝ) / 40677112899978960113373717104) * (value_113 h H) + ((577130983509152204314062725969921177174050064615895949 : ℝ) / 100357982672465440801225704295538722498632474981184512) * (value_112 h H) + ((-4463630485415337523083213045920005038690122236128062975 : ℝ) / 869769183161367153610622770561335594988148116503599104) * (value_114 h H)

/-- Coordinate 68.2, recovered from nonplanar cycle 15. -/
theorem value_274 (h : Assignment) (H : Constraints h) :
    h 68 2 = ((213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (h 1 0) + ((-5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (h 1 1) + ((4791476193002496478955552254 : ℝ) / 2542319556248685007085857319) * (h 1 2) + ((-213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (h 3 0) + ((5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (h 5 1) + ((-2249156636753811471869694935 : ℝ) / 2542319556248685007085857319) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-6891386201919943832205 : ℝ) / 14215936949970270914903678301410055431037710374888) * r0 + ((9513805022008255181599634814519463778016068386073 : ℝ) / 911907187163389009652139230805927101665311014413679801945385135459445361664) * r1 + ((6891386201919943832205 : ℝ) / 13685326477433260156455985819672174122170789563328) * r2 + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 877870211254342505200888900671351536263030342238210334948324203981096361984) * r3 + ((504602611896138109491455 : ℝ) / 30975580300163320749293403682477126190071301202508435848) * r4 + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 27136366495047925421052423627266492937817210563618687334472714909642442615174144) * r5 + ((-231612598860327392256577845 : ℝ) / 2542319556248685007085857319) * (value_097 h H) + ((-602712465732737609454320642470915528617649335995 : ℝ) / 559883416676701780779845266310021436772697463744) * (value_096 h H) + ((9513805022008255181599634814519463778016068386073 : ℝ) / 4852322944531415433425325641353519118696711352448) * (value_098 h H) + ((231612598860327392256577845 : ℝ) / 2542319556248685007085857319) * (value_113 h H) + ((602712465732737609454320642470915528617649335995 : ℝ) / 559883416676701780779845266310021436772697463744) * (value_112 h H) + ((-4661482077476839748174309173165944659319357033625 : ℝ) / 4852322944531415433425325641353519118696711352448) * (value_114 h H)

/-- Coordinate 68.3, recovered from nonplanar cycle 15. -/
theorem value_275 (h : Assignment) (H : Constraints h) :
    h 68 3 = ((-55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (h 1 0) + ((551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (h 1 1) + ((-400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (h 1 2) + h 1 3 + ((55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (h 3 0) + ((-551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (h 5 1) + ((400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 97 3
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 3 - h 24 3) - ((-55341082595537432543614304 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1389331382664902517441 : ℝ) / 7107968474985135457451839150705027715518855187444) * r0 + ((-1906234635814414731502031907435935465648575825 : ℝ) / 924855159394917859687767982561792192358327600825233064853331780384833024) * r1 + ((1 : ℝ) / 187932088937137115075554968) * r2 + ((-81725375450876618673 : ℝ) / 402509602277448828131058406460946297710905575392) * r3 + ((1906234635814414731502031907435935465648575825 : ℝ) / 890334899852274346045526268429362612842829961702038879257935298155270144) * r4 + ((-101729931241796750999291 : ℝ) / 15487790150081660374646701841238563095035650601254217924) * r5 + ((1906234635814414731502031907435935465648575825 : ℝ) / 27521669873273758033521727816700297097177698340384064233745146967183004680704) * r6 + ((93388076879969417417349138 : ℝ) / 2542319556248685007085857319) * (value_097 h H) + ((4189975011136046097829966434266362855217315731 : ℝ) / 9653162356494858289307677005345197185736163168) * (value_096 h H) + ((-32405988808845050435534542426410902916025789025 : ℝ) / 83660740422955438507333200712991708943046747456) * (value_098 h H) + (1 : ℝ) * (value_099 h H) + ((-93388076879969417417349138 : ℝ) / 2542319556248685007085857319) * (value_113 h H) + ((-4189975011136046097829966434266362855217315731 : ℝ) / 9653162356494858289307677005345197185736163168) * (value_112 h H) + ((32405988808845050435534542426410902916025789025 : ℝ) / 83660740422955438507333200712991708943046747456) * (value_114 h H)

/-- Coordinate 72.0, recovered from nonplanar cycle 15. -/
theorem value_288 (h : Assignment) (H : Constraints h) :
    h 72 0 = ((117623495268038676963969274 : ℝ) / 156035158738957144844598529) * (h 1 0) + ((-10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (h 1 1) + ((8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (h 1 2) + ((38411663470918467880629255 : ℝ) / 156035158738957144844598529) * (h 3 0) + ((10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (h 5 1) + ((-8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-4541912989243751698182 : ℝ) / 7089101380635581650263011196688282659059235320315) * r0 + ((40167025183887814339532869887701568814331952193 : ℝ) / 4458267935543443293169707252919769335572309810419150614566252093961332160) * r1 + ((27 : ℝ) / 40569141272128857659595617540) * r2 + ((-8118457840591213861853242457 : ℝ) / 867460504204954902772406354316940215208625346852375040) * r3 + ((110856320737467865522294 : ℝ) / 5148893335807301758810605447365792965709344244681464205) * r4 + ((-40167025183887814339532869887701568814331952193 : ℝ) / 132668317933051923064163599297345806623153564864708889338977748131014632823360) * r5 + ((-1221193229243946006593590704 : ℝ) / 10142285318032214414898904385) * (value_097 h H) + ((-463872253543380163828596694055964593625947984423 : ℝ) / 604930392671713842534091282968945410275585604060) * (value_096 h H) + ((2048518284378278531316176364272780009530929561843 : ℝ) / 1209860785343427685068182565937890820551171208120) * (value_098 h H) + ((1221193229243946006593590704 : ℝ) / 10142285318032214414898904385) * (value_113 h H) + ((1068802646215094006362687977024910003901533588483 : ℝ) / 604930392671713842534091282968945410275585604060) * (value_112 h H) + ((-2048518284378278531316176364272780009530929561843 : ℝ) / 1209860785343427685068182565937890820551171208120) * (value_114 h H)

/-- Coordinate 72.1, recovered from nonplanar cycle 15. -/
theorem value_289 (h : Assignment) (H : Constraints h) :
    h 72 1 = ((64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (h 1 0) + ((18039024383610170800030847157 : ℝ) / 40569141272128857659595617540) * (h 1 1) + ((-1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (h 1 2) + ((-64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (h 3 0) + ((22530116888518686859564770383 : ℝ) / 40569141272128857659595617540) * (h 5 1) + ((1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((5291029487620392184012724037 : ℝ) / 2541414488552333479292688461967962580142099625391646240) * r0 + ((-1590925919576706883212157662350376283016032949392327367 : ℝ) / 54341221541899796392157690625652671342661246445064809836464465763009898957066240) * r1 + ((24696052809267681107557445429 : ℝ) / 7339668242631835169432594679958654715683214846056792320) * r2 + ((1590925919576706883212157662350376283016032949392327367 : ℝ) / 52312933055389159575035921642127570813834012802364812493985439463330159213117440) * r3 + ((-195964055097051562370841631 : ℝ) / 2800997974679172156792969363366991373345883269106716527520) * r4 + ((1590925919576706883212157662350376283016032949392327367 : ℝ) / 1617076084394730995167553385585843597899918053251115051743849670995191541493871063040) * r5 + ((15873088462861176552038172111 : ℝ) / 40569141272128857659595617540) * (value_097 h H) + ((1080761246549379330859226378090605431750980959201692161 : ℝ) / 433730252102477451386203177158470107604312673426187520) * (value_096 h H) + ((-4772777758730120649636472987051128849048098848176982101 : ℝ) / 867460504204954902772406354316940215208625346852375040) * (value_098 h H) + ((24696052809267681107557445429 : ℝ) / 40569141272128857659595617540) * (value_113 h H) + ((-1080761246549379330859226378090605431750980959201692161 : ℝ) / 433730252102477451386203177158470107604312673426187520) * (value_112 h H) + ((4772777758730120649636472987051128849048098848176982101 : ℝ) / 867460504204954902772406354316940215208625346852375040) * (value_114 h H)

/-- Coordinate 72.2, recovered from nonplanar cycle 15. -/
theorem value_290 (h : Assignment) (H : Constraints h) :
    h 72 2 = ((85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (h 1 0) + ((-22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (h 1 1) + ((19216447856148906407574853279 : ℝ) / 10142285318032214414898904385) * (h 1 2) + ((-85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (h 3 0) + ((22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (h 5 1) + ((-9074162538116691992675948894 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-3689891620047561287592 : ℝ) / 7089101380635581650263011196688282659059235320315) * r0 + ((416058743801485280314444486468117907813820579077 : ℝ) / 56842916178178901987913767474727059028546950082844170335719714198006985040) * r1 + ((461236452505945160949 : ℝ) / 853062544936790922984797910339150078346203635705) * r2 + ((-113593547465628359047398844983645202676027777047 : ℝ) / 54721251829228038362041614455385385207053230164037547658117635339721530240) * r3 + ((270182064179038098724792 : ℝ) / 15446680007421905276431816342097378897128032734044392615) * r4 + ((-416058743801485280314444486468117907813820579077 : ℝ) / 1691521053646412019068085891041159034445207952025038339071966288670436568497840) * r5 + ((-992108539665427898517436224 : ℝ) / 10142285318032214414898904385) * (value_097 h H) + ((-282640543507080379369776304332055506279811675091 : ℝ) / 453697794503785381900568462226709057706689203045) * (value_096 h H) + ((416058743801485280314444486468117907813820579077 : ℝ) / 302465196335856921267045641484472705137792802030) * (value_098 h H) + ((992108539665427898517436224 : ℝ) / 10142285318032214414898904385) * (value_113 h H) + ((282640543507080379369776304332055506279811675091 : ℝ) / 453697794503785381900568462226709057706689203045) * (value_112 h H) + ((-113593547465628359047398844983645202676027777047 : ℝ) / 302465196335856921267045641484472705137792802030) * (value_114 h H)

/-- Coordinate 72.3, recovered from nonplanar cycle 15. -/
theorem value_291 (h : Assignment) (H : Constraints h) :
    h 72 3 = ((-44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (h 1 0) + ((2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (h 1 1) + ((-1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (h 1 2) + h 1 3 + ((44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (h 3 0) + ((-2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (h 5 1) + ((1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (h 9 2) := by
  have r0 := H 97 1
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 1 - h 24 1) - ((733209858686320349185065299 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 97 2
  change ((187932088937137115075554968 : ℤ) : ℝ) * (h 68 2 - h 24 2) - ((137251910435749565781675760 : ℤ) : ℝ) * (h 68 0 - h 24 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 114 1
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 1 - h 28 1) - ((-587892165291154687112524893 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 114 2
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 2 - h 28 2) - ((146979042913396725706286848 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 114 3
  change ((180917515443547556532383808 : ℤ) : ℝ) * (h 72 3 - h 28 3) - ((-60535202294100003863055392 : ℤ) : ℝ) * (h 72 0 - h 28 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 214 1
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 1 - h 68 1) - ((157416305070931654765911979816463 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 214 2
  change ((-5592448566439853996290183354728 : ℤ) : ℝ) * (h 72 2 - h 68 2) - ((8661480271276885997993684263152 : ℤ) : ℝ) * (h 72 0 - h 68 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1519729148015319654243 : ℝ) / 7089101380635581650263011196688282659059235320315) * r0 + ((-2780675460283970526406186086833738354214489023 : ℝ) / 922400262526229646862698052328228138394270995259134609910259053923034240) * r1 + ((-89395832236195273779 : ℝ) / 401441197617313375522257840159600036868801710920) * r2 + ((2780675460283970526406186086833738354214489023 : ℝ) / 887971632117290683359701654448444384698632538158824302768643169812925440) * r3 + ((1 : ℝ) / 180917515443547556532383808) * r4 + ((-111277945393566183571793 : ℝ) / 15446680007421905276431816342097378897128032734044392615) * r5 + ((2780675460283970526406186086833738354214489023 : ℝ) / 27448617503390053047757986061519822059962806523732873656340223751244406791040) * r6 + ((408612615485175026075623896 : ℝ) / 10142285318032214414898904385) * (value_097 h H) + ((32112863380584871689977567353677165378868782553 : ℝ) / 125158012276906312248432679234954222815638400840) * (value_096 h H) + ((-47271482824827498948905163476173552021646313391 : ℝ) / 83438674851270874832288452823302815210425600560) * (value_098 h H) + ((-408612615485175026075623896 : ℝ) / 10142285318032214414898904385) * (value_113 h H) + ((-32112863380584871689977567353677165378868782553 : ℝ) / 125158012276906312248432679234954222815638400840) * (value_112 h H) + ((47271482824827498948905163476173552021646313391 : ℝ) / 83438674851270874832288452823302815210425600560) * (value_114 h H) + (1 : ℝ) * (value_115 h H)

/-- Coordinate 64.0, recovered from nonplanar cycle 16. -/
theorem value_256 (h : Assignment) (H : Constraints h) :
    h 64 0 = ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (h 1 0) + ((291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 1 1) + ((-255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 1 2) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (h 3 0) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 5 1) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((811393683605415051318460 : ℝ) / 663681344105394983865718511197506853970787067503) * r0 + ((89688011097938993820652043 : ℝ) / 22565165699583429451434429380715233035006760295102) * r1 + ((296578554055302553528863329541123685854433970 : ℝ) / 3431567474668219302912368509547622398314593017054094771357523868607441) * r2 + ((65565067081439518617206164583593629485708658077 : ℝ) / 233346588277438912598041058649238323085392325159678444452311623065305988) * r3 + ((2520917709470071704995338301099551329762688745 : ℝ) / 32540860721636536313036856703228127524509756998986286691801739437212112) * r4 + ((65565067081439518617206164583593629485708658077 : ℝ) / 260326885773092290504294853625825020196078055991890293534413915497696896) * r5 + ((927697717084986387438284494804634889352669458160 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_101 h H) + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (value_100 h H) + ((3015993085746217856391483570845306956342598271542 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_102 h H) + ((-927697717084986387438284494804634889352669458160 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_109 h H) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (value_108 h H) + ((-3015993085746217856391483570845306956342598271542 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_110 h H)

/-- Coordinate 64.1, recovered from nonplanar cycle 16. -/
theorem value_257 (h : Assignment) (H : Constraints h) :
    h 64 1 = ((-21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (h 1 0) + ((771936032082788798665478471 : ℝ) / 114847936834788935281857860) * (h 1 1) + ((-19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (h 1 2) + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (h 3 0) + ((-657088095247999863383620611 : ℝ) / 114847936834788935281857860) * (h 5 1) + ((19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((135239652957254471780683139353780237678689081061 : ℝ) / 32991847732722971647818439428183602362673925823292567147016120273813156) * r0 + ((11759229082474685400841380760128618026334711253115 : ℝ) / 1121722822912581036025826940558242480330913477991947282998548089309647304) * r1 + ((611707668477864466772498423484859653159765449225 : ℝ) / 2683485765190547494877472174466240715482011739336302111201583665251018862) * r2 + ((11759229082474685400841380760128618026334711253115 : ℝ) / 15867568002865846056666791988148205969806678110858134222757190368440807184) * r3 + ((611707668477864466772498423484859653159765449225 : ℝ) / 2993759186390561340799390816696987732254897643906738375645760028223514304) * r4 + ((11759229082474685400841380760128618026334711253115 : ℝ) / 17702228232570275754292050046556101373333307807448539960340146253843388928) * r5 + ((3110512018016852850955712205136945466609848864403 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_101 h H) + ((-21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (value_100 h H) + ((270462268896917764219351757482958214605698358821645 : ℝ) / 22565165699583429451434429380715233035006760295102) * (value_102 h H) + ((-2446830673911457867089993693939438612639061796900 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_109 h H) + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (value_108 h H) + ((-270462268896917764219351757482958214605698358821645 : ℝ) / 22565165699583429451434429380715233035006760295102) * (value_110 h H)

/-- Coordinate 64.2, recovered from nonplanar cycle 16. -/
theorem value_258 (h : Assignment) (H : Constraints h) :
    h 64 2 = ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 1 0) + ((-10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 1 1) + ((9018608418867289852888476 : ℝ) / 5742396841739446764092893) * (h 1 2) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 3 0) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 5 1) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-550214682645822390832576088684993773662484720 : ℝ) / 485174231363573112467918226885052975921675379754302458044354709909017) * r0 + ((-125527339409406617420150417336595241008044055529 : ℝ) / 44636029285448726347048476873424873784794134937395826140080633311629564) * r1 + ((-275107341322911195416288044342496886831242360 : ℝ) / 3431567474668219302912368509547622398314593017054094771357523868607441) * r2 + ((-15204598446007105869610193510432749734280087019 : ℝ) / 58336647069359728149510264662309580771348081289919611113077905766326497) * r3 + ((-584603100311186290259612094227805884516390015 : ℝ) / 8135215180409134078259214175807031881127439249746571672950434859303028) * r4 + ((-15204598446007105869610193510432749734280087019 : ℝ) / 65081721443273072626073713406456255049019513997972573383603478874424224) * r5 + ((-860535763658066219262149002703330262008126102080 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_101 h H) + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_100 h H) + ((-2133964769959912496142557094722119097136748943993 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_102 h H) + ((860535763658066219262149002703330262008126102080 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_109 h H) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_108 h H) + ((2797646114065307480008275605919625951107536011496 : ℝ) / 663681344105394983865718511197506853970787067503) * (value_110 h H)

/-- Coordinate 64.3, recovered from nonplanar cycle 16. -/
theorem value_259 (h : Assignment) (H : Constraints h) :
    h 64 3 = ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (h 1 0) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 1 1) + ((-36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 1 2) + h 1 3 + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (h 3 0) + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 5 1) + ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 101 3
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 3 - h 25 3) - ((604462459218948328868640 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((35883598287009837482846295745709594872120800 : ℝ) / 55517449360010853665483180190826957443773799673377893209055514069191) * r0 + ((5072149010356347324070833567073385262364020 : ℝ) / 2413802146087428420238399138731606845381469551016430139524152785617) * r1 + ((1 : ℝ) / 1143338598549074470824196) * r2 + ((17941799143504918741423147872854797436060400 : ℝ) / 392666924962035044611863063281568732145450942249971043488671885462543) * r3 + ((2536074505178173662035416783536692631182010 : ℝ) / 17072474998349349765733176664416031832410910532607436673420516759241) * r4 + ((19063161589973976162762094614908222275814175 : ℝ) / 465447634700025084079507278715327694691370902348684448949900501900422) * r5 + ((21556633294014476127301042660061887365047085 : ℝ) / 161894829460878290114611227379244415544824661686498938765182783269712) * r6 + ((2440084683516668948833548110708252451304214400 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_101 h H) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (value_100 h H) + ((7932841052197327214846783698902774550337327280 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_102 h H) + (1 : ℝ) * (value_103 h H) + ((-2440084683516668948833548110708252451304214400 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_109 h H) + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (value_108 h H) + ((-7932841052197327214846783698902774550337327280 : ℝ) / 3301897234355198924705067219888093800849686903) * (value_110 h H)

/-- Coordinate 65.0, recovered from nonplanar cycle 16. -/
theorem value_260 (h : Assignment) (H : Constraints h) :
    h 65 0 = ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (h 1 0) + ((941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 1 1) + ((-823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 1 2) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (h 3 0) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 5 1) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2009949414449318445175543102150514863228724 : ℝ) / 1110277952338059257536807956365218747323331043121299051047043178435) * r0 + ((-176661765318222086994574475637740347559906929 : ℝ) / 37749450379494014756251470516417437408993255466124167735599468066790) * r1 + ((-14188780132307047460758 : ℝ) / 110870615699676288638897051091202587665906802045) * r2 + ((-2494206996321085668079111 : ℝ) / 7539201867577987627444999474201775961281662539060) * r3 + ((-8542285011409603391996058184139688168722077 : ℝ) / 74466857210853079683293035920367470585175353818217648967161699986160) * r4 + ((-176661765318222086994574475637740347559906929 : ℝ) / 595734857686824637466344287362939764681402830545741191737293599889280) * r5 + ((-3143560884198734048254549411763405246089724336 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_101 h H) + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (value_100 h H) + ((-8126441204638216001750425879336055987755718734 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_102 h H) + ((3143560884198734048254549411763405246089724336 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_109 h H) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (value_108 h H) + ((8126441204638216001750425879336055987755718734 : ℝ) / 1518775557529812173135576042345240926930230165) * (value_110 h H)

/-- Coordinate 65.1, recovered from nonplanar cycle 16. -/
theorem value_261 (h : Assignment) (H : Constraints h) :
    h 65 1 = ((-1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (h 1 0) + ((64228273569540695124725957 : ℝ) / 9592902966011722898178950) * (h 1 1) + ((-1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (h 1 2) + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (h 3 0) + ((-54635370603528972226547007 : ℝ) / 9592902966011722898178950) * (h 5 1) + ((1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((12462758961004109873627929604877056113958672713 : ℝ) / 2755709877703063077206357347698472930856507649027064244698761168875670) * r0 + ((4381588875737337762768014261262728951560368492317 : ℝ) / 374776543367616578500064599286992318596485040267680737279031518967091120) * r1 + ((462416296506512765547987710733141993576192142753 : ℝ) / 1793148001826284588570722594496409829339720176553628712597776500379863720) * r2 + ((4381588875737337762768014261262728951560368492317 : ℝ) / 5301481048877710957513440714163298625873955304593337063332556609818727520) * r3 + ((12462758961004109873627929604877056113958672713 : ℝ) / 43488644611138198535043132977494602821742406629839106996822432791917440) * r4 + ((4381588875737337762768014261262728951560368492317 : ℝ) / 5914455667114795000765866084939265983756967301658118551567850859700771840) * r5 + ((573286912206189054186884761824344581242098944798 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_101 h H) + ((-1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (value_100 h H) + ((100776544141958768543664328009042765885888475323291 : ℝ) / 7539201867577987627444999474201775961281662539060) * (value_102 h H) + ((-462416296506512765547987710733141993576192142753 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_109 h H) + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (value_108 h H) + ((-100776544141958768543664328009042765885888475323291 : ℝ) / 7539201867577987627444999474201775961281662539060) * (value_110 h H)

/-- Coordinate 65.2, recovered from nonplanar cycle 16. -/
theorem value_262 (h : Assignment) (H : Constraints h) :
    h 65 2 = ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 1 0) + ((-195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((170624048649954562499929323 : ℝ) / 110318384109134813329057925) * (h 1 2) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 3 0) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2943296506013068108791580540081692482399981746 : ℝ) / 1864156681975601493404300558737202276755872821400661106707985496592365) * r0 + ((-517394072576382095788525389758503863472695483757 : ℝ) / 126762654374340901551492437994129754819399351855244955256143013768280820) * r1 + ((-1471648253006534054395790270040846241199990873 : ℝ) / 13184911778134445504196489665414778156909707180541387592630709561616645) * r2 + ((-314132344138029192213711220424853225569301142901 : ℝ) / 896574000913142294285361297248204914669860088276814356298888250189931860) * r3 + ((-25018020301111078924728434590694386100399844841 : ℝ) / 250059706514044641576498014620593966225018838121574865231728988553525280) * r4 + ((-517394072576382095788525389758503863472695483757 : ℝ) / 2000477652112357132611984116964751729800150704972598921853831908428202240) * r5 + ((-200144162408888631397827476725555088803198758728 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_101 h H) + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_100 h H) + ((-517394072576382095788525389758503863472695483757 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_102 h H) + ((200144162408888631397827476725555088803198758728 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_109 h H) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_108 h H) + ((628264688276058384427422440849706451138602285802 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_110 h H)

/-- Coordinate 65.3, recovered from nonplanar cycle 16. -/
theorem value_263 (h : Assignment) (H : Constraints h) :
    h 65 3 = ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 1 0) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((-8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 1 2) + h 1 3 + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 3 0) + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 101 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 1 - h 25 1) - ((3015589994537552119187015 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 101 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 64 2 - h 25 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 64 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 109 1
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 1 - h 27 1) - ((40404242426792369309362381 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 109 2
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 2 - h 27 2) - ((-14105804765638148649732716 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 109 3
  change ((-16173338539794183554831816 : ℤ) : ℝ) * (h 65 3 - h 27 3) - ((8045014505986044391671664 : ℤ) : ℝ) * (h 65 0 - h 27 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 208 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 1 - h 64 1) - ((-2518546000937577486948747 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 208 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 65 2 - h 64 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 65 0 - h 64 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1678660911568482103083017987529810282853831784 : ℝ) / 1864156681975601493404300558737202276755872821400661106707985496592365) * r0 + ((4339518050677987598926188730216685949390373921 : ℝ) / 1864156681975601493404300558737202276755872821400661106707985496592365) * r1 + ((839330455784241051541508993764905141426915892 : ℝ) / 13184911778134445504196489665414778156909707180541387592630709561616645) * r2 + ((4339518050677987598926188730216685949390373921 : ℝ) / 26369823556268891008392979330829556313819414361082775185261419123233290) * r3 + ((-1 : ℝ) / 16173338539794183554831816) * r4 + ((3567154437083024469051413223500846851064392541 : ℝ) / 62514926628511160394124503655148491556254709530393716307932247138381320) * r5 + ((73771806861525789181745208413683661139636356657 : ℝ) / 500119413028089283152996029241187932450037676243149730463457977107050560) * r6 + ((114148941986656783009645223152027099234060561312 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_101 h H) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_100 h H) + ((295087227446103156726980833654734644558545426628 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_102 h H) + ((-114148941986656783009645223152027099234060561312 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_109 h H) + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_108 h H) + ((-295087227446103156726980833654734644558545426628 : ℝ) / 110870615699676288638897051091202587665906802045) * (value_110 h H) + (1 : ℝ) * (value_111 h H)

/-- Coordinate 50.0, recovered from nonplanar cycle 17. -/
theorem value_200 (h : Assignment) (H : Constraints h) :
    h 50 0 = ((7175518310899585132906597738 : ℝ) / 16734030054361447590207050033) * (h 1 0) + ((266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (h 1 1) + ((-216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (h 1 2) + ((9558511743461862457300452295 : ℝ) / 16734030054361447590207050033) * (h 3 0) + ((-266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (h 5 1) + ((216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-9 : ℝ) / 5706304248537253628260604061253) * r0 + ((1517548617611374584103080195167 : ℝ) / 50013172194531148819181143632993842031167110060714588972632) * r1 + ((9374640217059899270565 : ℝ) / 3244475380485319989683134790833635986269870013102774) * r2 + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 28436357196818668320314669527705604645769614658021618950262679077100036494367056) * r3 + ((15300454460932540042814365 : ℝ) / 133212909051698342703971478945377750877275312585922626826198) * r4 + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 715362332906282584242466264286318290404543945012678844466481124325816585576585176272) * r5 + ((18727756260181429012404782760 : ℝ) / 518754931685204875296418551023) * (value_105 h H) + ((50784208957724455858551476381938255773094952373497 : ℝ) / 105857617979967744660470947144137203190376950330342) * (value_104 h H) + ((-1580719144667027412002914435713724664411022348706595 : ℝ) / 2275938786569306510200125363598949868593104432102353) * (value_106 h H) + ((-18727756260181429012404782760 : ℝ) / 518754931685204875296418551023) * (value_121 h H) + ((55073409022243288801919470762198947417281997956845 : ℝ) / 105857617979967744660470947144137203190376950330342) * (value_120 h H) + ((1580719144667027412002914435713724664411022348706595 : ℝ) / 2275938786569306510200125363598949868593104432102353) * (value_122 h H)

/-- Coordinate 50.1, recovered from nonplanar cycle 17. -/
theorem value_201 (h : Assignment) (H : Constraints h) :
    h 50 1 = ((667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (h 1 0) + ((2505851061725781184189277630845 : ℝ) / 4150039453481639002371348408184) * (h 1 1) + ((-1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (h 1 2) + ((-667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (h 3 0) + ((1644188391755857818182070777339 : ℝ) / 4150039453481639002371348408184) * (h 5 1) + ((1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1282777513222044696730396421777 : ℝ) / 65307168124637655714763570906091129438313348134188287910060) * r0 + ((-176527394083388202929762878568836410235629937618932179431879 : ℝ) / 381591832786455092797068495790095095909038669994034267460829291755233922765115074061760) * r1 + ((-3140749222093164234799811217699 : ℝ) / 71296515900467502531369528146062697387467908451210104339856) * r2 + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 208293889897549283586608287438643856485332655029557540965857035157809854784791165877888) * r3 + ((-116324045262709786474067082137 : ℝ) / 66428837313780240228380444167428371770801289209513416577330736) * r4 + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 5239968044286111926795543362109395711385836542801231453788913095963997352999850547590691456) * r5 + ((2565555026444089393460792843554 : ℝ) / 5706304248537253628260604061253) * (value_105 h H) + ((559122116882098227437080796108418848029603117461565508539 : ℝ) / 70490728956351161126400484331210489120742931727575178256) * (value_104 h H) + ((176527394083388202929762878568836410235629937618932179431879 : ℝ) / 16671057398177049606393714544331280677055703353571529657544) * (value_106 h H) + ((3140749222093164234799811217699 : ℝ) / 5706304248537253628260604061253) * (value_121 h H) + ((-559122116882098227437080796108418848029603117461565508539 : ℝ) / 70490728956351161126400484331210489120742931727575178256) * (value_120 h H) + ((-176527394083388202929762878568836410235629937618932179431879 : ℝ) / 16671057398177049606393714544331280677055703353571529657544) * (value_122 h H)

/-- Coordinate 50.2, recovered from nonplanar cycle 17. -/
theorem value_202 (h : Assignment) (H : Constraints h) :
    h 50 2 = ((7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (h 1 0) + ((-970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (h 1 1) + ((1694800603370947737245720625373 : ℝ) / 1037509863370409750592837102046) * (h 1 2) + ((-7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (h 3 0) + ((970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (h 5 1) + ((-657290740000537986652883523327 : ℝ) / 1037509863370409750592837102046) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((20982234148533411580719 : ℝ) / 130764453842286256051474234233081836825302143128688310) * r0 + ((-73335984217544876883774097251033356309453036943373 : ℝ) / 1567840234021440852664118993242115118781691080378198662327673475943408708019440) * r1 + ((-20982234148533411580719 : ℝ) / 71378458370677039773028965398339991697937140288261028) * r2 + ((82277933918617715758979234682057822166555174403579 : ℝ) / 14548833914651411698765644874640076795510035406429665509436719527818623322699424) * r3 + ((-796403197436194528964293 : ℝ) / 68155441840403803243892384576704895797675741323030181166892) * r4 + ((82277933918617715758979234682057822166555174403579 : ℝ) / 365999333114842252403122274751139590439534111401835687866571738027161974015927299488) * r5 + ((-20958146543730895224224334588 : ℝ) / 5706304248537253628260604061253) * (value_105 h H) + ((11205891025796635388527829095130794675072495324277 : ℝ) / 211715235959935489320941894288274406380753900660684) * (value_104 h H) + ((1246711731698262907024159653267567057260701628037341 : ℝ) / 1164433797779645191265180418585509235094146453633762) * (value_106 h H) + ((20958146543730895224224334588 : ℝ) / 5706304248537253628260604061253) * (value_121 h H) + ((-11205891025796635388527829095130794675072495324277 : ℝ) / 211715235959935489320941894288274406380753900660684) * (value_120 h H) + ((-82277933918617715758979234682057822166555174403579 : ℝ) / 1164433797779645191265180418585509235094146453633762) * (value_122 h H)

/-- Coordinate 50.3, recovered from nonplanar cycle 17. -/
theorem value_203 (h : Assignment) (H : Constraints h) :
    h 50 3 = ((-3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (h 1 0) + ((14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (h 1 1) + ((-15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (h 1 2) + h 1 3 + ((3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (h 3 0) + ((-14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (h 5 1) + ((15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 105 3
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 3 - h 26 3) - ((4277405041606171325713171728 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((19270445158269464310738 : ℝ) / 65382226921143128025737117116540918412651071564344155) * r0 + ((-31856032037786091581927580936923396588365374916997 : ℝ) / 5618094171910163055379759725784245842301059704688545206674163288797214537069660) * r1 + ((-1 : ℝ) / 22889479873555079904050290040) * r2 + ((-9635222579134732155369 : ℝ) / 17844614592669259943257241349584997924484285072065257) * r3 + ((31856032037786091581927580936923396588365374916997 : ℝ) / 3066665972205934818857464360830996579445742757237625573067543822040200014098408) * r4 + ((-5241917943144817801119083 : ℝ) / 244223666594780294957281044733192543275004739740858149181363) * r5 + ((31856032037786091581927580936923396588365374916997 : ℝ) / 77146918254599102222226753991661776416176307795484973422855807525333161189631734696) * r6 + ((-38496645374455541931418545552 : ℝ) / 5706304248537253628260604061253) * (value_105 h H) + ((1715280547450279317509112058514906295014834943409 : ℝ) / 17642936329994624110078491190689533865062825055057) * (value_104 h H) + ((1083105089284727113785537751855395484004422747177898 : ℝ) / 8345108884087457204067126333196149518174716251041961) * (value_106 h H) + (1 : ℝ) * (value_107 h H) + ((38496645374455541931418545552 : ℝ) / 5706304248537253628260604061253) * (value_121 h H) + ((-1715280547450279317509112058514906295014834943409 : ℝ) / 17642936329994624110078491190689533865062825055057) * (value_120 h H) + ((-1083105089284727113785537751855395484004422747177898 : ℝ) / 8345108884087457204067126333196149518174716251041961) * (value_122 h H)

/-- Coordinate 54.0, recovered from nonplanar cycle 17. -/
theorem value_216 (h : Assignment) (H : Constraints h) :
    h 54 0 = ((61892404734917835710766598981 : ℝ) / 144175784701405287264620066096) * (h 1 0) + ((73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (h 1 1) + ((-120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (h 1 2) + ((82283379966487451553853467115 : ℝ) / 144175784701405287264620066096) * (h 3 0) + ((-73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (h 5 1) + ((120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-232599827334136148901 : ℝ) / 150177345509773707416010650654038312102556943029360) * r0 + ((16031952052697942114350543439143839153562329484831 : ℝ) / 188033773413807612055551011496496721678013456805291779770230803552585737013120) * r1 + ((9 : ℝ) / 3171867263430916319821641454112) * r2 + ((-4342277425120606374804115512653 : ℝ) / 27799979937072410827970810639586916212136448514769669340928) * r3 + ((4175916388980264978141631 : ℝ) / 37023408399209845576155098142071340424354213851888696777696) * r4 + ((-176351472579677363257855977830582230689185624333141 : ℝ) / 28402601083312472258539969612409683856371284358727865456004595002898763206792347392) * r5 + ((638915207513980541655669543 : ℝ) / 18021973087675660908077508262) * (value_105 h H) + ((1437215905628960793266328964637293386289813708427 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_104 h H) + ((-176351472579677363257855977830582230689185624333141 : ℝ) / 90363412317705696360105851646218807932208930770608) * (value_106 h H) + ((-638915207513980541655669543 : ℝ) / 18021973087675660908077508262) * (value_121 h H) + ((2765733504496885549064175763093813959394322606485 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_120 h H) + ((176351472579677363257855977830582230689185624333141 : ℝ) / 90363412317705696360105851646218807932208930770608) * (value_122 h H)

/-- Coordinate 54.1, recovered from nonplanar cycle 17. -/
theorem value_217 (h : Assignment) (H : Constraints h) :
    h 54 1 = ((42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (h 1 0) + ((1291636951393455771186204299781 : ℝ) / 2306812555222484596233921057536) * (h 1 1) + ((-516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (h 1 2) + ((-42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (h 3 0) + ((1015175603829028825047716757755 : ℝ) / 2306812555222484596233921057536) * (h 5 1) + ((516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1369771478981662774644264840507 : ℝ) / 72602391887890187804750182086710338442207392506840950644480) * r0 + ((220293621139116275099655691756821976044580630501799614275373 : ℝ) / 212109027084951321462165092504264047593297935281702361562100304087761254924284680919040) * r1 + ((-106005634379367855598669212565 : ℝ) / 2331199638069481864864098287886009750841025799896907254272) * r2 + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 115780817454323120548958573347774633292063643681547587716992334754520173048787616305152) * r3 + ((50732276999320843505343142241 : ℝ) / 36924679310145285987952017880359150183222602614950326919622144) * r4 + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 2912652809452933166146415681335582787368561466093162042290006444057771370467444177125249024) * r5 + ((1369771478981662774644264840507 : ℝ) / 3171867263430916319821641454112) * (value_105 h H) + ((163212027960856735574917150558898029156774064200447177721 : ℝ) / 39182494625894870793475420210834272321545381979943156224) * (value_104 h H) + ((-220293621139116275099655691756821976044580630501799614275373 : ℝ) / 9266659979024136942656936879862305404045482838256556446976) * (value_106 h H) + ((1802095784449253545177376613605 : ℝ) / 3171867263430916319821641454112) * (value_121 h H) + ((-163212027960856735574917150558898029156774064200447177721 : ℝ) / 39182494625894870793475420210834272321545381979943156224) * (value_120 h H) + ((220293621139116275099655691756821976044580630501799614275373 : ℝ) / 9266659979024136942656936879862305404045482838256556446976) * (value_122 h H)

/-- Coordinate 54.2, recovered from nonplanar cycle 17. -/
theorem value_218 (h : Assignment) (H : Constraints h) :
    h 54 2 = ((65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (h 1 0) + ((-269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (h 1 1) + ((471192179276402318567845397545 : ℝ) / 288351569402810574529240132192) * (h 1 2) + ((-65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (h 3 0) + ((269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (h 5 1) + ((-182840609873591744038605265353 : ℝ) / 288351569402810574529240132192) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((3262064912803509072687 : ℝ) / 18171458806682618597337288729138635764409390106552560) * r0 + ((-5228789527554336187013797930739844573045051179479 : ℝ) / 529118292629551652528410985838979147047433215661402450051114586740997073920640) * r1 + ((-466009273257644153241 : ℝ) / 1416997922442864111667682746008924165095009020292704) * r2 + ((-17887432228137818695803978071781245828217698552537 : ℝ) / 288821976568443897220982877748409243476120994746356494291141416611685929023232) * r3 + ((-123815171845402441262789 : ℝ) / 9471104474216472124132699524715924294602240752808736384992) * r4 + ((5228789527554336187013797930739844573045051179479 : ℝ) / 7265781672475283601021852691546663312094979719674570232931408023997358029644553984) * r5 + ((-814580015570902661067888831 : ℝ) / 198241703964432269988852590882) * (value_105 h H) + ((-166578848451764286967595738859096050709222140969 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_104 h H) + ((5228789527554336187013797930739844573045051179479 : ℝ) / 23116221755692154882817776002521090401262749732016) * (value_106 h H) + ((814580015570902661067888831 : ℝ) / 198241703964432269988852590882) * (value_121 h H) + ((166578848451764286967595738859096050709222140969 : ℝ) / 4202949410125846342330504727731107345684136314912) * (value_120 h H) + ((17887432228137818695803978071781245828217698552537 : ℝ) / 23116221755692154882817776002521090401262749732016) * (value_122 h H)

/-- Coordinate 54.3, recovered from nonplanar cycle 17. -/
theorem value_219 (h : Assignment) (H : Constraints h) :
    h 54 3 = ((-8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (h 1 0) + ((1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (h 1 1) + ((-2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (h 1 2) + h 1 3 + ((8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (h 3 0) + ((-1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (h 5 1) + ((2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (h 9 2) := by
  have r0 := H 105 1
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 1 - h 26 1) - ((348972135788129359422201246411 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 105 2
  change ((-22889479873555079904050290040 : ℤ) : ℝ) * (h 50 2 - h 26 2) - ((2328682949303432802691592732 : ℤ) : ℝ) * (h 50 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 120 1
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 1 - h 30 1) - ((-152196830997962530516029426723 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 120 2
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 2 - h 30 2) - ((1448142249903826953009580144 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 120 3
  change ((-12494341835828952814599759952 : ℤ) : ℝ) * (h 54 3 - h 30 3) - ((2357449182116273216713998912 : ℤ) : ℝ) * (h 54 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 178 1
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 1 - h 50 1) - ((8591864554531544450136414895379003 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 178 2
  change ((314315278217390882892551566236624 : ℤ) : ℝ) * (h 54 2 - h 50 2) - ((211152086777625240033355799810448 : ℤ) : ℝ) * (h 54 0 - h 50 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((1327589237384921574369 : ℝ) / 4542864701670654649334322182284658941102347526638140) * r0 + ((-12559391667384807653437740857072762424557577995623 : ℝ) / 780708853340661997112998562438885898339595087814128124830321032397255486520160) * r1 + ((-1327589237384921574369 : ℝ) / 2479746364275012195418444805515617288916265785512232) * r2 + ((12559391667384807653437740857072762424557577995623 : ℝ) / 426153994838733397370175716677799913168198134405163258733497874510379728607808) * r3 + ((-1 : ℝ) / 12494341835828952814599759952) * r4 + ((-722257715109152333552083 : ℝ) / 33938124365942358444808839963565395388991362697564638712888) * r5 + ((12559391667384807653437740857072762424557577995623 : ℝ) / 10720589624583629234841066961546792435983278900108066863295852035407866504524562496) * r6 + ((-663032582470201842200812194 : ℝ) / 99120851982216134994426295441) * (value_105 h H) + ((-158185898200834842079722795151971029726943328507 : ℝ) / 2451720489240077033026127757843145951649079517032) * (value_104 h H) + ((213509658345541730108441594570236961217478825925591 : ℝ) / 579831895705278218310679214729904017565007305778068) * (value_106 h H) + ((663032582470201842200812194 : ℝ) / 99120851982216134994426295441) * (value_121 h H) + ((158185898200834842079722795151971029726943328507 : ℝ) / 2451720489240077033026127757843145951649079517032) * (value_120 h H) + ((-213509658345541730108441594570236961217478825925591 : ℝ) / 579831895705278218310679214729904017565007305778068) * (value_122 h H) + (1 : ℝ) * (value_123 h H)

/-- Coordinate 70.0, recovered from nonplanar cycle 18. -/
theorem value_280 (h : Assignment) (H : Constraints h) :
    h 70 0 = ((2792769390001120810127813548 : ℝ) / 6204441341809179666130037393) * (h 1 0) + ((35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (h 1 1) + ((-30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (h 1 2) + ((3411671951808058856002223845 : ℝ) / 6204441341809179666130037393) * (h 3 0) + ((-35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (h 5 1) + ((30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-108 : ℝ) / 887235111878712692256595347199) * r0 + ((-98207707482786162666627588359 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * r1 + ((-615936094244448687162 : ℝ) / 173256020829145698777409744428212803701084599579) * r2 + ((-1120179106882381970990518927857763347969031554577 : ℝ) / 64566499058932026464947888965153318851347007442544719118979738161072657140) * r3 + ((167546023858457532698567 : ℝ) / 1815083188973145165763269636249208054296535712931590525706) * r4 + ((160025586697483138712931275408251906852718793511 : ℝ) / 355237599186509864734980813519763567630060940303274759952318783494875148300052080) * r5 + ((615228999608256060069138024 : ℝ) / 80657737443519335659690486109) * (value_105 h H) + ((1305993054546028114482003644609955014672541255479 : ℝ) / 1543224762260383973391762377509131775565745837210) * (value_104 h H) + ((1120179106882381970990518927857763347969031554577 : ℝ) / 30092882864077487481139366361428069623532043825595) * (value_106 h H) + ((-615228999608256060069138024 : ℝ) / 80657737443519335659690486109) * (value_121 h H) + ((237231707714355858909758732899176760893204581731 : ℝ) / 1543224762260383973391762377509131775565745837210) * (value_120 h H) + ((-1120179106882381970990518927857763347969031554577 : ℝ) / 30092882864077487481139366361428069623532043825595) * (value_122 h H)

/-- Coordinate 70.1, recovered from nonplanar cycle 18. -/
theorem value_281 (h : Assignment) (H : Constraints h) :
    h 70 1 = ((-1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (h 1 0) + ((244477053615011092885956197129 : ℝ) / 322630949774077342638761944436) * (h 1 1) + ((-138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (h 1 2) + ((1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (h 3 0) + ((78153896159066249752805747307 : ℝ) / 322630949774077342638761944436) * (h 5 1) + ((138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-454138090761673090274427569275 : ℝ) / 55596115493361621095292921855629684824058385845761673542) * r0 + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 10359370258833011344664010158059626359729595295794741498348506738621125388273083860) * r1 + ((108274255279259900495541944481 : ℝ) / 475907088022393058666836514614425342356698324761379097) * r2 + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 354708071949068048742113708337417275627181135929003727797871321819150601512818040) * r3 + ((-4010157602935551870205257203 : ℝ) / 678841112675956291995462843957203812306904356636414856614044) * r4 + ((-56261197832709374108868091686373862913843954508457671411 : ℝ) / 1951563825324540632756457805502135834799318966890936302903414368422826673963919911166880) * r5 + ((454138090761673090274427569275 : ℝ) / 887235111878712692256595347199) * (value_105 h H) + ((83405037377805661034005518349144588093441252798931217631 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * (value_104 h H) + ((-393828384828965618762076641804617040396907681559203699877 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * (value_106 h H) + ((433097021117039601982167777924 : ℝ) / 887235111878712692256595347199) * (value_121 h H) + ((-83405037377805661034005518349144588093441252798931217631 : ℝ) / 8477992271283199789246697488648632107580679985438856060) * (value_120 h H) + ((393828384828965618762076641804617040396907681559203699877 : ℝ) / 165320849290022395890310601028648326097823259716057693170) * (value_122 h H)

/-- Coordinate 70.2, recovered from nonplanar cycle 18. -/
theorem value_282 (h : Assignment) (H : Constraints h) :
    h 70 2 = ((3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (h 1 0) + ((-164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (h 1 1) + ((139000283339831846805438863309 : ℝ) / 80657737443519335659690486109) * (h 1 2) + ((-3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (h 3 0) + ((164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (h 5 1) + ((-58342545896312511145748377200 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((130370401105101752457006 : ℝ) / 111320026377004042831756700403322383744655636362067) * r0 + ((-141647942138152594705359580999092964383120712661813 : ℝ) / 13828368645649220431273782513071174187606833038721440878593300760768195739740) * r1 + ((65185200552550876228503 : ℝ) / 1905816229120602686551507188710340840711930595369) * r2 + ((79033198865082313489662438984712879522780942059217 : ℝ) / 473487659765501527409617852411124338243211387911994606872518079847866152360) * r3 + ((-11821054455758269394080007 : ℝ) / 13310610052469731215597310665827525731507928561498330521844) * r4 + ((-11290456980726044784237491283530411360397277437031 : ℝ) / 2605075727367739008056525965811599495953780228890681572983671078962417754200381920) * r5 + ((-65110367942316547822592678556 : ℝ) / 887235111878712692256595347199) * (value_105 h H) + ((16737663305534602825380752413048590659463469855651 : ℝ) / 11316981589909482471539590768400299687482136139540) * (value_104 h H) + ((141647942138152594705359580999092964383120712661813 : ℝ) / 220681141003234908195022019983805843905901654721030) * (value_106 h H) + ((65110367942316547822592678556 : ℝ) / 887235111878712692256595347199) * (value_121 h H) + ((-16737663305534602825380752413048590659463469855651 : ℝ) / 11316981589909482471539590768400299687482136139540) * (value_120 h H) + ((79033198865082313489662438984712879522780942059217 : ℝ) / 220681141003234908195022019983805843905901654721030) * (value_122 h H)

/-- Coordinate 70.3, recovered from nonplanar cycle 18. -/
theorem value_283 (h : Assignment) (H : Constraints h) :
    h 70 3 = ((-1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (h 1 0) + ((9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (h 1 1) + ((-5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (h 1 2) + h 1 3 + ((1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (h 3 0) + ((-9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (h 5 1) + ((5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 106 3
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 3 - h 26 3) - ((-226560544008554793078211948 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-48993321839319373946184 : ℝ) / 111320026377004042831756700403322383744655636362067) * r0 + ((-1310327292975456427839420823325372620244645144573 : ℝ) / 610075087308053842556196287341375331806183810531828274055586798269185106165) * r1 + ((-1 : ℝ) / 62662212923063117229264058) * r2 + ((-24496660919659686973092 : ℝ) / 1905816229120602686551507188710340840711930595369) * r3 + ((-1310327292975456427839420823325372620244645144573 : ℝ) / 20889161460242714444541964076961367863671090643176232656140503522699977310) * r4 + ((49727950835942667488633 : ℝ) / 148999366258989528532805716408517079084043976434682804349) * r5 + ((2793874825107583001789809857836615394977921417 : ℝ) / 1715370320918177573347141768532659896369916744221256523035779902740836975987960) * r6 + ((24468538752923917652446890384 : ℝ) / 887235111878712692256595347199) * (value_105 h H) + ((-4717522448817560538070579572726999896707387467223 : ℝ) / 8487736192432111853654693076300224765611602104655) * (value_104 h H) + ((44551127961165518546540307993062669088317934915482 : ℝ) / 331021711504852362292533029975708765858852482081545) * (value_106 h H) + (1 : ℝ) * (value_107 h H) + ((-24468538752923917652446890384 : ℝ) / 887235111878712692256595347199) * (value_121 h H) + ((4717522448817560538070579572726999896707387467223 : ℝ) / 8487736192432111853654693076300224765611602104655) * (value_120 h H) + ((-44551127961165518546540307993062669088317934915482 : ℝ) / 331021711504852362292533029975708765858852482081545) * (value_122 h H)

/-- Coordinate 74.0, recovered from nonplanar cycle 18. -/
theorem value_296 (h : Assignment) (H : Constraints h) :
    h 74 0 = ((281513443010244406222779958 : ℝ) / 617308285460186573299724243) * (h 1 0) + ((16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (h 1 1) + ((-14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (h 1 2) + ((335794842449942167076944285 : ℝ) / 617308285460186573299724243) * (h 3 0) + ((-16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (h 5 1) + ((14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((21089844167602855068 : ℝ) / 5034426941076396758397738451793612955734288923735) * r0 + ((-5832163527248582748141590948067132266801341663 : ℝ) / 187615599618220791105629469274203263444801636855116576474089805671678194010) * r1 + ((54 : ℝ) / 441375424104033399909302833745) * r2 + ((-29866207447394361881616210803 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * r3 + ((-2868414083128873500869 : ℝ) / 902954697792258126647372669685319987396114004809256067030) * r4 + ((833166218178368964020227278295304609543048809 : ℝ) / 35344215732543832349837673358301042152449600664328141855518498852917231165088080) * r5 + ((-10532816513249223495190968 : ℝ) / 40125038554912127264482075795) * (value_105 h H) + ((3875746513861291815278596306243072245532474421 : ℝ) / 1996052494438989105592348083556037672397568162230) * (value_104 h H) + ((5832163527248582748141590948067132266801341663 : ℝ) / 2994078741658483658388522125334056508596352243345) * (value_106 h H) + ((10532816513249223495190968 : ℝ) / 40125038554912127264482075795) * (value_121 h H) + ((1992176747925127813777069487249794600152035687809 : ℝ) / 1996052494438989105592348083556037672397568162230) * (value_120 h H) + ((-5832163527248582748141590948067132266801341663 : ℝ) / 2994078741658483658388522125334056508596352243345) * (value_122 h H)

/-- Coordinate 74.1, recovered from nonplanar cycle 18. -/
theorem value_297 (h : Assignment) (H : Constraints h) :
    h 74 1 = ((234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (h 1 0) + ((148719343766200154698074751953 : ℝ) / 321000308439297018115856606360) * (h 1 1) + ((-39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (h 1 2) + ((-234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (h 3 0) + ((172280964673096863417781854407 : ℝ) / 321000308439297018115856606360) * (h 5 1) + ((39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-86680596277490302948284144729 : ℝ) / 13828780402107112901027519082140123192168041390139018605) * r0 + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 2061402386008449810011842273078241259082037050336075929087273056322438181876041720) * r1 + ((268014231549052794012734544287 : ℝ) / 947003516870347515813023089075815481187413674178254940) * r2 + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 70583061284908199984481178809919638956941632451770345978121570223853064083472080) * r3 + ((3210392454721863072158672027 : ℝ) / 675410113948609078732234756924619350572293275597323538138440) * r4 + ((-13697463862896110515512889803406888297911535002881615383 : ℝ) / 388340046301711592333300656802142838116644473750420424635351999778574904020816147725760) * r5 + ((173361192554980605896568289458 : ℝ) / 441375424104033399909302833745) * (value_105 h H) + ((-63718255321767336390046129736069442460104761696085335627 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * (value_104 h H) + ((-95882247040272773608590228623848218085380745020171307681 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * (value_106 h H) + ((268014231549052794012734544287 : ℝ) / 441375424104033399909302833745) * (value_121 h H) + ((63718255321767336390046129736069442460104761696085335627 : ℝ) / 21931371287929104607090408747517268752646213293777359560) * (value_120 h H) + ((95882247040272773608590228623848218085380745020171307681 : ℝ) / 32897056931893656910635613121275903128969319940666039340) * (value_122 h H)

/-- Coordinate 74.2, recovered from nonplanar cycle 18. -/
theorem value_298 (h : Assignment) (H : Constraints h) :
    h 74 2 = ((314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (h 1 0) + ((-82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (h 1 1) + ((69571840443901781045647078438 : ℝ) / 40125038554912127264482075795) * (h 1 2) + ((-314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (h 3 0) + ((82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (h 5 1) + ((-29446801888989653781165002643 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((72087229224999271582938 : ℝ) / 55378696351840364342375122969729742513077178161085) * r0 + ((-13289951495936405795540667827846574975326637691847 : ℝ) / 1375847730533619134774616108010823931928545336937521560809991908258973422740) * r1 + ((36043614612499635791469 : ℝ) / 948091926401856847473923152855293357962354457095) * r2 + ((8666625942892474365975161091269839421046612092683 : ℝ) / 47109455845249146009272764340075499311170311819148613260103645801281914360) * r3 + ((-6536353765963051236307261 : ℝ) / 6621667783809892928747399577692346574238169368601211158220) * r4 + ((1898564499419486542220095403978082139332376813121 : ℝ) / 259190915371988103898809604627540975784630404871739706940468991588059695210645920) * r5 + ((-36002236542924486209580393588 : ℝ) / 441375424104033399909302833745) * (value_105 h H) + ((8831796800468169136271684327905010020524144680749 : ℝ) / 14637718292552586774343885946077609597582166523020) * (value_104 h H) + ((13289951495936405795540667827846574975326637691847 : ℝ) / 21956577438828880161515828919116414396373249784530) * (value_106 h H) + ((36002236542924486209580393588 : ℝ) / 441375424104033399909302833745) * (value_121 h H) + ((-8831796800468169136271684327905010020524144680749 : ℝ) / 14637718292552586774343885946077609597582166523020) * (value_120 h H) + ((8666625942892474365975161091269839421046612092683 : ℝ) / 21956577438828880161515828919116414396373249784530) * (value_122 h H)

/-- Coordinate 74.3, recovered from nonplanar cycle 18. -/
theorem value_299 (h : Assignment) (H : Constraints h) :
    h 74 3 = ((-162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (h 1 0) + ((4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (h 1 1) + ((-3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (h 1 2) + h 1 3 + ((162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (h 3 0) + ((-4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (h 5 1) + ((3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (h 9 2) := by
  have r0 := H 106 1
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 1 - h 26 1) - ((4010157602935551870205257203 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 106 2
  change ((-62662212923063117229264058 : ℤ) : ℝ) * (h 70 2 - h 26 2) - ((602873777243671739098080357 : ℤ) : ℝ) * (h 70 0 - h 26 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 121 1
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 1 - h 30 1) - ((-3210392454721863072158672027 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 121 2
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 2 - h 30 2) - ((666708084128231226103340622 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 121 3
  change ((2145573734180397378650012 : ℤ) : ℝ) * (h 74 3 - h 30 3) - ((-260646954530371667362044088 : ℤ) : ℝ) * (h 74 0 - h 30 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 218 1
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 1 - h 70 1) - ((1247144510868860900184089957586887 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 218 2
  change ((82632933691904661223484557708848 : ℤ) : ℝ) * (h 74 2 - h 70 2) - ((85695608510692968848737482227088 : ℤ) : ℝ) * (h 74 0 - h 70 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-28182224282756744818152 : ℝ) / 55378696351840364342375122969729742513077178161085) * r0 + ((229220086263019531801102380170335255566985711573 : ℝ) / 60699164582365550063586004765183408761553470747243598271029054776131180415) * r1 + ((-14091112141378372409076 : ℝ) / 948091926401856847473923152855293357962354457095) * r2 + ((229220086263019531801102380170335255566985711573 : ℝ) / 2078358346113932912173798426768036734316337286138909408533984373585966810) * r3 + ((1 : ℝ) / 2145573734180397378650012) * r4 + ((28604801858030253222349 : ℝ) / 74123146833692831291948502735362088517591448155983706995) * r5 + ((-488742188194071496377617015288561312509564417 : ℝ) / 170670049630369690890348730000575708374427395657422985254918124399512529769960) * r6 + ((14074935544640070037550380752 : ℝ) / 441375424104033399909302833745) * (value_105 h H) + ((-2589567676477683451056682597346697693386412662647 : ℝ) / 10978288719414440080757914459558207198186624892265) * (value_104 h H) + ((-7793482932942664081237480925791398689277514193482 : ℝ) / 32934866158243320242273743378674621594559874676795) * (value_106 h H) + ((-14074935544640070037550380752 : ℝ) / 441375424104033399909302833745) * (value_121 h H) + ((2589567676477683451056682597346697693386412662647 : ℝ) / 10978288719414440080757914459558207198186624892265) * (value_120 h H) + ((7793482932942664081237480925791398689277514193482 : ℝ) / 32934866158243320242273743378674621594559874676795) * (value_122 h H) + (1 : ℝ) * (value_123 h H)

/-- Coordinate 66.0, recovered from nonplanar cycle 19. -/
theorem value_264 (h : Assignment) (H : Constraints h) :
    h 66 0 = ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (h 1 0) + ((291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 1 1) + ((-255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 1 2) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (h 3 0) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (h 5 1) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-811393683605415051318460 : ℝ) / 517873774355332710498418715050165112570420769167) * r0 + ((71455183697356183931117077 : ℝ) / 17607708328081312156946236311705613827394306151678) * r1 + ((-593157108110605107057726659082247371708867940 : ℝ) / 2677668757522307941797664061715133457117348355716374364457589131088049) * r2 + ((52236233751663614334210416283161668115738593603 : ℝ) / 91040737755758470021120578098314537541989844094356728391558030456993666) * r3 + ((-2520917709470071704995338301099551329762688745 : ℝ) / 25391791576423973272589368714560470566582147455845819153857557553903568) * r4 + ((52236233751663614334210416283161668115738593603 : ℝ) / 203134332611391786180714949716483764532657179646766553230860460431228544) * r5 + ((-927697717084986387438284494804634889352669458160 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_117 h H) + ((131972807462839763526612 : ℝ) / 249669427901715076699691) * (value_116 h H) + ((2402866752576526259373679149025436733323975305738 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_118 h H) + ((927697717084986387438284494804634889352669458160 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_125 h H) + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (value_124 h H) + ((-2402866752576526259373679149025436733323975305738 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_126 h H)

/-- Coordinate 66.1, recovered from nonplanar cycle 19. -/
theorem value_265 (h : Assignment) (H : Constraints h) :
    h 66 1 = ((251753206123348448905855 : ℝ) / 253395837273382465904164) * (h 1 0) + ((-7226762153765448547821267 : ℝ) / 1714148310966999034057580) * (h 1 1) + ((214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (h 1 2) + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (h 3 0) + ((8940910464732447581878847 : ℝ) / 1714148310966999034057580) * (h 5 1) + ((-214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1604827183273609902100805769552786138329276487 : ℝ) / 384234312392437198995902224465650726762480338972134597335141714960652) * r0 + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 300471232290885889614795539532138868328259625076209255116080821099229864) * r1 + ((7295391474139179659100458865039844502220127975 : ℝ) / 15626395286436155302132636539262943010938555329628393679148020153066077) * r2 + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 2125189758955317121090038569339760249487643524829461540364130740816986472) * r3 + ((7295391474139179659100458865039844502220127975 : ℝ) / 34866340672104560314600327190142735703366530834892766599326795447151168) * r4 + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 4741822331406220202785644497859412055657848193545416257508444180812558848) * r5 + ((36911025215293027748318532699714081181573359201 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_117 h H) + ((251753206123348448905855 : ℝ) / 253395837273382465904164) * (value_116 h H) + ((-2569867369991748443419461387910468335595507969405 : ℝ) / 262801616837034509805167706144859907871556808234) * (value_118 h H) + ((-29181565896556718636401835460159378008880511900 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_125 h H) + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (value_124 h H) + ((2569867369991748443419461387910468335595507969405 : ℝ) / 262801616837034509805167706144859907871556808234) * (value_126 h H)

/-- Coordinate 66.2, recovered from nonplanar cycle 19. -/
theorem value_266 (h : Assignment) (H : Constraints h) :
    h 66 2 = ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 1 0) + ((-10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 1 1) + ((9018608418867289852888476 : ℝ) / 5742396841739446764092893) * (h 1 2) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (h 3 0) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (h 5 1) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((550214682645822390832576088684993773662484720 : ℝ) / 378583807798430769598903662341155863133620333987250265021389630917113) * r0 + ((-100649066561508782968367800768776737696362181881 : ℝ) / 34829710317455630803099136935386339408293070726827024381967846044374396) * r1 + ((550214682645822390832576088684993773662484720 : ℝ) / 2677668757522307941797664061715133457117348355716374364457589131088049) * r2 + ((-24227259846749804575659470957819235363136715882 : ℝ) / 45520368877879235010560289049157268770994922047178364195779015228496833) * r3 + ((584603100311186290259612094227805884516390015 : ℝ) / 6347947894105993318147342178640117641645536863961454788464389388475892) * r4 + ((-12113629923374902287829735478909617681568357941 : ℝ) / 50783583152847946545178737429120941133164294911691638307715115107807136) * r5 + ((860535763658066219262149002703330262008126102080 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_117 h H) + ((109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_116 h H) + ((-1711034131545649310462252613069204540838157091977 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_118 h H) + ((-860535763658066219262149002703330262008126102080 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_125 h H) + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (value_124 h H) + ((2228907905900982020960671328119369653408577861144 : ℝ) / 517873774355332710498418715050165112570420769167) * (value_126 h H)

/-- Coordinate 66.3, recovered from nonplanar cycle 19. -/
theorem value_267 (h : Assignment) (H : Constraints h) :
    h 66 3 = ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (h 1 0) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 1 1) + ((-36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 1 2) + h 1 3 + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (h 3 0) + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (h 5 1) + ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 117 3
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 3 - h 29 3) - ((604462459218948328868640 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-107650794861029512448538887237128784616362400 : ℝ) / 129961605662147876130966928863381863463780114652339643216297933001397) * r0 + ((278830605159619014340476296540840583789461820 : ℝ) / 129961605662147876130966928863381863463780114652339643216297933001397) * r1 + ((1 : ℝ) / 1143338598549074470824196) * r2 + ((-107650794861029512448538887237128784616362400 : ℝ) / 919199722731538547184272737603702530055209137036964334067530597239181) * r3 + ((278830605159619014340476296540840583789461820 : ℝ) / 919199722731538547184272737603702530055209137036964334067530597239181) * r4 + ((-57189484769921928488286283844724666827442525 : ℝ) / 1089573146003267509831260224691960490730204088590398956228962357723474) * r5 + ((1185030071928380810947024260298572481105212735 : ℝ) / 8716585168026140078650081797535683925841632708723191649831698861787792) * r6 + ((-7320254050550006846500644332124757353912643200 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_117 h H) + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (value_116 h H) + ((18960481150854092975152388164777159697683403760 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_118 h H) + (1 : ℝ) * (value_119 h H) + ((7320254050550006846500644332124757353912643200 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_125 h H) + ((928717562452291111080 : ℝ) / 3726409371667389204473) * (value_124 h H) + ((-18960481150854092975152388164777159697683403760 : ℝ) / 7729459318736309111916697239554703172692847301) * (value_126 h H)

/-- Coordinate 67.0, recovered from nonplanar cycle 19. -/
theorem value_268 (h : Assignment) (H : Constraints h) :
    h 67 0 = ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (h 1 0) + ((941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 1 1) + ((-823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 1 2) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (h 3 0) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (h 5 1) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2009949414449318445175543102150514863228724 : ℝ) / 866355275566569858948487600950711847873069632048958703361507183715) * r0 + ((-141494409519668287884700623372268574864544271 : ℝ) / 29456079369263375204248578432324202827684367489664595914291244246310) * r1 + ((28377560264614094921516 : ℝ) / 86512879603216544560540780902143301688406903005) * r2 + ((-1997695118287574906381689 : ℝ) / 2941437906509362515058386550672872257405834702170) * r3 + ((8542285011409603391996058184139688168722077 : ℝ) / 58106850148314456487527100565348505362765907145885914393304226176240) * r4 + ((-141494409519668287884700623372268574864544271 : ℝ) / 464854801186515651900216804522788042902127257167087315146433809409920) * r5 + ((3143560884198734048254549411763405246089724336 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_117 h H) + ((20682018593087191246588 : ℝ) / 41708273765268360426865) * (value_116 h H) + ((-6508742837904741242696228675124354443769036466 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_118 h H) + ((-3143560884198734048254549411763405246089724336 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_125 h H) + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (value_124 h H) + ((6508742837904741242696228675124354443769036466 : ℝ) / 1185107939770089651514257272632100023128861685) * (value_126 h H)

/-- Coordinate 67.1, recovered from nonplanar cycle 19. -/
theorem value_269 (h : Assignment) (H : Constraints h) :
    h 67 1 = ((16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (h 1 0) + ((-925399385763555945482272269 : ℝ) / 220636768218269626658115850) * (h 1 1) + ((27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (h 1 2) + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (h 3 0) + ((1146036153981825572140388119 : ℝ) / 220636768218269626658115850) * (h 5 1) + ((-27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((114502986016987110991293702763225036414084356073 : ℝ) / 24728378630496603483966681593936168273841026507573428270047499544777245) * r0 + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 3363059493747538073819468696775318885242379605029986244726459938089705320) * r1 + ((371499064464731899404634030150756843967930521287 : ℝ) / 699601044937638137382712226548254133833392708821745918579444028100003540) * r2 + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 23786435527879696671012215702640640550335352099939361231701096955400120360) * r3 + ((114502986016987110991293702763225036414084356073 : ℝ) / 390245605596079889770232007396880562016335832391769801065431182999627840) * r4 + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 53073402361066865008751553005975756434221673205280692944898640887949386240) * r5 + ((458011944067948443965174811052900145656337424292 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_117 h H) + ((16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (value_116 h H) + ((-32242666961150933094358397585000489763123313279043 : ℝ) / 2941437906509362515058386550672872257405834702170) * (value_118 h H) + ((-371499064464731899404634030150756843967930521287 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_125 h H) + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (value_124 h H) + ((32242666961150933094358397585000489763123313279043 : ℝ) / 2941437906509362515058386550672872257405834702170) * (value_126 h H)

/-- Coordinate 67.2, recovered from nonplanar cycle 19. -/
theorem value_270 (h : Assignment) (H : Constraints h) :
    h 67 2 = ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 1 0) + ((-195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((170624048649954562499929323 : ℝ) / 110318384109134813329057925) * (h 1 2) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (h 3 0) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2943296506013068108791580540081692482399981746 : ℝ) / 1454610507676270793174510681996245192578883912210201662943970561457485) * r0 + ((-414398489997543223485972233841662647776360685843 : ℝ) / 98913514521986413935866726375744673095364106030293713080189998179108980) * r1 + ((2943296506013068108791580540081692482399981746 : ℝ) / 10288250660847619667392826861003737262255775129731557626168294530882405) * r2 + ((-125227842400189942011628253685951487366191897212 : ℝ) / 174900261234409534345678056637063533458348177205436479644861007025000885) * r3 + ((25018020301111078924728434590694386100399844841 : ℝ) / 195122802798039944885116003698440281008167916195884900532715591499813920) * r4 + ((-414398489997543223485972233841662647776360685843 : ℝ) / 1560982422384319559080928029587522248065343329567079204261724731998511360) * r5 + ((200144162408888631397827476725555088803198758728 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_117 h H) + ((414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_116 h H) + ((-414398489997543223485972233841662647776360685843 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_118 h H) + ((-200144162408888631397827476725555088803198758728 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_125 h H) + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (value_124 h H) + ((500911369600759768046513014743805949464767588848 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_126 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource012

/- Original source: CubicalIndecomposability/Rigidity/Values03.lean -/
section VerificationSource013


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 67.3, recovered from nonplanar cycle 19. -/
theorem value_271 (h : Assignment) (H : Constraints h) :
    h 67 3 = ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 1 0) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 1 1) + ((-8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 1 2) + h 1 3 + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (h 3 0) + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (h 5 1) + ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (h 9 2) := by
  have r0 := H 117 1
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 1 - h 29 1) - ((-2409637830037763725241755 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 117 2
  change ((1143338598549074470824196 : ℤ) : ℝ) * (h 66 2 - h 29 2) - ((-1060565026627135066369648 : ℤ) : ℝ) * (h 66 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 123 1
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 1 - h 31 1) - ((-16139933799702809877368987 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 123 2
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 2 - h 31 2) - ((-7052902382819074324866358 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 123 3
  change ((-8086669269897091777415908 : ℤ) : ℝ) * (h 67 3 - h 31 3) - ((4022507252993022195835832 : ℤ) : ℝ) * (h 67 0 - h 31 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 211 1
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 1 - h 66 1) - ((2106363485580872011940213 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 211 2
  change ((18043352961358164180899072 : ℤ) : ℝ) * (h 67 2 - h 66 2) - ((2646424936362418154180472 : ℤ) : ℝ) * (h 67 0 - h 66 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1678660911568482103083017987529810282853831784 : ℝ) / 1454610507676270793174510681996245192578883912210201662943970561457485) * r0 + ((3475667431911991122571805736755723454904054879 : ℝ) / 1454610507676270793174510681996245192578883912210201662943970561457485) * r1 + ((-1678660911568482103083017987529810282853831784 : ℝ) / 10288250660847619667392826861003737262255775129731557626168294530882405) * r2 + ((3475667431911991122571805736755723454904054879 : ℝ) / 10288250660847619667392826861003737262255775129731557626168294530882405) * r3 + ((-1 : ℝ) / 8086669269897091777415908) * r4 + ((-3567154437083024469051413223500846851064392541 : ℝ) / 48780700699509986221279000924610070252041979048971225133178897874953480) * r5 + ((59086346342503849083720697524847298733368932943 : ℝ) / 390245605596079889770232007396880562016335832391769801065431182999627840) * r6 + ((-114148941986656783009645223152027099234060561312 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_117 h H) + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_116 h H) + ((236345385370015396334882790099389194933475731772 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_118 h H) + ((114148941986656783009645223152027099234060561312 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_125 h H) + ((236618073705471893872696 : ℝ) / 959290296601172289817895) * (value_124 h H) + ((-236345385370015396334882790099389194933475731772 : ℝ) / 86512879603216544560540780902143301688406903005) * (value_126 h H) + (1 : ℝ) * (value_127 h H)

/-- Coordinate 40.0, recovered from skew spokes on cycle 22. -/
theorem value_160 (h : Assignment) (H : Constraints h) :
    h 40 0 = ((373387608157540981246 : ℝ) / 704418962202810426877) * (h 1 0) + ((143533237735706606712 : ℝ) / 81008180653323199090855) * (h 1 1) + ((-125552494446375169052 : ℝ) / 81008180653323199090855) * (h 1 2) + ((331031354045269445631 : ℝ) / 704418962202810426877) * (h 3 0) + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (h 5 1) + ((125552494446375169052 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((154902820571522208603284900595583719821 : ℝ) / 2876607635172645194479293314897483335570456725277699104837436240) * r0 + ((20285336828218376714422205178368380373897 : ℝ) / 122145185739638472873274608447954677018068624027176146605404984960) * r1 + ((154902820571522208603284900595583719821 : ℝ) / 11863593480044170963678092832278248458352884547212128481182753380) * r2 + ((20285336828218376714422205178368380373897 : ℝ) / 503746430844952490150023634109045626846984020773930378585606143520) * r3 + ((159637946297717369 : ℝ) / 1139482967119812204375066247990656510977590) * r4 + ((4620099229554738330193 : ℝ) / 10692908163452317725855621671144320699013704560) * r5 + ((42133567195454040740093492961998771791312 : ℝ) / 569741483559906102187533123995328255488795) * (value_033 h H) + ((-20204832853080607363965756179286377734867819 : ℝ) / 39312162365633521050939785555677649628726855) * (value_032 h H) + ((8966118878072522507774614688838824125262474 : ℝ) / 39312162365633521050939785555677649628726855) * (value_034 h H) + ((-42133567195454040740093492961998771791312 : ℝ) / 569741483559906102187533123995328255488795) * (value_257 h H) + ((59516995218714128414905541734964027363594674 : ℝ) / 39312162365633521050939785555677649628726855) * (value_256 h H) + ((-8966118878072522507774614688838824125262474 : ℝ) / 39312162365633521050939785555677649628726855) * (value_258 h H)

/-- Coordinate 40.1, recovered from skew spokes on cycle 22. -/
theorem value_161 (h : Assignment) (H : Constraints h) :
    h 40 1 = ((-234599035402598809246983 : ℝ) / 191601957719164436110544) * (h 1 0) + ((8572056432343305206958001 : ℝ) / 1296130890453171185453680) * (h 1 1) + ((-216391415190288059972887769 : ℝ) / 44068450275407820305425120) * (h 1 2) + ((234599035402598809246983 : ℝ) / 191601957719164436110544) * (h 3 0) + ((-7275925541890134021504321 : ℝ) / 1296130890453171185453680) * (h 5 1) + ((216391415190288059972887769 : ℝ) / 44068450275407820305425120) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((154706583388856995742109334463313373080031 : ℝ) / 223553507647702712256676509043461562078618351221581187575937902080) * r0 + ((344413855177838220156659983510251268238296739 : ℝ) / 161371239674310942447434796989526407580442662143332143400969328701440) * r1 + ((154706583388856995742109334463313373080031 : ℝ) / 921970693306289857748697500108481023049138456240485413394773976960) * r2 + ((344413855177838220156659983510251268238296739 : ℝ) / 665520998922017232701059795462921993868701174873901163022812230753280) * r3 + ((-8076697628259033454328700963923271345339 : ℝ) / 85927443544532829232974321773244878495423450200666926205123731520) * r4 + ((4477380117311896862036579785633266487097857607 : ℝ) / 806343130221896069522231035520129939801053656683058435508881096583680) * r5 + ((154706583388856995742109334463313373080031 : ℝ) / 162783281017116029196438035427236644425370) * (value_033 h H) + ((-20179236550439498456702478086347359745383464009 : ℝ) / 3055116618129233635958749048898377342575344160) * (value_032 h H) + ((4477380117311896862036579785633266487097857607 : ℝ) / 1527558309064616817979374524449188671287672080) * (value_034 h H) + ((8076697628259033454328700963923271345339 : ℝ) / 162783281017116029196438035427236644425370) * (value_257 h H) + ((20179236550439498456702478086347359745383464009 : ℝ) / 3055116618129233635958749048898377342575344160) * (value_256 h H) + ((-4477380117311896862036579785633266487097857607 : ℝ) / 1527558309064616817979374524449188671287672080) * (value_258 h H)

/-- Coordinate 40.2, recovered from skew spokes on cycle 22. -/
theorem value_162 (h : Assignment) (H : Constraints h) :
    h 40 2 = ((621191793265828350363 : ℝ) / 1408837924405620853754) * (h 1 0) + ((-58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 1 1) + ((102955657658522908490713 : ℝ) / 64806544522658559272684) * (h 1 2) + ((-621191793265828350363 : ℝ) / 1408837924405620853754) * (h 3 0) + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 5 1) + ((-38149113135864349218029 : ℝ) / 64806544522658559272684) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((306212940345609350569647250125149301875 : ℝ) / 2301286108138116155583434651917986668456365380222159283869948992) * r0 + ((681703240932466582867265768063810700454375 : ℝ) / 1661174526059083231076534674892183607445733286769595593833507795456) * r1 + ((306212940345609350569647250125149301875 : ℝ) / 9490874784035336770942474265822598766682307637769702784946202704) * r2 + ((681703240932466582867265768063810700454375 : ℝ) / 6850951459491353866040321423883020525118982682525453148764243551872) * r3 + ((306212940345609350569647250125149301875 : ℝ) / 884547212958426183280618018253991396276417869712747769758626648) * r4 + ((-6862722814131342843101459237441520745583867 : ℝ) / 8300591046401871303905319483295455262657905289384425071414952464832) * r5 + ((20822479943501435838736013008510152527500 : ℝ) / 113948296711981220437506624799065651097759) * (value_033 h H) + ((-39941049842128006313378827261452396873023125 : ℝ) / 31449729892506816840751828444542119702981484) * (value_032 h H) + ((8862142132122065577274454984829539105906875 : ℝ) / 15724864946253408420375914222271059851490742) * (value_034 h H) + ((-20822479943501435838736013008510152527500 : ℝ) / 113948296711981220437506624799065651097759) * (value_257 h H) + ((39941049842128006313378827261452396873023125 : ℝ) / 31449729892506816840751828444542119702981484) * (value_256 h H) + ((6862722814131342843101459237441520745583867 : ℝ) / 15724864946253408420375914222271059851490742) * (value_258 h H)

/-- Coordinate 40.3, recovered from skew spokes on cycle 22. -/
theorem value_163 (h : Assignment) (H : Constraints h) :
    h 40 3 = ((-176638774353111342216 : ℝ) / 704418962202810426877) * (h 1 0) + ((8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 1 1) + ((-7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 1 2) + h 1 3 + ((176638774353111342216 : ℝ) / 704418962202810426877) * (h 3 0) + ((-8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 5 1) + ((7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 3
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 3 - h 40 3) - ((-548544797169282558194688 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-10060726662730031672300426387196679818 : ℝ) / 179787977198290324654955832181092708473153545329856194052339765) * r0 + ((-219584154264302343474140921337485354571 : ℝ) / 1272345684787900759096610504666194552271548166949751527139635260) * r1 + ((-40242906650920126689201705548786719272 : ℝ) / 2965898370011042740919523208069562114588221136803032120295688345) * r2 + ((-219584154264302343474140921337485354571 : ℝ) / 5247358654634921772396079521969225279656083549728441443600063995) * r3 + ((-4734459605990603139906083005739614032 : ℝ) / 32520118123471550855905074200514389568985951092380432711714215) * r4 + ((-5709188010871860930327663954774619218846 : ℝ) / 12715366186277376384658884012401126321473506877120749190280258065) * r5 + ((-1 : ℝ) / 527864059549812689780896) * r6 + ((-43784282436201097837851455637079950567936 : ℝ) / 569741483559906102187533123995328255488795) * (value_033 h H) + ((6998806945791233071998673065899291724646944 : ℝ) / 13104054121877840350313261851892549876242285) * (value_032 h H) + ((-3105798277914292346098249191397392855052224 : ℝ) / 13104054121877840350313261851892549876242285) * (value_034 h H) + ((43784282436201097837851455637079950567936 : ℝ) / 569741483559906102187533123995328255488795) * (value_257 h H) + ((-6998806945791233071998673065899291724646944 : ℝ) / 13104054121877840350313261851892549876242285) * (value_256 h H) + ((3105798277914292346098249191397392855052224 : ℝ) / 13104054121877840350313261851892549876242285) * (value_258 h H) + (1 : ℝ) * (value_259 h H)

/-- Coordinate 41.0, recovered from skew spokes on cycle 22. -/
theorem value_164 (h : Assignment) (H : Constraints h) :
    h 41 0 = ((17126635218530564174956 : ℝ) / 183708538376905553243199) * (h 1 0) + ((25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 1 1) + ((-6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 1 2) + ((166581903158374989068243 : ℝ) / 183708538376905553243199) * (h 3 0) + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 5 1) + ((6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-266002993616693518817 : ℝ) / 7726440942545159891765045541596967180692666580) * r0 + ((835903922193147363178383 : ℝ) / 619700186366186157472847755233725983107863104160) * r1 + ((-922418354331517547651708215781039182429 : ℝ) / 110498537247396058930491430912732130352816484673294486116691694645) * r2 + ((2898663318803623375927919730881677310533971 : ℝ) / 8862549346406535188066081946026310352400255488668337245461836432040) * r3 + ((-1844836708663035095303416431562078364858 : ℝ) / 20596873393078181401124622778983830914486022824240149273111335355) * r4 + ((37682623144447103887062956501461805036941623 : ℝ) / 10737836662258091903786303342110237183418713232370531154382042831740) * r5 + ((-1003591169512691091845058538769770630482752 : ℝ) / 21226486105893296405947927312079580166738095) * (value_033 h H) + ((-1449886291557224877161525374824892012481693047 : ℝ) / 488209180435545817336802328177830343834976185) * (value_032 h H) + ((301460985155576831096503652011694440295532984 : ℝ) / 162736393478515272445600776059276781278325395) * (value_034 h H) + ((1003591169512691091845058538769770630482752 : ℝ) / 21226486105893296405947927312079580166738095) * (value_257 h H) + ((1938095471992770694498327703002722356316669232 : ℝ) / 488209180435545817336802328177830343834976185) * (value_256 h H) + ((-301460985155576831096503652011694440295532984 : ℝ) / 162736393478515272445600776059276781278325395) * (value_258 h H)

/-- Coordinate 41.1, recovered from skew spokes on cycle 22. -/
theorem value_165 (h : Assignment) (H : Constraints h) :
    h 41 1 = ((-136151565219732618160718185 : ℝ) / 99937444877036620964300256) * (h 1 0) + ((874532080379190745238977007 : ℝ) / 112674570204502072655828720) * (h 1 1) + ((-6179510915861363677618869439 : ℝ) / 1044800560078110128263139040) * (h 1 2) + ((136151565219732618160718185 : ℝ) / 99937444877036620964300256) * (h 3 0) + ((-761857510174688672583148287 : ℝ) / 112674570204502072655828720) * (h 5 1) + ((6179510915861363677618869439 : ℝ) / 1044800560078110128263139040) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((31888065913250155144681234667091152358000427 : ℝ) / 48013007031052807363796716072117507822839683255625898257392015416320) * r0 + ((164176251845147701920370388992982364875848652199 : ℝ) / 65465119535468309855827030098741553743264692225670840147053277225082880) * r1 + ((-52244490439759661906960975397678654582659401 : ℝ) / 3366227438704673539258490951325471619068201389087243225058895785665280) * r2 + ((164176251845147701920370388992982364875848652199 : ℝ) / 269988703288928687969245120403745518575521383206792225845749385065666560) * r3 + ((-52244490439759661906960975397678654582659401 : ℝ) / 313731575523366859101930254169481712489451099658825953728031860127360) * r4 + ((2134291273986920124964815056908770743386032478587 : ℝ) / 327117456079030511756945945014046265555667679910935861087094552826127360) * r5 + ((542097120525252637459580989340549590086007259 : ℝ) / 594341610965012299366541964738228244668666660) * (value_033 h H) + ((-6860689206420862829106872475863004696875416119463 : ℝ) / 929550279549279236209271632850588974661794656240) * (value_032 h H) + ((2134291273986920124964815056908770743386032478587 : ℝ) / 619700186366186157472847755233725983107863104160) * (value_034 h H) + ((52244490439759661906960975397678654582659401 : ℝ) / 594341610965012299366541964738228244668666660) * (value_257 h H) + ((6860689206420862829106872475863004696875416119463 : ℝ) / 929550279549279236209271632850588974661794656240) * (value_256 h H) + ((-2134291273986920124964815056908770743386032478587 : ℝ) / 619700186366186157472847755233725983107863104160) * (value_258 h H)

/-- Coordinate 41.2, recovered from skew spokes on cycle 22. -/
theorem value_166 (h : Assignment) (H : Constraints h) :
    h 41 2 = ((-4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 1 0) + ((1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 1 1) + ((-524424025816764199423282393 : ℝ) / 99870641772172291672211820) * (h 1 2) + ((4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 3 0) + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 5 1) + ((624294667588936491095494213 : ℝ) / 99870641772172291672211820) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-4433727260330465767884803007764554873198687 : ℝ) / 78021136425460811966169663617190950212114485290392084668262025051520) * r0 + ((18489432165304017223271092706074278344089301573 : ℝ) / 6257695249713882559748171994732648519576772050983242072880092675927040) * r1 + ((-4433727260330465767884803007764554873198687 : ℝ) / 321771740464417323605591046817875963587401603368633543571806214806240) * r2 + ((13932813147905589594794270976414528468296190513 : ℝ) / 25807743696735830467648430626828615746189543983002198058784867690100480) * r3 + ((-4433727260330465767884803007764554873198687 : ℝ) / 29989047660321832120037450766200457811491649232093657341650104276880) * r4 + ((13932813147905589594794270976414528468296190513 : ℝ) / 2405275412345812586448131948632693129085791764050998978581577594309760) * r5 + ((-150746726851235836108083302263994865688755358 : ℝ) / 1931610235636289972941261385399241795173166645) * (value_033 h H) + ((-582232202919789872149174412818519530584451493681 : ℝ) / 88854070839269338755298023728365122577965665670) * (value_032 h H) + ((18489432165304017223271092706074278344089301573 : ℝ) / 4556619017398427628476821729659749875793111060) * (value_034 h H) + ((150746726851235836108083302263994865688755358 : ℝ) / 1931610235636289972941261385399241795173166645) * (value_257 h H) + ((582232202919789872149174412818519530584451493681 : ℝ) / 88854070839269338755298023728365122577965665670) * (value_256 h H) + ((-13932813147905589594794270976414528468296190513 : ℝ) / 4556619017398427628476821729659749875793111060) * (value_258 h H)

/-- Coordinate 41.3, recovered from skew spokes on cycle 22. -/
theorem value_167 (h : Assignment) (H : Constraints h) :
    h 41 3 = ((-5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 1 0) + ((-1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 1 1) + ((88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 1 2) + h 1 3 + ((5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 3 0) + ((1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 5 1) + ((-88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 152 3
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 3 - h 40 3) - ((717306105909058847318400 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 3
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 3 - h 40 3) - ((-548544797169282558194688 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-2509836536556296329463363898222204451247 : ℝ) / 56049666972313801699834528460625682623645463570683968870877891560) * r0 + ((-255751664015436547874085074254467092748593 : ℝ) / 793318363300441500982273325904240430980828099769680790172425542080) * r1 + ((-2509836536556296329463363898222204451247 : ℝ) / 231157859529035433624706211794451123266811496672868924979745843970) * r2 + ((-255751664015436547874085074254467092748593 : ℝ) / 3271772781026347675918918690013769744699485799062144784328710406960) * r3 + ((-1 : ℝ) / 5663792298235764294550208) * r4 + ((-147637443326840960556668464601306144191 : ℝ) / 1267285651636318125424165431296503457213135954703078826134639295) * r5 + ((-255751664015436547874085074254467092748593 : ℝ) / 304928424486031007409753036084266370320206866639325428319165516520) * r6 + ((-1 : ℝ) / 527864059549812689780896) * r7 + ((-1365351075886625203228069960632879221478368 : ℝ) / 22202416501566551413117946958611974657162835) * (value_033 h H) + ((431566285697866954890983774823660285535955572 : ℝ) / 510655579536030682501712780048075417114745205) * (value_032 h H) + ((-17391113153049685255437785049303762306904324 : ℝ) / 39281198425848514038593290772928878239595785) * (value_034 h H) + ((1365351075886625203228069960632879221478368 : ℝ) / 22202416501566551413117946958611974657162835) * (value_257 h H) + ((-431566285697866954890983774823660285535955572 : ℝ) / 510655579536030682501712780048075417114745205) * (value_256 h H) + ((17391113153049685255437785049303762306904324 : ℝ) / 39281198425848514038593290772928878239595785) * (value_258 h H) + (1 : ℝ) * (value_259 h H)

/-- Coordinate 42.0, recovered from skew spokes on cycle 22. -/
theorem value_168 (h : Assignment) (H : Constraints h) :
    h 42 0 = ((50182337158358922070838 : ℝ) / 67703568293298537493335) * (h 1 0) + ((-22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 1 1) + ((519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 1 2) + ((17521231134939615422497 : ℝ) / 67703568293298537493335) * (h 3 0) + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 5 1) + ((-519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((1160211594815817326515724530697300652299 : ℝ) / 12020798387906128511959840318686119760557160048332892575284352400) * r0 + ((-1173227800576294817772110335724673196395563 : ℝ) / 2892389027490028460416183116680783277770984356245022151960727254400) * r1 + ((7283128941549504697123121718764091327592984828334732506205365279 : ℝ) / 10439045950816890786007442473262828557910883155751728100786112609377825534705003970086675) * r2 + ((-451499603783385973009351138307912599167037816485452639085729413203 : ℝ) / 2511795056473479567587021542797394440703480193168569653789150787856449097889019416802393800) * r3 + ((1496607505916803958401615 : ℝ) / 334545221701350026094675724707167916321805936488) * r4 + ((-9450374220287914025645053 : ℝ) / 17499288519762924441875345600067244853756002831680) * r5 + ((1160211594815817326515724530697300652299 : ℝ) / 4620444052547746245834558486125468170000870466073131716740049350) * r6 + ((-1173227800576294817772110335724673196395563 : ℝ) / 1111749922797642327459269149584651110443286370605904308458682643600) * r7 + ((-907400266239168450951338894301388514947919065 : ℝ) / 3630946032918385375546881932246829348812643339958133478488838489708804) * r8 + ((337047467439717640803524997075722567509666379 : ℝ) / 11172141639748878078605790560759474919423517969101949164581041506796320) * r9 + ((106752972498725700111922222858986884111519890 : ℝ) / 1055316158610661104265589969901587266740092748443341316026663391232021) * r10 + ((-337047467439717640803524997075722567509666379 : ℝ) / 27600576455971136573100045366656897745510118036210465188389657924529780) * r11 + ((315577553789902312812277072349665777425328 : ℝ) / 2380841732935581396988193603624770265323575) * (value_033 h H) + ((36856096046751645306109466423036145059504023 : ℝ) / 54759359857518372130728452883369716102442225) * (value_032 h H) + ((-2346455601152589635544220671449346392791126 : ℝ) / 4212258450578336317748342529489978161726325) * (value_034 h H) + ((-315577553789902312812277072349665777425328 : ℝ) / 2380841732935581396988193603624770265323575) * (value_257 h H) + ((17903263810766726824618986460333571042938202 : ℝ) / 54759359857518372130728452883369716102442225) * (value_256 h H) + ((2346455601152589635544220671449346392791126 : ℝ) / 4212258450578336317748342529489978161726325) * (value_258 h H)

/-- Coordinate 42.1, recovered from skew spokes on cycle 22. -/
theorem value_169 (h : Assignment) (H : Constraints h) :
    h 42 1 = ((-523293629333666712175409207 : ℝ) / 405138152667098448360116640) * (h 1 0) + ((15828296484273802598108811 : ℝ) / 2206634818448248629412400) * (h 1 1) + ((-994381301605265439714838003 : ℝ) / 184153705757772021981871200) * (h 1 2) + ((523293629333666712175409207 : ℝ) / 405138152667098448360116640) * (h 3 0) + ((-13621661665825553968696411 : ℝ) / 2206634818448248629412400) * (h 5 1) + ((994381301605265439714838003 : ℝ) / 184153705757772021981871200) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((97604725296758743287492124486942253219269283 : ℝ) / 143864915106460546031135368934035481294348091458448058341003129523200) * r0 + ((80182769162546921837936109873086676978965565229 : ℝ) / 34616111881000660614260879540435614268363140775540425114665983780659200) * r1 + ((-687386778178714978206115447624401045858491497224904544453496672847 : ℝ) / 13691452267328936868705432495343510376008487628277992538105007748935212712257478083725734400) * r2 + ((1935680199706841287191519302084721049609003783664998116583702574713279 : ℝ) / 3294374053246531886562353295802653881242657638557966204553266479897641951072414726607238246400) * r3 + ((-990247113092859417787720941486415504966389359 : ℝ) / 3912241082355788686555554905809362795841856299884781930873753343935488) * r4 + ((35191248829732245406438004542735216894250303573 : ℝ) / 204640302769379715912136718150028207782497098763203977922627097990471680) * r5 + ((-7152310952406838179988394072547638454968017 : ℝ) / 55297474420891427070147995961949603058570417737963240385944910620800) * r6 + ((80182769162546921837936109873086676978965565229 : ℝ) / 13305423076042183375032533182229104489785251283411462763633513878604800) * r7 + ((5573058369275736487577799362132551344991128215 : ℝ) / 70032493347247761763972736446623777029153449625493862160442254705616384) * r8 + ((-35191248829732245406438004542735216894250303573 : ℝ) / 3663238113548344461500112367977243721524949672718140482238517938447626240) * r9 + ((-5573058369275736487577799362132551344991128215 : ℝ) / 173014024469210850628090147394276663128019589224245326989138458441983936) * r10 + ((35191248829732245406438004542735216894250303573 : ℝ) / 9049964356851029109777023094469856225157947744037447873278011672349928960) * r11 + ((97604725296758743287492124486942253219269283 : ℝ) / 104757036249165581467480518559489891674237300) * (value_033 h H) + ((-1144102031860781283542548758069246665632208931221 : ℝ) / 163840004693694969415139531027042190578507137200) * (value_032 h H) + ((80182769162546921837936109873086676978965565229 : ℝ) / 25206154568260764525406081696468029319770328800) * (value_034 h H) + ((7152310952406838179988394072547638454968017 : ℝ) / 104757036249165581467480518559489891674237300) * (value_257 h H) + ((1144102031860781283542548758069246665632208931221 : ℝ) / 163840004693694969415139531027042190578507137200) * (value_256 h H) + ((-80182769162546921837936109873086676978965565229 : ℝ) / 25206154568260764525406081696468029319770328800) * (value_258 h H)

/-- Coordinate 42.2, recovered from skew spokes on cycle 22. -/
theorem value_170 (h : Assignment) (H : Constraints h) :
    h 42 2 = ((1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 1 0) + ((-12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 1 1) + ((54965293097119131924855289 : ℝ) / 31143641414917327246934100) * (h 1 2) + ((-1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 3 0) + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 5 1) + ((-23821651682201804677921189 : ℝ) / 31143641414917327246934100) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((108272397154631915757354749494685799117241 : ℝ) / 784841804423290455103442477581313109527990062510508857173404169600) * r0 + ((65116916093092929718238564590885896661040183 : ℝ) / 188845012633542503351043697682642108200273301194836285018339095577600) * r1 + ((8273717177553385611897575483645138638033837343397272281253258731 : ℝ) / 74692457815124655593032482778202262487712337630548820772394491988972934625693073037403200) * r2 + ((1334880388881488737227780965475326557410677445018397753652239016933 : ℝ) / 17972154465054609438077354317708975158581860931412054721234613149346718423782148650845939200) * r3 + ((14756830165326321653773720541728012534683115 : ℝ) / 28766478546733740342320256660362961734131296322682220079954068705408) * r4 + ((1669437255044526042924801906486710230403285207 : ℝ) / 1504708108598380264059828809926677998400713961494146896489905132282880) * r5 + ((108272397154631915757354749494685799117241 : ℝ) / 301670282656665754889327302448966050841347155591355438538124512400) * r6 + ((-72392940422561146203094423791174035586283717 : ℝ) / 72586511088465421637985830927720446694748761745366139365173344214400) * r7 + ((-250866112810547468114153249209376213089612955 : ℝ) / 8754061668405970220496592055827972128644181203186732770055281838202048) * r8 + ((93182458871965137763689793761803554221614353 : ℝ) / 26935574364326062216912590941009145011212865240574562369400867194467840) * r9 + ((14756830165326321653773720541728012534683115 : ℝ) / 1272161944626550372265368730840269581823673450178274463155429841485176) * r10 + ((-93182458871965137763689793761803554221614353 : ℝ) / 66543855565081096395419287459337178126161380470863587303514791708455360) * r11 + ((3681261503257485135750061482819317169986194 : ℝ) / 19430740594603293336710096184421512165382725) * (value_033 h H) + ((-1013478390600740177026180976496382275683551117 : ℝ) / 893814067351751493488664424483389559607605350) * (value_032 h H) + ((65116916093092929718238564590885896661040183 : ℝ) / 137509856515654075921332988382059932247323900) * (value_034 h H) + ((-3681261503257485135750061482819317169986194 : ℝ) / 19430740594603293336710096184421512165382725) * (value_257 h H) + ((1013478390600740177026180976496382275683551117 : ℝ) / 893814067351751493488664424483389559607605350) * (value_256 h H) + ((72392940422561146203094423791174035586283717 : ℝ) / 137509856515654075921332988382059932247323900) * (value_258 h H)

/-- Coordinate 42.3, recovered from skew spokes on cycle 22. -/
theorem value_171 (h : Assignment) (H : Constraints h) :
    h 42 3 = ((-197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 1 0) + ((702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 1 1) + ((-1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 1 2) + h 1 3 + ((197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 3 0) + ((-702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 5 1) + ((1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 153 3
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 3 - h 40 3) - ((-55672055611990139857792 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 155 3
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 3 - h 40 3) - ((-548544797169282558194688 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  linear_combination ((-89323995687704735554811811782927213739979 : ℝ) / 1520630996070125256762919800313794149710480746114110910773470578600) * r0 + ((-2912009613313512008321101534402524781778581 : ℝ) / 21522777175146388249567480250595240272825265944999723660178352804800) * r1 + ((-8424812943703001519681134330151053619340931424817277070826275539 : ℝ) / 144716637016804020211500435382766883569942654159188340246514328228635060837280329009968700) * r2 + ((-56324243778507276168341514388899015632715142185684157342774860781 : ℝ) / 2048297016237841516839698470033008198220726797330050354258356645697603938004583118294941600) * r3 + ((-524521657803196592054029921825686711571585 : ℝ) / 1797904909170858771395016041272685108383206020167638754997129294088) * r4 + ((194829892559511833085515464594229517977411 : ℝ) / 5532015105141103911984664742377492641179095446669657707683474751040) * r5 + ((1 : ℝ) / 853677112946252813688448) * r6 + ((-5254352687512043267930106575466306690587 : ℝ) / 34381539567487641182239508734992454323830006703426538951036249575) * r7 + ((-2912009613313512008321101534402524781778581 : ℝ) / 8272727366700103201388091024850492086533866228332170295295491436200) * r8 + ((-1 : ℝ) / 527864059549812689780896) * r9 + ((8916868182654342064918508671036674096716945 : ℝ) / 547128854275373138781037003489248258040261325199170798128455114887628) * r10 + ((-3312108173511701162453762898101901805615987 : ℝ) / 1683473397770378888557036933813071563200804077535910148087554199654240) * r11 + ((-1049043315606393184108059843651373423143170 : ℝ) / 159020243078318796533171091355033697727959181272284307894428730185647) * r12 + ((194829892559511833085515464594229517977411 : ℝ) / 244646527812798148512570909776974919581475663495822012145274969516380) * r13 + ((-48592253654111376141817625609912404274548576 : ℝ) / 602352958432702093438012981717066877126864475) * (value_033 h H) + ((6326958564169635958199805775608606931282953284 : ℝ) / 13854118043952148149074298579492538173917882925) * (value_032 h H) + ((-198016653705318816565834904339371685160943508 : ℝ) / 1065701387996319088390330659960964474916760225) * (value_034 h H) + ((48592253654111376141817625609912404274548576 : ℝ) / 602352958432702093438012981717066877126864475) * (value_257 h H) + ((-6326958564169635958199805775608606931282953284 : ℝ) / 13854118043952148149074298579492538173917882925) * (value_256 h H) + ((198016653705318816565834904339371685160943508 : ℝ) / 1065701387996319088390330659960964474916760225) * (value_258 h H) + (1 : ℝ) * (value_259 h H)

/-- Coordinate 43.0, recovered from skew spokes on cycle 22. -/
theorem value_172 (h : Assignment) (H : Constraints h) :
    h 43 0 = ((2450485155582961681814836 : ℝ) / 2667143502384686423713107) * (h 1 0) + ((-110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 1 1) + ((867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 1 2) + ((216658346801724741898271 : ℝ) / 2667143502384686423713107) * (h 3 0) + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 5 1) + ((-867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((90128060699377275988088580390550915193621 : ℝ) / 680731724898181697687807291298606511512140095503052562585933417115) * r0 + ((-36296915495122067594015643342909480662426723 : ℝ) / 40948631451567545199374253984270022461730273437183623380169225552610) * r1 + ((658879626463814573502802636975594209017889243888129168907843388747909 : ℝ) / 983686721385423149197886886233848687858936498997770248125591082885340454239694408978528727720) * r2 + ((-59100014793337563395806692582943903520137115760080954922793122682256813 : ℝ) / 236690158807200277745460783087652207355596412989617333548988377481949610835520316252679835408320) * r3 + ((258527840265448532519643628120952174956309331137 : ℝ) / 61104763830978117890884987983270947526881095264162062259308170098238064) * r4 + ((-147442723385494842208082690824036408506159880511 : ℝ) / 639249837001001848704642951209603758742756073532772343635839317950798208) * r5 + ((721024485595018207904708643124407321548968 : ℝ) / 2093227253757637165069744692543567429708168473951409819229148550105) * r6 + ((-1887439605746347514888813453831292994446189596 : ℝ) / 818451856219236131542270174784534865015893873315001239318597083091055) * r7 + ((-18406388989996713080235479 : ℝ) / 77877199751388757952730436612674941434699508770584) * r8 + ((617498206403513170078361 : ℝ) / 47924430616239235663218730223184579344430466935744) * r9 + ((258527840265448532519643628120952174956309331137 : ℝ) / 2702282625760933784061936572001346333272225884785044275803647772124202633) * r10 + ((-147442723385494842208082690824036408506159880511 : ℝ) / 28270033623345153433263336445552546255770978486982001654561238231453196776) * r11 + ((392237320163689905100161501859677582922638592 : ℝ) / 2157213785335764077944272923241393800356525845) * (value_033 h H) + ((82922169649307818848813650815224137819433116107 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_032 h H) + ((-60398067383883120476442030522601375822278067072 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_034 h H) + ((-392237320163689905100161501859677582922638592 : ℝ) / 2157213785335764077944272923241393800356525845) * (value_257 h H) + ((-33306252586585245056095373580672080411233021672 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_256 h H) + ((60398067383883120476442030522601375822278067072 : ℝ) / 49615917062722573792718277234552057408200094435) * (value_258 h H)

/-- Coordinate 43.1, recovered from skew spokes on cycle 22. -/
theorem value_173 (h : Assignment) (H : Constraints h) :
    h 43 1 = ((-223518282605868375278937481 : ℝ) / 161214007255252157166658912) * (h 1 0) + ((868322307967072849438558517 : ℝ) / 109056534319729400436269264) * (h 1 1) + ((-22581126527363584798105121117 : ℝ) / 3707922166870799614833154976) * (h 1 2) + ((223518282605868375278937481 : ℝ) / 161214007255252157166658912) * (h 3 0) + ((-759265773647343449002289253 : ℝ) / 109056534319729400436269264) * (h 5 1) + ((22581126527363584798105121117 : ℝ) / 3707922166870799614833154976) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((10212595914251833956131919864071606576394607 : ℝ) / 15490428584349734631829214806439401506409587951002796090844351536128) * r0 + ((489118377446589676965220650126642805696679569427 : ℝ) / 190089007015703420488188536895512680270346826665198004213862900911955968) * r1 + ((-11506832808491372181811510375772427489017182312053684547233238186591 : ℝ) / 325799437706952933432968320311241209251300733914634407902783287116971206761883566809327018496) * r2 + ((146967818000899835668019140246160956945594920268098434637851593870402733 : ℝ) / 235177071034003563641151901369283654431862006696533021827670643561973677250270414687594210889728) * r3 + ((-2205711021802612176793318825846353088657041379 : ℝ) / 17857099932340637191856800141229865943928721903682063856601474366608384) * r4 + ((1257953649100451928250146961541809655025719837 : ℝ) / 186812737753717435237886524554404751413408167607750821884446193373749248) * r5 + ((-18138205932008963007470511043351026010760645 : ℝ) / 101219166759480410470928098910551171712110546651517061480947272111744) * r6 + ((6358538906805665800547868451646356474056834402551 : ℝ) / 949840660870964171859189280176612195346445369777836104937209201496605696) * r7 + ((393100739203469785785077454800460794446436866779 : ℝ) / 5434177623536317464944399212180180657872488812091213903144508343072751104) * r8 + ((-1257953649100451928250146961541809655025719837 : ℝ) / 3344109306791579978427322592110880404844608499748439325012005134198616064) * r9 + ((-2205711021802612176793318825846353088657041379 : ℝ) / 789708164605934987123123016475279293741655053087866820326180170849082048) * r10 + ((1257953649100451928250146961541809655025719837 : ℝ) / 8261562337415935249903440787741383380681929786149991351104654095036550656) * r11 + ((173614130542281177254242637689217311798708319 : ℝ) / 191752336474290140261713148732568337809468964) * (value_033 h H) + ((-6762294746594300064566584712392999677755557237655 : ℝ) / 899701962737369338107958093853210641002028379088) * (value_032 h H) + ((6358538906805665800547868451646356474056834402551 : ℝ) / 1799403925474738676215916187706421282004056758176) * (value_034 h H) + ((18138205932008963007470511043351026010760645 : ℝ) / 191752336474290140261713148732568337809468964) * (value_257 h H) + ((6762294746594300064566584712392999677755557237655 : ℝ) / 899701962737369338107958093853210641002028379088) * (value_256 h H) + ((-6358538906805665800547868451646356474056834402551 : ℝ) / 1799403925474738676215916187706421282004056758176) * (value_258 h H)

/-- Coordinate 43.2, recovered from skew spokes on cycle 22. -/
theorem value_174 (h : Assignment) (H : Constraints h) :
    h 43 2 = ((-30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 1 0) + ((3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 1 1) + ((-51019593198921921642827329967 : ℝ) / 15949518144260424813804379860) * (h 1 2) + ((30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 3 0) + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 5 1) + ((66969111343182346456631709827 : ℝ) / 15949518144260424813804379860) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((23941221499942420981960299765321546008591 : ℝ) / 161819655747224906421787333245840176450885874131011352020427600868480) * r0 + ((85319857379214133879197319199820611634564095233 : ℝ) / 38936298705947654406719290645614467072182385713984885316915195039738880) * r1 + ((3354571768400888256762485640165182516482943049352391811022732266461 : ℝ) / 15400183505055548324037368081938922706206442254368223062631562941453470907862143389096340160) * r2 + ((1270591105769495507697905900790425108434430651920725293712374537163763 : ℝ) / 3705521077216442704429914412331150017308750105512600133839348375451265923060983424699488616960) * r3 + ((9675992856565255837223417615658952041429000457 : ℝ) / 6696412474627738946946300052961199728973270713880773946225552887478144) * r4 + ((-5518379516750417837677232229366964627816244471 : ℝ) / 70054776657644038214207446707901781780028062852906558206667322515155968) * r5 + ((23941221499942420981960299765321546008591 : ℝ) / 62198752683084075762072413721294575054185577511699034628523271203120) * r6 + ((56967904771944091711929732208648007401306898413 : ℝ) / 14965976799437460691058654624631494674576345112045736947540060947950720) * r7 + ((-164491878561609349232798099466202184704293007769 : ℝ) / 2037816608826119049354149704567567746702183304534205213679190628652281664) * r8 + ((87580760708940889863736701789614531998416359087 : ℝ) / 1254040990046842491910245972041580151816728187405664746879501925324481024) * r9 + ((9675992856565255837223417615658952041429000457 : ℝ) / 296140561727225620171171131178229735153120644907950057622317564068405768) * r10 + ((-5518379516750417837677232229366964627816244471 : ℝ) / 3098085876530975718713790295403018767755723669806246756664245285638706496) * r11 + ((814001530998042313386650192020932564292094 : ℝ) / 4006254172766419001896506857448302772090690855) * (value_033 h H) + ((-915474330674066817838730914121232867510910144817 : ℝ) / 184287691947255274087239315442621927516171779330) * (value_032 h H) + ((85319857379214133879197319199820611634564095233 : ℝ) / 28351952607270042167267586991172604233257196820) * (value_034 h H) + ((-814001530998042313386650192020932564292094 : ℝ) / 4006254172766419001896506857448302772090690855) * (value_257 h H) + ((915474330674066817838730914121232867510910144817 : ℝ) / 184287691947255274087239315442621927516171779330) * (value_256 h H) + ((-56967904771944091711929732208648007401306898413 : ℝ) / 28351952607270042167267586991172604233257196820) * (value_258 h H)

/-- Coordinate 43.3, recovered from skew spokes on cycle 22. -/
theorem value_175 (h : Assignment) (H : Constraints h) :
    h 43 3 = ((-2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 1 0) + ((57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 1 1) + ((-149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 1 2) + h 1 3 + ((2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 3 0) + ((-57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 5 1) + ((149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 9 2) := by
  have r0 := H 40 1
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 1 - h 8 1) - ((2553273429304189931317589 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 40 2
  change ((1373319828982909675888384 : ℤ) : ℝ) * (h 41 2 - h 8 2) - ((2266842561455675908895096 : ℤ) : ℝ) * (h 41 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 152 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 1 - h 40 1) - ((-1788706911718189505443531 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 152 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 2 - h 40 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 152 3
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 41 3 - h 40 3) - ((717306105909058847318400 : ℤ) : ℝ) * (h 41 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 153 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 1 - h 40 1) - ((-271836977529995445635393 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 153 2
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 42 2 - h 40 2) - ((97891938468938791466728 : ℤ) : ℝ) * (h 42 0 - h 40 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 155 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 1 - h 40 1) - ((6783763565226244702732193 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 155 2
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 2 - h 40 2) - ((1304356540935979975475000 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 155 3
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 64 3 - h 40 3) - ((-548544797169282558194688 : ℤ) : ℝ) * (h 64 0 - h 40 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 157 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 1 - h 41 1) - ((-446141942269828752922023 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 157 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 2 - h 41 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 157 3
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 43 3 - h 41 3) - ((-1072921154218855975526496 : ℤ) : ℝ) * (h 43 0 - h 41 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 159 1
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 1 - h 42 1) - ((-20161997218604870937092651 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  have r14 := H 159 2
  change ((37752814767527211137468056 : ℤ) : ℝ) * (h 43 2 - h 42 2) - ((-144992312656829719974358604 : ℤ) : ℝ) * (h 43 0 - h 42 0) = 0 at r14
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r14
  linear_combination ((-166641364625305375423914052854768065513641 : ℝ) / 2949837474558787356647164928960628216552607080513227771205711474165) * r0 + ((-6907471282526874166283755374360878654897239 : ℝ) / 41751545793755144124852180532981199372744592524187223838603916249720) * r1 + ((-525270831129503210399036611137051232477973290158732628588546435787 : ℝ) / 8983440377949069855688464714464371578620424648381463453201745049181191362919583643639531760) * r2 + ((-4790326488200191329195329051745997880764586712965541800737906265453 : ℝ) / 127150233041740681034359808266264951574319856561706867337624699157641477752092568494590295680) * r3 + ((-1 : ℝ) / 5663792298235764294550208) * r4 + ((-165765210516959744095647250084527468070345519 : ℝ) / 558034372885644912245525004413433310747772559490064495518796073956512) * r5 + ((5561097303439184733774642496726922114646721 : ℝ) / 343405767929627638304938464254420498921706190455424304934643737819392) * r6 + ((-78419465706026059023018377814008501418184 : ℝ) / 533567731349985944037385902020909344827572356105261326470175120615) * r7 + ((-6907471282526874166283755374360878654897239 : ℝ) / 16048075612141884932201375976167350294429291633627475280756805550805) * r8 + ((-1 : ℝ) / 527864059549812689780896) * r9 + ((2818008578788315649626003251436966957195873823 : ℝ) / 169818050735509920779512475380630645558515275377850434473265885721023472) * r10 + ((-94538654158466140474168922444357675948994257 : ℝ) / 104503415837236874325853831003465012651394015617138728906625160443706752) * r11 + ((1 : ℝ) / 15281557418007073892361664) * r12 + ((-165765210516959744095647250084527468070345519 : ℝ) / 24678380143935468347597594264852477929426720408995838135193130339033814) * r13 + ((5561097303439184733774642496726922114646721 : ℝ) / 15186695473191057444675442624524601802724135636305131160118849439405424) * r14 + ((-725223218849328993844873958023950621115365632 : ℝ) / 9347926403121644337758516000712706468211611995) * (value_033 h H) + ((111644335025673490322596997601243526259359753408 : ℝ) / 215002307271797819768445868016392248768867075885) * (value_032 h H) + ((-3757664377694619546458362923652317988264098016 : ℝ) / 16538639020907524597572759078184019136066698145) * (value_034 h H) + ((725223218849328993844873958023950621115365632 : ℝ) / 9347926403121644337758516000712706468211611995) * (value_257 h H) + ((-111644335025673490322596997601243526259359753408 : ℝ) / 215002307271797819768445868016392248768867075885) * (value_256 h H) + ((3757664377694619546458362923652317988264098016 : ℝ) / 16538639020907524597572759078184019136066698145) * (value_258 h H) + (1 : ℝ) * (value_259 h H)

/-- Coordinate 44.0, recovered from skew spokes on cycle 23. -/
theorem value_176 (h : Assignment) (H : Constraints h) :
    h 44 0 = ((373387608157540981246 : ℝ) / 704418962202810426877) * (h 1 0) + ((143533237735706606712 : ℝ) / 81008180653323199090855) * (h 1 1) + ((-125552494446375169052 : ℝ) / 81008180653323199090855) * (h 1 2) + ((331031354045269445631 : ℝ) / 704418962202810426877) * (h 3 0) + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (h 5 1) + ((125552494446375169052 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_160 h H)

/-- Coordinate 44.1, recovered from skew spokes on cycle 23. -/
theorem value_177 (h : Assignment) (H : Constraints h) :
    h 44 1 = ((187564067094409291744857 : ℝ) / 191601957719164436110544) * (h 1 0) + ((-5356826484880496673676599 : ℝ) / 1296130890453171185453680) * (h 1 1) + ((159315987679964401072678111 : ℝ) / 44068450275407820305425120) * (h 1 2) + ((-187564067094409291744857 : ℝ) / 191601957719164436110544) * (h 3 0) + ((6652957375333667859130279 : ℝ) / 1296130890453171185453680) * (h 5 1) + ((-159315987679964401072678111 : ℝ) / 44068450275407820305425120) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-5223844288728131369092327 : ℝ) / 527864059549812689780896) * r0 + ((-1 : ℝ) / 527864059549812689780896) * r1 + ((-5223844288728131369092327 : ℝ) / 527864059549812689780896) * (value_160 h H) + (1 : ℝ) * (value_265 h H) + ((5223844288728131369092327 : ℝ) / 527864059549812689780896) * (value_264 h H)

/-- Coordinate 44.2, recovered from skew spokes on cycle 23. -/
theorem value_178 (h : Assignment) (H : Constraints h) :
    h 44 2 = ((621191793265828350363 : ℝ) / 1408837924405620853754) * (h 1 0) + ((-58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 1 1) + ((102955657658522908490713 : ℝ) / 64806544522658559272684) * (h 1 2) + ((-621191793265828350363 : ℝ) / 1408837924405620853754) * (h 3 0) + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (h 5 1) + ((-38149113135864349218029 : ℝ) / 64806544522658559272684) * (h 9 2) := by
  have r0 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_162 h H)

/-- Coordinate 44.3, recovered from skew spokes on cycle 23. -/
theorem value_179 (h : Assignment) (H : Constraints h) :
    h 44 3 = ((-176638774353111342216 : ℝ) / 704418962202810426877) * (h 1 0) + ((8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 1 1) + ((-7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 1 2) + h 1 3 + ((176638774353111342216 : ℝ) / 704418962202810426877) * (h 3 0) + ((-8661715161776066384874 : ℝ) / 81008180653323199090855) * (h 5 1) + ((7576641911662506870429 : ℝ) / 81008180653323199090855) * (h 9 2) := by
  have r0 := H 154 3
  change ((1 : ℤ) : ℝ) * (h 44 3 - h 40 3) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_163 h H)

/-- Coordinate 69.0, recovered from skew spokes on cycle 23. -/
theorem value_276 (h : Assignment) (H : Constraints h) :
    h 69 0 = ((158310860611951215976033802 : ℝ) / 92929579232735367585149843) * (h 1 0) + ((-2658624247514620828316061234 : ℝ) / 464647896163676837925749215) * (h 1 1) + ((421820523190100863556743991 : ℝ) / 92929579232735367585149843) * (h 1 2) + ((-65381281379215848390883959 : ℝ) / 92929579232735367585149843) * (h 3 0) + ((2658624247514620828316061234 : ℝ) / 464647896163676837925749215) * (h 5 1) + ((-421820523190100863556743991 : ℝ) / 92929579232735367585149843) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((1873361454216639109599325217483395041777931447095688386636219950432647769 : ℝ) / 63402662125011678792385314843134011221593269180784426084412944331478136) * r0 + ((-17410648560203246943440167959083457515356324491508233 : ℝ) / 898435694029920706985063677042680605054502445469930) * r1 + ((-27 : ℝ) / 40889014862403561737465930920) * r2 + ((11742780465456788153840121927 : ℝ) / 488749017552276864599874640311218249149649330335641920) * r3 + ((-40032044583335528084678133 : ℝ) / 39676179000479723968354768569282999175650072558280) * r4 + ((1482668317901315854988079 : ℝ) / 10586646373227645287977376560983389168231443574480) * r5 + ((-644838835563083220127413628114202130198382388574379 : ℝ) / 126542863199327102429049195126403500743376017356459731953615771767478308480) * r6 + ((494222772633771951662693 : ℝ) / 931498562940122263173208035275127662540469329378382080) * r7 + ((-644838835563083220127413628114202130198382388574379 : ℝ) / 33402786226597336422541972426263864502049040598299701638279632352239597475338240) * r8 + ((-169444988462287501834283848052151561031478082427211 : ℝ) / 39676179000479723968354768569282999175650072558280) * (value_160 h H) + ((-2722179031666815909758113044 : ℝ) / 5111126857800445217183241365) * (value_161 h H) + ((2722179031666815909758113044 : ℝ) / 5111126857800445217183241365) * (value_265 h H) + ((209121167462767225802638616621434560207128154985491 : ℝ) / 39676179000479723968354768569282999175650072558280) * (value_264 h H)

/-- Coordinate 69.1, recovered from skew spokes on cycle 23. -/
theorem value_277 (h : Assignment) (H : Constraints h) :
    h 69 1 = ((-3227092233895563801660850797 : ℝ) / 1486873267723765881362397488) * (h 1 0) + ((41734606533185916892637085959 : ℝ) / 3717183169309414703405993720) * (h 1 1) + ((-796472063505222428400640036 : ℝ) / 92929579232735367585149843) * (h 1 2) + ((3227092233895563801660850797 : ℝ) / 1486873267723765881362397488) * (h 3 0) + ((-38017423363876502189231092239 : ℝ) / 3717183169309414703405993720) * (h 5 1) + ((796472063505222428400640036 : ℝ) / 92929579232735367585149843) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-2464582049569601574916689689447570721513996483400078444027774317580987771931 : ℝ) / 103473144588019059789172833823994706313640215303040183369761925148972317952) * r0 + ((694101064292877952268359243378035207599293559392285899 : ℝ) / 44431728868388805872715876391928931740877211848694720) * r1 + ((5313119395064164002386149319 : ℝ) / 2998174246032263209859402577659865533957797495381950720) * r2 + ((-231367021430959317422786414459345069199764519797428633 : ℝ) / 11945789695430434549070351596141566818563132061339899402907052097298498924042240) * r3 + ((1595936225754749298980155599 : ℝ) / 1962167397841906348980454009244541050141239951973120) * r4 + ((-59108749102027751814079837 : ℝ) / 523557784275985366969062986288633064319809573137920) * r5 + ((77122340476986439140928804819781689733254839932476211 : ℝ) / 18774359340118348287655298767844592110289969120522025686209176320411327221760) * r6 + ((-59108749102027751814079837 : ℝ) / 138200514065298139408970501233546213206004176867774504960) * r7 + ((77122340476986439140928804819781689733254839932476211 : ℝ) / 4955758829255168458326227181787511533394912205129555733970214545350456643613818880) * r8 + ((8336922338083276843392336720420838250659825856988873 : ℝ) / 1962167397841906348980454009244541050141239951973120) * (value_160 h H) + ((5313119395064164002386149319 : ℝ) / 3717183169309414703405993720) * (value_161 h H) + ((-1595936225754749298980155599 : ℝ) / 3717183169309414703405993720) * (value_265 h H) + ((-8336922338083276843392336720420838250659825856988873 : ℝ) / 1962167397841906348980454009244541050141239951973120) * (value_264 h H)

/-- Coordinate 69.2, recovered from skew spokes on cycle 23. -/
theorem value_278 (h : Assignment) (H : Constraints h) :
    h 69 2 = ((457728542401119020019870777 : ℝ) / 185859158465470735170299686) * (h 1 0) + ((-1085185267384402951048261791 : ℝ) / 92929579232735367585149843) * (h 1 1) + ((874649178610136512651819408 : ℝ) / 92929579232735367585149843) * (h 1 2) + ((-457728542401119020019870777 : ℝ) / 185859158465470735170299686) * (h 3 0) + ((1085185267384402951048261791 : ℝ) / 92929579232735367585149843) * (h 5 1) + ((-781719599377401145066669565 : ℝ) / 92929579232735367585149843) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((38732056021101389202988471359936686650831441451255785304308975490123069255 : ℝ) / 760831945500140145508623778117608134659119230169413113012955331977737632) * r0 + ((-23997868070419447272154196900706560202640211740965369 : ℝ) / 718748555223936565588050941634144484043601956375944) * r1 + ((-18392646721882957581892023 : ℝ) / 16166625836448478092379131546205157290948908063334048) * r2 + ((24716616625643383837742247842340704686683813697341313 : ℝ) / 579722146984124029587237650989223095606740232388553941611665763545368330137344) * r3 + ((-55177940165648872745676069 : ℝ) / 31740943200383779174683814855426399340520058046624) * r4 + ((2043627413542550842432447 : ℝ) / 8469317098582116230381901248786711334585154859584) * r5 + ((-2666429785602160808017132988967395578071134637885041 : ℝ) / 303702871678385045829718068303368401784102441655503356688677852241947940352) * r6 + ((2043627413542550842432447 : ℝ) / 2235596551056293431615699284660306390097126390508116992) * r7 + ((-2666429785602160808017132988967395578071134637885041 : ℝ) / 80166686943833607414100733823033274804917697435919283931871117645375033940811776) * r8 + ((-288240967598107426822647223911233640425498495422563 : ℝ) / 31740943200383779174683814855426399340520058046624) * (value_160 h H) + (1 : ℝ) * (value_162 h H) + ((-938024982816030836676493173 : ℝ) / 1022225371560089043436648273) * (value_161 h H) + ((938024982816030836676493173 : ℝ) / 1022225371560089043436648273) * (value_265 h H) + ((288240967598107426822647223911233640425498495422563 : ℝ) / 31740943200383779174683814855426399340520058046624) * (value_264 h H)

/-- Coordinate 69.3, recovered from skew spokes on cycle 23. -/
theorem value_279 (h : Assignment) (H : Constraints h) :
    h 69 3 = ((-118503728264286481403345688 : ℝ) / 92929579232735367585149843) * (h 1 0) + ((2371339062383857627979294082 : ℝ) / 464647896163676837925749215) * (h 1 1) + ((-377060251595859534768709821 : ℝ) / 92929579232735367585149843) * (h 1 2) + h 1 3 + ((118503728264286481403345688 : ℝ) / 92929579232735367585149843) * (h 3 0) + ((-2371339062383857627979294082 : ℝ) / 464647896163676837925749215) * (h 5 1) + ((377060251595859534768709821 : ℝ) / 92929579232735367585149843) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 156 3
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 3 - h 40 3) - ((-704124656597635355368828288 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-72150703048373921133572508360330958384506677419903148415832663179882887 : ℝ) / 2797176270221103476134646243079441671540879522681665856665276955800506) * r0 + ((7599615131195938987296832143162902854637373052432602 : ℝ) / 449217847014960353492531838521340302527251222734965) * r1 + ((2912280289236543289668867 : ℝ) / 5052070573890149403868478608189111653421533769791890) * r2 + ((-74506030697999401836243452383950027986640912278751 : ℝ) / 3552219037892916847961015018316317987786398482773002093208736296233874571920) * r3 + ((1 : ℝ) / 806571564938315825113514976) * r4 + ((513931815747625286412153 : ℝ) / 583473220595290058358158361312985281994854008210) * r5 + ((-4829652220956124858489 : ℝ) / 39502411840401661522303643884266377493400908860) * r6 + ((370676769641788068837032101412686706401198568551 : ℝ) / 83324975767774650414211498107816176960080784036299208924681149100622240) * r7 + ((-323586698804060365518763 : ℝ) / 698623922205091697379906026456345746905351997033786560) * r8 + ((24835343565999800612081150794650009328880304092917 : ℝ) / 1473652333526353077465087018805758728031575320513222131100572015539982241559040) * r9 + ((2684699780488910678608913403878893061946031850031 : ℝ) / 583473220595290058358158361312985281994854008210) * (value_160 h H) + ((2376420716017019324369795472 : ℝ) / 5111126857800445217183241365) * (value_161 h H) + (1 : ℝ) * (value_163 h H) + ((-2376420716017019324369795472 : ℝ) / 5111126857800445217183241365) * (value_265 h H) + ((-2684699780488910678608913403878893061946031850031 : ℝ) / 583473220595290058358158361312985281994854008210) * (value_264 h H)

/-- Coordinate 73.0, recovered from skew spokes on cycle 23. -/
theorem value_292 (h : Assignment) (H : Constraints h) :
    h 73 0 = ((485082301003056610789154 : ℝ) / 430132094981751925650407) * (h 1 0) + ((-144110868863848355564920998 : ℝ) / 49465190922901471449796805) * (h 1 1) + ((114320518036606348086814481 : ℝ) / 49465190922901471449796805) * (h 1 2) + ((-54950206021304685138747 : ℝ) / 430132094981751925650407) * (h 3 0) + ((144110868863848355564920998 : ℝ) / 49465190922901471449796805) * (h 5 1) + ((-114320518036606348086814481 : ℝ) / 49465190922901471449796805) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((8820267324805567820467815081610146043673072353605600886065266903211557 : ℝ) / 293464364225215225874623465092605753973936624521837552224154088659864) * r0 + ((-76080579531576138998241078746262176284358965852053 : ℝ) / 4158482481790303989653367576809815744832650157570) * r1 + ((-31457777563867387143771 : ℝ) / 93535673695487928705077114730381067567604953062440) * r2 + ((25360193177192046332747026248754058761452988617351 : ℝ) / 1118037907702058976697107702821207024047418317789154449951924983967651589440) * r3 + ((-94373332691602161431313 : ℝ) / 183644412632137136146094713603990917780761431720) * r4 + ((27 : ℝ) / 378516243583941694572358160) * r5 + ((-21766484119674912919520412487 : ℝ) / 4524428940187850740742863923569079530377923371436160) * r6 + ((1165102872735829153473 : ℝ) / 4311516652265084302892988094327079706311148742257920) * r7 + ((-2817799241910227370305225138750450973494776513039 : ℝ) / 154607505344356353132294723004037631185582916980438309416078958913047022581760) * r8 + ((-309347182357128664353865549079911569135204403631 : ℝ) / 183644412632137136146094713603990917780761431720) * (value_160 h H) + ((-6417386623028946977329284 : ℝ) / 23657265223996355910772385) * (value_161 h H) + ((6417386623028946977329284 : ℝ) / 23657265223996355910772385) * (value_265 h H) + ((492991594989265800499960262683902486915965835351 : ℝ) / 183644412632137136146094713603990917780761431720) * (value_264 h H)

/-- Coordinate 73.1, recovered from skew spokes on cycle 23. -/
theorem value_293 (h : Assignment) (H : Constraints h) :
    h 73 1 = ((75046433451119088004039581 : ℝ) / 116995929835036523776910704) * (h 1 0) + ((-3936498959634851487470940513 : ℝ) / 1582886109532847086393497760) * (h 1 1) + ((124284974950167962944205166943 : ℝ) / 53818127724116800937378923840) * (h 1 2) + ((-75046433451119088004039581 : ℝ) / 116995929835036523776910704) * (h 3 0) + ((5519385069167698573864438273 : ℝ) / 1582886109532847086393497760) * (h 5 1) + ((-124284974950167962944205166943 : ℝ) / 53818127724116800937378923840) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-8398045679360728318338607575935446856734353153764673702578396488789432483 : ℝ) / 319289228277034165751590330020755060323643047479759256819879648461932032) * r0 + ((46738824988712509339391706550848699318866030327479179 : ℝ) / 4524428940187850740742863923569079530377923371436160) * r1 + ((19325556786554422776888453 : ℝ) / 101766812980690866431123900826654601513554188931934720) * r2 + ((-15579608329570836446463902183616233106288676775826393 : ℝ) / 1216425243579840166646453180669473242163591129754600041547694382556804929310720) * r3 + ((-320539573224278426241692801 : ℝ) / 199805120943765204126951048401142118545468437711360) * r4 + ((320539573224278426241692801 : ℝ) / 1439457824103557872285862555320483207969686935915520) * r5 + ((5193202776523612148821300727872077702096225591942131 : ℝ) / 1911770189801254254664919846981665072124764752965202621610493438678406881280) * r6 + ((-715761362464978621366239 : ℝ) / 4690930117664411721547571046627862720466529831576616960) * r7 + ((5193202776523612148821300727872077702096225591942131 : ℝ) / 504638897443979136623809975885178828189742641024150641934081721892185481706864640) * r8 + ((-1674448818898999518144360297668177946329191340237927 : ℝ) / 199805120943765204126951048401142118545468437711360) * (value_160 h H) + ((57976670359663268330665359 : ℝ) / 378516243583941694572358160) * (value_161 h H) + ((320539573224278426241692801 : ℝ) / 378516243583941694572358160) * (value_265 h H) + ((1674448818898999518144360297668177946329191340237927 : ℝ) / 199805120943765204126951048401142118545468437711360) * (value_264 h H)

/-- Coordinate 73.2, recovered from skew spokes on cycle 23. -/
theorem value_294 (h : Assignment) (H : Constraints h) :
    h 73 2 = ((1295134093827935973718659 : ℝ) / 860264189963503851300814) * (h 1 0) + ((-277343704725602265677456865 : ℝ) / 39572152738321177159837444) * (h 1 1) + ((2258753901926311137915028019 : ℝ) / 395721527383211771598374440) * (h 1 2) + ((-1295134093827935973718659 : ℝ) / 860264189963503851300814) * (h 3 0) + ((277343704725602265677456865 : ℝ) / 39572152738321177159837444) * (h 5 1) + ((-1863032374543099366316653579 : ℝ) / 395721527383211771598374440) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((364504395392830129824913971590443352937228639621228106572438740346960487 : ℝ) / 7043144741405165420990963162222538095374478988524101253379698127836736) * r0 + ((-1050831529310945992699004004818276886915762069137349 : ℝ) / 33267859854322431917226940614478525958661201260560) * r1 + ((-448253123878103705473563 : ℝ) / 748285389563903429640616917843048540540839624499520) * r2 + ((1084099389165268424616230945432755412874423270397909 : ℝ) / 26832909784849415440730584867708968577138039626939706798846199615223638146560) * r3 + ((-1344759371634311116420689 : ℝ) / 1469155301057097089168757708831927342246091453760) * r4 + ((49805902653122633941507 : ℝ) / 392009211357178069794624878899913727660590124160) * r5 + ((-116759058812327332522111556090919654101751341015261 : ℝ) / 14057133748538634225477351816041654942093858477685313394194804696164756480) * r6 + ((49805902653122633941507 : ℝ) / 103476399654362023269431714263849912951467569814190080) * r7 + ((-1084099389165268424616230945432755412874423270397909 : ℝ) / 33395221154380972276575660168872128336085910067774674833873055125218156877660160) * r8 + ((-7024813563225526832696947556750627703939013953303 : ℝ) / 1469155301057097089168757708831927342246091453760) * (value_160 h H) + (1 : ℝ) * (value_162 h H) + ((-22860909317783288979151713 : ℝ) / 47314530447992711821544770) * (value_161 h H) + ((22860909317783288979151713 : ℝ) / 47314530447992711821544770) * (value_265 h H) + ((7024813563225526832696947556750627703939013953303 : ℝ) / 1469155301057097089168757708831927342246091453760) * (value_264 h H)

/-- Coordinate 73.3, recovered from skew spokes on cycle 23. -/
theorem value_295 (h : Assignment) (H : Constraints h) :
    h 73 3 = ((-335616215828377762979568 : ℝ) / 430132094981751925650407) * (h 1 0) + ((133037823446536300935042744 : ℝ) / 49465190922901471449796805) * (h 1 1) + ((-105973566221906182221802206 : ℝ) / 49465190922901471449796805) * (h 1 2) + h 1 3 + ((335616215828377762979568 : ℝ) / 430132094981751925650407) * (h 3 0) + ((-133037823446536300935042744 : ℝ) / 49465190922901471449796805) * (h 5 1) + ((105973566221906182221802206 : ℝ) / 49465190922901471449796805) * (h 9 2) := by
  have r0 := H 154 0
  change ((1 : ℤ) : ℝ) * (h 44 0 - h 40 0) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 154 2
  change ((1 : ℤ) : ℝ) * (h 44 2 - h 40 2) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 154 3
  change ((1 : ℤ) : ℝ) * (h 44 3 - h 40 3) - ((0 : ℤ) : ℝ) * (h 44 1 - h 40 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 156 1
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 1 - h 40 1) - ((-650196240122305269954878207 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 156 2
  change ((806571564938315825113514976 : ℤ) : ℝ) * (h 69 2 - h 40 2) - ((1389666641208934572854063960 : ℤ) : ℝ) * (h 69 0 - h 40 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 166 1
  change ((527864059549812689780896 : ℤ) : ℝ) * (h 66 1 - h 44 1) - ((-5223844288728131369092327 : ℤ) : ℝ) * (h 66 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 167 1
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 1 - h 44 1) - ((-2147284087394935864098717 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 167 2
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 2 - h 44 2) - ((6773602760824678216044952 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 167 3
  change ((3802895776609746356935872 : ℤ) : ℝ) * (h 73 3 - h 44 3) - ((-3369073632315099153808448 : ℤ) : ℝ) * (h 73 0 - h 44 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 216 1
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 1 - h 69 1) - ((4901999946616340759521344617089 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 216 2
  change ((-1003828358680607840170309825536 : ℤ) : ℝ) * (h 73 2 - h 69 2) - ((-1668842356399561387523261789208 : ℤ) : ℝ) * (h 73 0 - h 69 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-1333075172955570244433993418715244580161299728933596943216831080714333 : ℝ) / 51787828980920333977874729133989250701282933739147803333674250939976) * r0 + ((67401551209376913838738001880135869416199229729127 : ℝ) / 4158482481790303989653367576809815744832650157570) * r1 + (1 : ℝ) * r2 + ((27869175267312401088489 : ℝ) / 93535673695487928705077114730381067567604953062440) * r3 + ((-3964797129963347872866941287066815848011719395831 : ℝ) / 197300807241539819417136653439036533655426761962791961756222055994291456960) * r4 + ((4918089753055129603851 : ℝ) / 10802612507772772714476159623764171634162437160) * r5 + ((-46217537756736983563 : ℝ) / 731360468949959085437732983022227103844384560) * r6 + ((59176076566617132430849869956221132059876408893 : ℝ) / 13884350717388905622179122733140352774236690770321314809893902794719360) * r7 + ((1 : ℝ) / 3802895776609746356935872) * r8 + ((-3096575029701377898721 : ℝ) / 12934549956795252908678964282981239118933446226773760) * r9 + ((3964797129963347872866941287066815848011719395831 : ℝ) / 245553096723389502033644560065236237765337574027754962013772464156015859394560) * r10 + ((25691335067949384755387725076642777252953751277 : ℝ) / 10802612507772772714476159623764171634162437160) * (value_160 h H) + (1 : ℝ) * (value_163 h H) + ((5685311754531729822051756 : ℝ) / 23657265223996355910772385) * (value_161 h H) + ((-5685311754531729822051756 : ℝ) / 23657265223996355910772385) * (value_265 h H) + ((-25691335067949384755387725076642777252953751277 : ℝ) / 10802612507772772714476159623764171634162437160) * (value_264 h H)

/-- Coordinate 46.0, recovered from skew spokes on cycle 24. -/
theorem value_184 (h : Assignment) (H : Constraints h) :
    h 46 0 = ((50182337158358922070838 : ℝ) / 67703568293298537493335) * (h 1 0) + ((-22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 1 1) + ((519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 1 2) + ((17521231134939615422497 : ℝ) / 67703568293298537493335) * (h 3 0) + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (h 5 1) + ((-519734538873226253932652 : ℝ) / 338517841466492687466675) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_168 h H)

/-- Coordinate 46.1, recovered from skew spokes on cycle 24. -/
theorem value_185 (h : Assignment) (H : Constraints h) :
    h 46 1 = ((46486447366095334287530017 : ℝ) / 45015350296344272040012960) * (h 1 0) + ((-232459156312884988920142587 : ℝ) / 50752600824309718476485200) * (h 1 1) + ((1885502045648956021241156539 : ℝ) / 470615025825417389509226400) * (h 1 2) + ((-46486447366095334287530017 : ℝ) / 45015350296344272040012960) * (h 3 0) + ((283211757137194707396627787 : ℝ) / 50752600824309718476485200) * (h 5 1) + ((-1885502045648956021241156539 : ℝ) / 470615025825417389509226400) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((217336141236379020593247 : ℝ) / 853677112946252813688448) * r0 + ((1 : ℝ) / 853677112946252813688448) * r1 + ((217336141236379020593247 : ℝ) / 853677112946252813688448) * (value_168 h H) + (1 : ℝ) * (value_177 h H) + ((-217336141236379020593247 : ℝ) / 853677112946252813688448) * (value_176 h H)

/-- Coordinate 46.2, recovered from skew spokes on cycle 24. -/
theorem value_186 (h : Assignment) (H : Constraints h) :
    h 46 2 = ((1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 1 0) + ((-12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 1 1) + ((54965293097119131924855289 : ℝ) / 31143641414917327246934100) * (h 1 2) + ((-1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (h 3 0) + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (h 5 1) + ((-23821651682201804677921189 : ℝ) / 31143641414917327246934100) * (h 9 2) := by
  have r0 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_170 h H)

/-- Coordinate 46.3, recovered from skew spokes on cycle 24. -/
theorem value_187 (h : Assignment) (H : Constraints h) :
    h 46 3 = ((-197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 1 0) + ((702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 1 1) + ((-1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 1 2) + h 1 3 + ((197004103519997441171332 : ℝ) / 744739251226283912426685) * (h 3 0) + ((-702618985889944829564302 : ℝ) / 3172037551519357404780325) * (h 5 1) + ((1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (h 9 2) := by
  have r0 := H 160 3
  change ((1 : ℤ) : ℝ) * (h 46 3 - h 42 3) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_171 h H)

/-- Coordinate 71.0, recovered from skew spokes on cycle 24. -/
theorem value_284 (h : Assignment) (H : Constraints h) :
    h 71 0 = ((20665430186437121202991110230 : ℝ) / 16181147326473197854629668721) * (h 1 0) + ((-13379951895815089576602050242 : ℝ) / 2996508764161703306412901615) * (h 1 1) + ((59937059233222266171502165333 : ℝ) / 16181147326473197854629668721) * (h 1 2) + ((-4484282859963923348361441509 : ℝ) / 16181147326473197854629668721) * (h 3 0) + ((13379951895815089576602050242 : ℝ) / 2996508764161703306412901615) * (h 5 1) + ((-59937059233222266171502165333 : ℝ) / 16181147326473197854629668721) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-274786941065412008667605711608391584664510326511271133350131139801425100577 : ℝ) / 33596063407895046253892515499470697454412380187446430882462878589747861920) * r0 + ((7647857008632859252877684658129095212247950984933232 : ℝ) / 2676108187851460450980853808289947050972417184277345) * r1 + ((-3 : ℝ) / 70994207643215739875013361340) * r2 + ((-262103807333149974618612401 : ℝ) / 500432231128223104333419662150220098531842013459863515) * r3 + ((781573204966291115410083 : ℝ) / 2893722794918220394739279113651064808347672269280) * r4 + ((781573204966291115410083 : ℝ) / 10178242024182730820252055866552222791189834307140) * r5 + ((477991063039553703304855291133068450765496936558327 : ℝ) / 502219036446712489766284035589142126190508768598025079796226564150138485955) * r6 + ((260524401655430371803361 : ℝ) / 82435477521054890444409769241379925859913744453565860) * r7 + ((68284437577079100472122184447581207252213848079761 : ℝ) / 1743242356361062267690373569578925677360184532539878675511641800505863028788055) * r8 + ((3063586899379343649556949171382747431350017778781 : ℝ) / 2893722794918220394739279113651064808347672269280) * (value_168 h H) + ((-53146977937707795847885644 : ℝ) / 230500674166284869724069355) * (value_169 h H) + ((53146977937707795847885644 : ℝ) / 230500674166284869724069355) * (value_177 h H) + ((-169864104461123254817670057731682623002345509501 : ℝ) / 2893722794918220394739279113651064808347672269280) * (value_176 h H)

/-- Coordinate 71.1, recovered from skew spokes on cycle 24. -/
theorem value_285 (h : Assignment) (H : Constraints h) :
    h 71 1 = ((-1028330136854063252507923764059 : ℝ) / 517796714447142331348149399072) * (h 1 0) + ((512236822229444639308343220177 : ℝ) / 47944140226587252902606425840) * (h 1 1) + ((-4250899001679056885007915587155 : ℝ) / 517796714447142331348149399072) * (h 1 2) + ((1028330136854063252507923764059 : ℝ) / 517796714447142331348149399072) * (h 3 0) + ((-464292682002857386405736794337 : ℝ) / 47944140226587252902606425840) * (h 5 1) + ((4250899001679056885007915587155 : ℝ) / 517796714447142331348149399072) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((1065175193441484621370768707022778896478914699926139801215413127505454440936979 : ℝ) / 100519421716421978391646406374416326783601841520839721200328932740525602864640) * r0 + ((-1852869066711789620979668344256967668362486985321346229 : ℝ) / 500432231128223104333419662150220098531842013459863515) * r1 + ((13171694706934723429643514461 : ℝ) / 55339204614012485470513228875675947197133487429435510080) * r2 + ((11508503519949003857016573566813463778648987486467989 : ℝ) / 16960061925680300277854417407751813618268939442614189859173422616985342912850160) * r3 + ((-3029665043618189161784462841 : ℝ) / 8658018602395315421059923108043985906576235429685760) * r4 + ((-3029665043618189161784462841 : ℝ) / 30453300136354730614194151152724250591239984246962880) * r5 + ((-1852869066711789620979668344256967668362486985321346229 : ℝ) / 1502639357048563769380721834482713241562002235645291038750309879937214349977360) * r6 + ((-1009888347872729720594820947 : ℝ) / 246646948742996232209674029570208738172861923405069053120) * r7 + ((-264695580958827088711381192036709666908926712188763747 : ℝ) / 5215781130232298304929597720180145626661672121359316997130832267113542182133860560) * r8 + ((-658455709818723165566324333989429224243143047034727 : ℝ) / 8658018602395315421059923108043985906576235429685760) * (value_168 h H) + ((13171694706934723429643514461 : ℝ) / 10142029663316534267859051620) * (value_169 h H) + ((-3029665043618189161784462841 : ℝ) / 10142029663316534267859051620) * (value_177 h H) + ((658455709818723165566324333989429224243143047034727 : ℝ) / 8658018602395315421059923108043985906576235429685760) * (value_176 h H)

/-- Coordinate 71.2, recovered from skew spokes on cycle 24. -/
theorem value_286 (h : Assignment) (H : Constraints h) :
    h 71 2 = ((1021003474254000833751307629833 : ℝ) / 453072125141249539929630724188) * (h 1 0) + ((-66287825663355286117291959149 : ℝ) / 5993017528323406612825803230) * (h 1 1) + ((4078643275538802490675336547185 : ℝ) / 453072125141249539929630724188) * (h 1 2) + ((-1021003474254000833751307629833 : ℝ) / 453072125141249539929630724188) * (h 3 0) + ((66287825663355286117291959149 : ℝ) / 5993017528323406612825803230) * (h 5 1) + ((-3625571150397552950745705822997 : ℝ) / 453072125141249539929630724188) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-141212363408788857935870832300644126814523320432147199290823233234515029854493 : ℝ) / 5173793764815837123099447386918487407979506548866750355899283302821170735680) * r0 + ((280729696306895894343103981161325463164875914019941992 : ℝ) / 29437190066366064960789391891189417560696589027050795) * r1 + ((-401648633746387087923735447 : ℝ) / 2848341413956524987452886780365673752793635382397415960) * r2 + ((-1560823020127514468213134094845565500647076552750877 : ℝ) / 997650701510605898697318671044224330486408202506717050539613095116784877226480) * r3 + ((401648633746387087923735447 : ℝ) / 445633310417405940789848983502263980485541529469120) * r4 + ((401648633746387087923735447 : ℝ) / 1567449271724140546318816603449042309843234483299560) * r5 + ((35091212038361986792887997645165682895609489252492749 : ℝ) / 11048818801827674774858248782961126776191192909156551755516984411303046691010) * r6 + ((133882877915462362641245149 : ℝ) / 12695063538242453128439104463172508582426716645849142440) * r7 + ((35091212038361986792887997645165682895609489252492749 : ℝ) / 268459322879603589224317529715154554313468418011141316028792837277902906433360470) * r8 + ((87292764191303453049159119764099347450614222726409 : ℝ) / 445633310417405940789848983502263980485541529469120) * (value_168 h H) + (1 : ℝ) * (value_170 h H) + ((-13656053547377160989407005198 : ℝ) / 17748551910803934968753340335) * (value_169 h H) + ((13656053547377160989407005198 : ℝ) / 17748551910803934968753340335) * (value_177 h H) + ((-87292764191303453049159119764099347450614222726409 : ℝ) / 445633310417405940789848983502263980485541529469120) * (value_176 h H)

/-- Coordinate 71.3, recovered from skew spokes on cycle 24. -/
theorem value_287 (h : Assignment) (H : Constraints h) :
    h 71 3 = ((-132166455728534812477523488076 : ℝ) / 113268031285312384982407681047) * (h 1 0) + ((14335953079860154106054582218 : ℝ) / 2996508764161703306412901615) * (h 1 1) + ((-435550986958983084455269195813 : ℝ) / 113268031285312384982407681047) * (h 1 2) + h 1 3 + ((132166455728534812477523488076 : ℝ) / 113268031285312384982407681047) * (h 3 0) + ((-14335953079860154106054582218 : ℝ) / 2996508764161703306412901615) * (h 5 1) + ((435550986958983084455269195813 : ℝ) / 113268031285312384982407681047) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 162 3
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 3 - h 42 3) - ((-9186827508067161043536414976 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((2226508502041644293031890654295723685462807527890663446313961430540166979641 : ℝ) / 161681055150494910096857730841202731499359579652085948621852603213161585490) * r0 + ((-141641321598665733666537177799273912453137519013865728 : ℝ) / 29437190066366064960789391891189417560696589027050795) * r1 + ((25331325849449892583280556 : ℝ) / 356042676744565623431610847545709219099204422799676995) * r2 + ((520740152936271079656386683085565854607123231668624 : ℝ) / 590521187291204226802457007493088666207028384571990607120873927624273401593615) * r3 + ((1 : ℝ) / 5456423068271333707049592784) * r4 + ((-6332831462362473145820139 : ℝ) / 13926040950543935649682780734445749390173172795910) * r5 + ((-25331325849449892583280556 : ℝ) / 195931158965517568289852075431130288730404310412445) * r6 + ((-520740152936271079656386683085565854607123231668624 : ℝ) / 324965258877284552201713199498856669887976262034016228103440717979501373265) * r7 + ((-8443775283149964194426852 : ℝ) / 1586882942280306641054888057896563572803339580731142805) * r8 + ((-520740152936271079656386683085565854607123231668624 : ℝ) / 7895862437635399683068162638681016303337306412092391647905671684644203130392955) * r9 + ((-1376353153130195155384020843881030659422140001333 : ℝ) / 13926040950543935649682780734445749390173172795910) * (value_168 h H) + ((6890120631050370782652311232 : ℝ) / 17748551910803934968753340335) * (value_169 h H) + (1 : ℝ) * (value_171 h H) + ((-6890120631050370782652311232 : ℝ) / 17748551910803934968753340335) * (value_177 h H) + ((1376353153130195155384020843881030659422140001333 : ℝ) / 13926040950543935649682780734445749390173172795910) * (value_176 h H)

/-- Coordinate 75.0, recovered from skew spokes on cycle 24. -/
theorem value_300 (h : Assignment) (H : Constraints h) :
    h 75 0 = ((525963403612626633064709654 : ℝ) / 484262205680419302549236265) * (h 1 0) + ((-7217593650578870064146152214 : ℝ) / 2062598283453637770117117425) * (h 1 1) + ((163233951289965804929195203843 : ℝ) / 55690153653248219793162170475) * (h 1 2) + ((-41701197932207330515473389 : ℝ) / 484262205680419302549236265) * (h 3 0) + ((7217593650578870064146152214 : ℝ) / 2062598283453637770117117425) * (h 5 1) + ((-163233951289965804929195203843 : ℝ) / 55690153653248219793162170475) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-25360293398137110963782021791005559135634617477935451548388797857025721 : ℝ) / 3093686448772213244990070506686831289773102996948001308409986724027424) * r0 + ((696194424879107539553224746355338649204729227776 : ℝ) / 246428860896210249645590460977309354184510263109) * r1 + ((-3010711572161095845291 : ℝ) / 110706362919666380835989798046290952459445252155820) * r2 + ((-270261810900274665975630724516824009784444576 : ℝ) / 521979860746082770300937802140865637443562174748083952555963598092836881) * r3 + ((3010711572161095845291 : ℝ) / 17320410660895124008603860547337559693283059040) * r4 + ((3 : ℝ) / 60705233760508402598764660) * r5 + ((43357343118435383562870688 : ℝ) / 46082196987591316683725416202756849232503419201383) * r6 + ((1003570524053698615097 : ℝ) / 493418487147111492099760735754877276689265176716980) * r7 + ((6216021650706317317439506663886952225042225248 : ℝ) / 160526106565586452993626202101073242153484419485851300232411404397701074771) * r8 + ((17974747096364328662666734235454371515034408917 : ℝ) / 17320410660895124008603860547337559693283059040) * (value_168 h H) + ((-204728386906954517479788 : ℝ) / 1379664403647918240881015) * (value_169 h H) + ((204728386906954517479788 : ℝ) / 1379664403647918240881015) * (value_177 h H) + ((-654336435469204654062873688116811821751349877 : ℝ) / 17320410660895124008603860547337559693283059040) * (value_176 h H)

/-- Coordinate 75.1, recovered from skew spokes on cycle 24. -/
theorem value_301 (h : Assignment) (H : Constraints h) :
    h 75 1 = ((18599735720609192380853033861 : ℝ) / 29270959987794233398531614240) * (h 1 0) + ((-84863619960320346321878670681 : ℝ) / 33001572535258204321873878800) * (h 1 1) + ((8074956830011493968555468420447 : ℝ) / 3366160398596336840831135637600) * (h 1 2) + ((-18599735720609192380853033861 : ℝ) / 29270959987794233398531614240) * (h 3 0) + ((117865192495578550643752549481 : ℝ) / 33001572535258204321873878800) * (h 5 1) + ((-8074956830011493968555468420447 : ℝ) / 3366160398596336840831135637600) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((11156696929237927417798696050351576250093921245772370321109542994707220803 : ℝ) / 1028478872747384669890032328445222135444569351874268879418075586476672512) * r0 + ((-16660542000129780851432571302940168624515795786848 : ℝ) / 5120244109732368520413935133639649914722602133487) * r1 + ((10375050721505950475398917 : ℝ) / 331233437855641811461281475754502529758660194450213440) * r2 + ((6467601708124914926798358425054413285914516998 : ℝ) / 10845581551057497560697263222260208244660680741987966569773910315928944083) * r3 + ((50330183039002452123365743 : ℝ) / 51822668697398211033742750757633978602302912647680) * r4 + ((50330183039002452123365743 : ℝ) / 182278573907444399692896293239769116271038007483840) * r5 + ((-1041283875008111303214535706433760539032237236678 : ℝ) / 960904374059064622974049966483952086224866537625314287041232822933755693) * r6 + ((-1152783413500661163933213 : ℝ) / 492102704514719194787494707126197603951427136245734720) * r7 + ((-148754839286873043316362243776251505576033890954 : ℝ) / 3335375769751629634423122199211188475855731827094910349273436958041122331353) * r8 + ((10938567769417444807067818023074964146742216937521 : ℝ) / 51822668697398211033742750757633978602302912647680) * (value_168 h H) + ((10375050721505950475398917 : ℝ) / 60705233760508402598764660) * (value_169 h H) + ((50330183039002452123365743 : ℝ) / 60705233760508402598764660) * (value_177 h H) + ((-10938567769417444807067818023074964146742216937521 : ℝ) / 51822668697398211033742750757633978602302912647680) * (value_176 h H)

/-- Coordinate 75.2, recovered from skew spokes on cycle 24. -/
theorem value_302 (h : Assignment) (H : Constraints h) :
    h 75 2 = ((2888909663545370771091460211 : ℝ) / 1937048822721677210196945060) * (h 1 0) + ((-14865341638549968439249778579 : ℝ) / 2062598283453637770117117425) * (h 1 1) + ((329575769576386775712360349048 : ℝ) / 55690153653248219793162170475) * (h 1 2) + ((-2888909663545370771091460211 : ℝ) / 1937048822721677210196945060) * (h 3 0) + ((14865341638549968439249778579 : ℝ) / 2062598283453637770117117425) * (h 5 1) + ((-273885615923138555919198178573 : ℝ) / 55690153653248219793162170475) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-3725224160351709195146722992450182370860087582230143113597441989742475005 : ℝ) / 136122203745977382779563102294220576750016531865712057570039415857206656) * r0 + ((25497339111325443976834272586122237525288117410935 : ℝ) / 2710717469858312746101495070750402896029612894199) * r1 + ((-394165440082830106531479 : ℝ) / 4871079968465320756783551114036801908215591094856080) * r2 + ((-8845738214855252806961481954725091082786686536 : ℝ) / 5741778468206910473310315823549522011879183922228923478115599579021205691) * r3 + ((394165440082830106531479 : ℝ) / 762098069079385456378569864082852626504454597760) * r4 + ((394165440082830106531479 : ℝ) / 2680567263344770583719063135878957592221147168880) * r5 + ((25497339111325443976834272586122237525288117410935 : ℝ) / 8139425286147370924015482069040535318610634201061485725525736853085930576) * r6 + ((131388480027610035510493 : ℝ) / 21710413434472905652389472373214600174327667775547120) * r7 + ((203451978941670814560114084958677094904093790328 : ℝ) / 1765787172221450982929888223111805663688328614344364302556525448374711822481) * r8 + ((85666395756341456390656105123764317380060322313 : ℝ) / 762098069079385456378569864082852626504454597760) * (value_168 h H) + (1 : ℝ) * (value_170 h H) + ((-6700812481408111811035143 : ℝ) / 15176308440127100649691165) * (value_169 h H) + ((6700812481408111811035143 : ℝ) / 15176308440127100649691165) * (value_177 h H) + ((-85666395756341456390656105123764317380060322313 : ℝ) / 762098069079385456378569864082852626504454597760) * (value_176 h H)

/-- Coordinate 75.3, recovered from skew spokes on cycle 24. -/
theorem value_303 (h : Assignment) (H : Constraints h) :
    h 75 3 = ((-374310634616781284906585336 : ℝ) / 484262205680419302549236265) * (h 1 0) + ((5759642033963314397148106256 : ℝ) / 2062598283453637770117117425) * (h 1 1) + ((-125373544643667335704090026622 : ℝ) / 55690153653248219793162170475) * (h 1 2) + h 1 3 + ((374310634616781284906585336 : ℝ) / 484262205680419302549236265) * (h 3 0) + ((-5759642033963314397148106256 : ℝ) / 2062598283453637770117117425) * (h 5 1) + ((125373544643667335704090026622 : ℝ) / 55690153653248219793162170475) * (h 9 2) := by
  have r0 := H 160 0
  change ((1 : ℤ) : ℝ) * (h 46 0 - h 42 0) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 160 2
  change ((1 : ℤ) : ℝ) * (h 46 2 - h 42 2) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 160 3
  change ((1 : ℤ) : ℝ) * (h 46 3 - h 42 3) - ((0 : ℤ) : ℝ) * (h 46 1 - h 42 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 162 1
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 1 - h 42 1) - ((-7069218435109108044163746629 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 162 2
  change ((5456423068271333707049592784 : ℤ) : ℝ) * (h 71 2 - h 42 2) - ((18208071396502881319209340264 : ℤ) : ℝ) * (h 71 0 - h 42 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 165 1
  change ((853677112946252813688448 : ℤ) : ℝ) * (h 46 1 - h 44 1) - ((217336141236379020593247 : ℤ) : ℝ) * (h 46 0 - h 44 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 171 1
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 1 - h 46 1) - ((-3458350240501983491799639 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 171 2
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 2 - h 46 2) - ((8934416641877482414713524 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 171 3
  change ((3002683007968666256370224 : ℤ) : ℝ) * (h 75 3 - h 46 3) - ((-4426224833314726983043856 : ℤ) : ℝ) * (h 75 0 - h 46 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 219 1
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 1 - h 71 1) - ((1001229873070670510868092533993 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 219 2
  change ((-72957866501350917195740659728 : ℤ) : ℝ) * (h 75 2 - h 71 2) - ((-291084989523996057055932712833 : ℤ) : ℝ) * (h 75 0 - h 71 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((461380981801510184985061884632800560668962232277743385844238151112170305 : ℝ) / 34030550936494345694890775573555144187504132966428014392509853964301664) * r0 + ((-11288785224550945919077689151905134625582797699584 : ℝ) / 2710717469858312746101495070750402896029612894199) * r1 + (1 : ℝ) * r2 + ((48818656249794782901219 : ℝ) / 1217769992116330189195887778509200477053897773714020) * r3 + ((257781905931470266694320632807479325575054752 : ℝ) / 337751674600406498430018577855854235992893171895819028124447034060070923) * r4 + ((-48818656249794782901219 : ℝ) / 190524517269846364094642466020713156626113649440) * r5 + ((-48818656249794782901219 : ℝ) / 670141815836192645929765783969739398055286792220) * r6 + ((-41502886854966712937785621882004171417583815072 : ℝ) / 29924357669659451926527507606766673965480272798020168108550503136345333) * r7 + ((1 : ℝ) / 3002683007968666256370224) * r8 + ((-16272885416598260967073 : ℝ) / 5427603358618226413097368093303650043581916943886780) * r9 + ((-5928983836423816133969374554572024488226259296 : ℝ) / 103869833660085351937052248418341509628725212608492017797442673433806577793) * r10 + ((-10610058369675636308688609003403909597179468093 : ℝ) / 190524517269846364094642466020713156626113649440) * (value_168 h H) + (1 : ℝ) * (value_171 h H) + ((3319668624986045237282892 : ℝ) / 15176308440127100649691165) * (value_169 h H) + ((-3319668624986045237282892 : ℝ) / 15176308440127100649691165) * (value_177 h H) + ((10610058369675636308688609003403909597179468093 : ℝ) / 190524517269846364094642466020713156626113649440) * (value_176 h H)

/-- Coordinate 45.0, recovered from nonplanar cycle 25. -/
theorem value_180 (h : Assignment) (H : Constraints h) :
    h 45 0 = ((17126635218530564174956 : ℝ) / 183708538376905553243199) * (h 1 0) + ((25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 1 1) + ((-6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 1 2) + ((166581903158374989068243 : ℝ) / 183708538376905553243199) * (h 3 0) + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (h 5 1) + ((6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-7483037529584019792008075 : ℝ) / 4165651268960339275354115306429716767313103203504) * r0 + ((-222297413406356337359743887 : ℝ) / 566528572578606141448159681674441480354582035676544) * r1 + ((50940348951282634021766832682486207940378880925 : ℝ) / 76511585396648381213674615181073157185441627005160184975783614753077008) * r2 + ((89016288035114024366069897813115997964182744809 : ℝ) / 612092683173187049709396921448585257483533016041281479806268918024616064) * r3 + ((-2996491114781331413045107804852129878845816525 : ℝ) / 5559426638262668377959656209078416324549020281221372682046351387763973) * r4 + ((-89016288035114024366069897813115997964182744809 : ℝ) / 756082022803722899402513244434664620138666758246106684758303788735900328) * r5 + ((203761395805130536087067330729944831761515523700 : ℝ) / 20027169562309323439202477434758253689005303863) * (value_177 h H) + ((22330687354138031378279951826364750392791363 : ℝ) / 99761741281740091851569003411000018376116084) * (value_176 h H) + ((89016288035114024366069897813115997964182744809 : ℝ) / 40054339124618646878404954869516507378010607726) * (value_178 h H) + ((-203761395805130536087067330729944831761515523700 : ℝ) / 20027169562309323439202477434758253689005303863) * (value_185 h H) + ((77431053927602060473289051584635267983324721 : ℝ) / 99761741281740091851569003411000018376116084) * (value_184 h H) + ((-89016288035114024366069897813115997964182744809 : ℝ) / 40054339124618646878404954869516507378010607726) * (value_186 h H)

/-- Coordinate 45.1, recovered from nonplanar cycle 25. -/
theorem value_181 (h : Assignment) (H : Constraints h) :
    h 45 1 = ((1550956070874721031953414451 : ℝ) / 1299186783401476072535903328) * (h 1 0) + ((-1734546100744891843958432241 : ℝ) / 292953882531705388905154672) * (h 1 1) + ((14069096150486344956551728177 : ℝ) / 2716481456203086333484161504) * (h 1 2) + ((-1550956070874721031953414451 : ℝ) / 1299186783401476072535903328) * (h 3 0) + ((2027499983276597232863586913 : ℝ) / 292953882531705388905154672) * (h 5 1) + ((-14069096150486344956551728177 : ℝ) / 2716481456203086333484161504) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((981216336610933620440118019901120518977476155263 : ℝ) / 1387846092604329875763891332459235567779908528662982321707356869033501696) * r0 + ((619278601166097264102159731139435340418631004251411 : ℝ) / 3208700166101210672766116760645752632707148518268815127787409081205455921152) * r1 + ((-20846328991346210822836121644748765589930197842975 : ℝ) / 63657639050011453169777279830652866778287433668293273899851967474560070656) * r2 + ((-619278601166097264102159731139435340418631004251411 : ℝ) / 8657438910801557631089710056968789881847090978887885250379867576540169609216) * r3 + ((20846328991346210822836121644748765589930197842975 : ℝ) / 78632530371587181537861377421205120494421342857595095214863594028533634112) * r4 + ((619278601166097264102159731139435340418631004251411 : ℝ) / 10694024130535856689149147329283896387241302628632932949221448787880574239232) * r5 + ((-16680677722385871547482006338319048822617094639471 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_177 h H) + ((538681131527151335838120303108603666326897196459 : ℝ) / 1411030068688931859148591984245184259911785892096) * (value_176 h H) + ((-619278601166097264102159731139435340418631004251411 : ℝ) / 566528572578606141448159681674441480354582035676544) * (value_178 h H) + ((20846328991346210822836121644748765589930197842975 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_185 h H) + ((-538681131527151335838120303108603666326897196459 : ℝ) / 1411030068688931859148591984245184259911785892096) * (value_184 h H) + ((619278601166097264102159731139435340418631004251411 : ℝ) / 566528572578606141448159681674441480354582035676544) * (value_186 h H)

/-- Coordinate 45.2, recovered from nonplanar cycle 25. -/
theorem value_182 (h : Assignment) (H : Constraints h) :
    h 45 2 = ((-4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 1 0) + ((1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 1 1) + ((-524424025816764199423282393 : ℝ) / 99870641772172291672211820) * (h 1 2) + ((4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (h 3 0) + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (h 5 1) + ((624294667588936491095494213 : ℝ) / 99870641772172291672211820) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-670346879179343207241141274360705634499206811575 : ℝ) / 173480761575541234470486416557404445972488566082872790213419608629187712) * r0 + ((-24079540079147162459958779282716795839841904893051 : ℝ) / 23593383574273607887986152651807004652258444987270699469025066773569528832) * r1 + ((11395896946048834523099401664131995786486515796775 : ℝ) / 7957204881251431646222159978831608347285929208536659237481495934320008832) * r2 + ((19913888810186823184604663976287079072528801689547 : ℝ) / 63657639050011453169777279830652866778287433668293273899851967474560070656) * r3 + ((-670346879179343207241141274360705634499206811575 : ℝ) / 578180370379317511307804245744155297753098109247022758932820544327453192) * r4 + ((-19913888810186823184604663976287079072528801689547 : ℝ) / 78632530371587181537861377421205120494421342857595095214863594028533634112) * r5 + ((11395896946048834523099401664131995786486515796775 : ℝ) / 520706408620042409419264413303714595914137900438) * (value_177 h H) + ((-17322148928088270527978443070761912905991249443 : ℝ) / 10375221093300969552563176354744001911116072736) * (value_176 h H) + ((24079540079147162459958779282716795839841904893051 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_178 h H) + ((-11395896946048834523099401664131995786486515796775 : ℝ) / 520706408620042409419264413303714595914137900438) * (value_185 h H) + ((17322148928088270527978443070761912905991249443 : ℝ) / 10375221093300969552563176354744001911116072736) * (value_184 h H) + ((-19913888810186823184604663976287079072528801689547 : ℝ) / 4165651268960339275354115306429716767313103203504) * (value_186 h H)

/-- Coordinate 45.3, recovered from nonplanar cycle 25. -/
theorem value_183 (h : Assignment) (H : Constraints h) :
    h 45 3 = ((-5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 1 0) + ((-1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 1 1) + ((88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 1 2) + h 1 3 + ((5364791332306573317908 : ℝ) / 27450701136778990714501) * (h 3 0) + ((1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (h 5 1) + ((-88726955960883908139193 : ℝ) / 286984602793598539287965) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 164 3
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 3 - h 44 3) - ((717306105909058847318400 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((85060035983729351203286621735000433822973125 : ℝ) / 373880951671425074289841414994406133561397771730329289253059501356008) * r0 + ((148639120447449660119082599706092831764986225 : ℝ) / 2991047613371400594318731319955249068491182173842634314024476010848064) * r1 + ((-1 : ℝ) / 5663792298235764294550208) * r2 + ((-1446020611723398970455872569495007374990543125 : ℝ) / 17149148450972913030651206850930190403633468121846248356641155030862088) * r3 + ((-2526865047606644222024404195003578140004765825 : ℝ) / 137193187607783304245209654807441523229067744974769986853129240246896704) * r4 + ((170120071967458702406573243470000867645946250 : ℝ) / 2492156768876368583223294162690324559280595298478546374710433380721781) * r5 + ((148639120447449660119082599706092831764986225 : ℝ) / 9968627075505474332893176650761298237122381193914185498841733522887124) * r6 + ((-11568164893787191763646980555960058999924345000 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_177 h H) + ((2198000254648027809328957097785756688524425 : ℝ) / 22360390287286572311558569730051728256715674) * (value_176 h H) + ((-2526865047606644222024404195003578140004765825 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_178 h H) + (1 : ℝ) * (value_179 h H) + ((11568164893787191763646980555960058999924345000 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_185 h H) + ((-2198000254648027809328957097785756688524425 : ℝ) / 22360390287286572311558569730051728256715674) * (value_184 h H) + ((2526865047606644222024404195003578140004765825 : ℝ) / 8977696700345558783090765746615768895071343111) * (value_186 h H)

/-- Coordinate 47.0, recovered from nonplanar cycle 25. -/
theorem value_188 (h : Assignment) (H : Constraints h) :
    h 47 0 = ((2450485155582961681814836 : ℝ) / 2667143502384686423713107) * (h 1 0) + ((-110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 1 1) + ((867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 1 2) + ((216658346801724741898271 : ℝ) / 2667143502384686423713107) * (h 3 0) + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (h 5 1) + ((-867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((40784629858666874252910471530195019208468331373 : ℝ) / 52471940302938975984363540595740816108789607962084676728290529329044792) * r0 + ((1512858859198645880466744236336765908903108781969 : ℝ) / 7136183881199700733873441521020750990795386682843516035047511988750091712) * r1 + ((-693338707597336862299478016013315326543961633341 : ℝ) / 2406779724248954447957362034693001440366721010233554783505104833798146712) * r2 + ((-1512858859198645880466744236336765908903108781969 : ℝ) / 19254237793991635583658896277544011522933768081868438268040838670385173696) * r3 + ((293843502527374669106526 : ℝ) / 1259965674133667854278691641402508092811678317989) * r4 + ((5449893103811402900398139 : ℝ) / 85677665841089414090951031615370550311194125623252) * r5 + ((-5546709660778694898395824128106522612351693066728 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_177 h H) + ((14411869095458869341378075147058039616017514285 : ℝ) / 34519607510511448062429907983630358707169268986) * (value_176 h H) + ((-1512858859198645880466744236336765908903108781969 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_178 h H) + ((5546709660778694898395824128106522612351693066728 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_185 h H) + ((20107738415052578721051832836572319091151754701 : ℝ) / 34519607510511448062429907983630358707169268986) * (value_184 h H) + ((1512858859198645880466744236336765908903108781969 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_186 h H)

/-- Coordinate 47.1, recovered from nonplanar cycle 25. -/
theorem value_189 (h : Assignment) (H : Constraints h) :
    h 47 1 = ((2504841805677907691351358515 : ℝ) / 2095782094318278043166565856) * (h 1 0) + ((-1828407008888257872078476613 : ℝ) / 308203249164452653406847920) * (h 1 1) + ((54378178819898928565889508157 : ℝ) / 10478910471591390215832829280) * (h 1 2) + ((-2504841805677907691351358515 : ℝ) / 2095782094318278043166565856) * (h 3 0) + ((2136610258052710525485324533 : ℝ) / 308203249164452653406847920) * (h 5 1) + ((-54378178819898928565889508157 : ℝ) / 10478910471591390215832829280) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((149303155571323979019801563267695338416510694183 : ℝ) / 209887761211755903937454162382963264435158431848338706913162117316179168) * r0 + ((94149885403328338509470180812746042814702923593283 : ℝ) / 485260503921579649903394023429411067374086294433359090383230815235006236416) * r1 + ((-2538153644712507643336626575550820753080681801111 : ℝ) / 9627118896995817791829448138772005761466884040934219134020419335192586848) * r2 + ((-94149885403328338509470180812746042814702923593283 : ℝ) / 1309288169991431219688804946872992783559496229567053802226777029586191811328) * r3 + ((6336272963558683140951944792504149598973041920211 : ℝ) / 23783625354505456818558255472993501746738107807300039862178645575148829692) * r4 + ((94149885403328338509470180812746042814702923593283 : ℝ) / 1617286524106371063661961372163558118778191330896402710628147899110120419056) * r5 + ((-5076307289425015286673253151101641506161363602222 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_177 h H) + ((896895183271724658910024935756374182441618017495 : ℝ) / 2347333310714778468245233742886864392087510291048) * (value_176 h H) + ((-94149885403328338509470180812746042814702923593283 : ℝ) / 85677665841089414090951031615370550311194125623252) * (value_178 h H) + ((6336272963558683140951944792504149598973041920211 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_185 h H) + ((-896895183271724658910024935756374182441618017495 : ℝ) / 2347333310714778468245233742886864392087510291048) * (value_184 h H) + ((94149885403328338509470180812746042814702923593283 : ℝ) / 85677665841089414090951031615370550311194125623252) * (value_186 h H)

/-- Coordinate 47.2, recovered from nonplanar cycle 25. -/
theorem value_190 (h : Assignment) (H : Constraints h) :
    h 47 2 = ((-30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 1 0) + ((3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 1 1) + ((-51019593198921921642827329967 : ℝ) / 15949518144260424813804379860) * (h 1 2) + ((30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (h 3 0) + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (h 5 1) + ((66969111343182346456631709827 : ℝ) / 15949518144260424813804379860) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-313272419048728250333311894574358147219048534189 : ℝ) / 104943880605877951968727081191481632217579215924169353456581058658089584) * r0 + ((-11620479483148868819983290099273062305976805297617 : ℝ) / 14272367762399401467746883042041501981590773365687032070095023977500183424) * r1 + ((5325631123828380255666302207764088502723825081213 : ℝ) / 4813559448497908895914724069386002880733442020467109567010209667596293424) * r2 + ((11620479483148868819983290099273062305976805297617 : ℝ) / 38508475587983271167317792555088023045867536163736876536081677340770347392) * r3 + ((-313272419048728250333311894574358147219048534189 : ℝ) / 349759196389786129684680227544022084510854526577941762679097729046306319) * r4 + ((-9100548134881533111425906816468046120353448661639 : ℝ) / 47567250709010913637116510945987003493476215614600079724357291150297659384) * r5 + ((21302524495313521022665208831056354010895300324852 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_177 h H) + ((-110699572613347814972067721219262523386922321005 : ℝ) / 69039215021022896124859815967260717414338537972) * (value_176 h H) + ((11620479483148868819983290099273062305976805297617 : ℝ) / 2519931348267335708557383282805016185623356635978) * (value_178 h H) + ((-21302524495313521022665208831056354010895300324852 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_185 h H) + ((110699572613347814972067721219262523386922321005 : ℝ) / 69039215021022896124859815967260717414338537972) * (value_184 h H) + ((-9100548134881533111425906816468046120353448661639 : ℝ) / 2519931348267335708557383282805016185623356635978) * (value_186 h H)

/-- Coordinate 47.3, recovered from nonplanar cycle 25. -/
theorem value_191 (h : Assignment) (H : Constraints h) :
    h 47 3 = ((-2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 1 0) + ((57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 1 1) + ((-149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 1 2) + h 1 3 + ((2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (h 3 0) + ((-57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (h 5 1) + ((149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (h 9 2) := by
  have r0 := H 164 1
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 1 - h 44 1) - ((2785811097289131610504253 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 164 2
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 2 - h 44 2) - ((-12183177647841976940712616 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 164 3
  change ((-5663792298235764294550208 : ℤ) : ℝ) * (h 45 3 - h 44 3) - ((717306105909058847318400 : ℤ) : ℝ) * (h 45 0 - h 44 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 168 1
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 1 - h 45 1) - ((25775781830954580063993 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 168 2
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 2 - h 45 2) - ((5219017001769721614586424 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 168 3
  change ((15281557418007073892361664 : ℤ) : ℝ) * (h 47 3 - h 45 3) - ((-1072921154218855975526496 : ℤ) : ℝ) * (h 47 0 - h 45 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 169 1
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 1 - h 46 1) - ((17275547173115059432614297 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 169 2
  change ((18876407383763605568734028 : ℤ) : ℝ) * (h 47 2 - h 46 2) - ((-72496156328414859987179302 : ℤ) : ℝ) * (h 47 0 - h 46 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((9824938264218145343539986921992677748265577287 : ℝ) / 209887761211755903937454162382963264435158431848338706913162117316179168) * r0 + ((12191600811668678942980447068705945405452863515 : ℝ) / 1679102089694047231499633299063706115481267454786709655305296938529433344) * r1 + ((-1 : ℝ) / 5663792298235764294550208) * r2 + ((-167023950491708470840179777673875521720514813879 : ℝ) / 9627118896995817791829448138772005761466884040934219134020419335192586848) * r3 + ((-207257213798367542030667600168001071892698679755 : ℝ) / 77016951175966542334635585110176046091735072327473753072163354681540694784) * r4 + ((1 : ℝ) / 15281557418007073892361664) * r5 + ((9824938264218145343539986921992677748265577287 : ℝ) / 699518392779572259369360455088044169021709053155883525358195458092612638) * r6 + ((12191600811668678942980447068705945405452863515 : ℝ) / 5596147142236578074954883640704353352173672425247068202865563664740901104) * r7 + ((-334047900983416941680359555347751043441029627758 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_177 h H) + ((11695529595593825173285452199614740691742054977 : ℝ) / 138078430042045792249719631934521434828677075944) * (value_176 h H) + ((-207257213798367542030667600168001071892698679755 : ℝ) / 5039862696534671417114766565610032371246713271956) * (value_178 h H) + (1 : ℝ) * (value_179 h H) + ((334047900983416941680359555347751043441029627758 : ℝ) / 1259965674133667854278691641402508092811678317989) * (value_185 h H) + ((-11695529595593825173285452199614740691742054977 : ℝ) / 138078430042045792249719631934521434828677075944) * (value_184 h H) + ((207257213798367542030667600168001071892698679755 : ℝ) / 5039862696534671417114766565610032371246713271956) * (value_186 h H)

/-- Coordinate 56.0, recovered from skew spokes on cycle 26. -/
theorem value_224 (h : Assignment) (H : Constraints h) :
    h 56 0 = ((395474070089323488804761 : ℝ) / 337451016732989027785850) * (h 1 0) + ((-3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 1 1) + ((68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 1 2) + ((-58023053356334461018911 : ℝ) / 337451016732989027785850) * (h 3 0) + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 5 1) + ((-68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-7070833869954043322835181 : ℝ) / 5675668585845396568869444903674103716102377189500) * r0 + ((-887948231346336926642465959 : ℝ) / 771890927674973933366244506899678105389923297772000) * r1 + ((6512243982700322845865023475482811535723446157 : ℝ) / 141224640052118996276910649639319009480397825666568380945333223898703500) * r2 + ((817801073096370210792463118607667489378551948423 : ℝ) / 19206551047088183493659848350947385289334104290653299808565318450223676000) * r3 + ((-6512243982700322845865023475482811535723446157 : ℝ) / 4009247353352326860241172004472545337196829571708770982940550751450048000) * r4 + ((-817801073096370210792463118607667489378551948423 : ℝ) / 545257640055916452992799392608266165858768821752392853679914902197206528000) * r5 + ((-221416295411810976759410798166415592214597169338 : ℝ) / 472972382153783047405787075306175309675198099125) * (value_101 h H) + ((120002361890228715074412627109210117320253128407 : ℝ) / 145529963739625553047934484709592402976984030500) * (value_100 h H) + ((-817801073096370210792463118607667489378551948423 : ℝ) / 1891889528615132189623148301224701238700792396500) * (value_102 h H) + ((221416295411810976759410798166415592214597169338 : ℝ) / 472972382153783047405787075306175309675198099125) * (value_277 h H) + ((25527601849396837973521857600382285656730902093 : ℝ) / 145529963739625553047934484709592402976984030500) * (value_276 h H) + ((817801073096370210792463118607667489378551948423 : ℝ) / 1891889528615132189623148301224701238700792396500) * (value_278 h H)

/-- Coordinate 56.1, recovered from skew spokes on cycle 26. -/
theorem value_225 (h : Assignment) (H : Constraints h) :
    h 56 1 = ((18019105745549530002971079 : ℝ) / 45893338275686507778875600) * (h 1 0) + ((-11343011263264265908812981439 : ℝ) / 8071828320253097544637532000) * (h 1 1) + ((5738876243940075067449936857 : ℝ) / 3759481683405552281064056000) * (h 1 2) + ((-18019105745549530002971079 : ℝ) / 45893338275686507778875600) * (h 3 0) + ((19414839583517363453450513439 : ℝ) / 8071828320253097544637532000) * (h 5 1) + ((-5738876243940075067449936857 : ℝ) / 3759481683405552281064056000) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-391479186150561539799228958036451098016471702419 : ℝ) / 2132736594369310332751291547770046305055987323817088748093188589341252000) * r0 + ((-761906337009682047322800895110567244910535291380941 : ℝ) / 290052176834226205254175650496726297487614276039124069740673648150410272000) * r1 + ((6067147771995958108668673861710554814118848891919 : ℝ) / 57619653141264550480979545052842155868002312871959899425695955350671028000) * r2 + ((761906337009682047322800895110567244910535291380941 : ℝ) / 7836272827211978865413218127186533198048314550586546321894649927691259808000) * r3 + ((-6067147771995958108668673861710554814118848891919 : ℝ) / 1635772920167749358978398177824798497576306465257178561039744706591619584000) * r4 + ((-761906337009682047322800895110567244910535291380941 : ℝ) / 222465117142813912821062152184172595670377679274976284301405280096460263424000) * r5 + ((-391479186150561539799228958036451098016471702419 : ℝ) / 5675668585845396568869444903674103716102377189500) * (value_101 h H) + ((-23782851670853177640873573339979215304963070090831 : ℝ) / 59376225205767225643557269761513700414609484444000) * (value_100 h H) + ((-761906337009682047322800895110567244910535291380941 : ℝ) / 771890927674973933366244506899678105389923297772000) * (value_102 h H) + ((6067147771995958108668673861710554814118848891919 : ℝ) / 5675668585845396568869444903674103716102377189500) * (value_277 h H) + ((23782851670853177640873573339979215304963070090831 : ℝ) / 59376225205767225643557269761513700414609484444000) * (value_276 h H) + ((761906337009682047322800895110567244910535291380941 : ℝ) / 771890927674973933366244506899678105389923297772000) * (value_278 h H)

/-- Coordinate 56.2, recovered from skew spokes on cycle 26. -/
theorem value_226 (h : Assignment) (H : Constraints h) :
    h 56 2 = ((-16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 1 0) + ((480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 1 1) + ((-9545790293705793165213571 : ℝ) / 13821623836049824562735500) * (h 1 2) + ((16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 3 0) + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 5 1) + ((23367414129755617727949071 : ℝ) / 13821623836049824562735500) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((5522641851082922881729109757127026561358008557 : ℝ) / 7840943361651876223350336572683993768588188690504002750342605107872250) * r0 + ((3531362122061217394818013154062731977365677036773 : ℝ) / 1066368297184655166375645773885023152527993661908544374046594294670626000) * r1 + ((-5522641851082922881729109757127026561358008557 : ℝ) / 211836960078178494415365974458978514220596738499852571417999835848055250) * r2 + ((-693527829138519110383290702225680119314488442023 : ℝ) / 28809826570632275240489772526421077934001156435979949712847977675335514000) * r3 + ((5522641851082922881729109757127026561358008557 : ℝ) / 6013871030028490290361758006708818005795244357563156474410826127175072000) * r4 + ((693527829138519110383290702225680119314488442023 : ℝ) / 817886460083874679489199088912399248788153232628589280519872353295809792000) * r5 + ((375539645873638755957579463484637806172344581876 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_101 h H) + ((21648421451311022869068485842025324890545739693 : ℝ) / 218294945609438329571901727064388604465476045750) * (value_100 h H) + ((3531362122061217394818013154062731977365677036773 : ℝ) / 2837834292922698284434722451837051858051188594750) * (value_102 h H) + ((-375539645873638755957579463484637806172344581876 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_277 h H) + ((-21648421451311022869068485842025324890545739693 : ℝ) / 218294945609438329571901727064388604465476045750) * (value_276 h H) + ((-693527829138519110383290702225680119314488442023 : ℝ) / 2837834292922698284434722451837051858051188594750) * (value_278 h H)

/-- Coordinate 56.3, recovered from skew spokes on cycle 26. -/
theorem value_227 (h : Assignment) (H : Constraints h) :
    h 56 3 = ((9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 1 0) + ((-372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 1 1) + ((8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 1 2) + h 1 3 + ((-9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 3 0) + ((372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 5 1) + ((-8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 100 3
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 3 - h 25 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1655477232319071302030650006045099624580294009 : ℝ) / 3920471680825938111675168286341996884294094345252001375171302553936125) * r0 + ((-12229010105684635187247961561424726951819090203 : ℝ) / 31363773446607504893401346290735975074352754762016011001370420431489000) * r1 + ((1 : ℝ) / 375768345545785080884376) * r2 + ((1655477232319071302030650006045099624580294009 : ℝ) / 105918480039089247207682987229489257110298369249926285708999917924027625) * r3 + ((12229010105684635187247961561424726951819090203 : ℝ) / 847347840312713977661463897835914056882386953999410285671999343392221000) * r4 + ((-1655477232319071302030650006045099624580294009 : ℝ) / 3006935515014245145180879003354409002897622178781578237205413063587536000) * r5 + ((-12229010105684635187247961561424726951819090203 : ℝ) / 24055484120113961161447032026835272023180977430252625897643304508700288000) * r6 + ((-225144903595393697076168400822133548942919985224 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_101 h H) + ((-6489370448903127256499234349570837983516541241 : ℝ) / 109147472804719164785950863532194302232738022875) * (value_100 h H) + ((-207893171796638798183215346544220358180924533451 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_102 h H) + (1 : ℝ) * (value_103 h H) + ((225144903595393697076168400822133548942919985224 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_277 h H) + ((6489370448903127256499234349570837983516541241 : ℝ) / 109147472804719164785950863532194302232738022875) * (value_276 h H) + ((207893171796638798183215346544220358180924533451 : ℝ) / 1418917146461349142217361225918525929025594297375) * (value_278 h H)

/-- Coordinate 57.0, recovered from skew spokes on cycle 26. -/
theorem value_228 (h : Assignment) (H : Constraints h) :
    h 57 0 = ((24702794285873566689225010 : ℝ) / 20299831706871375888292479) * (h 1 0) + ((-13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 1 1) + ((85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 1 2) + ((-4402962579002190800932531 : ℝ) / 20299831706871375888292479) * (h 3 0) + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 5 1) + ((-85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-143708688557219059520488021576814232424000023296 : ℝ) / 108849870241204768408310816534528777961715334745057490751630130979495665) * r0 + ((-2387910859513914509198295770939839273957869995728 : ℝ) / 1850447794100481062941283881086989225349160690665977342777712226651426305) * r1 + ((143708688557219059520488021576814232424000023296 : ℝ) / 2940771862933494360965314481158984820118363897005517250317872715306668685) * r2 + ((2387910859513914509198295770939839273957869995728 : ℝ) / 49993121669869404136410346179702741942012186249093793255403836160213367645) * r3 + ((-67813466990277639241018 : ℝ) / 39395501319575952118438738049253072263940370332315) * r4 + ((-9014487063968844878373067 : ℝ) / 5357788179462329488107668374698417827895890365194840) * r5 + ((-19544381643781792094786370934446735609664003168256 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_101 h H) + ((33828617199721740217313497888133502260175581692928 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_100 h H) + ((-19103286876111316073586366167518714191662959965824 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_102 h H) + ((19544381643781792094786370934446735609664003168256 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_277 h H) + ((5566884119854211901125240161119570003764788639387 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_276 h H) + ((19103286876111316073586366167518714191662959965824 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_278 h H)

/-- Coordinate 57.1, recovered from skew spokes on cycle 26. -/
theorem value_229 (h : Assignment) (H : Constraints h) :
    h 57 1 = ((-380670708372338388420360203 : ℝ) / 306753012459389680089753016) * (h 1 0) + ((535508976048016260738090661 : ℝ) / 79811304146673785543714020) * (h 1 1) + ((-1206980366386691997475730201 : ℝ) / 241620523512532967193983540) * (h 1 2) + ((380670708372338388420360203 : ℝ) / 306753012459389680089753016) * (h 3 0) + ((-455697671901342475194376641 : ℝ) / 79811304146673785543714020) * (h 5 1) + ((1206980366386691997475730201 : ℝ) / 241620523512532967193983540) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2073648575824479953463595042745149215720727847063 : ℝ) / 822421241822436027973903947149772989044071418073767707901205434067300580) * r0 + ((551302833835856686708975518416131143893223631831969 : ℝ) / 223698577775702599608901873624738253019987425716064816549127878066305757760) * r1 + ((-2073648575824479953463595042745149215720727847063 : ℝ) / 22219165186608624060626820524312329752005416110708352557957260515650385620) * r2 + ((-551302833835856686708975518416131143893223631831969 : ℝ) / 6043612930757545744490495182612953692545473182112671895764374860256904888640) * r3 + ((-229980772748368106232669697760042931218585453909 : ℝ) / 1261566383674024574500978064359845807253866168162705899825523315303020958720) * r4 + ((551302833835856686708975518416131143893223631831969 : ℝ) / 171573028179667342132133016752939029786525798870128002376271170881210850385920) * r5 + ((4147297151648959906927190085490298431441455694126 : ℝ) / 4377277924397328013159859783250341362660041148035) * (value_101 h H) + ((-122032746562821944089709163691988107803857589910421 : ℝ) / 74413724714754576223717616315255803165220699516595) * (value_100 h H) + ((551302833835856686708975518416131143893223631831969 : ℝ) / 595309797718036609789740930522046425321765596132760) * (value_102 h H) + ((229980772748368106232669697760042931218585453909 : ℝ) / 4377277924397328013159859783250341362660041148035) * (value_277 h H) + ((122032746562821944089709163691988107803857589910421 : ℝ) / 74413724714754576223717616315255803165220699516595) * (value_276 h H) + ((-551302833835856686708975518416131143893223631831969 : ℝ) / 595309797718036609789740930522046425321765596132760) * (value_278 h H)

/-- Coordinate 57.2, recovered from skew spokes on cycle 26. -/
theorem value_230 (h : Assignment) (H : Constraints h) :
    h 57 2 = ((33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 1 0) + ((-154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 1 1) + ((201456234728327216730076966 : ℝ) / 31979186935482304481556645) * (h 1 2) + ((-33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 3 0) + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 5 1) + ((-169477047792844912248520321 : ℝ) / 31979186935482304481556645) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-238912503689514633109761649183355085249986129738 : ℝ) / 108849870241204768408310816534528777961715334745057490751630130979495665) * r0 + ((-31758790244986427261219470608293115879208312607747 : ℝ) / 14803582352803848503530271048695913802793285525327818742221697813211410440) * r1 + ((238912503689514633109761649183355085249986129738 : ℝ) / 2940771862933494360965314481158984820118363897005517250317872715306668685) * r2 + ((31758790244986427261219470608293115879208312607747 : ℝ) / 399944973358955233091282769437621935536097489992750346043230689281706941160) * r3 + ((-119456251844757316554880824591677542624993064869 : ℝ) / 41743005342155224891576480070730192151782336446560121685403344991644075840) * r4 + ((-35577145782281189689829104328773094071574341470031 : ℝ) / 5677048726533110585254401289619306132642397756732176549214854918863594314240) * r5 + ((-32492100501773990102927584288936291593998113644368 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_101 h H) + ((56239324933521588398238023888434325031774566478584 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_100 h H) + ((-31758790244986427261219470608293115879208312607747 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_102 h H) + ((32492100501773990102927584288936291593998113644368 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_277 h H) + ((-56239324933521588398238023888434325031774566478584 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_276 h H) + ((71154291564562379379658208657546188143148682940062 : ℝ) / 39395501319575952118438738049253072263940370332315) * (value_278 h H)

/-- Coordinate 57.3, recovered from skew spokes on cycle 26. -/
theorem value_231 (h : Assignment) (H : Constraints h) :
    h 57 3 = ((-599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 1 0) + ((2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 1 1) + ((-2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 1 2) + h 1 3 + ((599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 3 0) + ((-2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 5 1) + ((2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 100 3
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 3 - h 25 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 184 3
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 3 - h 56 3) - ((206686098914908403040993376 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((4102862128481005288710377706981103444646483044 : ℝ) / 3753443801420854083045200570156164757300528784312327267297590723430885) * r0 + ((18484271416488626517260522069951507127754874747 : ℝ) / 7506887602841708166090401140312329514601057568624654534595181446861770) * r1 + ((1 : ℝ) / 375768345545785080884376) * r2 + ((-4102862128481005288710377706981103444646483044 : ℝ) / 101405926308051529688459120039964993797184961965707491390271472941609265) * r3 + ((-18484271416488626517260522069951507127754874747 : ℝ) / 202811852616103059376918240079929987594369923931414982780542945883218530) * r4 + ((-1 : ℝ) / 10152046806426074108734264) * r5 + ((1025715532120251322177594426745275861161620761 : ℝ) / 719706988657848705027180690874658485375557524940691753196609396407656480) * r6 + ((18484271416488626517260522069951507127754874747 : ℝ) / 5757655909262789640217445526997267883004460199525534025572875171261251840) * r7 + ((557989249473416719264611368149430068471921693984 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_101 h H) + ((-1023976406640148520466460092386864631622265684512 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_100 h H) + ((1256930456321226603173715500756702484687331482796 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_102 h H) + (1 : ℝ) * (value_103 h H) + ((-557989249473416719264611368149430068471921693984 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_277 h H) + ((1023976406640148520466460092386864631622265684512 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_276 h H) + ((-1256930456321226603173715500756702484687331482796 : ℝ) / 1358465562743998348911680622388036974618633459735) * (value_278 h H)

/-- Coordinate 58.0, recovered from skew spokes on cycle 26. -/
theorem value_232 (h : Assignment) (H : Constraints h) :
    h 58 0 = ((-355785217299252588876116 : ℝ) / 3456801008592869729912095) * (h 1 0) + ((16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 1 1) + ((-368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 1 2) + ((3812586225892122318788211 : ℝ) / 3456801008592869729912095) * (h 3 0) + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 5 1) + ((368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((69489617249844888865723226945149686765141783433 : ℝ) / 80321526908672796314781864318336380580490867130033686471731009313780575) * r0 + ((30836662313597510814675288690922642166550991128187 : ℝ) / 10923727659579500298810333547293747758946757929684581360155417266674158200) * r1 + ((153327496248766545379756974048630909957029786749065605343725116368512815559 : ℝ) / 73810628274631086391358604005183011888856606843642509914803004332897378869977414724209339777499725) * r2 + ((19487831962888745167154705891723303917261450714923425822542421855207627464721 : ℝ) / 10038245445349827749224770144704889616884498530735381348413208589274043526316928402492470209739962600) * r3 + ((45725570889250235206517378 : ℝ) / 20938636604998637724438453124409297360406683738965) * r4 + ((3015754838942986103133761157 : ℝ) / 1423827289139907365261814812459832220507654494249620) * r5 + ((-4003398801976338534107803703905394973150757821519 : ℝ) / 4015898028338630335726107305831262587242703600878311353046230893217415760) * r6 + ((-31063245291376901724102701242448932077877564731291 : ℝ) / 32127184226709042685808858446650100697941628807026490824369847145739326080) * r7 + ((69489617249844888865723226945149686765141783433 : ℝ) / 61605253536987278477071762930399739460185464879846068202533851688962390400) * r8 + ((30836662313597510814675288690922642166550991128187 : ℝ) / 8378314481030269872881759758534364566585223223659065275544603829698885094400) * r9 + ((-78498015725026245766819680468733234767661918069 : ℝ) / 1299076418129410053167225233372735526006047790235282647880571864500292395) * r10 + ((-3451471699041877969344744582494325786430840525699 : ℝ) / 58891464288533255743580877246230677178940833157332813370585924524013255240) * r11 + ((9450587945978904885738358864540357400059282546888 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_101 h H) + ((-318941984643491542758080435169736872204451599883 : ℝ) / 2236182885027480665741954760218925495918337922025) * (value_100 h H) + ((30836662313597510814675288690922642166550991128187 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_102 h H) + ((-9450587945978904885738358864540357400059282546888 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_277 h H) + ((2555124869670972208500035195388662368122789521908 : ℝ) / 2236182885027480665741954760218925495918337922025) * (value_276 h H) + ((-30836662313597510814675288690922642166550991128187 : ℝ) / 29070377505357248654645411882846031446938392986325) * (value_278 h H)

/-- Coordinate 58.1, recovered from skew spokes on cycle 26. -/
theorem value_233 (h : Assignment) (H : Constraints h) :
    h 58 1 = ((66070054400348276677560623 : ℝ) / 235062468584315141634022460) * (h 1 0) + ((-70374903524614779867548090651 : ℝ) / 82686680125541443939497312400) * (h 1 1) + ((41636451361200205751305460393 : ℝ) / 38511604442033001286889159200) * (h 1 2) + ((-66070054400348276677560623 : ℝ) / 235062468584315141634022460) * (h 3 0) + ((153061583650156223807045403051 : ℝ) / 82686680125541443939497312400) * (h 5 1) + ((-41636451361200205751305460393 : ℝ) / 38511604442033001286889159200) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((75986734727941350471164937687076669829699289347 : ℝ) / 65542365957477001792862001283762486553680547578107488160932503600044949200) * r0 + ((-1195029107341698040143874483797036148538401165350401 : ℝ) / 524338927659816014342896010270099892429444380624859905287460028800359593600) * r1 + ((17046965755643454764276579094204176969562120277737948036932066752220169707281 : ℝ) / 60229472672098966495348620868229337701306991184412288090479251535644261157901570414954821258439775600) * r2 + ((2157386242385245416677811650224846029552235869439034283120643849584278998905739 : ℝ) / 8191208283405459443367412438079189927377750801080071180305178208847619517474613576433855691147809481600) * r3 + ((20057861362444327575749048066029080140762298467129 : ℝ) / 68440769863613632540683507716695274343874617460297411266450432896588460280) * r4 + ((862558815008989815619636558602278268919345428009181 : ℝ) / 4653972350725727012766478524735278655383473987300223966118629436968015299040) * r5 + ((-2802496248738167500200620790976995932991443690173 : ℝ) / 32127184226709042685808858446650100697941628807026490824369847145739326080) * r6 + ((-369668063575281349551272810829547829536862326289649 : ℝ) / 4369297054832429805270004748744413694920061517755602752114299211820548346880) * r7 + ((-174346278297415550577401306359389112011800658628603 : ℝ) / 50269886886181619237290558551206187399511339341954391653267622978193310566400) * r8 + ((-1195029107341698040143874483797036148538401165350401 : ℝ) / 402159095089452953898324468409649499196090714735635133226140983825546484531200) * r9 + ((-2802496248738167500200620790976995932991443690173 : ℝ) / 530023178596799301692227895216076094610467498415995320335273320716119297160) * r10 + ((-123222687858427116517090936943182609845620775429883 : ℝ) / 24027717429721568343380997916462116289007859928191787855199057205797408137920) * r11 + ((75986734727941350471164937687076669829699289347 : ℝ) / 174422265032143491927872471297076188681630357917950) * (value_101 h H) + ((-885320207775857739990271065949769120648526800985797 : ℝ) / 1824725234182424223245435084338643204669363744372400) * (value_100 h H) + ((-1195029107341698040143874483797036148538401165350401 : ℝ) / 1395378120257147935422979770376609509453042863343600) * (value_102 h H) + ((174346278297415550577401306359389112011800658628603 : ℝ) / 174422265032143491927872471297076188681630357917950) * (value_277 h H) + ((885320207775857739990271065949769120648526800985797 : ℝ) / 1824725234182424223245435084338643204669363744372400) * (value_276 h H) + ((1195029107341698040143874483797036148538401165350401 : ℝ) / 1395378120257147935422979770376609509453042863343600) * (value_278 h H)

/-- Coordinate 58.2, recovered from skew spokes on cycle 26. -/
theorem value_234 (h : Assignment) (H : Constraints h) :
    h 58 2 = ((-240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 1 0) + ((4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 1 1) + ((-82173261632986900318333999 : ℝ) / 141586781036886034142974850) * (h 1 2) + ((240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 3 0) + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 5 1) + ((223760042669872934461308849 : ℝ) / 141586781036886034142974850) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((158699291543561712652300342861445759834160319409 : ℝ) / 240964580726018388944345592955009141741472601390101059415193027941341725) * r0 + ((52851690315109747994908081269285072830708057649913 : ℝ) / 16385591489369250448215500320940621638420136894526872040233125900011237300) * r1 + ((-15517058435700926999704783602080493105609436060288847767290258800520829043 : ℝ) / 221431884823893259174075812015549035666569820530927529744409012998692136609932244172628019332499175) * r2 + ((-1963768149201957566022364221809522112755478406106374973254763813542118034017 : ℝ) / 30114736336049483247674310434114668850653495592206144045239625767822130578950785207477410629219887800) * r3 + ((-71427488214844345106426203928646989636408067332 : ℝ) / 1509722864638536011926842081985925169350175385153619366171700725660039565) * r4 + ((11516871538830778237292146994071210867673951562049 : ℝ) / 205322309590840897622050523150085823031623852380892233799351298689765380840) * r5 + ((43366689273298352386044480956678529422104898023 : ℝ) / 2007949014169315167863053652915631293621351800439155676523115446608707880) * r6 + ((336491609505994981683796647512074517597597577747 : ℝ) / 16063592113354521342904429223325050348970814403513245412184923572869663040) * r7 + ((158699291543561712652300342861445759834160319409 : ℝ) / 184815760610961835431215288791199218380556394639538204607601555066887171200) * r8 + ((1087779300832220589757642758237179489447113902403 : ℝ) / 1478526084887694683449722310329593747044451157116305636860812440535097369600) * r9 + ((5101963443917453221887585994903356402600576238 : ℝ) / 3897229254388230159501675700118206578018143370705847943641715593500877185) * r10 + ((112163869835331660561265549170691505865865859249 : ℝ) / 88337196432799883615371315869346015768411249735999220055878886786019882860) * r11 + ((21583103649924392920712846629156623337445803439624 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_101 h H) + ((805865723864495006214237370188588892222683803791 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_100 h H) + ((105703380630219495989816162538570145661416115299826 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_102 h H) + ((-21583103649924392920712846629156623337445803439624 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_277 h H) + ((-805865723864495006214237370188588892222683803791 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_276 h H) + ((-18492248114147750025879926890032051320600936340851 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_278 h H)

/-- Coordinate 58.3, recovered from skew spokes on cycle 26. -/
theorem value_235 (h : Assignment) (H : Constraints h) :
    h 58 3 = ((144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 1 0) + ((-7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 1 1) + ((80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 1 2) + h 1 3 + ((-144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 3 0) + ((7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 5 1) + ((-80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 100 3
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 3 - h 25 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 185 3
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 3 - h 56 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  linear_combination ((-95143980370197696005262169840944026252071883866 : ℝ) / 240964580726018388944345592955009141741472601390101059415193027941341725) * r0 + ((-326074714760397730013324934867294315924367083511 : ℝ) / 963858322904073555777382371820036566965890405560404237660772111765366900) * r1 + ((1 : ℝ) / 375768345545785080884376) * r2 + ((9302843691676416604360200733712589424872857056896502298354579799626034382 : ℝ) / 221431884823893259174075812015549035666569820530927529744409012998692136609932244172628019332499175) * r3 + ((34627219749268085766308639497231354283735862959566646772864662895794812237 : ℝ) / 885727539295573036696303248062196142666279282123710118977636051994768546439728976690512077329996700) * r4 + ((42822469278259238736020554558364265118620347368 : ℝ) / 1509722864638536011926842081985925169350175385153619366171700725660039565) * r5 + ((13844536989798336294167332730876902083211978123 : ℝ) / 503240954879512003975614027328641723116725128384539788723900241886679855) * r6 + ((1 : ℝ) / 9805906347399177090242376) * r7 + ((-12999678173757268902006239776646294768152605451 : ℝ) / 1003974507084657583931526826457815646810675900219577838261557723304353940) * r8 + ((-100867340925673593000361995610674572320544412039 : ℝ) / 8031796056677260671452214611662525174485407201756622706092461786434831520) * r9 + ((-47571990185098848002631084920472013126035941933 : ℝ) / 92407880305480917715607644395599609190278197319769102303800777533443585600) * r10 + ((-326074714760397730013324934867294315924367083511 : ℝ) / 739263042443847341724861155164796873522225578558152818430406220267548684800) * r11 + ((-179926341505290919058909893102370861842942636 : ℝ) / 229248779669895891735392688242247445765773139453285173155395034911816305) * r12 + ((-1977790998542619470595333247268128869030282589 : ℝ) / 2598152836258820106334450466745471052012095580470565295761143729000584790) * r13 + ((-12939581330346886656715655098368387570281776205776 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_101 h H) + ((-483135569583386936489878321080751469687325712934 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_100 h H) + ((-11086540301853522820453047785488006741428480839374 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_102 h H) + (1 : ℝ) * (value_103 h H) + ((12939581330346886656715655098368387570281776205776 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_277 h H) + ((483135569583386936489878321080751469687325712934 : ℝ) / 6708548655082441997225864280656776487755013766075) * (value_276 h H) + ((11086540301853522820453047785488006741428480839374 : ℝ) / 87211132516071745963936235648538094340815178958975) * (value_278 h H)

/-- Coordinate 59.0, recovered from skew spokes on cycle 26. -/
theorem value_236 (h : Assignment) (H : Constraints h) :
    h 59 0 = ((69463083005130850032370138 : ℝ) / 80398009002116453602781515) * (h 1 0) + ((-14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 1 2) + ((10934925996985603570411377 : ℝ) / 80398009002116453602781515) * (h 3 0) + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((-159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-105748877410967909129015044724762543235358455488 : ℝ) / 143700909674197281543400891779480094577966852504948652166281448601213175) * r0 + ((-465571766444067803080518848330794967845654934104 : ℝ) / 2442915464461353786237815160251161607825436492584127086826784626220623975) * r1 + ((4353973354009210784270098754338899878453381653571234303050739798794234306688 : ℝ) / 1716681851724886045199425717849731961023436804592128052772233362275566815540381039924502906502759825) * r2 + ((69227692673011464577018655975551913723195367717920290500733181770362725204284 : ℝ) / 29183591479323062768390237203445443337398425678066176897127967158684635864186477678716549410546917025) * r3 + ((30403203808613461719186468832229534951244588291392 : ℝ) / 11704338988580142721452913028520314339135197448896911940004458547072660635) * r4 + ((487202376503966036642654362048249090136923273031172 : ℝ) / 198973762805862426264699521484845343765298356631247502980075795300235230795) * r5 + ((-577467057463769222908070802 : ℝ) / 486989181638194092151565423796036137512206884539705) * r6 + ((-4354700859742078414174414293 : ℝ) / 3895913453105552737212523390368289100097655076317640) * r7 + ((-1652326209546373580140860073824414738052475867 : ℝ) / 1722127638654463315250528178623771880119463804814153162643067167412600150) * r8 + ((-58196470805508475385064856041349370980706866763 : ℝ) / 234209358857007010874071832292832975696247077454724830119457134768113620400) * r9 + ((-2171657414900961551370462059444966782231756306528 : ℝ) / 30213818296043684008286720340171497895419910463988191863825186002568012615) * r10 + ((-11600056583427762777206056239244025955641030310266 : ℝ) / 171211637010914209380291415260971821407379492629266420561676054014552071485) * r11 + ((-14381847327891635641546046082567705880008749946368 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_101 h H) + ((30734674029278881522099597776224914351714397178944 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_100 h H) + ((-3724574131552542424644150786646359742765239472832 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_102 h H) + ((14381847327891635641546046082567705880008749946368 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_277 h H) + ((21274293589601074136004685664254390022918824765981 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_276 h H) + ((3724574131552542424644150786646359742765239472832 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_278 h H)

/-- Coordinate 59.1, recovered from skew spokes on cycle 26. -/
theorem value_237 (h : Assignment) (H : Constraints h) :
    h 59 1 = ((-13065867661683706731400226723 : ℝ) / 10934129224287837689978286040) * (h 1 0) + ((59923238221578451462311092536 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((-82881235079194589895477500167 : ℝ) / 17224998093056182662294560200) * (h 1 2) + ((13065867661683706731400226723 : ℝ) / 10934129224287837689978286040) * (h 3 0) + ((-50677467186335059297991218311 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((82881235079194589895477500167 : ℝ) / 17224998093056182662294560200) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((17920371395645914033237363047339880163261332956308 : ℝ) / 7328746393384061358713445480753484823476309477752381260480353878661871925) * r0 + ((18507750689315434267356830205165496736193703179643771 : ℝ) / 7973676076001858758280228683059791487942224711794590811402625019984116654400) * r1 + ((-146242950345485929734385855207370238293766548420088922486988231752377960531107 : ℝ) / 350203097751876753220682846441345320048781108136794122765535605904215630370237732144598592926563004300) * r2 + ((-4694127999429549683190958483254183271807031341887651384705310419600055814033927 : ℝ) / 11906905323563809609503216779005740881658557676651000174028210600743331432588082892916352159503142146200) * r3 + ((-15853912678699679860930114437107194988045067874053 : ℝ) / 46817355954320570885811652114081257356540789795587647760017834188290642540) * r4 + ((-4064868417195193290824147225918798139881569424999793 : ℝ) / 12734320819575195280940769375030102000979094824399840190724850899215054770880) * r5 + ((2104088274865561437966437096380970026292803807693111 : ℝ) / 10460961728347342385419250273259685340297122261895094034367443908822658973440) * r6 + ((1742086464512225696067491668250913488520672610714197 : ℝ) / 11955384832396962726193428883725354674625282585022964610705650181511610255360) * r7 + ((-12663931691472554708413945942718871817809002184311 : ℝ) / 44968196900545346087821791800223931333679438871307167382935769875477815116800) * r8 + ((18507750689315434267356830205165496736193703179643771 : ℝ) / 6115674778474167067943763684830454661380403686497774764079264703064982855884800) * r9 + ((83883135866135872280053515540249708931455385577 : ℝ) / 8952242458087017483936806026717480857902195693033538330022277334094225960) * r10 + ((21507240302620070321820884793221154179267563095237 : ℝ) / 2435009948599668755630811239267154793349397228505122425766059434873629461120) * r11 + ((143362971165167312265898904378719041306090663650464 : ℝ) / 156026902856639866974312850321437913123899665834775) * (value_101 h H) + ((-17028973315664964466471119961010194258674554701537991 : ℝ) / 10609829394251510954253273821857778092425177276764700) * (value_100 h H) + ((18507750689315434267356830205165496736193703179643771 : ℝ) / 21219658788503021908506547643715556184850354553529400) * (value_102 h H) + ((12663931691472554708413945942718871817809002184311 : ℝ) / 156026902856639866974312850321437913123899665834775) * (value_277 h H) + ((17028973315664964466471119961010194258674554701537991 : ℝ) / 10609829394251510954253273821857778092425177276764700) * (value_276 h H) + ((-18507750689315434267356830205165496736193703179643771 : ℝ) / 21219658788503021908506547643715556184850354553529400) * (value_278 h H)

/-- Coordinate 59.2, recovered from skew spokes on cycle 26. -/
theorem value_238 (h : Assignment) (H : Constraints h) :
    h 59 2 = ((125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 1 0) + ((-67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((753062971344274112653576967 : ℝ) / 126654397743060166634518825) * (h 1 2) + ((-125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 3 0) + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((-626408573601213946019058142 : ℝ) / 126654397743060166634518825) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-294320161399272762417136611299902605344195609948 : ℝ) / 143700909674197281543400891779480094577966852504948652166281448601213175) * r0 + ((-36529514641256263148008464071435830721348547649847 : ℝ) / 19543323715690830289902521282009292862603491940673016694614277009764991800) * r1 + ((1211729783114762968125647569931692068844677480505717003874183888742950407598 : ℝ) / 1716681851724886045199425717849731961023436804592128052772233362275566815540381039924502906502759825) * r2 + ((77404781657585732650444081266575895597822349816264217762091318309941241570031 : ℝ) / 116734365917292251073560948813781773349593702712264707588511868634738543456745910714866197642187668100) * r3 + ((7634573655185543161643333156685670361352291304322 : ℝ) / 11704338988580142721452913028520314339135197448896911940004458547072660635) * r4 + ((978734333872321925732215339333654308442614555380541 : ℝ) / 1591790102446899410117596171878762750122386853049980023840606362401881846360) * r5 + ((-194681628207231350621904995495484594214483428260211 : ℝ) / 653810108021708899088703142078730333768570141368443377147965244301416185840) * r6 + ((-174943844284197977503220042443209056272545484400137 : ℝ) / 747211552024810170387089305232834667164080161563935288169103136344475640960) * r7 + ((-73580040349818190604284152824975651336048902487 : ℝ) / 27554042218471413044008450857980350081911420877026450602289074678601602400) * r8 + ((-22134620565034054701528186877978783773995442398693 : ℝ) / 3747349741712112173985149316685327611139953239275597281911314156289817926400) * r9 + ((-3817286827592771580821666578342835180676145652161 : ℝ) / 211496728072305788058007042381200485267939373247917343046776302017976088305) * r10 + ((-326244777957440641910738446444551436147538185126847 : ℝ) / 19175703345222391450592638509228843997626503174477839102907718049629832006320) * r11 + ((-40027541950301095688730579136786754326810602952928 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_101 h H) + ((70749041469361345416686813062846490289065010055874 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_100 h H) + ((-36529514641256263148008464071435830721348547649847 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_102 h H) + ((40027541950301095688730579136786754326810602952928 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_277 h H) + ((-70749041469361345416686813062846490289065010055874 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_276 h H) + ((88538482260136218806112747511915135095981769594772 : ℝ) / 52008967618879955658104283440479304374633221944925) * (value_278 h H)

/-- Coordinate 59.3, recovered from skew spokes on cycle 26. -/
theorem value_239 (h : Assignment) (H : Constraints h) :
    h 59 3 = ((-65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 1 0) + ((26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((-286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 1 2) + h 1 3 + ((65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 3 0) + ((-26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 9 2) := by
  have r0 := H 100 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 1 - h 25 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 100 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 2 - h 25 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 100 3
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 56 3 - h 25 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 56 0 - h 25 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 184 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 1 - h 56 1) - ((368939968243269143533432389 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 184 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 2 - h 56 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 184 3
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 57 3 - h 56 3) - ((206686098914908403040993376 : ℤ) : ℝ) * (h 57 0 - h 56 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 185 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 1 - h 56 1) - ((858052654549977619189099 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 185 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 58 2 - h 56 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 58 0 - h 56 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 188 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 1 - h 57 1) - ((-2800331330292075623770503 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 188 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 2 - h 57 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 188 3
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 59 3 - h 57 3) - ((-2798542402819443398557312 : ℤ) : ℝ) * (h 59 0 - h 57 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 191 1
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 1 - h 57 1) - ((-550416842279896856929753563 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 191 2
  change ((288207969761874200450849792 : ℤ) : ℝ) * (h 69 2 - h 57 2) - ((479139350100362155476101576 : ℤ) : ℝ) * (h 69 0 - h 57 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  have r13 := H 192 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 1 - h 58 1) - ((540983466137532583282709805 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r13
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r13
  have r14 := H 192 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 59 2 - h 58 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 59 0 - h 58 0) = 0 at r14
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r14
  linear_combination ((1804179373265298000335010690811954032422080172 : ℝ) / 1774085304619719525227171503450371537999590771666032742793598130879175) * r0 + ((222163197779633495975295139648100824256575027787 : ℝ) / 95800606449464854362267261186320063051977901669965768110854299067475450) * r1 + ((1 : ℝ) / 375768345545785080884376) * r2 + ((-208588455701333659407944126387206664332167396562465719619015586943093637644 : ℝ) / 572227283908295348399808572616577320341145601530709350924077787425188938513460346641500968834253275) * r3 + ((-450870985872734032144255228115004299220083402113811448753808741731605699477 : ℝ) / 1144454567816590696799617145233154640682291203061418701848155574850377877026920693283001937668506550) * r4 + ((-1 : ℝ) / 10152046806426074108734264) * r5 + ((-3960946192509142934249577259931381217580411644128 : ℝ) / 11704338988580142721452913028520314339135197448896911940004458547072660635) * r6 + ((-3733705578303459588812350921358291177719380757494 : ℝ) / 11704338988580142721452913028520314339135197448896911940004458547072660635) * r7 + ((6312757994311446551460263758015638815518781057829 : ℝ) / 40863131751356806193043946379920645860535633835527711071747827768838511615) * r8 + ((95209492246738219514714948494636425031844209316097 : ℝ) / 653810108021708899088703142078730333768570141368443377147965244301416185840) * r9 + ((1 : ℝ) / 21480891409450766409856768) * r10 + ((12178210769540761502261322162980689718849041161 : ℝ) / 9184680739490471014669483619326783360637140292342150200763024892867200800) * r11 + ((222163197779633495975295139648100824256575027787 : ℝ) / 73477445915923768117355868954614266885097122338737201606104199142937606400) * r12 + ((116498417426739498066164037056805329928835636592 : ℝ) / 12440984004253281650471002493011793251055257249877490767457429530469181665) * r13 + ((622284263050576598135391820226381862953230126249 : ℝ) / 70498909357435262686002347460400161755979791082639114348925434005992029435) * r14 + ((6624946658630174257230159256661495207053878391584 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_101 h H) + ((-12462953874855368827937271893790628025755062110272 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_100 h H) + ((15107097449015077726320069496070856049447101889516 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_102 h H) + (1 : ℝ) * (value_103 h H) + ((-6624946658630174257230159256661495207053878391584 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_277 h H) + ((12462953874855368827937271893790628025755062110272 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_276 h H) + ((-15107097449015077726320069496070856049447101889516 : ℝ) / 17336322539626651886034761146826434791544407314975) * (value_278 h H)

/-- Coordinate 60.0, recovered from skew spokes on cycle 27. -/
theorem value_240 (h : Assignment) (H : Constraints h) :
    h 60 0 = ((395474070089323488804761 : ℝ) / 337451016732989027785850) * (h 1 0) + ((-3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 1 1) + ((68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 1 2) + ((-58023053356334461018911 : ℝ) / 337451016732989027785850) * (h 3 0) + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (h 5 1) + ((-68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((74647402988427015505399 : ℝ) / 1108449943644242739286340670140492100527307169600) * r0 + ((4016880610017580681716866980437077697810321597 : ℝ) / 4075183616339127717964487757869456251938629300) * r1 + ((-206250964119490534173532133762673264055314309 : ℝ) / 8150367232678255435928975515738912503877258600) * r2 + ((-2763002540777831477091 : ℝ) / 1108449943644242739286340670140492100527307169600) * r3 + ((206250964119490534173532133762673264055314309 : ℝ) / 8150367232678255435928975515738912503877258600) * (value_118 h H) + ((58303006321547036247620777432378554128307703 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_116 h H) + ((4016880610017580681716866980437077697810321597 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_228 h H) + ((-206250964119490534173532133762673264055314309 : ℝ) / 8150367232678255435928975515738912503877258600) * (value_230 h H)

/-- Coordinate 60.1, recovered from skew spokes on cycle 27. -/
theorem value_241 (h : Assignment) (H : Constraints h) :
    h 60 1 = ((-14794973814770092723650381 : ℝ) / 45893338275686507778875600) * (h 1 0) + ((18572494168528014899067680421 : ℝ) / 8071828320253097544637532000) * (h 1 1) + ((-5784129614890699131802604323 : ℝ) / 3759481683405552281064056000) * (h 1 2) + ((14794973814770092723650381 : ℝ) / 45893338275686507778875600) * (h 3 0) + ((-10500665848274917354430148421 : ℝ) / 8071828320253097544637532000) * (h 5 1) + ((5784129614890699131802604323 : ℝ) / 3759481683405552281064056000) * (h 9 2) := by
  have r0 := H 116 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 1 - h 29 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((1 : ℝ) / 375768345545785080884376) * r0 + ((-5843419960605124134038812333767820570808962471 : ℝ) / 46280044604835089452005528565113226273299861249895393293405263713574400) * r1 + ((-1024241917730442951489074296632725510461335841287 : ℝ) / 554224971822121369643170335070246050263653584800) * r2 + ((52590779645446117206349311003910385137280662239 : ℝ) / 1108449943644242739286340670140492100527307169600) * r3 + ((704522562608099653507161 : ℝ) / 150749192335617012542942331139106925671713775065600) * r4 + (1 : ℝ) * (value_117 h H) + ((1024241917730442951489074296632725510461335841287 : ℝ) / 554224971822121369643170335070246050263653584800) * (value_116 h H) + ((-52590779645446117206349311003910385137280662239 : ℝ) / 1108449943644242739286340670140492100527307169600) * (value_118 h H) + ((-1024241917730442951489074296632725510461335841287 : ℝ) / 554224971822121369643170335070246050263653584800) * (value_228 h H) + ((52590779645446117206349311003910385137280662239 : ℝ) / 1108449943644242739286340670140492100527307169600) * (value_230 h H)

/-- Coordinate 60.2, recovered from skew spokes on cycle 27. -/
theorem value_242 (h : Assignment) (H : Constraints h) :
    h 60 2 = ((-16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 1 0) + ((480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 1 1) + ((-9545790293705793165213571 : ℝ) / 13821623836049824562735500) * (h 1 2) + ((16401952160911844438037 : ℝ) / 168725508366494513892925) * (h 3 0) + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (h 5 1) + ((23367414129755617727949071 : ℝ) / 13821623836049824562735500) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((1453809958816310582921567 : ℝ) / 554224971822121369643170335070246050263653584800) * r0 + ((-1135491495026778330175747990639452007179163999 : ℝ) / 2037591808169563858982243878934728125969314650) * r1 + ((58303006321547036247620777432378554128307703 : ℝ) / 4075183616339127717964487757869456251938629300) * r2 + ((781045340995802116097 : ℝ) / 554224971822121369643170335070246050263653584800) * r3 + ((4016880610017580681716866980437077697810321597 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_118 h H) + ((1135491495026778330175747990639452007179163999 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_116 h H) + ((-1135491495026778330175747990639452007179163999 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_228 h H) + ((58303006321547036247620777432378554128307703 : ℝ) / 4075183616339127717964487757869456251938629300) * (value_230 h H)

/-- Coordinate 60.3, recovered from skew spokes on cycle 27. -/
theorem value_243 (h : Assignment) (H : Constraints h) :
    h 60 3 = ((9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 1 0) + ((-372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 1 1) + ((8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 1 2) + h 1 3 + ((-9833358418001256641538 : ℝ) / 168725508366494513892925) * (h 3 0) + ((372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (h 5 1) + ((-8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 116 3
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 3 - h 29 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((1028059759885407499336037624397405398384683 : ℝ) / 45038970744324805911337560238540120724448394382467402642803565465200) * r0 + ((1 : ℝ) / 375768345545785080884376) * r1 + ((340377009445248283434687727104557481773529763 : ℝ) / 1018795904084781929491121939467364062984657325) * r2 + ((-17477015918051927488712639614755891772539611 : ℝ) / 2037591808169563858982243878934728125969314650) * r3 + ((-13772210669469547117 : ℝ) / 16300734465356510871857951031477825007754517200) * r4 + ((17477015918051927488712639614755891772539611 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_118 h H) + ((-340377009445248283434687727104557481773529763 : ℝ) / 1018795904084781929491121939467364062984657325) * (value_116 h H) + (1 : ℝ) * (value_119 h H) + ((340377009445248283434687727104557481773529763 : ℝ) / 1018795904084781929491121939467364062984657325) * (value_228 h H) + ((-17477015918051927488712639614755891772539611 : ℝ) / 2037591808169563858982243878934728125969314650) * (value_230 h H)

/-- Coordinate 61.0, recovered from skew spokes on cycle 27. -/
theorem value_244 (h : Assignment) (H : Constraints h) :
    h 61 0 = ((24702794285873566689225010 : ℝ) / 20299831706871375888292479) * (h 1 0) + ((-13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 1 1) + ((85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 1 2) + ((-4402962579002190800932531 : ℝ) / 20299831706871375888292479) * (h 3 0) + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (h 5 1) + ((-85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (h 9 2) := by
  have r0 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_228 h H)

/-- Coordinate 61.1, recovered from skew spokes on cycle 27. -/
theorem value_245 (h : Assignment) (H : Constraints h) :
    h 61 1 = ((2027064785014945318712380073 : ℝ) / 2760777112134507120807777144) * (h 1 0) + ((-235272579258668511597182619 : ℝ) / 79811304146673785543714020) * (h 1 1) + ((5827470807254752012871525461 : ℝ) / 2174584711612796704745851860) * (h 1 2) + ((-2027064785014945318712380073 : ℝ) / 2760777112134507120807777144) * (h 3 0) + ((315083883405342297140896639 : ℝ) / 79811304146673785543714020) * (h 5 1) + ((-5827470807254752012871525461 : ℝ) / 2174584711612796704745851860) * (h 9 2) := by
  have r0 := H 116 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 1 - h 29 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1 : ℝ) / 375768345545785080884376) * r0 + ((-658162236221922019004917 : ℝ) / 385063664927311776556028057449561546825357414272) * r1 + ((-871405633609100756943061 : ℝ) / 576414469417359933548653) * r2 + ((5923460125997298171044253 : ℝ) / 9222631510677758936778448) * r3 + ((-1 : ℝ) / 10152046806426074108734264) * r4 + ((5923460125997298171044253 : ℝ) / 93628586774820622010456163866020287613179074342272) * r5 + (1 : ℝ) * (value_117 h H) + ((871405633609100756943061 : ℝ) / 576414469417359933548653) * (value_116 h H) + ((-5923460125997298171044253 : ℝ) / 9222631510677758936778448) * (value_118 h H) + ((-871405633609100756943061 : ℝ) / 576414469417359933548653) * (value_228 h H) + ((5923460125997298171044253 : ℝ) / 9222631510677758936778448) * (value_230 h H)

/-- Coordinate 61.2, recovered from skew spokes on cycle 27. -/
theorem value_246 (h : Assignment) (H : Constraints h) :
    h 61 2 = ((33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 1 0) + ((-154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 1 1) + ((201456234728327216730076966 : ℝ) / 31979186935482304481556645) * (h 1 2) + ((-33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (h 3 0) + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (h 5 1) + ((-169477047792844912248520321 : ℝ) / 31979186935482304481556645) * (h 9 2) := by
  have r0 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_230 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource013

/- Original source: CubicalIndecomposability/Rigidity/Values04.lean -/
section VerificationSource014


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 61.3, recovered from skew spokes on cycle 27. -/
theorem value_247 (h : Assignment) (H : Constraints h) :
    h 61 3 = ((-599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 1 0) + ((2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 1 1) + ((-2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 1 2) + h 1 3 + ((599816457482315935619492 : ℝ) / 699994196788668134079051) * (h 3 0) + ((-2112356982453003366864414 : ℝ) / 688028484023049875376845) * (h 5 1) + ((2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (h 9 2) := by
  have r0 := H 189 3
  change ((1 : ℤ) : ℝ) * (h 61 3 - h 57 3) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_231 h H)

/-- Coordinate 62.0, recovered from skew spokes on cycle 27. -/
theorem value_248 (h : Assignment) (H : Constraints h) :
    h 62 0 = ((-355785217299252588876116 : ℝ) / 3456801008592869729912095) * (h 1 0) + ((16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 1 1) + ((-368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 1 2) + ((3812586225892122318788211 : ℝ) / 3456801008592869729912095) * (h 3 0) + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (h 5 1) + ((368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((11225865095908060396188103 : ℝ) / 5677403079505292682362515210983163763988217765360) * r0 + ((12104895807551309826750335912859206560688724264 : ℝ) / 20872805439357693685156305922732219720544918255) * r1 + ((-31017093782423145710315601904681450822371248373 : ℝ) / 41745610878715387370312611845464439441089836510) * r2 + ((-3296916660451102322206426579686795860241800558898 : ℝ) / 346922124906117334998530693598981217503720622359233706198452196899725505) * r3 + ((239176040720711102552674927309639910326106438114401327487019338129620862487 : ℝ) / 41593953971835760248467544969278353617298714248482629083231306724424830023152724395529782598911120) * r4 + ((-45725570889250235206517378 : ℝ) / 4647477487728575365214255418255355196234209247495) * r5 + ((1905338850730207435700494267 : ℝ) / 316028469165543124834569368441364153343926228829660) * r6 + ((4003398801976338534107803703905394973150757821519 : ℝ) / 891356778944326644897084804773240095464558761334263296934554503428685680) * r7 + ((-19625603288152935185632676588630549180145048349221 : ℝ) / 7130854231554613159176678438185920763716470090674106375476436027429485440) * r8 + ((78498015725026245766819680468733234767661918069 : ℝ) / 288339136973904216044144441239048023734280927521338781234242241308388985) * r9 + ((-6541867762717645061877558862876849726715016116407 : ℝ) / 39214122628450973382003644008510531227862206142902074247856944817940901960) * r10 + ((31017093782423145710315601904681450822371248373 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_118 h H) + ((8767909631806383858405970009873013159856193991 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_116 h H) + ((12104895807551309826750335912859206560688724264 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_228 h H) + ((-31017093782423145710315601904681450822371248373 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_230 h H)

/-- Coordinate 62.1, recovered from skew spokes on cycle 27. -/
theorem value_249 (h : Assignment) (H : Constraints h) :
    h 62 1 = ((-54248237320823673320051397 : ℝ) / 235062468584315141634022460) * (h 1 0) + ((152631455522264344757678195889 : ℝ) / 82686680125541443939497312400) * (h 1 1) + ((-45168965696159126417226512027 : ℝ) / 38511604442033001286889159200) * (h 1 2) + ((54248237320823673320051397 : ℝ) / 235062468584315141634022460) * (h 3 0) + ((-69944775396722900818180883489 : ℝ) / 82686680125541443939497312400) * (h 5 1) + ((45168965696159126417226512027 : ℝ) / 38511604442033001286889159200) * (h 9 2) := by
  have r0 := H 116 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 1 - h 29 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((1 : ℝ) / 375768345545785080884376) * r0 + ((-124914880748834161252317611772514712395019332049 : ℝ) / 474086302707166477545105463061262654476115078888618337392282867390670080) * r1 + ((-10326681449670835768524253428905508449520629922663 : ℝ) / 5677403079505292682362515210983163763988217765360) * r2 + ((1124233926739507451270858505952632411555173988441 : ℝ) / 11354806159010585364725030421966327527976435530720) * r3 + ((16107348189806448890484208981548537718921196971929 : ℝ) / 23590704493615978779900087164730722790253002320427892021494749389181334340) * r4 + ((-4623206702558088922600051203048892857336991728563965584704253771288479718879 : ℝ) / 11313555480339326787583172231643712183905250275587275110638915429043553766297541035584100866903824640) * r5 + ((36862173867341473146182673381352430634076603191353 : ℝ) / 45572728996312418327540750648446942072587538893941524927673606590120848120) * r6 + ((-447451403251072402777977993598608387662829241315329 : ℝ) / 1032981857249748148757590348031464020311984214929341231693935082709405890720) * r7 + ((-2301049741400921270069172711649791102703028138847 : ℝ) / 7130854231554613159176678438185920763716470090674106375476436027429485440) * r8 + ((191764887107602458333419140113689308998355389135141 : ℝ) / 969796175491427389648028267593285223865439932331678467064795299730410019840) * r9 + ((-255672193488991252229908079072199011411447570983 : ℝ) / 13071374209483657794001214669503510409287402047634024749285648272646967320) * r10 + ((21307209678622495370379904457076589888706154348349 : ℝ) / 1777706892489777459984165195052477415663086678478227365902848165079987555520) * r11 + (1 : ℝ) * (value_117 h H) + ((10326681449670835768524253428905508449520629922663 : ℝ) / 5677403079505292682362515210983163763988217765360) * (value_116 h H) + ((-1124233926739507451270858505952632411555173988441 : ℝ) / 11354806159010585364725030421966327527976435530720) * (value_118 h H) + ((-10326681449670835768524253428905508449520629922663 : ℝ) / 5677403079505292682362515210983163763988217765360) * (value_228 h H) + ((1124233926739507451270858505952632411555173988441 : ℝ) / 11354806159010585364725030421966327527976435530720) * (value_230 h H)

/-- Coordinate 62.2, recovered from skew spokes on cycle 27. -/
theorem value_250 (h : Assignment) (H : Constraints h) :
    h 62 2 = ((-240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 1 0) + ((4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 1 1) + ((-82173261632986900318333999 : ℝ) / 141586781036886034142974850) * (h 1 2) + ((240561965026707051757876 : ℝ) / 3456801008592869729912095) * (h 3 0) + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (h 5 1) + ((223760042669872934461308849 : ℝ) / 141586781036886034142974850) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((14657701538247532435880383 : ℝ) / 5677403079505292682362515210983163763988217765360) * r0 + ((-11448329496155237184448366720203550360570825151 : ℝ) / 20872805439357693685156305922732219720544918255) * r1 + ((1246344286574326462988625494104847885209030657 : ℝ) / 41745610878715387370312611845464439441089836510) * r2 + ((71427488214844345106426203928646989636408067332 : ℝ) / 346922124906117334998530693598981217503720622359233706198452196899725505) * r3 + ((-5125363256112199327582934659215388442609082313235422430836009155303796983 : ℝ) / 41593953971835760248467544969278353617298714248482629083231306724424830023152724395529782598911120) * r4 + ((71427488214844345106426203928646989636408067332 : ℝ) / 335093595561120722996623166532698103474908374220158271527011813162653295) * r5 + ((-435048880598640977363497875311390980705152805367 : ℝ) / 15190909665437472775846916882815647357529179631313841642557868863373616040) * r6 + ((-43366689273298352386044480956678529422104898023 : ℝ) / 445678389472163322448542402386620047732279380667131648467277251714342840) * r7 + ((212593718911589224903741037292483147798202416557 : ℝ) / 3565427115777306579588339219092960381858235045337053187738218013714742720) * r8 + ((-5101963443917453221887585994903356402600576238 : ℝ) / 865017410921712648132433323717144071202842782564016343702726723925166955) * r9 + ((212593718911589224903741037292483147798202416557 : ℝ) / 58821183942676460073005466012765796841793309214353111371785417226911352940) * r10 + ((40499266592141060907323986351359591555880805853 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_118 h H) + ((11448329496155237184448366720203550360570825151 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_116 h H) + ((-11448329496155237184448366720203550360570825151 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_228 h H) + ((1246344286574326462988625494104847885209030657 : ℝ) / 41745610878715387370312611845464439441089836510) * (value_230 h H)

/-- Coordinate 62.3, recovered from skew spokes on cycle 27. -/
theorem value_251 (h : Assignment) (H : Constraints h) :
    h 62 3 = ((144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 1 0) + ((-7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 1 1) + ((80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 1 2) + h 1 3 + ((-144222590130685097409224 : ℝ) / 3456801008592869729912095) * (h 3 0) + ((7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (h 5 1) + ((-80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 116 3
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 3 - h 29 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 199 3
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 3 - h 60 3) - ((127365404271254371738016 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  linear_combination ((21976849717209446878037138296684551455431277 : ℝ) / 461372915696853189652459901335571354918364588018767845645604001569640) * r0 + ((1 : ℝ) / 375768345545785080884376) * r1 + ((6863544419508397215366522750433286838613197574 : ℝ) / 20872805439357693685156305922732219720544918255) * r2 + ((-373606445192560596926631351043637374742331709 : ℝ) / 20872805439357693685156305922732219720544918255) * r3 + ((-42822469278259238736020554558364265118620347368 : ℝ) / 346922124906117334998530693598981217503720622359233706198452196899725505) * r4 + ((90375780784684301210439737397729469095043915514458103782342668196478763 : ℝ) / 1223351587406934124954927793214069224038197477896547914212685491894847941857433070456758311732680) * r5 + ((-42822469278259238736020554558364265118620347368 : ℝ) / 335093595561120722996623166532698103474908374220158271527011813162653295) * r6 + ((26240728048981407650805940878795864581544878239 : ℝ) / 335093595561120722996623166532698103474908374220158271527011813162653295) * r7 + ((1 : ℝ) / 9805906347399177090242376) * r8 + ((12999678173757268902006239776646294768152605451 : ℝ) / 222839194736081661224271201193310023866139690333565824233638625857171420) * r9 + ((-63727482404669132866242999277075671126608990009 : ℝ) / 1782713557888653289794169609546480190929117522668526593869109006857371360) * r10 + ((179926341505290919058909893102370861842942636 : ℝ) / 50883377113041920478378430806890827717814281327295079041336866113245115) * r11 + ((-3748675435568772521543705839827980654506411177 : ℝ) / 1730034821843425296264866647434288142405685565128032687405453447850333910) * r12 + ((373606445192560596926631351043637374742331709 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_118 h H) + ((-6863544419508397215366522750433286838613197574 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_116 h H) + (1 : ℝ) * (value_119 h H) + ((6863544419508397215366522750433286838613197574 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_228 h H) + ((-373606445192560596926631351043637374742331709 : ℝ) / 20872805439357693685156305922732219720544918255) * (value_230 h H)

/-- Coordinate 63.0, recovered from skew spokes on cycle 27. -/
theorem value_252 (h : Assignment) (H : Constraints h) :
    h 63 0 = ((69463083005130850032370138 : ℝ) / 80398009002116453602781515) * (h 1 0) + ((-14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 1 2) + ((10934925996985603570411377 : ℝ) / 80398009002116453602781515) * (h 3 0) + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((-159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((335638928272668225154012 : ℝ) / 634829804125576481838051680255249799076238103415) * r0 + ((33148542115498607855981308940328018593568236871 : ℝ) / 37342929654445675402238334132661752886837535495) * r1 + ((-7418969692810645136203174191726452119397912736 : ℝ) / 37342929654445675402238334132661752886837535495) * r2 + ((-91209611425840385157559406496688604853733764874176 : ℝ) / 8068687798893314104048410139197333717652276506634574472420501458100529685) * r3 + ((31807328307450178929056067383748223880933784430910312862717108718078651968 : ℝ) / 4650908396493415440506215896219460148656725131491972997858773012172252591394177028087341018264305) * r4 + ((-30403203808613461719186468832229534951244588291392 : ℝ) / 2597860261120549469889498084655024458337115052966540099913989393147615305) * r5 + ((313589085539244977218166662388713979986893828946252 : ℝ) / 44163624439049340988121467439135415791730955900431181698537819683509460185) * r6 + ((577467057463769222908070802 : ℝ) / 108090669947945084591449388841784767991774467071315) * r7 + ((-2802914612614509300824178063 : ℝ) / 864725359583560676731595110734278143934195736570520) * r8 + ((2171657414900961551370462059444966782231756306528 : ℝ) / 6706169221909274448055890430837281969575149379947803534619009689304934445) * r9 + ((-22399220395660355515583333027765284284778130639018 : ℝ) / 114004876772457665616950137324233793482777539459112660088523164718183885565) * r10 + ((7418969692810645136203174191726452119397912736 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_118 h H) + ((4194387538947067546257025192333734293269298624 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_116 h H) + ((33148542115498607855981308940328018593568236871 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_228 h H) + ((-7418969692810645136203174191726452119397912736 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_230 h H)

/-- Coordinate 63.1, recovered from skew spokes on cycle 27. -/
theorem value_253 (h : Assignment) (H : Constraints h) :
    h 63 1 = ((7700484084216196182764171737 : ℝ) / 10934129224287837689978286040) * (h 1 0) + ((-25878497438885413121565821784 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((44098331053156324319269247573 : ℝ) / 17224998093056182662294560200) * (h 1 2) + ((-7700484084216196182764171737 : ℝ) / 10934129224287837689978286040) * (h 3 0) + ((35124268474128805285885696009 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((-44098331053156324319269247573 : ℝ) / 17224998093056182662294560200) * (h 9 2) := by
  have r0 := H 116 1
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 1 - h 29 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((1 : ℝ) / 375768345545785080884376) * r0 + ((-705817136960917286315079379000052012305604803273 : ℝ) / 424087013687862547099906792806124097092827103524299971296446572703544960) * r1 + ((-3863090877156687933645459717594030951720889283013 : ℝ) / 2539319216502305927352206721020999196304952413660) * r2 + ((6352354232648255576835714411000468110750443229457 : ℝ) / 10157276866009223709408826884083996785219809654640) * r3 + ((-1161724448936658625685936296593810347052893560063829 : ℝ) / 1097341540649490718150583778930837385600709604902302128249188198301672037160) * r4 + ((6519173226837548846548820134805404941829340084372934732331340820599598249927 : ℝ) / 10120376670769671998541525790173545283477033886126533243340690074486821638873729213118054055743127680) * r5 + ((-10329742931261897461710655958353191951579598950907 : ℝ) / 10391441044482197879557992338620097833348460211866160399655957572590461220) * r6 + ((1704712258648047453808774432773926212686344595269597 : ℝ) / 2826471964099157823239773916104666610670781177627595628706420459744605451840) * r7 + ((1161724448936658625685936296593810347052893560063829 : ℝ) / 2321883943526591688035691501450244770330269231375512343995237036061591409920) * r8 + ((-5114136775944142361426323298321778638059033785808791 : ℝ) / 18575071548212733504285532011601958162642153851004098751961896288492731279360) * r9 + ((10329742931261897461710655958353191951579598950907 : ℝ) / 375545476426919369091129864126887790296208365277076997938664542601076328920) * r10 + ((-1704712258648047453808774432773926212686344595269597 : ℝ) / 102148369588122068392787323042513478960568675355364943439316755587492761466240) * r11 + (1 : ℝ) * (value_117 h H) + ((3863090877156687933645459717594030951720889283013 : ℝ) / 2539319216502305927352206721020999196304952413660) * (value_116 h H) + ((-6352354232648255576835714411000468110750443229457 : ℝ) / 10157276866009223709408826884083996785219809654640) * (value_118 h H) + ((-3863090877156687933645459717594030951720889283013 : ℝ) / 2539319216502305927352206721020999196304952413660) * (value_228 h H) + ((6352354232648255576835714411000468110750443229457 : ℝ) / 10157276866009223709408826884083996785219809654640) * (value_230 h H)

/-- Coordinate 63.2, recovered from skew spokes on cycle 27. -/
theorem value_254 (h : Assignment) (H : Constraints h) :
    h 63 2 = ((125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 1 0) + ((-67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((753062971344274112653576967 : ℝ) / 126654397743060166634518825) * (h 1 2) + ((-125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (h 3 0) + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((-626408573601213946019058142 : ℝ) / 126654397743060166634518825) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((674260551111855735550811 : ℝ) / 5078638433004611854704413442041998392609904827320) * r0 + ((-1053256124126353649204297264753648051329009334 : ℝ) / 37342929654445675402238334132661752886837535495) * r1 + ((35479946038577357100382348591456225286224564694 : ℝ) / 37342929654445675402238334132661752886837535495) * r2 + ((-313749602267899034040136979041876864165162656342 : ℝ) / 110529969847853617863676851221881283803455842556638006471513718604116845) * r3 + ((109413212595264935510907783948783490070182257034168082034500805696748506 : ℝ) / 63711073924567334801455012276978906145982536047835246546010589207839076594440781206675904359785) * r4 + ((-7634573655185543161643333156685670361352291304322 : ℝ) / 2597860261120549469889498084655024458337115052966540099913989393147615305) * r5 + ((629964917140310889149482488359109246168002549353031 : ℝ) / 353308995512394727904971739513083326333847647203449453588302557468075681480) * r6 + ((194681628207231350621904995495484594214483428260211 : ℝ) / 145117746470411980502230718840640298145641826960969521499702314753849463120) * r7 + ((-890902040736493791428499038117771485256116590493889 : ℝ) / 1160941971763295844017845750725122385165134615687756171997618518030795704960) * r8 + ((3817286827592771580821666578342835180676145652161 : ℝ) / 46943184553364921136391233015860973787026045659634624742333067825134541115) * r9 + ((-629964917140310889149482488359109246168002549353031 : ℝ) / 12768546198515258549098415380314184870071084419420617929914594448436595183280) * r10 + ((1862983615868318301855985541205527600612970801 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_118 h H) + ((1053256124126353649204297264753648051329009334 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_116 h H) + ((-1053256124126353649204297264753648051329009334 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_228 h H) + ((35479946038577357100382348591456225286224564694 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_230 h H)

/-- Coordinate 63.3, recovered from skew spokes on cycle 27. -/
theorem value_255 (h : Assignment) (H : Constraints h) :
    h 63 3 = ((-65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 1 0) + ((26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 1 1) + ((-286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 1 2) + h 1 3 + ((65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (h 3 0) + ((-26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (h 5 1) + ((286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (h 9 2) := by
  have r0 := H 116 2
  change ((375768345545785080884376 : ℤ) : ℝ) * (h 60 2 - h 29 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 60 0 - h 29 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 189 0
  change ((1 : ℤ) : ℝ) * (h 61 0 - h 57 0) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 189 2
  change ((1 : ℤ) : ℝ) * (h 61 2 - h 57 2) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 189 3
  change ((1 : ℤ) : ℝ) * (h 61 3 - h 57 3) - ((0 : ℤ) : ℝ) * (h 61 1 - h 57 1) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 198 1
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 1 - h 60 1) - ((-238631066687653224146906471 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 198 2
  change ((-10152046806426074108734264 : ℤ) : ℝ) * (h 61 2 - h 60 2) - ((-395436308798036478554666224 : ℤ) : ℝ) * (h 61 0 - h 60 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 199 1
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 1 - h 60 1) - ((-704522562608099653507161 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 199 2
  change ((9805906347399177090242376 : ℤ) : ℝ) * (h 62 2 - h 60 2) - ((-212444332750858175578384 : ℤ) : ℝ) * (h 62 0 - h 60 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 201 1
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 1 - h 61 1) - ((1824578156226373875118457 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 201 2
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 2 - h 61 2) - ((5394084408894845884406488 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 201 3
  change ((21480891409450766409856768 : ℤ) : ℝ) * (h 63 3 - h 61 3) - ((-2798542402819443398557312 : ℤ) : ℝ) * (h 63 0 - h 61 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 204 1
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 1 - h 62 1) - ((-342703679408331707635026983 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 204 2
  change ((-354384320256255433150255536 : ℤ) : ℝ) * (h 63 2 - h 62 2) - ((-599128311074166242988148304 : ℤ) : ℝ) * (h 63 0 - h 62 0) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  linear_combination ((-2572189708473753123674 : ℝ) / 37342929654445675402238334132661752886837535495) * r0 + ((546447126325330893637933993956292161633062816 : ℝ) / 37342929654445675402238334132661752886837535495) * r1 + ((966547471183077455310866171655847876422317424 : ℝ) / 37342929654445675402238334132661752886837535495) * r2 + (1 : ℝ) * r3 + ((162778610651060668530804544928686899352619656608 : ℝ) / 110529969847853617863676851221881283803455842556638006471513718604116845) * r4 + ((-3339142875192809583082516432170418784821149312189750464157764166318432 : ℝ) / 3747710230856902047144412486881112126234266826343249796824152306343475093790634188627994374105) * r5 + ((3960946192509142934249577259931381217580411644128 : ℝ) / 2597860261120549469889498084655024458337115052966540099913989393147615305) * r6 + ((-2403209373432579116055950052162718568003278921154 : ℝ) / 2597860261120549469889498084655024458337115052966540099913989393147615305) * r7 + ((-6312757994311446551460263758015638815518781057829 : ℝ) / 9069859154400748781389419927540018634102614185060595093731394672115591445) * r8 + ((61281839022530767459426726330149323484083612489427 : ℝ) / 145117746470411980502230718840640298145641826960969521499702314753849463120) * r9 + ((1 : ℝ) / 21480891409450766409856768) * r10 + ((-116498417426739498066164037056805329928835636592 : ℝ) / 2761363797256760066846543118580057281589767391743213220137239283831443595) * r11 + ((1201604686716289558027975026081359284001639460577 : ℝ) / 46943184553364921136391233015860973787026045659634624742333067825134541115) * r12 + ((-966547471183077455310866171655847876422317424 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_118 h H) + ((-546447126325330893637933993956292161633062816 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_116 h H) + ((546447126325330893637933993956292161633062816 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_228 h H) + ((966547471183077455310866171655847876422317424 : ℝ) / 37342929654445675402238334132661752886837535495) * (value_230 h H) + (1 : ℝ) * (value_231 h H)

/-- Coordinate 117.0, recovered from nonplanar cycle 28. -/
theorem value_468 (h : Assignment) (H : Constraints h) :
    h 117 0 = ((2496476032402122435583484089 : ℝ) / 3262316970720903125342558132) * (h 1 1) + ((-896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (h 1 2) + h 3 0 + ((-2496476032402122435583484089 : ℝ) / 3262316970720903125342558132) * (h 5 1) + ((896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-774799900246779444452526593111 : ℝ) / 64830678173449669550336795753629499896009056322050816768) * r0 + ((-9 : ℝ) / 143541946711719737515072557808) * r1 + ((648793639805118185614925682519137268457215089845992689 : ℝ) / 259644616961889216134739139439493835169302456258713643183008010850749912003584) * r2 + ((52754265062119622717051337 : ℝ) / 4024163617500789397729065600630881897860742564385728) * r3 + ((648793639805118185614925682519137268457215089845992689 : ℝ) / 113067784500992188492541360683321359841441758757852203008798091868346271684060489984) * r4 + ((5861585006902180301894593 : ℝ) / 194711983216102411504443778993105061078219992330369609392) * r5 + ((-4541555478635827299304479777633960879200505628921948823 : ℝ) / 43336014821824645421348125503763034689845625883723808) * (value_321 h H) + ((1391371010186957425142984785518273590531439634546311455 : ℝ) / 21668007410912322710674062751881517344922812941861904) * (value_320 h H) + ((-896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (value_322 h H) + ((4541555478635827299304479777633960879200505628921948823 : ℝ) / 43336014821824645421348125503763034689845625883723808) * (value_329 h H) + ((-1369703002776045102432310722766392073186516821604449551 : ℝ) / 21668007410912322710674062751881517344922812941861904) * (value_328 h H) + ((896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (value_330 h H)

/-- Coordinate 117.1, recovered from nonplanar cycle 28. -/
theorem value_469 (h : Assignment) (H : Constraints h) :
    h 117 1 = ((7713355567306296627106247603 : ℝ) / 8971371669482483594692034863) * (h 1 1) + ((-2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (h 1 2) + ((1258016102176186967585787260 : ℝ) / 8971371669482483594692034863) * (h 5 1) + ((2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-7472481975300828945630184422148213707660011896717796381 : ℝ) / 1045028960714180780630773107555646827851925350639532964940262515133246857105572416) * r0 + ((-88183935133168754878580907 : ℝ) / 2313804137444162370456685218408546104134927273516613396) * r1 + ((1084522288008692388648413109611937436151012481128290979 : ℝ) / 714022696645195344370532633458608046715581754711462518753272029839562258009856) * r2 + ((88183935133168754878580907 : ℝ) / 11066449948127170843754930401734925219117042052060752) * r3 + ((1084522288008692388648413109611937436151012481128290979 : ℝ) / 310936407377728518354488741879133739563964836584093558274194752637952247131166347456) * r4 + ((9798215014796528319842323 : ℝ) / 535457953844281631637220392231038917965104978908516425828) * r5 + ((-7472481975300828945630184422148213707660011896717796381 : ℝ) / 119174040760017774908707345135348345397075471180240472) * (value_321 h H) + ((2289593089891036589809366201483294279457361007637197661 : ℝ) / 59587020380008887454353672567674172698537735590120236) * (value_320 h H) + ((-2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (value_322 h H) + ((7591656016060846720538891767283562053057087367898036853 : ℝ) / 119174040760017774908707345135348345397075471180240472) * (value_329 h H) + ((-2289593089891036589809366201483294279457361007637197661 : ℝ) / 59587020380008887454353672567674172698537735590120236) * (value_328 h H) + ((2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (value_330 h H)

/-- Coordinate 117.2, recovered from nonplanar cycle 28. -/
theorem value_470 (h : Assignment) (H : Constraints h) :
    h 117 2 = ((-4393522730936721890853175693 : ℝ) / 287083893423439475030145115616) * (h 1 1) + ((70208145694016106016574415265 : ℝ) / 143541946711719737515072557808) * (h 1 2) + ((4393522730936721890853175693 : ℝ) / 287083893423439475030145115616) * (h 5 1) + ((73333801017703631498498142543 : ℝ) / 143541946711719737515072557808) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2104408211601257281089416387589030115203786601857238511899 : ℝ) / 189498584876171448221046856836757291450482463582635310975834269410828763421810464768) * r0 + ((70208145694016106016574415265 : ℝ) / 1258709450769624329528436758814249080649400436793037687424) * r1 + ((300629744514465325869916626798432873600540943122462644557 : ℝ) / 129476115658328755779189917533827592471092158187678536733926661410907289452453888) * r2 + ((73333801017703631498498142543 : ℝ) / 6020148771781180939002682138543799319199670876321049088) * r3 + ((300629744514465325869916626798432873600540943122462644557 : ℝ) / 56383135204494771328280625194082918107598957033915631900387315145015340813118164338688) * r4 + ((2716066704359393759203634909 : ℝ) / 97096375630429735870215964457895057124339036175410978550144) * r5 + ((-2104408211601257281089416387589030115203786601857238511899 : ℝ) / 21610226057816556516778931917876499965336352107350272256) * (value_321 h H) + ((634675555557149348686113836998555015486773848796308240563 : ℝ) / 10805113028908278258389465958938249982668176053675136128) * (value_320 h H) + ((70208145694016106016574415265 : ℝ) / 143541946711719737515072557808) * (value_322 h H) + ((2104408211601257281089416387589030115203786601857238511899 : ℝ) / 21610226057816556516778931917876499965336352107350272256) * (value_329 h H) + ((-634675555557149348686113836998555015486773848796308240563 : ℝ) / 10805113028908278258389465958938249982668176053675136128) * (value_328 h H) + ((73333801017703631498498142543 : ℝ) / 143541946711719737515072557808) * (value_330 h H)

/-- Coordinate 117.3, recovered from nonplanar cycle 28. -/
theorem value_471 (h : Assignment) (H : Constraints h) :
    h 117 3 = ((2426322943114626526678742106 : ℝ) / 8971371669482483594692034863) * (h 1 1) + ((-297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (h 1 2) + h 1 3 + ((-2426322943114626526678742106 : ℝ) / 8971371669482483594692034863) * (h 5 1) + ((297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 240 3
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 3 - h 80 3) - ((529767551903157376559408544 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-14794688810861695760889861180279186320489735269229561 : ℝ) / 20490763935572172169230845246189153487292653934108489508632598335946016805991616) * r0 + ((-8764536704280177185725509 : ℝ) / 2313804137444162370456685218408546104134927273516613396) * r1 + ((1 : ℝ) / 8768931170325661731634311128) * r2 + ((2113526972980242251555694454325598045784247895604223 : ℝ) / 14000445032258732242559463401149177386580034406107108210848471173324750157056) * r3 + ((8764536704280177185725509 : ℝ) / 11066449948127170843754930401734925219117042052060752) * r4 + ((2113526972980242251555694454325598045784247895604223 : ℝ) / 6096792301524088595186053762335955677724800717335167809297936326234357786885614656) * r5 + ((324612470528895451323167 : ℝ) / 178485984614760543879073464077012972655034992969505475276) * r6 + ((-251509709784648827935127640064746167448325499576902537 : ℝ) / 39724680253339258302902448378449448465691823726746824) * (value_321 h H) + ((75853659905712005905582150656068742751027427474442769 : ℝ) / 19862340126669629151451224189224724232845911863373412) * (value_320 h H) + ((-297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (value_322 h H) + (1 : ℝ) * (value_323 h H) + ((251509709784648827935127640064746167448325499576902537 : ℝ) / 39724680253339258302902448378449448465691823726746824) * (value_329 h H) + ((-75853659905712005905582150656068742751027427474442769 : ℝ) / 19862340126669629151451224189224724232845911863373412) * (value_328 h H) + ((297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (value_330 h H)

/-- Coordinate 121.0, recovered from nonplanar cycle 28. -/
theorem value_484 (h : Assignment) (H : Constraints h) :
    h 121 0 = ((18914006173254357364399801 : ℝ) / 24919876730332642263219377) * (h 1 1) + ((-13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (h 1 2) + h 3 0 + ((-18914006173254357364399801 : ℝ) / 24919876730332642263219377) * (h 5 1) + ((13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-15764250292253921991816388216860406570142347672414559 : ℝ) / 725697079556153847059748237322599926441439163769258467172373618907966788456816) * r0 + ((-99122891366552195350053 : ℝ) / 1606769733980051775136157670051199412321799580414171) * r1 + ((204476700839719127457655410461 : ℝ) / 45020220094153884203208208966107439796943035608987968) * r2 + ((9 : ℝ) / 697756548449313983370142556) * r3 + ((2252035756036274570259484030980058081448906810344937 : ℝ) / 215922860747794163842140617142661175601759037788087631293693657936364072996667856) * r4 + ((11013654596283577261117 : ℝ) / 371836846573467468833207412929086729375766993476272903) * r5 + ((-15764250292253921991816388216860406570142347672414559 : ℝ) / 82757757526018169491191560599462205509086462516522) * (value_321 h H) + ((4811980346964960907188679630563501948876721741616939 : ℝ) / 41378878763009084745595780299731102754543231258261) * (value_320 h H) + ((-13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (value_322 h H) + ((15764250292253921991816388216860406570142347672414559 : ℝ) / 82757757526018169491191560599462205509086462516522) * (value_329 h H) + ((-4770601468201951822443083850263770846122178510358678 : ℝ) / 41378878763009084745595780299731102754543231258261) * (value_328 h H) + ((13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (value_330 h H)

/-- Coordinate 121.1, recovered from nonplanar cycle 28. -/
theorem value_485 (h : Assignment) (H : Constraints h) :
    h 121 1 = ((149302932363421640305550014 : ℝ) / 174439137112328495842535639) * (h 1 1) + ((-57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (h 1 2) + ((25136204748906855536985625 : ℝ) / 174439137112328495842535639) * (h 5 1) + ((57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-19158916918742557695400869873679366304669766965165717 : ℝ) / 1451394159112307694119496474645199852882878327538516934344747237815933576913632) * r0 + ((-843275794066356730419873 : ℝ) / 22494776275720724851906207380716791772505194125798394) * r1 + ((19324432433794594034383252994878290715687939890198761 : ℝ) / 6941720155519466662731408049585187956374926093208944914748317533591061363584) * r2 + ((843275794066356730419873 : ℝ) / 107587894636820521236982842655527663621700561130728) * r3 + ((19158916918742557695400869873679366304669766965165717 : ℝ) / 3022920050469118293789968639997256458424626529033226838111711211109097021953349984) * r4 + ((93697310451817414491097 : ℝ) / 5205715852028544563664903781007214211260737908667820642) * r5 + ((-19158916918742557695400869873679366304669766965165717 : ℝ) / 165515515052036338982383121198924411018172925033044) * (value_321 h H) + ((40937330339900113224069070961328780763007853164799599 : ℝ) / 579304302682127186438340924196235438563605237615654) * (value_320 h H) + ((-57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (value_322 h H) + ((19324432433794594034383252994878290715687939890198761 : ℝ) / 165515515052036338982383121198924411018172925033044) * (value_329 h H) + ((-40937330339900113224069070961328780763007853164799599 : ℝ) / 579304302682127186438340924196235438563605237615654) * (value_328 h H) + ((57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (value_330 h H)

/-- Coordinate 121.2, recovered from nonplanar cycle 28. -/
theorem value_486 (h : Assignment) (H : Constraints h) :
    h 121 2 = ((734066461754127170845303 : ℝ) / 199359013842661138105755016) * (h 1 1) + ((46077754888497773053609785 : ℝ) / 99679506921330569052877508) * (h 1 2) + ((-734066461754127170845303 : ℝ) / 199359013842661138105755016) * (h 5 1) + ((53601752032832795999267723 : ℝ) / 99679506921330569052877508) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2442695967107735298173956539556793085694197984566915785 : ℝ) / 131593070426182564266834347034498119994714301696825535380590416228644644306835968) * r0 + ((46077754888497773053609785 : ℝ) / 874082735285148165674069772507852480303058971745309024) * r1 + ((-348956566729676471167708077079541869384885426366702255 : ℝ) / 89911803919109282488711570927960529720665709397753953181502017577941366233088) * r2 + ((3153044237225458588192219 : ℝ) / 245915187741304048541675068926920373992458425441664) * r3 + ((-348956566729676471167708077079541869384885426366702255 : ℝ) / 39154012082266675043374831908535893175785638852239890474589783305794018570062437888) * r4 + ((-1706583514388806409392955 : ℝ) / 67426414845322101015088277544474393593472414817030819744) * r5 + ((2442695967107735298173956539556793085694197984566915785 : ℝ) / 15006740031384628067736069655369146598981011869662656) * (value_321 h H) + ((-745624103234941233090529098238305516128812060487219485 : ℝ) / 7503370015692314033868034827684573299490505934831328) * (value_320 h H) + ((46077754888497773053609785 : ℝ) / 99679506921330569052877508) * (value_322 h H) + ((-2442695967107735298173956539556793085694197984566915785 : ℝ) / 15006740031384628067736069655369146598981011869662656) * (value_329 h H) + ((745624103234941233090529098238305516128812060487219485 : ℝ) / 7503370015692314033868034827684573299490505934831328) * (value_328 h H) + ((53601752032832795999267723 : ℝ) / 99679506921330569052877508) * (value_330 h H)

/-- Coordinate 121.3, recovered from nonplanar cycle 28. -/
theorem value_487 (h : Assignment) (H : Constraints h) :
    h 121 3 = ((47102140364334606424138497 : ℝ) / 174439137112328495842535639) * (h 1 1) + ((-5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (h 1 2) + h 1 3 + ((-47102140364334606424138497 : ℝ) / 174439137112328495842535639) * (h 5 1) + ((5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (h 9 2) := by
  have r0 := H 240 1
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 1 - h 80 1) - ((5330228968049311405994223712 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 240 2
  change ((8768931170325661731634311128 : ℤ) : ℝ) * (h 117 2 - h 80 2) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 117 0 - h 80 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 248 1
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 1 - h 82 1) - ((25485668442894336741578384 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 248 2
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 2 - h 82 2) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 248 3
  change ((41939996702647862210333536 : ℤ) : ℝ) * (h 121 3 - h 82 3) - ((2527909764593526516805248 : ℤ) : ℝ) * (h 121 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 356 1
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 1 - h 117 1) - ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 356 2
  change ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 121 2 - h 117 2) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 121 0 - h 117 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-4657751664185006896400977068808336419140078826403 : ℝ) / 3557338625275263956175236457463725129614897861614012093982223622097876414004) * r0 + ((-41822036546584078403028 : ℝ) / 11247388137860362425953103690358395886252597062899197) * r1 + ((4657751664185006896400977068808336419140078826403 : ℝ) / 17014019989018300643949529533297029304840505130414080673402739052919268048) * r2 + ((10455509136646019600757 : ℝ) / 13448486829602565154622855331940957952712570141341) * r3 + ((1 : ℝ) / 41939996702647862210333536) * r4 + ((4657751664185006896400977068808336419140078826403 : ℝ) / 7409117770757642876936197647052099162805457179003006956156154929188963289101348) * r5 + ((1548964316540151051964 : ℝ) / 867619308671424093944150630167869035210122984777970107) * r6 + ((-158363556582290234477633220339483438250762680097702 : ℝ) / 13792959587669694915198593433243700918181077086087) * (value_321 h H) + ((676758634854623166893449583211556831803906541674788 : ℝ) / 96550717113687864406390154032705906427267539602609) * (value_320 h H) + ((-5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (value_322 h H) + ((158363556582290234477633220339483438250762680097702 : ℝ) / 13792959587669694915198593433243700918181077086087) * (value_329 h H) + ((-676758634854623166893449583211556831803906541674788 : ℝ) / 96550717113687864406390154032705906427267539602609) * (value_328 h H) + ((5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (value_330 h H) + (1 : ℝ) * (value_331 h H)

/-- Coordinate 119.0, recovered from nonplanar cycle 29. -/
theorem value_476 (h : Assignment) (H : Constraints h) :
    h 119 0 = ((2231362585778583771038978354791 : ℝ) / 3764067531117351640712072899818) * (h 1 1) + ((-236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (h 1 2) + h 3 0 + ((-2231362585778583771038978354791 : ℝ) / 3764067531117351640712072899818) * (h 5 1) + ((236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((42906353427531915767796465071 : ℝ) / 179091871764900192403125895321350468534581151167401274784) * r0 + ((-9 : ℝ) / 1254689177039117213570690966606) * r1 + ((-8307801125620258177501138157535472486710316671729499231 : ℝ) / 33182262660138612997569981864822445388033664682759440294353364274905286501959168) * r2 + ((1742637258998668047351122649 : ℝ) / 232469656043344703611003804242787603303575578404302112) * r3 + ((-755254647783659834318285287048679316973665151975409021 : ℝ) / 2530749269824508878335125768120440475522378433995708854549793695809914545168553273664) * r4 + ((193626362110963116372346961 : ℝ) / 21670032977999286607657937018895870934257126135591091286004) * r5 + ((8307801125620258177501138157535472486710316671729499231 : ℝ) / 658425999135662472070315791622612016671254232233092922) * (value_325 h H) + ((17810752454321079322337937150397659561556916095324389799 : ℝ) / 3621342995246143596386736853924366091691898277282011071) * (value_324 h H) + ((-236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (value_326 h H) + ((-8307801125620258177501138157535472486710316671729499231 : ℝ) / 658425999135662472070315791622612016671254232233092922) * (value_333 h H) + ((-14189409459074935725951200296473293469865017818042378728 : ℝ) / 3621342995246143596386736853924366091691898277282011071) * (value_332 h H) + ((236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (value_334 h H)

/-- Coordinate 119.1, recovered from nonplanar cycle 29. -/
theorem value_477 (h : Assignment) (H : Constraints h) :
    h 119 1 = ((9599590205553679886220594602 : ℝ) / 24441996955307478186442031817) * (h 1 1) + ((1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (h 1 2) + ((14842406749753798300221437215 : ℝ) / 24441996955307478186442031817) * (h 5 1) + ((-1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-319690867908925903845740680165480539666482551981502263 : ℝ) / 4953843944782962250872480501225511820587500404897429356252507703638333411049761632) * r0 + ((7889837087867802562725201 : ℝ) / 3155076635455615830106308099575725920720629147816838758) * r1 + ((413751724928306256998642936111567970619518870871944109 : ℝ) / 4740323237162658999652854552117492198290523526108491470621909182129326643137024) * r2 + ((-7889837087867802562725201 : ℝ) / 3019086442121359787155893561594644198747734784471456) * r3 + ((37613793175300568818058448737415270056319897351994919 : ℝ) / 361535609974929839762160824017205782217482633427958407792827670829987792166936181952) * r4 + ((-876648565318644729191689 : ℝ) / 281428999714276449450103078167478843302040599163520666052) * r5 + ((-319690867908925903845740680165480539666482551981502263 : ℝ) / 94060857019380353152902255946087430953036318890441846) * (value_325 h H) + ((-64242933190513867602281216569287171714679266512866472 : ℝ) / 47030428509690176576451127973043715476518159445220923) * (value_324 h H) + ((1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (value_326 h H) + ((413751724928306256998642936111567970619518870871944109 : ℝ) / 94060857019380353152902255946087430953036318890441846) * (value_333 h H) + ((64242933190513867602281216569287171714679266512866472 : ℝ) / 47030428509690176576451127973043715476518159445220923) * (value_332 h H) + ((-1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (value_334 h H)

/-- Coordinate 119.2, recovered from nonplanar cycle 29. -/
theorem value_478 (h : Assignment) (H : Constraints h) :
    h 119 2 = ((-66893936986311160142107637049 : ℝ) / 10037513416312937708565527732848) * (h 1 1) + ((602870056514230939827016065041 : ℝ) / 1254689177039117213570690966606) * (h 1 2) + ((66893936986311160142107637049 : ℝ) / 10037513416312937708565527732848) * (h 5 1) + ((651819120524886273743674901565 : ℝ) / 1254689177039117213570690966606) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1035821539113473817710577674790054641229769553393736508745 : ℝ) / 3144039623622253375220400958111124835466200256974901831434924889242462271546248715776) * r0 + ((602870056514230939827016065041 : ℝ) / 66079925052982417945746516837514003683572856871875870947552) * r1 + ((-1035821539113473817710577674790054641229769553393736508745 : ℝ) / 3008525147852567578446345022410568381848385597903522586688038360924745976177631232) * r2 + ((651819120524886273743674901565 : ℝ) / 63231746443789759382193034754038228098572557325970174464) * r3 + ((-94165594464861256155507061344550421929979050308521500795 : ℝ) / 229454600464088804969051402976253269780695644682277602812514628420098918761948830145536) * r4 + ((24141448908329121249765737095 : ℝ) / 1964749656671935319094319623046558964705979436293592276597696) * r5 + ((1035821539113473817710577674790054641229769553393736508745 : ℝ) / 59697290588300064134375298440450156178193717055800424928) * (value_325 h H) + ((221142991430132451438945588146152216366716230734657387195 : ℝ) / 41041887279456294092383017677809482372508180475862792138) * (value_324 h H) + ((602870056514230939827016065041 : ℝ) / 1254689177039117213570690966606) * (value_326 h H) + ((-1035821539113473817710577674790054641229769553393736508745 : ℝ) / 59697290588300064134375298440450156178193717055800424928) * (value_333 h H) + ((-221142991430132451438945588146152216366716230734657387195 : ℝ) / 41041887279456294092383017677809482372508180475862792138) * (value_332 h H) + ((651819120524886273743674901565 : ℝ) / 1254689177039117213570690966606) * (value_334 h H)

/-- Coordinate 119.3, recovered from nonplanar cycle 29. -/
theorem value_479 (h : Assignment) (H : Constraints h) :
    h 119 3 = ((148866993062121542009973162791 : ℝ) / 627344588519558606785345483303) * (h 1 1) + ((-88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (h 1 2) + h 1 3 + ((-148866993062121542009973162791 : ℝ) / 627344588519558606785345483303) * (h 5 1) + ((88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 244 3
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 3 - h 81 3) - ((19650205671972399073020144 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((60778450799116207976748495549731919437712209571467 : ℝ) / 679939364970210505021713009972129073413970643809451088113089292656241840732320224) * r0 + ((-650190628852027910504343 : ℝ) / 242940900930082418918185723667330895895488444381896584366) * r1 + ((1 : ℝ) / 52666370494181967653278373392) * r2 + ((-60778450799116207976748495549731919437712209571467 : ℝ) / 650632601179188490148431016957302850745758131034498829301046358331476205920768) * r3 + ((650190628852027910504343 : ℝ) / 232469656043344703611003804242787603303575578404302112) * r4 + ((-5525313709010564361522590504521083585246564506497 : ℝ) / 49622534702441350555590701335694911284752518313641350089211641094312049905265750464) * r5 + ((24081134401926959648309 : ℝ) / 7223344325999762202552645672965290311419042045197030428668) * r6 + ((1033233663584975535604724424345442630441107562714939 : ℝ) / 219475333045220824023438597207537338890418077411030974) * (value_325 h H) + ((1764723938118188568964017838674059510805148142916232 : ℝ) / 1207114331748714532128912284641455363897299425760670357) * (value_324 h H) + ((-88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (value_326 h H) + (1 : ℝ) * (value_327 h H) + ((-1033233663584975535604724424345442630441107562714939 : ℝ) / 219475333045220824023438597207537338890418077411030974) * (value_333 h H) + ((-1764723938118188568964017838674059510805148142916232 : ℝ) / 1207114331748714532128912284641455363897299425760670357) * (value_332 h H) + ((88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (value_334 h H)

/-- Coordinate 123.0, recovered from nonplanar cycle 29. -/
theorem value_492 (h : Assignment) (H : Constraints h) :
    h 123 0 = ((1076063047865449966450768109 : ℝ) / 1825689846984872190465565290) * (h 1 1) + ((-113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (h 1 2) + h 3 0 + ((-1076063047865449966450768109 : ℝ) / 1825689846984872190465565290) * (h 5 1) + ((113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((896860661423113653189197169762995261378162286519733 : ℝ) / 2102422367272560373473862433722620813909766763538007666910729221866989229572340) * r0 + ((-416881515892137435592092 : ℝ) / 58916947235766951037602197124225294728851675146430615) * r1 + ((-77448825578503030707864758939 : ℝ) / 173730258161248286645169343953621918336723850239839040) * r2 + ((9 : ℝ) / 1217126564656581460310376860) * r3 + ((-81532787402101241199017924523908660125287480592703 : ℝ) / 153436515451259860225183521658314698379270771882245759524033668914999717106963240) * r4 + ((23160084216229857532894 : ℝ) / 2627660028991069324866845471808426440334873282269193405) * r5 + ((3587442645692454612756788679051981045512649146078932 : ℝ) / 159678546104088498754751235251490733765371185882205) * (value_325 h H) + ((14657291289595107383397781078957064823593701677209336 : ℝ) / 1756464007144973486302263587766398071419083044704255) * (value_324 h H) + ((-113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (value_326 h H) + ((-3587442645692454612756788679051981045512649146078932 : ℝ) / 159678546104088498754751235251490733765371185882205) * (value_333 h H) + ((-12900827282450133897095517491190666752174618632505081 : ℝ) / 1756464007144973486302263587766398071419083044704255) * (value_332 h H) + ((113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (value_334 h H)

/-- Coordinate 123.1, recovered from nonplanar cycle 29. -/
theorem value_493 (h : Assignment) (H : Constraints h) :
    h 123 1 = ((65438079437624354349170147 : ℝ) / 165971804271352017315051390) * (h 1 1) + ((3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (h 1 2) + ((100533724833727662965881243 : ℝ) / 165971804271352017315051390) * (h 5 1) + ((-3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-4983176789702666426333095948333512990101188576852651 : ℝ) / 33638757876360965975581798939561933022556268216608122670571667549871827673157440) * r0 + ((52643079035300828282571 : ℝ) / 21424344449369800377309889863354652628673336416883860) * r1 + ((5621890974119020421352100889339475925162673320381471 : ℝ) / 32188859279374918679342498844407977442288152537559734790874326175408523054080) * r2 + ((-52643079035300828282571 : ℝ) / 20500911810368699235508582521545108919670535587520) * r3 + ((453016071791151493303008722575773908191017143350241 : ℝ) / 2454984247220157763602936346533035174068332350115932152384538702639995473711411840) * r4 + ((-531748273083846750329 : ℝ) / 173729588693624418173014576648491004319661043455814440) * r5 + ((-4983176789702666426333095948333512990101188576852651 : ℝ) / 638714184416353995019004941005962935061484743528820) * (value_325 h H) + ((-925448735896009583047709361687325207722837788649059 : ℝ) / 319357092208176997509502470502981467530742371764410) * (value_324 h H) + ((3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (value_326 h H) + ((5621890974119020421352100889339475925162673320381471 : ℝ) / 638714184416353995019004941005962935061484743528820) * (value_333 h H) + ((925448735896009583047709361687325207722837788649059 : ℝ) / 319357092208176997509502470502981467530742371764410) * (value_332 h H) + ((-3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (value_334 h H)

/-- Coordinate 123.2, recovered from nonplanar cycle 29. -/
theorem value_494 (h : Assignment) (H : Constraints h) :
    h 123 2 = ((86306860777438791550635177 : ℝ) / 9737012517252651682483014880) * (h 1 1) + ((556368780748240554606645741 : ℝ) / 1217126564656581460310376860) * (h 1 2) + ((-86306860777438791550635177 : ℝ) / 9737012517252651682483014880) * (h 5 1) + ((660757783908340905703731119 : ℝ) / 1217126564656581460310376860) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1595929950277588060212212248372888464448599385938371437 : ℝ) / 3049914047456727581786083103853615260711768318305803122131831191188379042366274560) * r0 + ((556368780748240554606645741 : ℝ) / 64101638592514442728911190471157120664990622559316509120) * r1 + ((1595929950277588060212212248372888464448599385938371437 : ℝ) / 2918456574663325960260386561892989954767459163405415954372605573237039423569920) * r2 + ((38868104935784759159043007 : ℝ) / 3608160478624891065449510523791939169862014263403520) * r3 + ((145084540934326187292019295306626224040781762358033767 : ℝ) / 222585238414627637233332895418995189115528799743844515149531509039359589616501340160) * r4 + ((-20606251138823724244690583 : ℝ) / 1905929407694855616970085248885045311389561420739254949760) * r5 + ((-1595929950277588060212212248372888464448599385938371437 : ℝ) / 57910086053749428881723114651207306112241283413279680) * (value_325 h H) + ((-3260262597800009783067154383141092993032411071889798663 : ℝ) / 318505473295621858849477130581640183617327058773038240) * (value_324 h H) + ((556368780748240554606645741 : ℝ) / 1217126564656581460310376860) * (value_326 h H) + ((1595929950277588060212212248372888464448599385938371437 : ℝ) / 57910086053749428881723114651207306112241283413279680) * (value_333 h H) + ((3260262597800009783067154383141092993032411071889798663 : ℝ) / 318505473295621858849477130581640183617327058773038240) * (value_332 h H) + ((660757783908340905703731119 : ℝ) / 1217126564656581460310376860) * (value_334 h H)

/-- Coordinate 123.3, recovered from nonplanar cycle 29. -/
theorem value_495 (h : Assignment) (H : Constraints h) :
    h 123 3 = ((14439774503848767519240428 : ℝ) / 60856328232829073015518843) * (h 1 1) + ((-6696008247861808220880 : ℝ) / 60856328232829073015518843) * (h 1 2) + h 1 3 + ((-14439774503848767519240428 : ℝ) / 60856328232829073015518843) * (h 5 1) + ((6696008247861808220880 : ℝ) / 60856328232829073015518843) * (h 9 2) := by
  have r0 := H 244 1
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 1 - h 81 1) - ((-18360527552033695208190734416 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 244 2
  change ((52666370494181967653278373392 : ℤ) : ℝ) * (h 119 2 - h 81 2) - ((72424346724987363749297211285 : ℤ) : ℝ) * (h 119 0 - h 81 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 251 1
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 1 - h 83 1) - ((-17500899163735564246828048 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 251 2
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 2 - h 83 2) - ((-61818753416471172734071749 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 251 3
  change ((50396343254516169991577344 : ℤ) : ℝ) * (h 123 3 - h 83 3) - ((14880018328581796046400 : ℤ) : ℝ) * (h 123 0 - h 83 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 359 1
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 1 - h 119 1) - ((18901839787907195230958830004784 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 359 2
  change ((-42279985912788644686643591694432 : ℤ) : ℝ) * (h 123 2 - h 119 2) - ((192790792006801728230070866606287 : ℤ) : ℝ) * (h 123 0 - h 119 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((4153834862079223328490739197137670646368941965 : ℝ) / 32979174388589182329001763666237189237800262957458943794678105441050811444272) * r0 + ((-24617677381844883165 : ℝ) / 11783389447153390207520439424845058945770335029286123) * r1 + ((-4153834862079223328490739197137670646368941965 : ℝ) / 31557705175857763411120096906282330825772698566235034108700319779812277504) * r2 + ((24617677381844883165 : ℝ) / 11275501495702784579529720386849809905818794573136) * r3 + ((1 : ℝ) / 50396343254516169991577344) * r4 + ((-377621351098111211680976290648879149669903815 : ℝ) / 2406847301196233101571506222091210954968953284427384463122096767294113209520992) * r5 + ((911765828957217895 : ℝ) / 350354670532142576648912729574456858711316437635892454) * r6 + ((70615192655346796584342566351340400988272013405 : ℝ) / 10645236406939233250316749016766048917691412392147) * (value_325 h H) + ((288514005781550871102670742110296533411620086190 : ℝ) / 117097600476331565753484239184426538094605536313617) * (value_324 h H) + ((-6696008247861808220880 : ℝ) / 60856328232829073015518843) * (value_326 h H) + ((-70615192655346796584342566351340400988272013405 : ℝ) / 10645236406939233250316749016766048917691412392147) * (value_333 h H) + ((-288514005781550871102670742110296533411620086190 : ℝ) / 117097600476331565753484239184426538094605536313617) * (value_332 h H) + ((6696008247861808220880 : ℝ) / 60856328232829073015518843) * (value_334 h H) + (1 : ℝ) * (value_335 h H)

/-- Coordinate 84.0, recovered from skew spokes on cycle 30. -/
theorem value_336 (h : Assignment) (H : Constraints h) :
    h 84 0 = ((-48908546472523 : ℝ) / 617857941263449) * (h 1 0) + ((-306483803023377 : ℝ) / 617857941263449) * (h 1 1) + ((814601591351640 : ℝ) / 617857941263449) * (h 1 2) + ((666766487735972 : ℝ) / 617857941263449) * (h 3 0) + ((306483803023377 : ℝ) / 617857941263449) * (h 5 1) + ((-814601591351640 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-765693044879117 : ℝ) / 1249942525918781739173858642) * r0 + ((-270 : ℝ) / 617857941263449) * r1 + ((-1155064394158169283660073522 : ℝ) / 3460514175864949993349945012017032335767) * r2 + ((-814601591351640 : ℝ) / 3421127163973022380771586023) * r3 + ((2690866844741470855 : ℝ) / 4492863411943920535063911238888752) * r4 + ((5 : ℝ) / 159407348845969842) * r5 + ((-166691621933993 : ℝ) / 80621292921761422176713882409) * r6 + ((2029615198001637555044463996715 : ℝ) / 80621292921761422176713882409) * r7 + ((814601591351640 : ℝ) / 617857941263449) * r8 + ((-666766487735972 : ℝ) / 617857941263449) * r9 + ((-1880611891155233717452314512377 : ℝ) / 80621292921761422176713882409) * r10 + ((1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_305 h H) + ((-48908546472523 : ℝ) / 617857941263449) * (value_304 h H) + ((814601591351640 : ℝ) / 617857941263449) * (value_306 h H) + ((-1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_329 h H) + ((666766487735972 : ℝ) / 617857941263449) * (value_328 h H) + ((-814601591351640 : ℝ) / 617857941263449) * (value_330 h H)

/-- Coordinate 84.1, recovered from skew spokes on cycle 30. -/
theorem value_337 (h : Assignment) (H : Constraints h) :
    h 84 1 = ((447088691072218 : ℝ) / 617857941263449) * (h 1 0) + ((434743100796814 : ℝ) / 617857941263449) * (h 1 1) + ((-546216952893660 : ℝ) / 617857941263449) * (h 1 2) + ((-447088691072218 : ℝ) / 617857941263449) * (h 3 0) + ((183114840466635 : ℝ) / 617857941263449) * (h 5 1) + ((546216952893660 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((49 : ℝ) / 617857941263449) * r0 + ((136554238223415 : ℝ) / 466025983502271918530776117) * r1 + ((765693044879117 : ℝ) / 3421127163973022380771586023) * r2 + ((546216952893660 : ℝ) / 3421127163973022380771586023) * r3 + ((-2690866844741470855 : ℝ) / 6700439570222569244777837593629408) * r4 + ((-5057564378645 : ℝ) / 240469407487172309961880476372) * r5 + ((221 : ℝ) / 159407348845969842) * r6 + ((-2690866844741470855 : ℝ) / 159407348845969842) * r7 + ((-546216952893660 : ℝ) / 617857941263449) * r8 + ((447088691072218 : ℝ) / 617857941263449) * r9 + ((2493318039162658669 : ℝ) / 159407348845969842) * r10 + ((-147835103615668 : ℝ) / 617857941263449) * (value_305 h H) + ((447088691072218 : ℝ) / 617857941263449) * (value_304 h H) + ((-546216952893660 : ℝ) / 617857941263449) * (value_306 h H) + ((765693044879117 : ℝ) / 617857941263449) * (value_329 h H) + ((-447088691072218 : ℝ) / 617857941263449) * (value_328 h H) + ((546216952893660 : ℝ) / 617857941263449) * (value_330 h H)

/-- Coordinate 84.2, recovered from skew spokes on cycle 30. -/
theorem value_338 (h : Assignment) (H : Constraints h) :
    h 84 2 = ((-666766487735972 : ℝ) / 617857941263449) * (h 1 0) + ((-306483803023377 : ℝ) / 617857941263449) * (h 1 1) + ((1432459532615089 : ℝ) / 617857941263449) * (h 1 2) + ((666766487735972 : ℝ) / 617857941263449) * (h 3 0) + ((306483803023377 : ℝ) / 617857941263449) * (h 5 1) + ((-814601591351640 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-765693044879117 : ℝ) / 1249942525918781739173858642) * r0 + ((-1432459532615089 : ℝ) / 1864103934009087674123104468) * r1 + ((-1155064394158169283660073522 : ℝ) / 3460514175864949993349945012017032335767) * r2 + ((-814601591351640 : ℝ) / 3421127163973022380771586023) * r3 + ((2690866844741470855 : ℝ) / 4492863411943920535063911238888752) * r4 + ((5 : ℝ) / 159407348845969842) * r5 + ((-166691621933993 : ℝ) / 80621292921761422176713882409) * r6 + ((2029615198001637555044463996715 : ℝ) / 80621292921761422176713882409) * r7 + ((814601591351640 : ℝ) / 617857941263449) * r8 + ((-666766487735972 : ℝ) / 617857941263449) * r9 + ((-1880611891155233717452314512377 : ℝ) / 80621292921761422176713882409) * r10 + ((1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_305 h H) + ((-666766487735972 : ℝ) / 617857941263449) * (value_304 h H) + ((1432459532615089 : ℝ) / 617857941263449) * (value_306 h H) + ((-1155064394158169283660073522 : ℝ) / 624971262959390869586929321) * (value_329 h H) + ((666766487735972 : ℝ) / 617857941263449) * (value_328 h H) + ((-814601591351640 : ℝ) / 617857941263449) * (value_330 h H)

/-- Coordinate 84.3, recovered from skew spokes on cycle 30. -/
theorem value_339 (h : Assignment) (H : Constraints h) :
    h 84 3 = ((72046178738391 : ℝ) / 617857941263449) * (h 1 0) + ((160570216538298 : ℝ) / 617857941263449) * (h 1 1) + ((-88020218368170 : ℝ) / 617857941263449) * (h 1 2) + h 1 3 + ((-72046178738391 : ℝ) / 617857941263449) * (h 3 0) + ((-160570216538298 : ℝ) / 617857941263449) * (h 5 1) + ((88020218368170 : ℝ) / 617857941263449) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 227 3
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 3 - h 76 3) - ((326000808771 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((249616551900921741928335207 : ℝ) / 3771130261894548634543898837575537314344) * r0 + ((44010109184085 : ℝ) / 932051967004543837061552234) * r1 + ((-1 : ℝ) / 3017042930932) * r2 + ((249616551900921741928335207 : ℝ) / 6921028351729899986699890024034064671534) * r3 + ((88020218368170 : ℝ) / 3421127163973022380771586023) * r4 + ((-292408255893596129044708289735 : ℝ) / 4518387265549477235576041480038805184255892288) * r5 + ((-543334681285 : ℝ) / 160312938324781539974586984248) * r6 + ((24015392912797 : ℝ) / 107495057229015229568951843212) * r7 + ((-292408255893596129044708289735 : ℝ) / 107495057229015229568951843212) * r8 + ((-88020218368170 : ℝ) / 617857941263449) * r9 + ((72046178738391 : ℝ) / 617857941263449) * r10 + ((270941232430116859238871461933 : ℝ) / 107495057229015229568951843212) * r11 + ((-249616551900921741928335207 : ℝ) / 1249942525918781739173858642) * (value_305 h H) + ((72046178738391 : ℝ) / 617857941263449) * (value_304 h H) + ((-88020218368170 : ℝ) / 617857941263449) * (value_306 h H) + (1 : ℝ) * (value_307 h H) + ((249616551900921741928335207 : ℝ) / 1249942525918781739173858642) * (value_329 h H) + ((-72046178738391 : ℝ) / 617857941263449) * (value_328 h H) + ((88020218368170 : ℝ) / 617857941263449) * (value_330 h H)

/-- Coordinate 88.0, recovered from skew spokes on cycle 30. -/
theorem value_352 (h : Assignment) (H : Constraints h) :
    h 88 0 = ((119424129235175 : ℝ) / 2542109602773571) * (h 1 0) + ((-1091004794628483 : ℝ) / 2542109602773571) * (h 1 1) + ((2769645410595576 : ℝ) / 2542109602773571) * (h 1 2) + ((2422685473538396 : ℝ) / 2542109602773571) * (h 3 0) + ((1091004794628483 : ℝ) / 2542109602773571) * (h 5 1) + ((-2769645410595576 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((-2889069539830751 : ℝ) / 5142753189439601353297116518) * r0 + ((-918 : ℝ) / 2542109602773571) * r1 + ((-4358223416058666756131344966 : ℝ) / 14237910900702328362570367753411156346893) * r2 + ((-2769645410595576 : ℝ) / 14075857304773336065930555517) * r3 + ((9804811549636582225 : ℝ) / 18485400058300311721966940250824208) * r4 + ((17 : ℝ) / 655864277515581318) * r5 + ((-605671368384599 : ℝ) / 331707580718854287287664015411) * r6 + ((7395384343737869708890303470925 : ℝ) / 331707580718854287287664015411) * r7 + ((2769645410595576 : ℝ) / 2542109602773571) * r8 + ((-2422685473538396 : ℝ) / 2542109602773571) * r9 + ((-6833173523066301697349359970311 : ℝ) / 331707580718854287287664015411) * r10 + ((4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((119424129235175 : ℝ) / 2542109602773571) * (value_304 h H) + ((2769645410595576 : ℝ) / 2542109602773571) * (value_306 h H) + ((-4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((2422685473538396 : ℝ) / 2542109602773571) * (value_328 h H) + ((-2769645410595576 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 88.1, recovered from skew spokes on cycle 30. -/
theorem value_353 (h : Assignment) (H : Constraints h) :
    h 88 1 = ((1624489678420774 : ℝ) / 2542109602773571) * (h 1 0) + ((1674719823442006 : ℝ) / 2542109602773571) * (h 1 1) + ((-1857137639838444 : ℝ) / 2542109602773571) * (h 1 2) + ((-1624489678420774 : ℝ) / 2542109602773571) * (h 3 0) + ((867389779331565 : ℝ) / 2542109602773571) * (h 5 1) + ((1857137639838444 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((115 : ℝ) / 2542109602773571) * r0 + ((464284409959611 : ℝ) / 1917413451675589231546999543) * r1 + ((2889069539830751 : ℝ) / 14075857304773336065930555517) * r2 + ((1857137639838444 : ℝ) / 14075857304773336065930555517) * r3 + ((-9148947272121000907 : ℝ) / 27568233143424127067478007157334432) * r4 + ((-17195718887393 : ℝ) / 989385341064604043478251764188) * r5 + ((803 : ℝ) / 655864277515581318) * r6 + ((-9804811549636582225 : ℝ) / 655864277515581318) * r7 + ((-1857137639838444 : ℝ) / 2542109602773571) * r8 + ((1624489678420774 : ℝ) / 2542109602773571) * r9 + ((9059431608360248467 : ℝ) / 655864277515581318) * r10 + ((-346959937057180 : ℝ) / 2542109602773571) * (value_305 h H) + ((1624489678420774 : ℝ) / 2542109602773571) * (value_304 h H) + ((-1857137639838444 : ℝ) / 2542109602773571) * (value_306 h H) + ((2889069539830751 : ℝ) / 2542109602773571) * (value_329 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (value_328 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 88.2, recovered from skew spokes on cycle 30. -/
theorem value_354 (h : Assignment) (H : Constraints h) :
    h 88 2 = ((1362128995946455 : ℝ) / 2542109602773571) * (h 1 0) + ((1830920974610259 : ℝ) / 5084219205547142) * (h 1 1) + ((-1557203509687230 : ℝ) / 2542109602773571) * (h 1 2) + ((-1362128995946455 : ℝ) / 2542109602773571) * (h 3 0) + ((-1830920974610259 : ℝ) / 5084219205547142) * (h 5 1) + ((4099313112460801 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((195074513740775 : ℝ) / 5142753189439601353297116518) * r0 + ((778601754843615 : ℝ) / 3834826903351178463093999086) * r1 + ((294274091343301256638576150 : ℝ) / 14237910900702328362570367753411156346893) * r2 + ((4099313112460801 : ℝ) / 14075857304773336065930555517) * r3 + ((-15519360350860818647921893372895 : ℝ) / 55771245571344936151892373302354791733017601856) * r4 + ((-28837102031245 : ℝ) / 1978770682129208086956503528376) * r5 + ((1362128995946455 : ℝ) / 1326830322875417149150656061644) * r6 + ((-15519360350860818647921893372895 : ℝ) / 1326830322875417149150656061644) * r7 + ((-4099313112460801 : ℝ) / 2542109602773571) * r8 + ((1362128995946455 : ℝ) / 2542109602773571) * r9 + ((15367514919727675199496388079495 : ℝ) / 1326830322875417149150656061644) * r10 + ((-294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((1362128995946455 : ℝ) / 2542109602773571) * (value_304 h H) + ((-1557203509687230 : ℝ) / 2542109602773571) * (value_306 h H) + ((294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((-1362128995946455 : ℝ) / 2542109602773571) * (value_328 h H) + ((4099313112460801 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 88.3, recovered from skew spokes on cycle 30. -/
theorem value_355 (h : Assignment) (H : Constraints h) :
    h 88 3 = ((261778649443113 : ℝ) / 2542109602773571) * (h 1 0) + ((642280866153192 : ℝ) / 2542109602773571) * (h 1 1) + ((-299268742451778 : ℝ) / 2542109602773571) * (h 1 2) + h 1 3 + ((-261778649443113 : ℝ) / 2542109602773571) * (h 3 0) + ((-642280866153192 : ℝ) / 2542109602773571) * (h 5 1) + ((299268742451778 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 227 3
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 3 - h 76 3) - ((326000808771 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 254 3
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 3 - h 84 3) - ((-4541843267797572 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  linear_combination ((941839006580485624456317021 : ℝ) / 15515907155726745897541206041291030334776) * r0 + ((149634371225889 : ℝ) / 3834826903351178463093999086) * r1 + ((-1 : ℝ) / 3017042930932) * r2 + ((941839006580485624456317021 : ℝ) / 28475821801404656725140735506822312693786) * r3 + ((299268742451778 : ℝ) / 14075857304773336065930555517) * r4 + ((-1065458831676255872159414231825 : ℝ) / 18590415190448312050630791100784930577672533952) * r5 + ((-1847337916369 : ℝ) / 659590227376402695652167842792) * r6 + ((1 : ℝ) / 42033442113744624) * r7 + ((87259549814371 : ℝ) / 442276774291805716383552020548) * r8 + ((-1065458831676255872159414231825 : ℝ) / 442276774291805716383552020548) * r9 + ((-299268742451778 : ℝ) / 2542109602773571) * r10 + ((261778649443113 : ℝ) / 2542109602773571) * r11 + ((984460677110334108456170968019 : ℝ) / 442276774291805716383552020548) * r12 + ((-941839006580485624456317021 : ℝ) / 5142753189439601353297116518) * (value_305 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (value_304 h H) + ((-299268742451778 : ℝ) / 2542109602773571) * (value_306 h H) + (1 : ℝ) * (value_307 h H) + ((941839006580485624456317021 : ℝ) / 5142753189439601353297116518) * (value_329 h H) + ((-261778649443113 : ℝ) / 2542109602773571) * (value_328 h H) + ((299268742451778 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 92.0, recovered from skew spokes on cycle 30. -/
theorem value_368 (h : Assignment) (H : Constraints h) :
    h 92 0 = ((4446273049517981 : ℝ) / 2542109602773571) * (h 1 0) + ((1202812302276942 : ℝ) / 2542109602773571) * (h 1 1) + ((-5083036935812586 : ℝ) / 2542109602773571) * (h 1 2) + ((-1904163446744410 : ℝ) / 2542109602773571) * (h 3 0) + ((-1202812302276942 : ℝ) / 2542109602773571) * (h 5 1) + ((5083036935812586 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((636763886294605 : ℝ) / 5142753189439601353297116518) * r0 + ((2541518467906293 : ℝ) / 3834826903351178463093999086) * r1 + ((173479968528590 : ℝ) / 2571376594719800676648558259) * r2 + ((918 : ℝ) / 2542109602773571) * r3 + ((-50658428004349509659600452819189 : ℝ) / 55771245571344936151892373302354791733017601856) * r4 + ((-94130313626159 : ℝ) / 1978770682129208086956503528376) * r5 + ((4446273049517981 : ℝ) / 1326830322875417149150656061644) * r6 + ((-50658428004349509659600452819189 : ℝ) / 1326830322875417149150656061644) * r7 + ((-5083036935812586 : ℝ) / 2542109602773571) * r8 + ((1904163446744410 : ℝ) / 2542109602773571) * r9 + ((50162772857040484789160293579309 : ℝ) / 1326830322875417149150656061644) * r10 + ((-960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((4446273049517981 : ℝ) / 2542109602773571) * (value_304 h H) + ((-5083036935812586 : ℝ) / 2542109602773571) * (value_306 h H) + ((960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((-1904163446744410 : ℝ) / 2542109602773571) * (value_328 h H) + ((5083036935812586 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 92.1, recovered from skew spokes on cycle 30. -/
theorem value_369 (h : Assignment) (H : Constraints h) :
    h 92 1 = ((1624489678420774 : ℝ) / 2542109602773571) * (h 1 0) + ((1674719823442006 : ℝ) / 2542109602773571) * (h 1 1) + ((-1857137639838444 : ℝ) / 2542109602773571) * (h 1 2) + ((-1624489678420774 : ℝ) / 2542109602773571) * (h 3 0) + ((867389779331565 : ℝ) / 2542109602773571) * (h 5 1) + ((1857137639838444 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((115 : ℝ) / 2542109602773571) * r0 + ((464284409959611 : ℝ) / 1917413451675589231546999543) * r1 + ((2889069539830751 : ℝ) / 14075857304773336065930555517) * r2 + ((1857137639838444 : ℝ) / 14075857304773336065930555517) * r3 + ((-9148947272121000907 : ℝ) / 27568233143424127067478007157334432) * r4 + ((-17195718887393 : ℝ) / 989385341064604043478251764188) * r5 + ((803 : ℝ) / 655864277515581318) * r6 + ((-9148947272121000907 : ℝ) / 655864277515581318) * r7 + ((-1857137639838444 : ℝ) / 2542109602773571) * r8 + ((1624489678420774 : ℝ) / 2542109602773571) * r9 + ((8403567330844667149 : ℝ) / 655864277515581318) * r10 + ((-346959937057180 : ℝ) / 2542109602773571) * (value_305 h H) + ((1624489678420774 : ℝ) / 2542109602773571) * (value_304 h H) + ((-1857137639838444 : ℝ) / 2542109602773571) * (value_306 h H) + ((2889069539830751 : ℝ) / 2542109602773571) * (value_329 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (value_328 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 92.2, recovered from skew spokes on cycle 30. -/
theorem value_370 (h : Assignment) (H : Constraints h) :
    h 92 2 = ((-2422685473538396 : ℝ) / 2542109602773571) * (h 1 0) + ((-1091004794628483 : ℝ) / 2542109602773571) * (h 1 1) + ((5311755013369147 : ℝ) / 2542109602773571) * (h 1 2) + ((2422685473538396 : ℝ) / 2542109602773571) * (h 3 0) + ((1091004794628483 : ℝ) / 2542109602773571) * (h 5 1) + ((-2769645410595576 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 255 2
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 2 - h 84 2) - ((778397076180456 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((-2889069539830751 : ℝ) / 5142753189439601353297116518) * r0 + ((-5311755013369147 : ℝ) / 7669653806702356926187998172) * r1 + ((-4358223416058666756131344966 : ℝ) / 14237910900702328362570367753411156346893) * r2 + ((-2769645410595576 : ℝ) / 14075857304773336065930555517) * r3 + ((9148947272121000907 : ℝ) / 18485400058300311721966940250824208) * r4 + ((17 : ℝ) / 655864277515581318) * r5 + ((-6338480852533999675610234088217 : ℝ) / 3742318980693769662822443318418892976900220579) * r6 + ((1 : ℝ) / 11281982077659089) * r7 + ((6900691673205567687151177588831 : ℝ) / 331707580718854287287664015411) * r8 + ((2769645410595576 : ℝ) / 2542109602773571) * r9 + ((-2422685473538396 : ℝ) / 2542109602773571) * r10 + ((-6338480852533999675610234088217 : ℝ) / 331707580718854287287664015411) * r11 + ((4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((-2422685473538396 : ℝ) / 2542109602773571) * (value_304 h H) + ((5311755013369147 : ℝ) / 2542109602773571) * (value_306 h H) + ((-4358223416058666756131344966 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((2422685473538396 : ℝ) / 2542109602773571) * (value_328 h H) + ((-2769645410595576 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 92.3, recovered from skew spokes on cycle 30. -/
theorem value_371 (h : Assignment) (H : Constraints h) :
    h 92 3 = ((261778649443113 : ℝ) / 2542109602773571) * (h 1 0) + ((642280866153192 : ℝ) / 2542109602773571) * (h 1 1) + ((-299268742451778 : ℝ) / 2542109602773571) * (h 1 2) + h 1 3 + ((-261778649443113 : ℝ) / 2542109602773571) * (h 3 0) + ((-642280866153192 : ℝ) / 2542109602773571) * (h 5 1) + ((299268742451778 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 246 3
  change ((5537077272127 : ℤ) : ℝ) * (h 96 3 - h 82 3) - ((326000808771 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  have r12 := H 274 3
  change ((1 : ℤ) : ℝ) * (h 96 3 - h 92 3) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r12
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r12
  linear_combination ((37490093008665 : ℝ) / 5142753189439601353297116518) * r0 + ((149634371225889 : ℝ) / 3834826903351178463093999086) * r1 + ((56554610045887966836262890 : ℝ) / 14237910900702328362570367753411156346893) * r2 + ((299268742451778 : ℝ) / 14075857304773336065930555517) * r3 + ((1 : ℝ) / 5537077272127) * r4 + ((-994188070038226838752008185099 : ℝ) / 18590415190448312050630791100784930577672533952) * r5 + ((-1847337916369 : ℝ) / 659590227376402695652167842792) * r6 + ((87259549814371 : ℝ) / 442276774291805716383552020548) * r7 + ((-994188070038226838752008185099 : ℝ) / 442276774291805716383552020548) * r8 + ((-299268742451778 : ℝ) / 2542109602773571) * r9 + ((261778649443113 : ℝ) / 2542109602773571) * r10 + ((984460677110334108456170968019 : ℝ) / 442276774291805716383552020548) * r11 + (-1 : ℝ) * r12 + ((-56554610045887966836262890 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (value_304 h H) + ((-299268742451778 : ℝ) / 2542109602773571) * (value_306 h H) + ((56554610045887966836262890 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((-261778649443113 : ℝ) / 2542109602773571) * (value_328 h H) + ((299268742451778 : ℝ) / 2542109602773571) * (value_330 h H) + (1 : ℝ) * (value_331 h H)

/-- Coordinate 96.0, recovered from skew spokes on cycle 30. -/
theorem value_384 (h : Assignment) (H : Constraints h) :
    h 96 0 = ((4446273049517981 : ℝ) / 2542109602773571) * (h 1 0) + ((1202812302276942 : ℝ) / 2542109602773571) * (h 1 1) + ((-5083036935812586 : ℝ) / 2542109602773571) * (h 1 2) + ((-1904163446744410 : ℝ) / 2542109602773571) * (h 3 0) + ((-1202812302276942 : ℝ) / 2542109602773571) * (h 5 1) + ((5083036935812586 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((636763886294605 : ℝ) / 5142753189439601353297116518) * r0 + ((2541518467906293 : ℝ) / 3834826903351178463093999086) * r1 + ((173479968528590 : ℝ) / 2571376594719800676648558259) * r2 + ((918 : ℝ) / 2542109602773571) * r3 + ((-50658428004349509659600452819189 : ℝ) / 55771245571344936151892373302354791733017601856) * r4 + ((-94130313626159 : ℝ) / 1978770682129208086956503528376) * r5 + ((4446273049517981 : ℝ) / 1326830322875417149150656061644) * r6 + ((-50658428004349509659600452819189 : ℝ) / 1326830322875417149150656061644) * r7 + ((-5083036935812586 : ℝ) / 2542109602773571) * r8 + ((4446273049517981 : ℝ) / 2542109602773571) * r9 + ((50162772857040484789160293579309 : ℝ) / 1326830322875417149150656061644) * r10 + ((-960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((4446273049517981 : ℝ) / 2542109602773571) * (value_304 h H) + ((-5083036935812586 : ℝ) / 2542109602773571) * (value_306 h H) + ((960571990908962927209610930 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((-1904163446744410 : ℝ) / 2542109602773571) * (value_328 h H) + ((5083036935812586 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 96.1, recovered from skew spokes on cycle 30. -/
theorem value_385 (h : Assignment) (H : Constraints h) :
    h 96 1 = ((1624489678420774 : ℝ) / 2542109602773571) * (h 1 0) + ((1674719823442006 : ℝ) / 2542109602773571) * (h 1 1) + ((-1857137639838444 : ℝ) / 2542109602773571) * (h 1 2) + ((-1624489678420774 : ℝ) / 2542109602773571) * (h 3 0) + ((867389779331565 : ℝ) / 2542109602773571) * (h 5 1) + ((1857137639838444 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((115 : ℝ) / 2542109602773571) * r0 + ((464284409959611 : ℝ) / 1917413451675589231546999543) * r1 + ((2889069539830751 : ℝ) / 14075857304773336065930555517) * r2 + ((1857137639838444 : ℝ) / 14075857304773336065930555517) * r3 + ((-9148947272121000907 : ℝ) / 27568233143424127067478007157334432) * r4 + ((-17195718887393 : ℝ) / 989385341064604043478251764188) * r5 + ((803 : ℝ) / 655864277515581318) * r6 + ((-9148947272121000907 : ℝ) / 655864277515581318) * r7 + ((-1857137639838444 : ℝ) / 2542109602773571) * r8 + ((1624489678420774 : ℝ) / 2542109602773571) * r9 + ((9059431608360248467 : ℝ) / 655864277515581318) * r10 + ((-346959937057180 : ℝ) / 2542109602773571) * (value_305 h H) + ((1624489678420774 : ℝ) / 2542109602773571) * (value_304 h H) + ((-1857137639838444 : ℝ) / 2542109602773571) * (value_306 h H) + ((2889069539830751 : ℝ) / 2542109602773571) * (value_329 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (value_328 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 96.2, recovered from skew spokes on cycle 30. -/
theorem value_386 (h : Assignment) (H : Constraints h) :
    h 96 2 = ((1362128995946455 : ℝ) / 2542109602773571) * (h 1 0) + ((1830920974610259 : ℝ) / 5084219205547142) * (h 1 1) + ((-1557203509687230 : ℝ) / 2542109602773571) * (h 1 2) + ((-1362128995946455 : ℝ) / 2542109602773571) * (h 3 0) + ((-1830920974610259 : ℝ) / 5084219205547142) * (h 5 1) + ((4099313112460801 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  linear_combination ((195074513740775 : ℝ) / 5142753189439601353297116518) * r0 + ((778601754843615 : ℝ) / 3834826903351178463093999086) * r1 + ((294274091343301256638576150 : ℝ) / 14237910900702328362570367753411156346893) * r2 + ((4099313112460801 : ℝ) / 14075857304773336065930555517) * r3 + ((-15519360350860818647921893372895 : ℝ) / 55771245571344936151892373302354791733017601856) * r4 + ((-28837102031245 : ℝ) / 1978770682129208086956503528376) * r5 + ((1362128995946455 : ℝ) / 1326830322875417149150656061644) * r6 + ((-15519360350860818647921893372895 : ℝ) / 1326830322875417149150656061644) * r7 + ((-1557203509687230 : ℝ) / 2542109602773571) * r8 + ((1362128995946455 : ℝ) / 2542109602773571) * r9 + ((15367514919727675199496388079495 : ℝ) / 1326830322875417149150656061644) * r10 + ((-294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((1362128995946455 : ℝ) / 2542109602773571) * (value_304 h H) + ((-1557203509687230 : ℝ) / 2542109602773571) * (value_306 h H) + ((294274091343301256638576150 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((-1362128995946455 : ℝ) / 2542109602773571) * (value_328 h H) + ((4099313112460801 : ℝ) / 2542109602773571) * (value_330 h H)

/-- Coordinate 96.3, recovered from skew spokes on cycle 30. -/
theorem value_387 (h : Assignment) (H : Constraints h) :
    h 96 3 = ((261778649443113 : ℝ) / 2542109602773571) * (h 1 0) + ((642280866153192 : ℝ) / 2542109602773571) * (h 1 1) + ((-299268742451778 : ℝ) / 2542109602773571) * (h 1 2) + h 1 3 + ((-261778649443113 : ℝ) / 2542109602773571) * (h 3 0) + ((-642280866153192 : ℝ) / 2542109602773571) * (h 5 1) + ((299268742451778 : ℝ) / 2542109602773571) * (h 9 2) := by
  have r0 := H 227 1
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 1 - h 76 1) - ((2023025751458 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 227 2
  change ((-3017042930932 : ℤ) : ℝ) * (h 84 2 - h 76 2) - ((-3017042930932 : ℤ) : ℝ) * (h 84 0 - h 76 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 246 1
  change ((5537077272127 : ℤ) : ℝ) * (h 96 1 - h 82 1) - ((2023025751458 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 246 2
  change ((5537077272127 : ℤ) : ℝ) * (h 96 2 - h 82 2) - ((1696300119485 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 246 3
  change ((5537077272127 : ℤ) : ℝ) * (h 96 3 - h 82 3) - ((326000808771 : ℤ) : ℝ) * (h 96 0 - h 82 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 254 1
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 1 - h 84 1) - ((-28184794769312856 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 254 2
  change ((42033442113744624 : ℤ) : ℝ) * (h 88 2 - h 84 2) - ((538173368948294171 : ℤ) : ℝ) * (h 88 0 - h 84 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 255 1
  change ((11281982077659089 : ℤ) : ℝ) * (h 92 1 - h 84 1) - ((-521940643876164 : ℤ) : ℝ) * (h 92 0 - h 84 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 266 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 88 1) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 266 2
  change ((1 : ℤ) : ℝ) * (h 96 2 - h 88 2) - ((0 : ℤ) : ℝ) * (h 96 0 - h 88 0) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  have r10 := H 274 0
  change ((1 : ℤ) : ℝ) * (h 96 0 - h 92 0) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r10
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r10
  have r11 := H 274 1
  change ((1 : ℤ) : ℝ) * (h 96 1 - h 92 1) - ((0 : ℤ) : ℝ) * (h 96 2 - h 92 2) = 0 at r11
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r11
  linear_combination ((37490093008665 : ℝ) / 5142753189439601353297116518) * r0 + ((149634371225889 : ℝ) / 3834826903351178463093999086) * r1 + ((56554610045887966836262890 : ℝ) / 14237910900702328362570367753411156346893) * r2 + ((299268742451778 : ℝ) / 14075857304773336065930555517) * r3 + ((1 : ℝ) / 5537077272127) * r4 + ((-994188070038226838752008185099 : ℝ) / 18590415190448312050630791100784930577672533952) * r5 + ((-1847337916369 : ℝ) / 659590227376402695652167842792) * r6 + ((87259549814371 : ℝ) / 442276774291805716383552020548) * r7 + ((-994188070038226838752008185099 : ℝ) / 442276774291805716383552020548) * r8 + ((-299268742451778 : ℝ) / 2542109602773571) * r9 + ((261778649443113 : ℝ) / 2542109602773571) * r10 + ((984460677110334108456170968019 : ℝ) / 442276774291805716383552020548) * r11 + ((-56554610045887966836262890 : ℝ) / 2571376594719800676648558259) * (value_305 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (value_304 h H) + ((-299268742451778 : ℝ) / 2542109602773571) * (value_306 h H) + ((56554610045887966836262890 : ℝ) / 2571376594719800676648558259) * (value_329 h H) + ((-261778649443113 : ℝ) / 2542109602773571) * (value_328 h H) + ((299268742451778 : ℝ) / 2542109602773571) * (value_330 h H) + (1 : ℝ) * (value_331 h H)

/-- Coordinate 85.0, recovered from skew spokes on cycle 31. -/
theorem value_340 (h : Assignment) (H : Constraints h) :
    h 85 0 = ((26941969465273 : ℝ) / 13520913290240) * (h 1 0) + ((-1639676546271 : ℝ) / 1352091329024) * (h 1 2) + ((-13421056175033 : ℝ) / 13520913290240) * (h 3 0) + ((1639676546271 : ℝ) / 1352091329024) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 2
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 2 - h 85 2) - ((2502805068546721 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-14594466810637 : ℝ) / 1221820008425171448412160) * r0 + ((-3483 : ℝ) / 2714323343015680) * r1 + ((14594466810637 : ℝ) / 4255599089344872154819553280) * r2 + ((1 : ℝ) / 2714323343015680) * r3 + ((-886303886471556026869801 : ℝ) / 126953474987131004270920692886424719360) * r4 + ((-211518274468959 : ℝ) / 282032360133535178548423201280) * r5 + ((886303886471556026869801 : ℝ) / 1221820008425171448412160) * (value_353 h H) + ((-501676082838624031404156289 : ℝ) / 981121466765412673074964480) * (value_352 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_354 h H)

/-- Coordinate 85.1, recovered from skew spokes on cycle 31. -/
theorem value_341 (h : Assignment) (H : Constraints h) :
    h 85 1 = ((5304072280039 : ℝ) / 2704182658048) * (h 1 0) + h 1 1 + ((-3240044152965 : ℝ) / 1352091329024) * (h 1 2) + ((-5304072280039 : ℝ) / 2704182658048) * (h 3 0) + ((3240044152965 : ℝ) / 1352091329024) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 2
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 2 - h 85 2) - ((2502805068546721 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1743950861587 : ℝ) / 244364001685034289682432) * r0 + ((-83593139146497 : ℝ) / 32967498700286703942211328) * r1 + ((350271976707008620126583 : ℝ) / 51687451978748242450656020217551628288) * r2 + ((24000327059 : ℝ) / 32967498700286703942211328) * r3 + ((-350271976707008620126583 : ℝ) / 25390694997426200854184138577284943872) * r4 + ((-83593139146497 : ℝ) / 56406472026707035709684640256) * r5 + ((350271976707008620126583 : ℝ) / 244364001685034289682432) * (value_353 h H) + ((-198265037403909983955417887 : ℝ) / 196224293353082534614992896) * (value_352 h H) + ((83593139146497 : ℝ) / 542864668603136) * (value_354 h H)

/-- Coordinate 85.2, recovered from skew spokes on cycle 31. -/
theorem value_342 (h : Assignment) (H : Constraints h) :
    h 85 2 = ((13421056175033 : ℝ) / 13520913290240) * (h 1 0) + ((-287585217247 : ℝ) / 1352091329024) * (h 1 2) + ((-13421056175033 : ℝ) / 13520913290240) * (h 3 0) + ((1639676546271 : ℝ) / 1352091329024) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 2
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 2 - h 85 2) - ((2502805068546721 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-14594466810637 : ℝ) / 1221820008425171448412160) * r0 + ((2502805068546721 : ℝ) / 164837493501433519711056640) * r1 + ((14594466810637 : ℝ) / 4255599089344872154819553280) * r2 + ((1 : ℝ) / 2714323343015680) * r3 + ((-886303886471556026869801 : ℝ) / 126953474987131004270920692886424719360) * r4 + ((-211518274468959 : ℝ) / 282032360133535178548423201280) * r5 + ((886303886471556026869801 : ℝ) / 1221820008425171448412160) * (value_353 h H) + ((-501676082838624031404156289 : ℝ) / 981121466765412673074964480) * (value_352 h H) + ((211518274468959 : ℝ) / 2714323343015680) * (value_354 h H)

/-- Coordinate 85.3, recovered from skew spokes on cycle 31. -/
theorem value_343 (h : Assignment) (H : Constraints h) :
    h 85 3 = ((-6549652612581 : ℝ) / 6760456645120) * (h 1 0) + ((800183803347 : ℝ) / 676045664512) * (h 1 2) + h 1 3 + ((6549652612581 : ℝ) / 6760456645120) * (h 3 0) + ((-800183803347 : ℝ) / 676045664512) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 10 3
  change ((60728760973 : ℤ) : ℝ) * (h 85 3 - h 1 3) - ((-59272874322 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 257 2
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 2 - h 85 2) - ((2502805068546721 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((432527998531743536881557 : ℝ) / 37099807621840541523583132513315840) * r0 + ((103223710631763 : ℝ) / 82418746750716759855528320) * r1 + ((1 : ℝ) / 60728760973) * r2 + ((-144175999510581178960519 : ℝ) / 43072876648956868708880016847959690240) * r3 + ((-29636437161 : ℝ) / 82418746750716759855528320) * r4 + ((432527998531743536881557 : ℝ) / 63476737493565502135460346443212359680) * r5 + ((103223710631763 : ℝ) / 141016180066767589274211600640) * r6 + ((-432527998531743536881557 : ℝ) / 610910004212585724206080) * (value_353 h H) + ((244824552090462944186466573 : ℝ) / 490560733382706336537482240) * (value_352 h H) + ((-103223710631763 : ℝ) / 1357161671507840) * (value_354 h H)

/-- Coordinate 89.0, recovered from skew spokes on cycle 31. -/
theorem value_356 (h : Assignment) (H : Constraints h) :
    h 89 0 = ((89998332273229 : ℝ) / 41233137211910) * (h 1 0) + ((-27874501286607 : ℝ) / 20616568605955) * (h 1 2) + ((-48765195061319 : ℝ) / 41233137211910) * (h 3 0) + ((27874501286607 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-51952609268023 : ℝ) / 3726040613840655494575940) * r0 + ((51952609268023 : ℝ) / 12977799458007003087607999020) * r1 + ((-60728760973 : ℝ) / 7452081227681310989151880) * r2 + ((3155017590161433259266379 : ℝ) / 3726040613840655494575940) * (value_353 h H) + ((-501671491232855491419169 : ℝ) / 745208122768131098915188) * (value_352 h H)

/-- Coordinate 89.1, recovered from skew spokes on cycle 31. -/
theorem value_357 (h : Assignment) (H : Constraints h) :
    h 89 1 = ((19272262628377 : ℝ) / 8246627442382) * (h 1 0) + h 1 1 + ((-11016150120081 : ℝ) / 4123313721191) * (h 1 2) + ((-19272262628377 : ℝ) / 8246627442382) * (h 3 0) + ((11016150120081 : ℝ) / 4123313721191) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-8260855041253 : ℝ) / 745208122768131098915188) * r0 + ((8260855041253 : ℝ) / 2595559891601400617521599804) * r1 + ((-24000327059 : ℝ) / 1490416245536262197830376) * r2 + ((1246879614000986590334357 : ℝ) / 745208122768131098915188) * (value_353 h H) + ((-991316113885304685824635 : ℝ) / 745208122768131098915188) * (value_352 h H)

/-- Coordinate 89.2, recovered from skew spokes on cycle 31. -/
theorem value_358 (h : Assignment) (H : Constraints h) :
    h 89 2 = ((-103596562034867 : ℝ) / 82466274423820) * (h 1 0) + ((59216465721051 : ℝ) / 41233137211910) * (h 1 2) + ((103596562034867 : ℝ) / 82466274423820) * (h 3 0) + ((-17983328509141 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((87186713076679 : ℝ) / 7452081227681310989151880) * r0 + ((-87186713076679 : ℝ) / 25955598916014006175215998040) * r1 + ((5294741058455172411648667 : ℝ) / 774310128510592586627277757000748666480) * r2 + ((-1 : ℝ) / 103905218536046) * r3 + ((-5294741058455172411648667 : ℝ) / 7452081227681310989151880) * (value_353 h H) + ((2092509629039488145557061 : ℝ) / 1490416245536262197830376) * (value_352 h H) + (1 : ℝ) * (value_354 h H)

/-- Coordinate 89.3, recovered from skew spokes on cycle 31. -/
theorem value_359 (h : Assignment) (H : Constraints h) :
    h 89 3 = ((-23798059040283 : ℝ) / 20616568605955) * (h 1 0) + ((27206249313798 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((23798059040283 : ℝ) / 20616568605955) * (h 3 0) + ((-27206249313798 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 3
  change ((60728760973 : ℤ) : ℝ) * (h 85 3 - h 1 3) - ((-59272874322 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 3
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 3 - h 85 3) - ((206447421263526 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((1539690239921749846202703 : ℝ) / 113138914906809681519870679128394810) * r0 + ((1 : ℝ) / 60728760973) * r1 + ((-513230079973916615400901 : ℝ) / 131354280206806040244569858468066374410) * r2 + ((-1 : ℝ) / 211518274468959) * r3 + ((29636437161 : ℝ) / 3726040613840655494575940) * r4 + ((-1539690239921749846202703 : ℝ) / 1863020306920327747287970) * (value_353 h H) + ((244822311326224597202733 : ℝ) / 372604061384065549457594) * (value_352 h H)

/-- Coordinate 93.0, recovered from skew spokes on cycle 31. -/
theorem value_372 (h : Assignment) (H : Constraints h) :
    h 93 0 = ((-12483568010518 : ℝ) / 20616568605955) * (h 1 0) + ((14271376629708 : ℝ) / 20616568605955) * (h 1 2) + ((33100136616473 : ℝ) / 20616568605955) * (h 3 0) + ((-14271376629708 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 2
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 2 - h 85 2) - ((2502805068546721 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 258 1
  change ((107093752801523 : ℤ) : ℝ) * (h 93 1 - h 85 1) - ((-15480210953055 : ℤ) : ℝ) * (h 93 0 - h 85 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 268 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 89 1) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 279 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 93 1) - ((0 : ℤ) : ℝ) * (h 97 2 - h 93 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((28638388149451 : ℝ) / 1863020306920327747287970) * r0 + ((-918 : ℝ) / 48765195061319) * r1 + ((34519011692618457522173518715127317809 : ℝ) / 1220035180312832672851154072426683339253054737993530) * r2 + ((34 : ℝ) / 6290710162910151) * r3 + ((1 : ℝ) / 15480210953055) * r4 + ((1739173828580005580175823 : ℝ) / 193577532127648146656819439250187166620) * r5 + ((-459 : ℝ) / 41717945242222469) * r6 + ((-107093752801523 : ℝ) / 15480210953055) * r7 + ((107093752801523 : ℝ) / 15480210953055) * r8 + ((-1739173828580005580175823 : ℝ) / 1863020306920327747287970) * (value_353 h H) + ((509077070610451720161947717 : ℝ) / 299201061291404636214447982) * (value_352 h H) + ((918 : ℝ) / 803) * (value_354 h H)

/-- Coordinate 93.1, recovered from skew spokes on cycle 31. -/
theorem value_373 (h : Assignment) (H : Constraints h) :
    h 93 1 = ((19272262628377 : ℝ) / 8246627442382) * (h 1 0) + h 1 1 + ((-11016150120081 : ℝ) / 4123313721191) * (h 1 2) + ((-19272262628377 : ℝ) / 8246627442382) * (h 3 0) + ((11016150120081 : ℝ) / 4123313721191) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 268 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 89 1) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 279 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 93 1) - ((0 : ℤ) : ℝ) * (h 97 2 - h 93 2) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-8260855041253 : ℝ) / 745208122768131098915188) * r0 + ((8260855041253 : ℝ) / 2595559891601400617521599804) * r1 + ((-24000327059 : ℝ) / 1490416245536262197830376) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((1246879614000986590334357 : ℝ) / 745208122768131098915188) * (value_353 h H) + ((-991316113885304685824635 : ℝ) / 745208122768131098915188) * (value_352 h H)

/-- Coordinate 93.2, recovered from skew spokes on cycle 31. -/
theorem value_374 (h : Assignment) (H : Constraints h) :
    h 93 2 = ((48765195061319 : ℝ) / 41233137211910) * (h 1 0) + ((-7257932680652 : ℝ) / 20616568605955) * (h 1 2) + ((-48765195061319 : ℝ) / 41233137211910) * (h 3 0) + ((27874501286607 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 258 1
  change ((107093752801523 : ℤ) : ℝ) * (h 93 1 - h 85 1) - ((-15480210953055 : ℤ) : ℝ) * (h 93 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 258 2
  change ((107093752801523 : ℤ) : ℝ) * (h 93 2 - h 85 2) - ((-7834010165517 : ℤ) : ℝ) * (h 93 0 - h 85 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 268 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 89 1) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 279 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 93 1) - ((0 : ℤ) : ℝ) * (h 97 2 - h 93 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-51952609268023 : ℝ) / 3726040613840655494575940) * r0 + ((1 : ℝ) / 60728760973) * r1 + ((501671491232855491419169 : ℝ) / 311471431498281010415014806464551482180) * r2 + ((-60728760973 : ℝ) / 12851425466061247566554285) * r3 + ((1 : ℝ) / 107093752801523) * r4 + ((-60728760973 : ℝ) / 7452081227681310989151880) * r5 + ((60728760973 : ℝ) / 120001635295) * r6 + ((-60728760973 : ℝ) / 120001635295) * r7 + ((3155017590161433259266379 : ℝ) / 3726040613840655494575940) * (value_353 h H) + ((-501671491232855491419169 : ℝ) / 745208122768131098915188) * (value_352 h H)

/-- Coordinate 93.3, recovered from skew spokes on cycle 31. -/
theorem value_375 (h : Assignment) (H : Constraints h) :
    h 93 3 = ((-23798059040283 : ℝ) / 20616568605955) * (h 1 0) + ((27206249313798 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((23798059040283 : ℝ) / 20616568605955) * (h 3 0) + ((-27206249313798 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 3
  change ((60728760973 : ℤ) : ℝ) * (h 85 3 - h 1 3) - ((-59272874322 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 258 1
  change ((107093752801523 : ℤ) : ℝ) * (h 93 1 - h 85 1) - ((-15480210953055 : ℤ) : ℝ) * (h 93 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 258 3
  change ((107093752801523 : ℤ) : ℝ) * (h 93 3 - h 85 3) - ((7646200787538 : ℤ) : ℝ) * (h 93 0 - h 85 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 268 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 89 1) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 279 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 93 1) - ((0 : ℤ) : ℝ) * (h 97 2 - h 93 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((1539690239921749846202703 : ℝ) / 113138914906809681519870679128394810) * r0 + ((1 : ℝ) / 60728760973) * r1 + ((-81607437108741532400911 : ℝ) / 51911905249713501735835801077425247030) * r2 + ((59272874322 : ℝ) / 12851425466061247566554285) * r3 + ((1 : ℝ) / 107093752801523) * r4 + ((29636437161 : ℝ) / 3726040613840655494575940) * r5 + ((-59272874322 : ℝ) / 120001635295) * r6 + ((59272874322 : ℝ) / 120001635295) * r7 + ((-1539690239921749846202703 : ℝ) / 1863020306920327747287970) * (value_353 h H) + ((244822311326224597202733 : ℝ) / 372604061384065549457594) * (value_352 h H)

/-- Coordinate 97.0, recovered from skew spokes on cycle 31. -/
theorem value_388 (h : Assignment) (H : Constraints h) :
    h 97 0 = ((-12483568010518 : ℝ) / 20616568605955) * (h 1 0) + ((14271376629708 : ℝ) / 20616568605955) * (h 1 2) + ((33100136616473 : ℝ) / 20616568605955) * (h 3 0) + ((-14271376629708 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 2
  change ((60728760973 : ℤ) : ℝ) * (h 85 2 - h 1 2) - ((60728760973 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 2
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 2 - h 85 2) - ((2502805068546721 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 258 1
  change ((107093752801523 : ℤ) : ℝ) * (h 93 1 - h 85 1) - ((-15480210953055 : ℤ) : ℝ) * (h 93 0 - h 85 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 268 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 89 1) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 279 0
  change ((1 : ℤ) : ℝ) * (h 97 0 - h 93 0) - ((0 : ℤ) : ℝ) * (h 97 2 - h 93 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 279 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 93 1) - ((0 : ℤ) : ℝ) * (h 97 2 - h 93 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((28638388149451 : ℝ) / 1863020306920327747287970) * r0 + ((-918 : ℝ) / 48765195061319) * r1 + ((34519011692618457522173518715127317809 : ℝ) / 1220035180312832672851154072426683339253054737993530) * r2 + ((34 : ℝ) / 6290710162910151) * r3 + ((1 : ℝ) / 15480210953055) * r4 + ((1739173828580005580175823 : ℝ) / 193577532127648146656819439250187166620) * r5 + ((-459 : ℝ) / 41717945242222469) * r6 + ((-107093752801523 : ℝ) / 15480210953055) * r7 + (1 : ℝ) * r8 + ((107093752801523 : ℝ) / 15480210953055) * r9 + ((-1739173828580005580175823 : ℝ) / 1863020306920327747287970) * (value_353 h H) + ((509077070610451720161947717 : ℝ) / 299201061291404636214447982) * (value_352 h H) + ((918 : ℝ) / 803) * (value_354 h H)

/-- Coordinate 97.1, recovered from skew spokes on cycle 31. -/
theorem value_389 (h : Assignment) (H : Constraints h) :
    h 97 1 = ((19272262628377 : ℝ) / 8246627442382) * (h 1 0) + h 1 1 + ((-11016150120081 : ℝ) / 4123313721191) * (h 1 2) + ((-19272262628377 : ℝ) / 8246627442382) * (h 3 0) + ((11016150120081 : ℝ) / 4123313721191) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 268 1
  change ((1 : ℤ) : ℝ) * (h 97 1 - h 89 1) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-8260855041253 : ℝ) / 745208122768131098915188) * r0 + ((8260855041253 : ℝ) / 2595559891601400617521599804) * r1 + ((-24000327059 : ℝ) / 1490416245536262197830376) * r2 + (1 : ℝ) * r3 + ((1246879614000986590334357 : ℝ) / 745208122768131098915188) * (value_353 h H) + ((-991316113885304685824635 : ℝ) / 745208122768131098915188) * (value_352 h H)

/-- Coordinate 97.2, recovered from skew spokes on cycle 31. -/
theorem value_390 (h : Assignment) (H : Constraints h) :
    h 97 2 = ((-103596562034867 : ℝ) / 82466274423820) * (h 1 0) + ((59216465721051 : ℝ) / 41233137211910) * (h 1 2) + ((103596562034867 : ℝ) / 82466274423820) * (h 3 0) + ((-17983328509141 : ℝ) / 41233137211910) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 264 2
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 2 - h 88 2) - ((87186713076679 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 268 2
  change ((1 : ℤ) : ℝ) * (h 97 2 - h 89 2) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((87186713076679 : ℝ) / 7452081227681310989151880) * r0 + ((-87186713076679 : ℝ) / 25955598916014006175215998040) * r1 + ((5294741058455172411648667 : ℝ) / 774310128510592586627277757000748666480) * r2 + ((-1 : ℝ) / 103905218536046) * r3 + (1 : ℝ) * r4 + ((-5294741058455172411648667 : ℝ) / 7452081227681310989151880) * (value_353 h H) + ((2092509629039488145557061 : ℝ) / 1490416245536262197830376) * (value_352 h H) + (1 : ℝ) * (value_354 h H)

/-- Coordinate 97.3, recovered from skew spokes on cycle 31. -/
theorem value_391 (h : Assignment) (H : Constraints h) :
    h 97 3 = ((-23798059040283 : ℝ) / 20616568605955) * (h 1 0) + ((27206249313798 : ℝ) / 20616568605955) * (h 1 2) + h 1 3 + ((23798059040283 : ℝ) / 20616568605955) * (h 3 0) + ((-27206249313798 : ℝ) / 20616568605955) * (h 9 2) := by
  have r0 := H 10 1
  change ((60728760973 : ℤ) : ℝ) * (h 85 1 - h 1 1) - ((120001635295 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 10 3
  change ((60728760973 : ℤ) : ℝ) * (h 85 3 - h 1 3) - ((-59272874322 : ℤ) : ℝ) * (h 85 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 257 1
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 1 - h 85 1) - ((-417965695732485 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 257 3
  change ((-211518274468959 : ℤ) : ℝ) * (h 89 3 - h 85 3) - ((206447421263526 : ℤ) : ℝ) * (h 89 0 - h 85 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 264 1
  change ((-103905218536046 : ℤ) : ℝ) * (h 89 1 - h 88 1) - ((-82608550412530 : ℤ) : ℝ) * (h 89 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 268 3
  change ((1 : ℤ) : ℝ) * (h 97 3 - h 89 3) - ((0 : ℤ) : ℝ) * (h 97 0 - h 89 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1539690239921749846202703 : ℝ) / 113138914906809681519870679128394810) * r0 + ((1 : ℝ) / 60728760973) * r1 + ((-513230079973916615400901 : ℝ) / 131354280206806040244569858468066374410) * r2 + ((-1 : ℝ) / 211518274468959) * r3 + ((29636437161 : ℝ) / 3726040613840655494575940) * r4 + (1 : ℝ) * r5 + ((-1539690239921749846202703 : ℝ) / 1863020306920327747287970) * (value_353 h H) + ((244822311326224597202733 : ℝ) / 372604061384065549457594) * (value_352 h H)

/-- Coordinate 86.0, recovered from skew spokes on cycle 32. -/
theorem value_344 (h : Assignment) (H : Constraints h) :
    h 86 0 = ((296925249523141 : ℝ) / 4859967125994466) * (h 1 0) + ((-1123773944419049 : ℝ) / 2429983562997233) * (h 1 1) + ((2787378521826375 : ℝ) / 2429983562997233) * (h 1 2) + ((4563041876471325 : ℝ) / 4859967125994466) * (h 3 0) + ((1123773944419049 : ℝ) / 2429983562997233) * (h 5 1) + ((-2787378521826375 : ℝ) / 2429983562997233) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 2
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 2 - h 86 2) - ((2095105532813019049 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1065396077176501 : ℝ) / 187881393795291881670723904268) * r0 + ((-6966 : ℝ) / 1951276801086778099) * r1 + ((-1065396077176501 : ℝ) / 1308781789178003247718262717130888) * r2 + ((1 : ℝ) / 1951276801086778099) * r3 + ((-301335580188721856581608525 : ℝ) / 19521857281156719957017803492842536411244328) * r4 + ((71914365863120475 : ℝ) / 7400296249105203038449802672264221) * r5 + ((-21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_309 h H) + ((-839237002942591822386166859249 : ℝ) / 37717189804404845245397823781801) * (value_308 h H) + ((143828731726240950 : ℝ) / 1951276801086778099) * (value_310 h H) + ((21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_353 h H) + ((38556426807347437067783990641050 : ℝ) / 37717189804404845245397823781801) * (value_352 h H) + ((-143828731726240950 : ℝ) / 1951276801086778099) * (value_354 h H)

/-- Coordinate 86.1, recovered from skew spokes on cycle 32. -/
theorem value_345 (h : Assignment) (H : Constraints h) :
    h 86 1 = ((-1002763796232614 : ℝ) / 2429983562997233) * (h 1 0) + ((1048714533548638 : ℝ) / 2429983562997233) * (h 1 1) + ((1225096040646180 : ℝ) / 2429983562997233) * (h 1 2) + ((1002763796232614 : ℝ) / 2429983562997233) * (h 3 0) + ((1381269029448595 : ℝ) / 2429983562997233) * (h 5 1) + ((-1225096040646180 : ℝ) / 2429983562997233) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 2
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 2 - h 86 2) - ((2095105532813019049 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-2157831763618120 : ℝ) / 46970348448822970417680976067) * r0 + ((-21071651899114296 : ℝ) / 13429498877746570609244192174225) * r1 + ((-2417060214572043320936947067 : ℝ) / 6755685646133816758129815168516509832825343650) * r2 + ((9074785486268 : ℝ) / 40288496633239711827732576522675) * r3 + ((-33110413898247168779958179 : ℝ) / 4880464320289179989254450873210634102811082) * r4 + ((31607477848671444 : ℝ) / 7400296249105203038449802672264221) * r5 + ((44553288234250927096744029000 : ℝ) / 46970348448822970417680976067) * (value_309 h H) + ((-16946146873584848079413203802392 : ℝ) / 37717189804404845245397823781801) * (value_308 h H) + ((63214955697342888 : ℝ) / 1951276801086778099) * (value_310 h H) + ((2417060214572043320936947067 : ℝ) / 46970348448822970417680976067) * (value_353 h H) + ((16946146873584848079413203802392 : ℝ) / 37717189804404845245397823781801) * (value_352 h H) + ((-63214955697342888 : ℝ) / 1951276801086778099) * (value_354 h H)

/-- Coordinate 86.2, recovered from skew spokes on cycle 32. -/
theorem value_346 (h : Assignment) (H : Constraints h) :
    h 86 2 = ((-4563041876471325 : ℝ) / 4859967125994466) * (h 1 0) + ((-1123773944419049 : ℝ) / 2429983562997233) * (h 1 1) + ((5217362084823608 : ℝ) / 2429983562997233) * (h 1 2) + ((4563041876471325 : ℝ) / 4859967125994466) * (h 3 0) + ((1123773944419049 : ℝ) / 2429983562997233) * (h 5 1) + ((-2787378521826375 : ℝ) / 2429983562997233) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 2
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 2 - h 86 2) - ((2095105532813019049 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1065396077176501 : ℝ) / 187881393795291881670723904268) * r0 + ((-2095105532813019049 : ℝ) / 40288496633239711827732576522675) * r1 + ((-1065396077176501 : ℝ) / 1308781789178003247718262717130888) * r2 + ((1 : ℝ) / 1951276801086778099) * r3 + ((-301335580188721856581608525 : ℝ) / 19521857281156719957017803492842536411244328) * r4 + ((71914365863120475 : ℝ) / 7400296249105203038449802672264221) * r5 + ((-21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_309 h H) + ((-38556426807347437067783990641050 : ℝ) / 37717189804404845245397823781801) * (value_308 h H) + ((2095105532813019049 : ℝ) / 1951276801086778099) * (value_310 h H) + ((21997497353776695530457422325 : ℝ) / 187881393795291881670723904268) * (value_353 h H) + ((38556426807347437067783990641050 : ℝ) / 37717189804404845245397823781801) * (value_352 h H) + ((-143828731726240950 : ℝ) / 1951276801086778099) * (value_354 h H)

/-- Coordinate 86.3, recovered from skew spokes on cycle 32. -/
theorem value_347 (h : Assignment) (H : Constraints h) :
    h 86 3 = ((3613601441424 : ℝ) / 83792536655077) * (h 1 0) + ((20301981401394 : ℝ) / 83792536655077) * (h 1 1) + ((-4414807190880 : ℝ) / 83792536655077) * (h 1 2) + h 1 3 + ((-3613601441424 : ℝ) / 83792536655077) * (h 3 0) + ((-20301981401394 : ℝ) / 83792536655077) * (h 5 1) + ((4414807190880 : ℝ) / 83792536655077) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 230 3
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 3 - h 77 3) - ((948365989152 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 260 2
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 2 - h 86 2) - ((2095105532813019049 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-170788607939511984813272 : ℝ) / 655719031522549957043339761592577434725) * r0 + ((4466746099008 : ℝ) / 27240362835185741600900998325) * r1 + ((-1 : ℝ) / 20647248309825) * r2 + ((85394303969755992406636 : ℝ) / 2283869386793041500381952389626947205147175) * r3 + ((-641221088 : ℝ) / 27240362835185741600900998325) * r4 + ((59659034280240487845732 : ℝ) / 84145936556709999814731911607079898324329) * r5 + ((-113902025524704 : ℝ) / 255182629279489759946544919733249) * r6 + ((8710219004915111225476872 : ℝ) / 1619667187890447255782102623) * (value_309 h H) + ((61067841698149803566661867072 : ℝ) / 1300592751876029146393028406269) * (value_308 h H) + ((-227804051049408 : ℝ) / 67285406934026831) * (value_310 h H) + (1 : ℝ) * (value_311 h H) + ((-8710219004915111225476872 : ℝ) / 1619667187890447255782102623) * (value_353 h H) + ((-61067841698149803566661867072 : ℝ) / 1300592751876029146393028406269) * (value_352 h H) + ((227804051049408 : ℝ) / 67285406934026831) * (value_354 h H)

/-- Coordinate 90.0, recovered from skew spokes on cycle 32. -/
theorem value_360 (h : Assignment) (H : Constraints h) :
    h 90 0 = ((3065736366373189 : ℝ) / 19645476759162664) * (h 1 0) + ((-4000350913637771 : ℝ) / 9822738379581332) * (h 1 1) + ((9477086974209675 : ℝ) / 9822738379581332) * (h 1 2) + ((16579740392789475 : ℝ) / 19645476759162664) * (h 3 0) + ((4000350913637771 : ℝ) / 9822738379581332) * (h 5 1) + ((-9477086974209675 : ℝ) / 9822738379581332) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((3792540476565679 : ℝ) / 759474181531469464953022207472) * r0 + ((-3792540476565679 : ℝ) / 5290497148548216292862752697249952) * r1 + ((-20647248309825 : ℝ) / 1518948363062938929906044414944) * r2 + ((-78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_309 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_308 h H) + ((78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_353 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_352 h H)

/-- Coordinate 90.1, recovered from skew spokes on cycle 32. -/
theorem value_361 (h : Assignment) (H : Constraints h) :
    h 90 1 = ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 0) + ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 1) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 2) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 3 0) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 5 1) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination ((-8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((-2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_309 h H) + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_308 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_353 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_352 h H)

/-- Coordinate 90.2, recovered from skew spokes on cycle 32. -/
theorem value_362 (h : Assignment) (H : Constraints h) :
    h 90 2 = ((17457042264366243 : ℝ) / 39290953518325328) * (h 1 0) + ((6713376906904283 : ℝ) / 19645476759162664) * (h 1 1) + ((-9978558405160779 : ℝ) / 19645476759162664) * (h 1 2) + ((-17457042264366243 : ℝ) / 39290953518325328) * (h 3 0) + ((-6713376906904283 : ℝ) / 19645476759162664) * (h 5 1) + ((29624035164323443 : ℝ) / 19645476759162664) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-6364630054597567 : ℝ) / 1518948363062938929906044414944) * r0 + ((6364630054597567 : ℝ) / 10580994297096432585725505394499904) * r1 + ((1800165714211657708374071175 : ℝ) / 157826661609024011459010426072854262245071424) * r2 + ((-1 : ℝ) / 7585080953131358) * r3 + ((131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_309 h H) + ((-14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_308 h H) + ((-131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_353 h H) + ((14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_352 h H) + (1 : ℝ) * (value_354 h H)

/-- Coordinate 90.3, recovered from skew spokes on cycle 32. -/
theorem value_363 (h : Assignment) (H : Constraints h) :
    h 90 3 = ((95192236161132 : ℝ) / 2455684594895333) * (h 1 0) + ((588757460640426 : ℝ) / 2455684594895333) * (h 1 1) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((-95192236161132 : ℝ) / 2455684594895333) * (h 3 0) + ((-588757460640426 : ℝ) / 2455684594895333) * (h 5 1) + ((108824997255192 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 3
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 3 - h 77 3) - ((948365989152 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 3
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 3 - h 86 3) - ((-6606317480432832 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-4407740686834813285207738 : ℝ) / 19216975503653625171936133390014635399525) * r0 + ((-1 : ℝ) / 20647248309825) * r1 + ((2203870343417406642603869 : ℝ) / 66932725679225576473853552597420975096545575) * r2 + ((1 : ℝ) / 143828731726240950) * r3 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r4 + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_309 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_308 h H) + (1 : ℝ) * (value_311 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_353 h H) + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_352 h H)

/-- Coordinate 94.0, recovered from skew spokes on cycle 32. -/
theorem value_376 (h : Assignment) (H : Constraints h) :
    h 94 0 = ((15999234359976659 : ℝ) / 9822738379581332) * (h 1 0) + ((2205155887507727 : ℝ) / 4911369189790666) * (h 1 1) + ((-9145265966661627 : ℝ) / 4911369189790666) * (h 1 2) + ((-6176495980395327 : ℝ) / 9822738379581332) * (h 3 0) + ((-2205155887507727 : ℝ) / 4911369189790666) * (h 5 1) + ((9145265966661627 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 2
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 2 - h 86 2) - ((2095105532813019049 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 261 1
  change ((43973215602920386 : ℤ) : ℝ) * (h 94 1 - h 86 1) - ((1170647327728572 : ℤ) : ℝ) * (h 94 0 - h 86 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 270 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 90 1) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 283 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 94 1) - ((0 : ℤ) : ℝ) * (h 98 2 - h 94 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((-2090602334909923 : ℝ) / 379737090765734732476511103736) * r0 + ((18 : ℝ) / 325092948878225) * r1 + ((246305767261092703917347421021912358995897497 : ℝ) / 940255397447699884112585801283998425362154067705621132026800) * r2 + ((-1 : ℝ) / 125810971215873075) * r3 + ((-1 : ℝ) / 1170647327728572) * r4 + ((591303911314864469251656075 : ℝ) / 39456665402256002864752606518213565561267856) * r5 + ((-459 : ℝ) / 3045410002682240237) * r6 + ((21986607801460193 : ℝ) / 585323663864286) * r7 + ((-21986607801460193 : ℝ) / 585323663864286) * r8 + ((43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_309 h H) + ((83341079959661609825314960756589 : ℝ) / 76232220971221247544659604075002) * (value_308 h H) + ((-918 : ℝ) / 803) * (value_310 h H) + ((-43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_353 h H) + ((-7108858988440362280655356681587 : ℝ) / 76232220971221247544659604075002) * (value_352 h H) + ((918 : ℝ) / 803) * (value_354 h H)

/-- Coordinate 94.1, recovered from skew spokes on cycle 32. -/
theorem value_377 (h : Assignment) (H : Constraints h) :
    h 94 1 = ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 0) + ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 1) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 2) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 3 0) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 5 1) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 270 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 90 1) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 283 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 94 1) - ((0 : ℤ) : ℝ) * (h 98 2 - h 94 2) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((-2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + (1 : ℝ) * r3 + (-1 : ℝ) * r4 + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_309 h H) + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_308 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_353 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_352 h H)

/-- Coordinate 94.2, recovered from skew spokes on cycle 32. -/
theorem value_378 (h : Assignment) (H : Constraints h) :
    h 94 2 = ((-16579740392789475 : ℝ) / 19645476759162664) * (h 1 0) + ((-4000350913637771 : ℝ) / 9822738379581332) * (h 1 1) + ((19299825353791007 : ℝ) / 9822738379581332) * (h 1 2) + ((16579740392789475 : ℝ) / 19645476759162664) * (h 3 0) + ((4000350913637771 : ℝ) / 9822738379581332) * (h 5 1) + ((-9477086974209675 : ℝ) / 9822738379581332) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 261 1
  change ((43973215602920386 : ℤ) : ℝ) * (h 94 1 - h 86 1) - ((1170647327728572 : ℤ) : ℝ) * (h 94 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 261 2
  change ((43973215602920386 : ℤ) : ℝ) * (h 94 2 - h 86 2) - ((2663495031967425 : ℤ) : ℝ) * (h 94 0 - h 86 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 270 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 90 1) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 283 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 94 1) - ((0 : ℤ) : ℝ) * (h 98 2 - h 94 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((3792540476565679 : ℝ) / 759474181531469464953022207472) * r0 + ((-1 : ℝ) / 20647248309825) * r1 + ((60421474188220609765863967625 : ℝ) / 4000843894898966035122546294458202853888304928) * r2 + ((-1214544018225 : ℝ) / 23473382278700910580464721144) * r3 + ((1 : ℝ) / 43973215602920386) * r4 + ((-20647248309825 : ℝ) / 1518948363062938929906044414944) * r5 + ((20647248309825 : ℝ) / 9074785486268) * r6 + ((-20647248309825 : ℝ) / 9074785486268) * r7 + ((-78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_309 h H) + ((-181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_308 h H) + (1 : ℝ) * (value_310 h H) + ((78305524944713615753353496175 : ℝ) / 759474181531469464953022207472) * (value_353 h H) + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_352 h H)

/-- Coordinate 94.3, recovered from skew spokes on cycle 32. -/
theorem value_379 (h : Assignment) (H : Constraints h) :
    h 94 3 = ((95192236161132 : ℝ) / 2455684594895333) * (h 1 0) + ((588757460640426 : ℝ) / 2455684594895333) * (h 1 1) + ((-108824997255192 : ℝ) / 2455684594895333) * (h 1 2) + h 1 3 + ((-95192236161132 : ℝ) / 2455684594895333) * (h 3 0) + ((-588757460640426 : ℝ) / 2455684594895333) * (h 5 1) + ((108824997255192 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 3
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 3 - h 77 3) - ((948365989152 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 261 1
  change ((43973215602920386 : ℤ) : ℝ) * (h 94 1 - h 86 1) - ((1170647327728572 : ℤ) : ℝ) * (h 94 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 261 3
  change ((43973215602920386 : ℤ) : ℝ) * (h 94 3 - h 86 3) - ((-122339212600608 : ℤ) : ℝ) * (h 94 0 - h 86 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 270 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 90 1) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 283 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 94 1) - ((0 : ℤ) : ℝ) * (h 98 2 - h 94 2) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-4407740686834813285207738 : ℝ) / 19216975503653625171936133390014635399525) * r0 + ((-1 : ℝ) / 20647248309825) * r1 + ((-86727160737544345484756785 : ℝ) / 125026371715592688597579571701818839184009529) * r2 + ((6973279332 : ℝ) / 2934172784837613822558090143) * r3 + ((1 : ℝ) / 43973215602920386) * r4 + ((29636437161 : ℝ) / 47467136345716841559563887967) * r5 + ((-237091497288 : ℝ) / 2268696371567) * r6 + ((237091497288 : ℝ) / 2268696371567) * r7 + ((224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_309 h H) + ((2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_308 h H) + (1 : ℝ) * (value_311 h H) + ((-224794775028575477545594638 : ℝ) / 47467136345716841559563887967) * (value_353 h H) + ((-2081451857701064291634162840 : ℝ) / 47467136345716841559563887967) * (value_352 h H)

/-- Coordinate 98.0, recovered from skew spokes on cycle 32. -/
theorem value_392 (h : Assignment) (H : Constraints h) :
    h 98 0 = ((15999234359976659 : ℝ) / 9822738379581332) * (h 1 0) + ((2205155887507727 : ℝ) / 4911369189790666) * (h 1 1) + ((-9145265966661627 : ℝ) / 4911369189790666) * (h 1 2) + ((-6176495980395327 : ℝ) / 9822738379581332) * (h 3 0) + ((-2205155887507727 : ℝ) / 4911369189790666) * (h 5 1) + ((9145265966661627 : ℝ) / 4911369189790666) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 230 2
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 2 - h 77 2) - ((-20647248309825 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 260 2
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 2 - h 86 2) - ((2095105532813019049 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 261 1
  change ((43973215602920386 : ℤ) : ℝ) * (h 94 1 - h 86 1) - ((1170647327728572 : ℤ) : ℝ) * (h 94 0 - h 86 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 270 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 90 1) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 283 0
  change ((1 : ℤ) : ℝ) * (h 98 0 - h 94 0) - ((0 : ℤ) : ℝ) * (h 98 2 - h 94 2) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  have r9 := H 283 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 94 1) - ((0 : ℤ) : ℝ) * (h 98 2 - h 94 2) = 0 at r9
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r9
  linear_combination ((-2090602334909923 : ℝ) / 379737090765734732476511103736) * r0 + ((18 : ℝ) / 325092948878225) * r1 + ((246305767261092703917347421021912358995897497 : ℝ) / 940255397447699884112585801283998425362154067705621132026800) * r2 + ((-1 : ℝ) / 125810971215873075) * r3 + ((-1 : ℝ) / 1170647327728572) * r4 + ((591303911314864469251656075 : ℝ) / 39456665402256002864752606518213565561267856) * r5 + ((-459 : ℝ) / 3045410002682240237) * r6 + ((21986607801460193 : ℝ) / 585323663864286) * r7 + (1 : ℝ) * r8 + ((-21986607801460193 : ℝ) / 585323663864286) * r9 + ((43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_309 h H) + ((83341079959661609825314960756589 : ℝ) / 76232220971221247544659604075002) * (value_308 h H) + ((-918 : ℝ) / 803) * (value_310 h H) + ((-43165185525985106255370893475 : ℝ) / 379737090765734732476511103736) * (value_353 h H) + ((-7108858988440362280655356681587 : ℝ) / 76232220971221247544659604075002) * (value_352 h H) + ((918 : ℝ) / 803) * (value_354 h H)

/-- Coordinate 98.1, recovered from skew spokes on cycle 32. -/
theorem value_393 (h : Assignment) (H : Constraints h) :
    h 98 1 = ((-1821763186368301 : ℝ) / 4911369189790666) * (h 1 0) + ((1119392371268413 : ℝ) / 2455684594895333) * (h 1 1) + ((1041331634549253 : ℝ) / 2455684594895333) * (h 1 2) + ((1821763186368301 : ℝ) / 4911369189790666) * (h 3 0) + ((1336292223626920 : ℝ) / 2455684594895333) * (h 5 1) + ((-1041331634549253 : ℝ) / 2455684594895333) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 270 1
  change ((1 : ℤ) : ℝ) * (h 98 1 - h 90 1) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  linear_combination ((-8779107987886555 : ℝ) / 189868545382867366238255551868) * r0 + ((8779107987886555 : ℝ) / 1322624287137054073215688174312488) * r1 + ((-2268696371567 : ℝ) / 379737090765734732476511103736) * r2 + (1 : ℝ) * r3 + ((181264422564661829297591902875 : ℝ) / 189868545382867366238255551868) * (value_309 h H) + ((-19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_308 h H) + ((8604122818205536940663648993 : ℝ) / 189868545382867366238255551868) * (value_353 h H) + ((19917130437713093517323581685 : ℝ) / 47467136345716841559563887967) * (value_352 h H)

/-- Coordinate 98.2, recovered from skew spokes on cycle 32. -/
theorem value_394 (h : Assignment) (H : Constraints h) :
    h 98 2 = ((17457042264366243 : ℝ) / 39290953518325328) * (h 1 0) + ((6713376906904283 : ℝ) / 19645476759162664) * (h 1 1) + ((-9978558405160779 : ℝ) / 19645476759162664) * (h 1 2) + ((-17457042264366243 : ℝ) / 39290953518325328) * (h 3 0) + ((-6713376906904283 : ℝ) / 19645476759162664) * (h 5 1) + ((29624035164323443 : ℝ) / 19645476759162664) * (h 9 2) := by
  have r0 := H 230 1
  change ((-20647248309825 : ℤ) : ℝ) * (h 86 1 - h 77 1) - ((-9074785486268 : ℤ) : ℝ) * (h 86 0 - h 77 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 260 1
  change ((143828731726240950 : ℤ) : ℝ) * (h 90 1 - h 86 1) - ((63214955697342888 : ℤ) : ℝ) * (h 90 0 - h 86 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 265 1
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 1 - h 88 1) - ((70232863903092440 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 265 2
  change ((-7585080953131358 : ℤ) : ℝ) * (h 90 2 - h 88 2) - ((6364630054597567 : ℤ) : ℝ) * (h 90 0 - h 88 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 270 2
  change ((1 : ℤ) : ℝ) * (h 98 2 - h 90 2) - ((0 : ℤ) : ℝ) * (h 98 0 - h 90 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  linear_combination ((-6364630054597567 : ℝ) / 1518948363062938929906044414944) * r0 + ((6364630054597567 : ℝ) / 10580994297096432585725505394499904) * r1 + ((1800165714211657708374071175 : ℝ) / 157826661609024011459010426072854262245071424) * r2 + ((-1 : ℝ) / 7585080953131358) * r3 + (1 : ℝ) * r4 + ((131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_309 h H) + ((-14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_308 h H) + ((-131412097137451012711307195775 : ℝ) / 1518948363062938929906044414944) * (value_353 h H) + ((14439413111231777359286177489 : ℝ) / 379737090765734732476511103736) * (value_352 h H) + (1 : ℝ) * (value_354 h H)

end CubicalIndecomposability.Rigidity
end VerificationSource014

/- Original source: CubicalIndecomposability/Rigidity/Values05.lean -/

end -- global noncomputable section
end -- global public section
