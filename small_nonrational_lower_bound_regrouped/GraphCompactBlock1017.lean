module
prelude
import GraphInputsSix0Part00052Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1017
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 20036579262720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 20036636903552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record001_result⟩)
 (.leaf ⟨(32, 20038576832768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 20038585221120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 20042869702912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record004_result⟩)
 (.leaf ⟨(32, 20042878091264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 20043272306944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 20045418742016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record007_result⟩)
 (.leaf ⟨(32, 20046898331904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 20047170961408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 20047435202560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record010_result⟩)
 (.leaf ⟨(32, 20047443525632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 20047567323136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 20047707766784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record013_result⟩)
 (.leaf ⟨(32, 20049119152256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 20051463831552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 20060049571840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record016_result⟩)
 (.leaf ⟨(32, 20062129946624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 20084545339520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 20106023305472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record019_result⟩)
 (.leaf ⟨(32, 20106027499648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 20123198980224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record021_result⟩)
 (.leaf ⟨(32, 20123203174400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 20130682667008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record023_result⟩)
 (.leaf ⟨(32, 20138235560192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 20138239754368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 20140381995264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record026_result⟩)
 (.leaf ⟨(32, 20140386189440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 20141459406976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 20144674865408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record029_result⟩)
 (.leaf ⟨(32, 20149950251008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 20150016311296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 20158531797120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record032_result⟩)
 (.leaf ⟨(32, 20158535991296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 20158602051584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 20158635081728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record035_result⟩)
 (.leaf ⟨(32, 20158732058752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 20161854734336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 20162894921728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record038_result⟩)
 (.leaf ⟨(32, 20171471225088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 20171475419264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 20171727046784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record041_result⟩)
 (.leaf ⟨(32, 20173617660160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 20173621854336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 20173675300992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record044_result⟩)
 (.leaf ⟨(32, 20173749780736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 20173807421568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record046_result⟩)
 (.leaf ⟨(32, 20173873481856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 20174018216064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record048_result⟩)
 (.leaf ⟨(32, 20177968171136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 20180312850432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 20186553911424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record051_result⟩)
 (.leaf ⟨(32, 20192923123840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 20192927318016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 20193057325184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record054_result⟩)
 (.leaf ⟨(32, 20193063470080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 20193191395968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 20197220188160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record057_result⟩)
 (.leaf ⟨(32, 20199300562944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 20199432520320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 20209099374848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record060_result⟩)
 (.leaf ⟨(32, 20227319431168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 20242335039744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 20242392680576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record063_result⟩)
 (.leaf ⟨(32, 20244737359872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 20249028083968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 20251174519040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record066_result⟩)
 (.leaf ⟨(32, 20274547294464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 20274604935296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 20276751370368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record069_result⟩)
 (.leaf ⟨(32, 20279029989376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 20283320713472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record071_result⟩)
 (.leaf ⟨(32, 20283386773760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 20289629980800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record073_result⟩)
 (.leaf ⟨(32, 20344364695680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 20344498897024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 20344763138176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record076_result⟩)
 (.leaf ⟨(32, 20346511130752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 20346645332096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 20346907492480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record079_result⟩)
 (.leaf ⟨(32, 20346909573248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 20346910613632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 20351202443392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record082_result⟩)
 (.leaf ⟨(32, 20359792345216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 20379779825792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 20379914027136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record085_result⟩)
 (.leaf ⟨(32, 20380182429824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 20381239001216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 20385397539072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record088_result⟩)
 (.leaf ⟨(32, 20385403781376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 20388624994560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 20411992080512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record091_result⟩)
 (.leaf ⟨(32, 20412126281856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 20414273757312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 20414542160000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record094_result⟩)
 (.leaf ⟨(32, 20415598731392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 20418837110912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record096_result⟩)
 (.leaf ⟨(32, 20419690168576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 20419696410880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record098_result⟩)
 (.leaf ⟨(32, 20419893682304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00052.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31950 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31950 32050 :=
  block_of_table results 31950 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1017
