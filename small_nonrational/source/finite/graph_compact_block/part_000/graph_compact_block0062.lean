module
prelude
import GraphInputsRow19Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0062
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 24335847284832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 24338683215872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record001_result⟩)
 (.leaf ⟨(19, 24339213778944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 24339220021248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 24341292007680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record004_result⟩)
 (.leaf ⟨(19, 24341294153728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 24347268956160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 24347273117696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record007_result⟩)
 (.leaf ⟨(19, 24347408343104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 24347541520384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 24347672584256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record010_result⟩)
 (.leaf ⟨(19, 24347935785024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 24347937882112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 24350117347328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record013_result⟩)
 (.leaf ⟨(19, 24350627995712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 24353642135808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 24353642201088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record016_result⟩)
 (.leaf ⟨(19, 24353649467456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 24353742852096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 24353748557888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record019_result⟩)
 (.leaf ⟨(19, 24362282483968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 24362284564736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record021_result⟩)
 (.leaf ⟨(19, 24362416685312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 24362422976576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record023_result⟩)
 (.leaf ⟨(19, 24362685088000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 24362685136960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 24369821728776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record026_result⟩)
 (.leaf ⟨(19, 24373999190272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 24373999255552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 24375082549504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record029_result⟩)
 (.leaf ⟨(19, 24375088857088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 24375090742528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 24375558561792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record032_result⟩)
 (.leaf ⟨(19, 24382582915072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 24382584930560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 24382584995840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record035_result⟩)
 (.leaf ⟨(19, 24382592262208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 24383880060928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 24386884091968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record038_result⟩)
 (.leaf ⟨(19, 24386885132352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 24386977996800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 24387000737856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record041_result⟩)
 (.leaf ⟨(19, 24387973693504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 24388040810496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 24388438066240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record044_result⟩)
 (.leaf ⟨(19, 24391155975424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 24391161356352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record046_result⟩)
 (.leaf ⟨(19, 24391161372672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 24398124326976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record048_result⟩)
 (.leaf ⟨(19, 24415565266944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 24415884706048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 24416086918400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record051_result⟩)
 (.leaf ⟨(19, 24416092315648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 24421269520640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 24423366344704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record054_result⟩)
 (.leaf ⟨(19, 24429862404352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 24430067867904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 24430332952584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record057_result⟩)
 (.leaf ⟨(19, 24430336319552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 24432198486080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 24432198500360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record060_result⟩)
 (.leaf ⟨(19, 24434140449024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 24438439624712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 24447025365000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record063_result⟩)
 (.leaf ⟨(19, 24447230828552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 24453530681600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 24453601886208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record066_result⟩)
 (.leaf ⟨(19, 24457693561856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 24471684726912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 24471692009600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record069_result⟩)
 (.leaf ⟨(19, 24471792660608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 24476390539264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record071_result⟩)
 (.leaf ⟨(19, 24476784803904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 24476786900992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record073_result⟩)
 (.leaf ⟨(19, 24511433949440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 24511434014720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 24511936733248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record076_result⟩)
 (.leaf ⟨(19, 24512521535488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 24512523550976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 24512523616256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record079_result⟩)
 (.leaf ⟨(19, 24512729063488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 24512798130177), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 24513326612992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record082_result⟩)
 (.leaf ⟨(19, 24567502627072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 24569498994944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 24602934796544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record085_result⟩)
 (.leaf ⟨(19, 24604007022656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 24604008014080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 24608837738560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record088_result⟩)
 (.leaf ⟨(19, 24608838795264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 24610266497032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 24610717851712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record091_result⟩)
 (.leaf ⟨(19, 24612998488128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 24612999544832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 24616639807744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record094_result⟩)
 (.leaf ⟨(19, 24616639873024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 24616641758464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record096_result⟩)
 (.leaf ⟨(19, 24616647139392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 24616647155712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record098_result⟩)
 (.leaf ⟨(19, 24616674463744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00022.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4256 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 4256 4356 :=
  block_of_table results 4256 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0062
