module
prelude
import GraphInputsRow19Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0040
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 115643351040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 186507165696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record001_result⟩)
 (.leaf ⟨(19, 194828599552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 194828664832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 265027584001), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record004_result⟩)
 (.leaf ⟨(19, 401921376512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 406086320256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 406823387264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record007_result⟩)
 (.leaf ⟨(19, 474805780608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 476952215680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 630938697984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record010_result⟩)
 (.leaf ⟨(19, 663134240768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 735071207680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 741312397312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record013_result⟩)
 (.leaf ⟨(19, 742905708544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 742909870080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 744853962752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record016_result⟩)
 (.leaf ⟨(19, 744990179329), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 744990244864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 746026270720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record019_result⟩)
 (.leaf ⟨(19, 777198272768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 777198338048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record021_result⟩)
 (.leaf ⟨(19, 836892721152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 880340467712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record023_result⟩)
 (.leaf ⟨(19, 880348790784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 882420777216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 882429165568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record026_result⟩)
 (.leaf ⟨(19, 886581592064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 886589915136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 886785982592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record029_result⟩)
 (.leaf ⟨(19, 921577799936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 956574007808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 956578136704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record032_result⟩)
 (.leaf ⟨(19, 990101192832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 1025295581184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 1026572894336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record035_result⟩)
 (.leaf ⟨(19, 1432042438656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 1432048648320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 1432050761728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record038_result⟩)
 (.leaf ⟨(19, 1432240619520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 1438991335552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 1466409451520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record041_result⟩)
 (.leaf ⟨(19, 1470693998592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 1470702321664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 1501229711616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record044_result⟩)
 (.leaf ⟨(19, 1502034854400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 1502038983296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record046_result⟩)
 (.leaf ⟨(19, 1505799274496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 1505801289984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record048_result⟩)
 (.leaf ⟨(19, 1506327691520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 1506331918336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 1506338160640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record051_result⟩)
 (.leaf ⟨(19, 1506340241408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 1508073635844), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 1508143890432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record054_result⟩)
 (.leaf ⟨(19, 1508351418432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 1535628099712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 1574518669568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record057_result⟩)
 (.leaf ⟨(19, 1575047151872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 1575055540224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 1576464908288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record060_result⟩)
 (.leaf ⟨(19, 1576863285504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 1577201975296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 1874310823936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record063_result⟩)
 (.leaf ⟨(19, 1874314985472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 1882883981312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 1883152384000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record066_result⟩)
 (.leaf ⟨(19, 1945257476096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 1945265799168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 1947412234240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record069_result⟩)
 (.leaf ⟨(19, 1947544354816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 1980680929280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record071_result⟩)
 (.leaf ⟨(19, 1981997384448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 1981997449728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record073_result⟩)
 (.leaf ⟨(19, 1982001578624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 1982005772289), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 2003145162816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record076_result⟩)
 (.leaf ⟨(19, 2012893184000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 2020318740480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 2020450828800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record079_result⟩)
 (.leaf ⟨(19, 2020582916352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 2020587143168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 2020593385472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record082_result⟩)
 (.leaf ⟨(19, 2020595466240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 2053818581248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 2053822808064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record085_result⟩)
 (.leaf ⟨(19, 2053829050368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 2053831131136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 2057566388224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record088_result⟩)
 (.leaf ⟨(19, 2058096771328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 2058233118720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 2058241441792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record091_result⟩)
 (.leaf ⟨(19, 2089038200832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 2089310765056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 2089376825344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record094_result⟩)
 (.leaf ⟨(19, 2091826315520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 2091826380800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record096_result⟩)
 (.leaf ⟨(19, 2091960582144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 2092228984832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record098_result⟩)
 (.leaf ⟨(19, 2126285848576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2098 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2098 2198 :=
  block_of_table results 2098 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0040
