module
prelude
import GraphInputsSix0Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0969
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 1907525484800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 1907529646336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record001_result⟩)
 (.leaf ⟨(32, 1907529711616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 1907649153280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 1912070013184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record004_result⟩)
 (.leaf ⟨(32, 1912078401536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 1912082531072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 1912090919424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record007_result⟩)
 (.leaf ⟨(32, 1912090984448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 1916362883328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 1919858902272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record010_result⟩)
 (.leaf ⟨(32, 1919858967552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 1920127271168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 1920387449088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record013_result⟩)
 (.leaf ⟨(32, 1920395641348), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 1920395771905), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 1920395837440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record016_result⟩)
 (.leaf ⟨(32, 1920664141824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 1931271569424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 1937644814352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record019_result⟩)
 (.leaf ⟨(32, 1942606676224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 1942610870400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record021_result⟩)
 (.leaf ⟨(32, 1942745071744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 1942807978240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record023_result⟩)
 (.leaf ⟨(32, 1942811132032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 1971805290752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 1972073693440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record026_result⟩)
 (.leaf ⟨(32, 1972073758720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 1972207894784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 1981460578560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record029_result⟩)
 (.leaf ⟨(32, 1981468966912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 1981728981248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 1981737369600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record032_result⟩)
 (.leaf ⟨(32, 1981861101824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 1981997449216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 1982005772288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record035_result⟩)
 (.leaf ⟨(32, 1985092796480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 1986030239744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 1994028843264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record038_result⟩)
 (.leaf ⟨(32, 1994152574984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 1994227024128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 1994229104896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record041_result⟩)
 (.leaf ⟨(32, 1994230145280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 1994284695560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 1994497507584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record044_result⟩)
 (.leaf ⟨(32, 1994548936712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 1996501352704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record046_result⟩)
 (.leaf ⟨(32, 1996769755392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 1996769820672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record048_result⟩)
 (.leaf ⟨(32, 1998581727488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 1999890317568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 1999890382848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record051_result⟩)
 (.leaf ⟨(32, 2001566007304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 2001632067592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 2001741627648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record054_result⟩)
 (.leaf ⟨(32, 2001742668032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 2001743188224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 2001766268936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record057_result⟩)
 (.leaf ⟨(32, 2001799299080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 2002010030336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 2002011070720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record060_result⟩)
 (.leaf ⟨(32, 2002011590912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 2002034671624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 2002742477056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record063_result⟩)
 (.leaf ⟨(32, 2002874597632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 2003143000320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 2003143065600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record066_result⟩)
 (.leaf ⟨(32, 2004013875456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 2004183187712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 2004183252992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record069_result⟩)
 (.leaf ⟨(32, 2011732934784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 2011735015552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record071_result⟩)
 (.leaf ⟨(32, 2016290078720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 2016298401792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record073_result⟩)
 (.leaf ⟨(32, 2018688139520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 2018688204800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 2018787229952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record076_result⟩)
 (.leaf ⟨(32, 2018787295232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 2019452526656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 2019777741056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record079_result⟩)
 (.leaf ⟨(32, 2019777806336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 2019781772544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 2019913957632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record082_result⟩)
 (.leaf ⟨(32, 2019922280449), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 2019922345984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 2020314480896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record085_result⟩)
 (.leaf ⟨(32, 2020318642177), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 2020322869248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 2020450828288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record088_result⟩)
 (.leaf ⟨(32, 2020459151360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 2027380113664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 2027388239880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record091_result⟩)
 (.leaf ⟨(32, 2027514315008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 2027518476544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 2027520360456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record094_result⟩)
 (.leaf ⟨(32, 2031792359680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 2031792489728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record096_result⟩)
 (.leaf ⟨(32, 2031796584456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 2031817392384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record098_result⟩)
 (.leaf ⟨(32, 2032085795072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00004.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27186 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27186 27286 :=
  block_of_table results 27186 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0969
