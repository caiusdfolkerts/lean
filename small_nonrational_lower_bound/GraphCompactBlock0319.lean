module
prelude
import GraphInputsRow26Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0319
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 1507602891008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 1507602956288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record001_result⟩)
 (.leaf ⟨(26, 1507747495936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 1508148019200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 1535621759232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record004_result⟩)
 (.leaf ⟨(26, 1654813458816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 1654947660160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 1688098668928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record007_result⟩)
 (.leaf ⟨(26, 1688216355200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 1688484757888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 1722576085376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record010_result⟩)
 (.leaf ⟨(26, 1857114177544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 1874294046720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 1876766491392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record013_result⟩)
 (.leaf ⟨(26, 1876774879744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 1912082531072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 1912090919424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record016_result⟩)
 (.leaf ⟨(26, 1919858902272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 1919858967552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 1920395641348), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record019_result⟩)
 (.leaf ⟨(26, 1972073758720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 1981468966912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record021_result⟩)
 (.leaf ⟨(26, 1981737369600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 1981861101824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record023_result⟩)
 (.leaf ⟨(26, 1981997449216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(26, 1982005772288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 1986030239744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record026_result⟩)
 (.leaf ⟨(26, 1994152574984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(26, 1994229104896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 1994230145280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record029_result⟩)
 (.leaf ⟨(26, 1994284695560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(26, 1994548936712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 2001632067592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record032_result⟩)
 (.leaf ⟨(26, 2001766268936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(26, 2002010030336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 2002011590912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record035_result⟩)
 (.leaf ⟨(26, 2002034671624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(26, 2003143065600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record037_result⟩)
 (.branch 39
 (.leaf ⟨(26, 2011735015552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record038_result⟩)
 (.leaf ⟨(26, 2016290078720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(26, 2016298401792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record040_result⟩)
 (.branch 42
 (.leaf ⟨(26, 2018688204800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record041_result⟩)
 (.leaf ⟨(26, 2018787229952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(26, 2018787295232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 2019777741056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record044_result⟩)
 (.leaf ⟨(26, 2019777806336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(26, 2019781772544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record046_result⟩)
 (.leaf ⟨(26, 2019922280449), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(26, 2020314480896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record048_result⟩)
 (.leaf ⟨(26, 2020318642177), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record049_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14156 + i))) 0 50 :=
  interval_of_check _ 0 50 (by decide +kernel)

public theorem complete : Block 14156 14206 :=
  block_of_table results 14156 50 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0319
