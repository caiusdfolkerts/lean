module
prelude
import GraphInputsRow28Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0429
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 27094337716224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 27097754509312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record001_result⟩)
 (.leaf ⟨(28, 27123532169216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(28, 27127569219584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record003_result⟩)
 (.leaf ⟨(28, 27127573381120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record004_result⟩))
 (.branch 6
 (.leaf ⟨(28, 27129299402752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record005_result⟩)
 (.leaf ⟨(28, 27132113715712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(28, 27226603528192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record007_result⟩)
 (.branch 9
 (.leaf ⟨(28, 27238717210752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record008_result⟩)
 (.leaf ⟨(28, 27266738323456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(28, 27404177244160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record010_result⟩)
 (.leaf ⟨(28, 27562495442944), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record011_result⟩))
 (.branch 13
 (.leaf ⟨(28, 27575435952128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record012_result⟩)
 (.leaf ⟨(28, 28041170976768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(28, 28076487016448), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record014_result⟩)
 (.branch 16
 (.leaf ⟨(28, 28076495339520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record015_result⟩)
 (.leaf ⟨(28, 28090298335232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(28, 28231625342976), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record017_result⟩)
 (.leaf ⟨(28, 28235257610240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record018_result⟩))
 (.branch 20
 (.leaf ⟨(28, 28331787452416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record019_result⟩)
 (.leaf ⟨(28, 28497644879872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 28597269053696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record021_result⟩)
 (.leaf ⟨(28, 28597537489024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 28662196895744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record023_result⟩)
 (.leaf ⟨(28, 28665754714368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(28, 28666089242624), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record025_result⟩)
 (.leaf ⟨(28, 28666357645312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record026_result⟩))
 (.branch 28
 (.leaf ⟨(28, 28674344648832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record027_result⟩)
 (.leaf ⟨(28, 28674679144448), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record028_result⟩))))))
 (.branch 44
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf ⟨(28, 28692667465984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record029_result⟩)
 (.branch 31
 (.leaf ⟨(28, 28697096683520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record030_result⟩)
 (.leaf ⟨(28, 28697633488896), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record031_result⟩)))
 (.branch 34
 (.branch 33
 (.leaf ⟨(28, 28701257433088), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record032_result⟩)
 (.leaf ⟨(28, 28701529997312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record033_result⟩))
 (.branch 35
 (.leaf ⟨(28, 28701794238464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record034_result⟩)
 (.leaf ⟨(28, 28709847334912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record035_result⟩))))
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf ⟨(28, 28716220579840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record036_result⟩)
 (.leaf ⟨(28, 28830106451968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record037_result⟩))
 (.branch 39
 (.leaf ⟨(28, 28834539765760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record038_result⟩)
 (.leaf ⟨(28, 28835068248064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record039_result⟩)))
 (.branch 42
 (.branch 41
 (.leaf ⟨(28, 28847286255616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record040_result⟩)
 (.leaf ⟨(28, 28871055908928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record041_result⟩))
 (.branch 43
 (.leaf ⟨(28, 28875099750528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record042_result⟩)
 (.leaf ⟨(28, 28875468316672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record043_result⟩)))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf ⟨(28, 28898823798912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record044_result⟩)
 (.branch 46
 (.leaf ⟨(28, 28967545372672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record045_result⟩)
 (.leaf ⟨(28, 28971974524928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(28, 28976135274496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record047_result⟩)
 (.leaf ⟨(28, 28976399515648), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record048_result⟩))
 (.branch 50
 (.leaf ⟨(28, 29177596084224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record049_result⟩)
 (.leaf ⟨(28, 29181220028416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record050_result⟩))))
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(28, 29181492592640), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record051_result⟩)
 (.leaf ⟨(28, 29181756833792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record052_result⟩))
 (.branch 54
 (.leaf ⟨(28, 29185108606976), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record053_result⟩)
 (.leaf ⟨(28, 29189809930240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(28, 29190078332928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record055_result⟩)
 (.leaf ⟨(28, 29197223362560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record056_result⟩))
 (.branch 58
 (.leaf ⟨(28, 29265907318784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record057_result⟩)
 (.leaf ⟨(28, 29275640070400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00009.record058_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20156 + i))) 0 59 :=
  interval_of_check _ 0 59 (by decide +kernel)

public theorem complete : Block 20156 20215 :=
  block_of_table results 20156 59 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0429
