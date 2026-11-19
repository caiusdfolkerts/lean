module
prelude
import GraphInputsRow30Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0753
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 12650067066880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 12650327081216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record001_result⟩)
 (.leaf ⟨(30, 12650335469568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 12650558292224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record003_result⟩)
 (.leaf ⟨(30, 12650570321920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 12653261492480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record005_result⟩)
 (.leaf ⟨(30, 12654359937024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(30, 12654624178176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record007_result⟩)
 (.leaf ⟨(30, 12654628339712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record008_result⟩))
 (.branch 10
 (.leaf ⟨(30, 12654719041792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record009_result⟩)
 (.leaf ⟨(30, 12654731071488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 12658074456320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record011_result⟩)
 (.leaf ⟨(30, 12663040540928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 12663052570624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record013_result⟩)
 (.leaf ⟨(30, 12663209885824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(30, 12663214080000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 12663308976256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record016_result⟩)
 (.leaf ⟨(30, 12663443177600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(30, 12666664390784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record018_result⟩)
 (.leaf ⟨(30, 12713392869632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record019_result⟩))
 (.branch 21
 (.leaf ⟨(30, 12722247336192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record020_result⟩)
 (.leaf ⟨(30, 12722255724544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 12722259365888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record022_result⟩)
 (.leaf ⟨(30, 12722498703616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 12723312295936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record024_result⟩)
 (.leaf ⟨(30, 12723572179712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(30, 12730837270656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record026_result⟩)
 (.leaf ⟨(30, 12731088638080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record027_result⟩))
 (.branch 29
 (.leaf ⟨(30, 12732162114176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record028_result⟩)
 (.leaf ⟨(30, 12739678306832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(30, 12781978128640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 12786411831296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record031_result⟩)
 (.leaf ⟨(30, 12786683875328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(30, 12790976745472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record033_result⟩)
 (.leaf ⟨(30, 12791083962624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record034_result⟩))
 (.branch 36
 (.leaf ⟨(30, 12795513470976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record035_result⟩)
 (.leaf ⟨(30, 12799562485760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(30, 12800478937856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record037_result⟩)
 (.leaf ⟨(30, 12800747373184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record038_result⟩))
 (.branch 40
 (.leaf ⟨(30, 12804102816272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record039_result⟩)
 (.leaf ⟨(30, 12864240746496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(30, 12923854393344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record041_result⟩)
 (.leaf ⟨(30, 12924110798976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record042_result⟩))
 (.branch 44
 (.leaf ⟨(30, 12928405749888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record043_result⟩)
 (.leaf ⟨(30, 12928411504640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record044_result⟩)))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf ⟨(30, 12932951835152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record045_result⟩)
 (.leaf ⟨(30, 12936844415104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record046_result⟩))
 (.branch 48
 (.leaf ⟨(30, 12937917891200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record047_result⟩)
 (.leaf ⟨(30, 13125437128960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(30, 13125705596928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record049_result⟩)
 (.leaf ⟨(30, 13125713920000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record050_result⟩))
 (.branch 52
 (.leaf ⟨(30, 13125973999616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record051_result⟩)
 (.leaf ⟨(30, 13126225627136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record052_result⟩))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf ⟨(30, 13134010124544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record053_result⟩)
 (.leaf ⟨(30, 13134303592448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record054_result⟩))
 (.branch 56
 (.leaf ⟨(30, 13134546995200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record055_result⟩)
 (.leaf ⟨(30, 13134563639808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record056_result⟩)))
 (.branch 59
 (.branch 58
 (.leaf ⟨(30, 13142600059008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record057_result⟩)
 (.leaf ⟨(30, 13151189860868), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record058_result⟩))
 (.branch 60
 (.leaf ⟨(30, 13197668073728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record059_result⟩)
 (.leaf ⟨(30, 13199815549184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00025.record060_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24312 + i))) 0 61 :=
  interval_of_check _ 0 61 (by decide +kernel)

public theorem complete : Block 24312 24373 :=
  block_of_table results 24312 61 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0753
