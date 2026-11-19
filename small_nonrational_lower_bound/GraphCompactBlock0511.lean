module
prelude
import GraphInputsRow29Part00077Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0511
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 12650058678528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record000_result⟩)
 (.leaf ⟨(29, 12650067066880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12650327081216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record002_result⟩)
 (.leaf ⟨(29, 12650335469568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 12650558292224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record004_result⟩)
 (.leaf ⟨(29, 12650570321920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 12653261492480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_result⟩)
 (.leaf ⟨(29, 12654359937024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 12654450639104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record008_result⟩)
 (.leaf ⟨(29, 12654619951360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 12654624178176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record010_result⟩)
 (.leaf ⟨(29, 12654628339712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 12654719041792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record012_result⟩)
 (.leaf ⟨(29, 12654731071488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 12658074456320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 12663040540928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record015_result⟩)
 (.leaf ⟨(29, 12663052570624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(29, 12663209885824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record017_result⟩)
 (.leaf ⟨(29, 12663214080000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record018_result⟩))
 (.branch 20
 (.leaf ⟨(29, 12663308976256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record019_result⟩)
 (.leaf ⟨(29, 12663443177600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(29, 12666664390784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record021_result⟩)
 (.leaf ⟨(29, 12713392869632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_result⟩))
 (.branch 24
 (.leaf ⟨(29, 12722247336192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_result⟩)
 (.leaf ⟨(29, 12722255724544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(29, 12722259365888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record025_result⟩)
 (.leaf ⟨(29, 12722498703616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record026_result⟩))
 (.branch 28
 (.leaf ⟨(29, 12723312295936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record027_result⟩)
 (.leaf ⟨(29, 12723572179712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(29, 12730837270656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record029_result⟩)
 (.leaf ⟨(29, 12731088638080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record030_result⟩))
 (.branch 32
 (.leaf ⟨(29, 12732162114176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record031_result⟩)
 (.branch 33
 (.leaf ⟨(29, 12739678306832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record032_result⟩)
 (.leaf ⟨(29, 12781978128640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21520 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 21520 21554 :=
  block_of_table results 21520 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0511
