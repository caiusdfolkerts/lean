module
prelude
import GraphInputsRow16Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0038
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 33204477689856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_result⟩)
 (.leaf ⟨(16, 33204484972544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 33206574448640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record002_result⟩)
 (.leaf ⟨(16, 33206581731328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 33206615671808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record004_result⟩)
 (.leaf ⟨(16, 33207078093824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 33240907908096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record006_result⟩)
 (.leaf ⟨(16, 33581678788608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 33613807681536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record008_result⟩)
 (.leaf ⟨(16, 33613816004608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 33685487755264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record010_result⟩)
 (.leaf ⟨(16, 34121521332480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 34124790792448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record012_result⟩)
 (.leaf ⟨(16, 34126908424192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 34159242780672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record014_result⟩)
 (.leaf ⟨(16, 34190238712064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(16, 34190255227136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record016_result⟩)
 (.leaf ⟨(16, 34194399461632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record017_result⟩))
 (.branch 19
 (.leaf ⟨(16, 34194436718592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record018_result⟩)
 (.leaf ⟨(16, 34194445041664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(16, 34194667929600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record020_result⟩)
 (.leaf ⟨(16, 34194676252672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record021_result⟩))
 (.branch 23
 (.leaf ⟨(16, 34195187699712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record022_result⟩)
 (.leaf ⟨(16, 34195724500992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 34195732824064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record024_result⟩)
 (.leaf ⟨(16, 34642443370496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 34642971852800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record026_result⟩)
 (.leaf ⟨(16, 34670205534208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(16, 34673565110272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record028_result⟩)
 (.leaf ⟨(16, 34673581885440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record029_result⟩))
 (.branch 31
 (.leaf ⟨(16, 34674362056960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 34674399313920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record031_result⟩)
 (.leaf ⟨(16, 34674407636992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2051 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 2051 2084 :=
  block_of_table results 2051 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0038
