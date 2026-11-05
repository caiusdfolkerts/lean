module
prelude
import GraphInputsRow16Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0029
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 28153120555008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_result⟩)
 (.leaf ⟨(16, 28153384796160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 28168946253824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record002_result⟩)
 (.leaf ⟨(16, 28185245794304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 28214919495936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record004_result⟩)
 (.leaf ⟨(16, 28216459297024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 28232107687936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_result⟩)
 (.leaf ⟨(16, 28233139552256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 28233147875328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_result⟩)
 (.leaf ⟨(16, 28244868923648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 28244873085184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record010_result⟩)
 (.leaf ⟨(16, 28244873150464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 28244934983936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record012_result⟩)
 (.leaf ⟨(16, 28244939145472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 28244939210752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 28244942266624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record015_result⟩)
 (.leaf ⟨(16, 28245335507200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 28245335572480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_result⟩)
 (.leaf ⟨(16, 28248286757120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 28248294039808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record019_result⟩)
 (.leaf ⟨(16, 28248294105088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 28248311335168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record021_result⟩)
 (.leaf ⟨(16, 28248555225088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 28248558280960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record023_result⟩)
 (.leaf ⟨(16, 28248558346240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 28248566140960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record025_result⟩)
 (.leaf ⟨(16, 28256641286400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 28256649674752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record027_result⟩)
 (.leaf ⟨(16, 28257144021248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(16, 28257152409600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record029_result⟩)
 (.leaf ⟨(16, 28257730887936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record030_result⟩))
 (.branch 32
 (.leaf ⟨(16, 28257739276288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 28265235415040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_result⟩)
 (.leaf ⟨(16, 28265465520384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1677 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 1677 1711 :=
  block_of_table results 1677 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0029
