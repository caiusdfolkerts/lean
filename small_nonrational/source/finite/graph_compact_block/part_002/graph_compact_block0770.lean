module
prelude
import GraphInputsRow30Part00042Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0770
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 26139171098688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 26207890440708), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record001_result⟩)
 (.leaf ⟨(30, 26319559723264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 26319576694784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record003_result⟩)
 (.leaf ⟨(30, 26320113500160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 26336739592192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record005_result⟩)
 (.leaf ⟨(30, 26393820832000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(30, 26393952952576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record007_result⟩)
 (.leaf ⟨(30, 26398254243904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record008_result⟩))
 (.branch 10
 (.leaf ⟨(30, 26398287274048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record009_result⟩)
 (.leaf ⟨(30, 26427221647616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 26428353642496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record011_result⟩)
 (.leaf ⟨(30, 26466873081856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 26467275653248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record013_result⟩)
 (.leaf ⟨(30, 26467275685888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(30, 26467345899552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 26468419637280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record016_result⟩)
 (.leaf ⟨(30, 26502779371521), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(30, 26532370808832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record018_result⟩)
 (.leaf ⟨(30, 26648730697728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record019_result⟩))
 (.branch 21
 (.leaf ⟨(30, 26777579716608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record020_result⟩)
 (.leaf ⟨(30, 26943986606208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 27015910527008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record022_result⟩)
 (.leaf ⟨(30, 27016762032640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 27016766226432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record024_result⟩)
 (.leaf ⟨(30, 27080063000576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(30, 27110997557248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record026_result⟩)
 (.leaf ⟨(30, 27121378459648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record027_result⟩))
 (.branch 29
 (.leaf ⟨(30, 27128693293056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record028_result⟩)
 (.leaf ⟨(30, 27130373144576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00042.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24960 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 24960 24990 :=
  block_of_table results 24960 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0770
