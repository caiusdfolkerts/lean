module
prelude
import GraphInputsRow16Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0011
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 16607174725632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 16607703269632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record001_result⟩)
 (.leaf ⟨(16, 16607975899136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 16608240140288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record003_result⟩)
 (.leaf ⟨(16, 16608248463360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 16608512704512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record005_result⟩)
 (.leaf ⟨(16, 16610823831808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(16, 16611096461312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record007_result⟩)
 (.leaf ⟨(16, 16611360702464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record008_result⟩))
 (.branch 10
 (.leaf ⟨(16, 16611369025536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record009_result⟩)
 (.leaf ⟨(16, 16611591913472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(16, 16614349144064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record011_result⟩)
 (.leaf ⟨(16, 16623075328000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record012_result⟩))
 (.branch 14
 (.leaf ⟨(16, 16623706603776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record013_result⟩)
 (.leaf ⟨(16, 16623842951168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(16, 16623851274240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record015_result⟩)
 (.leaf ⟨(16, 16624074162176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016_result⟩))
 (.branch 18
 (.leaf ⟨(16, 16624610967552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record017_result⟩)
 (.leaf ⟨(16, 16640367460352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(16, 16644777771008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record019_result⟩)
 (.leaf ⟨(16, 16644786094080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record020_result⟩))
 (.branch 22
 (.leaf ⟨(16, 16648661114944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record021_result⟩)
 (.leaf ⟨(16, 16652830802176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 16652842311680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record023_result⟩)
 (.leaf ⟨(16, 16652974432256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 16655942426688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record025_result⟩)
 (.leaf ⟨(16, 16670047404288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(16, 16671587205376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record027_result⟩)
 (.leaf ⟨(16, 16687227273216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record028_result⟩))
 (.branch 30
 (.leaf ⟨(16, 16687499837440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record029_result⟩)
 (.leaf ⟨(16, 16688267460608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record030_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (823 + i))) 0 31 :=
  interval_of_check _ 0 31 (by decide +kernel)

public theorem complete : Block 823 854 :=
  block_of_table results 823 31 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0011
