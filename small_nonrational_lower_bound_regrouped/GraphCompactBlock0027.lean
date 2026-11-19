module
prelude
import GraphInputsRow16Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0027
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 27128496136448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record000_result⟩)
 (.leaf ⟨(16, 27130643677184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 27132724051968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 27140005363712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record003_result⟩)
 (.leaf ⟨(16, 27140071424000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(16, 27140301529344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record005_result⟩)
 (.leaf ⟨(16, 27147756437760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record006_result⟩))
 (.branch 8
 (.leaf ⟨(16, 27149902872832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 27158488613120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record008_result⟩)
 (.leaf ⟨(16, 27158497001472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 27159025483776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record010_result⟩)
 (.leaf ⟨(16, 27159033806848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 27159330619648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 27159339008000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record013_result⟩)
 (.leaf ⟨(16, 27159528800512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(16, 27159537188864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record015_result⟩)
 (.leaf ⟨(16, 27159797203200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record016_result⟩))
 (.branch 18
 (.leaf ⟨(16, 27159801430016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record017_result⟩)
 (.branch 19
 (.leaf ⟨(16, 27159808712704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record018_result⟩)
 (.leaf ⟨(16, 27160031535360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(16, 27162788765952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record020_result⟩)
 (.leaf ⟨(16, 27167082741760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record021_result⟩))
 (.branch 23
 (.leaf ⟨(16, 27168122929152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record022_result⟩)
 (.branch 24
 (.leaf ⟨(16, 27171243491328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record023_result⟩)
 (.leaf ⟨(16, 27171507732480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 27171516055552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record025_result⟩)
 (.leaf ⟨(16, 27172217618432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 27172283678720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 27172415799296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record028_result⟩)
 (.leaf ⟨(16, 27172513784064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(16, 27174364053504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record030_result⟩)
 (.leaf ⟨(16, 27174594158848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record031_result⟩))
 (.branch 33
 (.leaf ⟨(16, 27180992102656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record032_result⟩)
 (.branch 34
 (.leaf ⟨(16, 27183138537728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record033_result⟩)
 (.leaf ⟨(16, 27187702931712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 27187753257216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 27193854066944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record036_result⟩)
 (.leaf ⟨(16, 27193862455296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(16, 27194134889472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record038_result⟩)
 (.branch 40
 (.leaf ⟨(16, 27196074756352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record039_result⟩)
 (.leaf ⟨(16, 27206608945152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00027.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1579 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 1579 1620 :=
  block_of_table results 1579 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0027
