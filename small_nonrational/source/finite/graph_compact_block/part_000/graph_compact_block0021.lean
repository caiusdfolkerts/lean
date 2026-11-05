module
prelude
import GraphInputsRow16Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0021
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 23376610541568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_result⟩)
 (.leaf ⟨(16, 23377141104640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 23377147346944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 23385468846080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record003_result⟩)
 (.leaf ⟨(16, 23404562383104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(16, 23420512321536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record005_result⟩)
 (.leaf ⟨(16, 23420543205632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_result⟩))
 (.branch 8
 (.leaf ⟨(16, 23421601923072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 23421807386624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record008_result⟩)
 (.leaf ⟨(16, 23424805191680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 23424838221824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_result⟩)
 (.leaf ⟨(16, 23424905322496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 23436774637824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 23451799683328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record013_result⟩)
 (.leaf ⟨(16, 23453492592640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(16, 23456092553472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 23470010302720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record016_result⟩)
 (.leaf ⟨(16, 23472553099520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(16, 23491529211904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 23522077851648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_result⟩)
 (.leaf ⟨(16, 23525718179840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 23525759012864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record021_result⟩)
 (.leaf ⟨(16, 23679842943232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 23731071156480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record023_result⟩)
 (.branch 25
 (.leaf ⟨(16, 23731339559168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record024_result⟩)
 (.leaf ⟨(16, 23731351068672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(16, 23763655655424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_result⟩)
 (.leaf ⟨(16, 23766776217600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record027_result⟩))
 (.branch 29
 (.leaf ⟨(16, 23766784540672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 23937095336192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record029_result⟩)
 (.leaf ⟨(16, 23955851739392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 23971491807232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_result⟩)
 (.leaf ⟨(16, 23972531994624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 23984265527552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 23984331587840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record034_result⟩)
 (.leaf ⟨(16, 23987947602176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(16, 24004623630592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 24004627857408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record037_result⟩)
 (.leaf ⟨(16, 24004635140096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(16, 24004857962752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record039_result⟩)
 (.branch 41
 (.leaf ⟨(16, 24004866351104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record040_result⟩)
 (.leaf ⟨(16, 24005377789984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record041_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1321 + i))) 0 42 :=
  interval_of_check _ 0 42 (by decide +kernel)

public theorem complete : Block 1321 1363 :=
  block_of_table results 1321 42 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0021
