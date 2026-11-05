module
prelude
import GraphInputsRow30Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0755
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 13350445531264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 13350445563904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record001_result⟩)
 (.leaf ⟨(30, 13350446571648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 13350515777568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 13351589515296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record004_result⟩)
 (.leaf ⟨(30, 13377221115904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 13377359380480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 13383682236544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record007_result⟩)
 (.leaf ⟨(30, 13385949249537), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 13523310641280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record009_result⟩)
 (.leaf ⟨(30, 13660749594624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 13745263312928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record011_result⟩)
 (.leaf ⟨(30, 13752779477024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(30, 13753043718176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 13762731974784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record014_result⟩)
 (.leaf ⟨(30, 13890486804736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(30, 13890486870016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record016_result⟩)
 (.leaf ⟨(30, 13899076739200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record017_result⟩))
 (.branch 19
 (.leaf ⟨(30, 13899936104448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record018_result⟩)
 (.leaf ⟨(30, 13900394299648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(30, 13900405809152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record020_result⟩)
 (.branch 22
 (.leaf ⟨(30, 14027929423904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record021_result⟩)
 (.leaf ⟨(30, 14294884909088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(30, 14295019110432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record023_result⟩)
 (.leaf ⟨(30, 14298240323616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record024_result⟩))
 (.branch 26
 (.leaf ⟨(30, 14298504564768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record025_result⟩)
 (.leaf ⟨(30, 14302797434912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00027.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24394 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 24394 24421 :=
  block_of_table results 24394 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0755
