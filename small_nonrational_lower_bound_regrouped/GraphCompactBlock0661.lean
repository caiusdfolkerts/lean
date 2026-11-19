module
prelude
import GraphInputsRow29Part00227Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0661
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 30789724045568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 30789724110848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record001_result⟩)
 (.leaf ⟨(29, 30789727166720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 30790126682240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record003_result⟩)
 (.leaf ⟨(29, 30790126714880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 30790127722624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record005_result⟩)
 (.leaf ⟨(29, 30790230478880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 30792005722368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record007_result⟩)
 (.leaf ⟨(29, 30792005787648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 30792038752512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record009_result⟩)
 (.leaf ⟨(29, 30792038817792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 30792274157696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record011_result⟩)
 (.leaf ⟨(29, 30792277303328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 30792310853664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record013_result⟩)
 (.leaf ⟨(29, 30793347375232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 30805155913760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record015_result⟩)
 (.leaf ⟨(29, 30805189464096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 30824009335040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record017_result⟩)
 (.leaf ⟨(29, 30825274417408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(29, 30825274482688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record019_result⟩)
 (.leaf ⟨(29, 30825290997760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record020_result⟩))
 (.branch 22
 (.leaf ⟨(29, 30825542852736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record021_result⟩)
 (.leaf ⟨(29, 30826393829632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(29, 30826398024192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record023_result⟩)
 (.leaf ⟨(29, 30826402217984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record024_result⟩))
 (.branch 26
 (.leaf ⟨(29, 30826599424128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record025_result⟩)
 (.leaf ⟨(29, 30826670587905), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(29, 30826860413184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record027_result⟩)
 (.leaf ⟨(29, 30826871922688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record028_result⟩))
 (.branch 30
 (.leaf ⟨(29, 30830695088128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record029_result⟩)
 (.leaf ⟨(29, 30830955102464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record030_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23186 + i))) 0 31 :=
  interval_of_check _ 0 31 (by decide +kernel)

public theorem complete : Block 23186 23217 :=
  block_of_table results 23186 31 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0661
