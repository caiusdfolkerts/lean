module
prelude
import GraphInputsRow29Part00050Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0484
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 8943400222976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record000_result⟩)
 (.leaf ⟨(29, 8943406465280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 8944849354816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 8951992205568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record003_result⟩)
 (.leaf ⟨(29, 8979174621248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 8979310804992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record005_result⟩)
 (.leaf ⟨(29, 8981460295936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 8987632304128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 8987902754944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record008_result⟩)
 (.leaf ⟨(29, 8990050230400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 9024544186400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record010_result⟩)
 (.leaf ⟨(29, 9118630813952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 9118899249280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 9125067063296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record013_result⟩)
 (.leaf ⟨(29, 9125073272960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(29, 9423448252672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 9423465548032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record016_result⟩)
 (.leaf ⟨(29, 9424580182272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(29, 9424848650240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 9425049886976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record019_result⟩)
 (.leaf ⟨(29, 9433438519424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record020_result⟩))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(29, 9433639821440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record021_result⟩)
 (.leaf ⟨(29, 9441156010016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record022_result⟩))
 (.branch 24
 (.leaf ⟨(29, 9475515744257), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record023_result⟩)
 (.branch 25
 (.leaf ⟨(29, 9501956645120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record024_result⟩)
 (.leaf ⟨(29, 9502151770112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record025_result⟩))))
 (.branch 29
 (.branch 27
 (.leaf ⟨(29, 9502157979776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record026_result⟩)
 (.branch 28
 (.leaf ⟨(29, 9502225080448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record027_result⟩)
 (.leaf ⟨(29, 9505580519456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(29, 9529597165824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record029_result⟩)
 (.branch 31
 (.leaf ⟨(29, 9529869795328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record030_result⟩)
 (.leaf ⟨(29, 9530134036480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record031_result⟩)))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf ⟨(29, 9530142359552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record032_result⟩)
 (.leaf ⟨(29, 9531350384640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record033_result⟩))
 (.branch 35
 (.leaf ⟨(29, 9535387435008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record034_result⟩)
 (.branch 36
 (.leaf ⟨(29, 9535393644672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record035_result⟩)
 (.leaf ⟨(29, 9537782317312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record036_result⟩))))
 (.branch 40
 (.branch 38
 (.leaf ⟨(29, 9539940253697), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record037_result⟩)
 (.branch 39
 (.leaf ⟨(29, 9634429538336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record038_result⟩)
 (.leaf ⟨(29, 9639395598464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(29, 9668789272577), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record040_result⟩)
 (.branch 42
 (.leaf ⟨(29, 9675221270656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record041_result⟩)
 (.leaf ⟨(29, 9794964488192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00050.record042_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21206 + i))) 0 43 :=
  interval_of_check _ 0 43 (by decide +kernel)

public theorem complete : Block 21206 21249 :=
  block_of_table results 21206 43 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0484
