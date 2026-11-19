module
prelude
import GraphInputsRow24Part00089Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0205
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24681633546816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24741319086208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record001_result⟩)
 (.leaf ⟨(24, 24741335601280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 24742413303808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 24742541197568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record004_result⟩)
 (.leaf ⟨(24, 24742648090880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 24743050743872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 24743415976064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record007_result⟩)
 (.leaf ⟨(24, 24748980502784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 24748986745088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record009_result⟩)
 (.leaf ⟨(24, 24748986810368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 24749087396096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record011_result⟩)
 (.leaf ⟨(24, 24749248970752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 24749258317888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 24749291868224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record014_result⟩)
 (.leaf ⟨(24, 24757607076096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 24777956327680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record016_result⟩)
 (.leaf ⟨(24, 24777960554496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 24778484221968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record018_result⟩)
 (.leaf ⟨(24, 24779012899072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(24, 24779017060608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 24779017125888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record021_result⟩)
 (.leaf ⟨(24, 24779146985728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 24779557961729), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record023_result⟩)
 (.leaf ⟨(24, 24782519681280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 24782519746560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record025_result⟩)
 (.leaf ⟨(24, 24782521241856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10738 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 10738 10765 :=
  block_of_table results 10738 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0205
