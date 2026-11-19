module
prelude
import GraphInputsRow24Part00103Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0219
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 25705934503936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 25705949962304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record001_result⟩)
 (.leaf ⟨(24, 25706654335744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 25707056988736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 25718365110336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record004_result⟩)
 (.leaf ⟨(24, 25718432211008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 25718435088384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 25735597457408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record007_result⟩)
 (.leaf ⟨(24, 25735603699712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 25735605520384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record009_result⟩)
 (.leaf ⟨(24, 25739881744384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 25769887940864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record011_result⟩)
 (.leaf ⟨(24, 25769890086912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 25769896329216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 25769898149888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record014_result⟩)
 (.leaf ⟨(24, 25769964210176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 25770005367040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record016_result⟩)
 (.leaf ⟨(24, 25770357694528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 25770360571904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record018_result⟩)
 (.leaf ⟨(24, 25772085610752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(24, 25772093999104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 25772102255360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record021_result⟩)
 (.leaf ⟨(24, 25772488263744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 25772504908352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record023_result⟩)
 (.leaf ⟨(24, 25772622348808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 25774174373888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record025_result⟩)
 (.leaf ⟨(24, 25787052984320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10994 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 10994 11021 :=
  block_of_table results 10994 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0219
