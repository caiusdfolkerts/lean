module
prelude
import GraphInputsRow24Part00047Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0163
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 19179786797056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 19179793039360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record001_result⟩)
 (.leaf ⟨(24, 19179982831872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 19184077521152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 19184085909504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record004_result⟩)
 (.leaf ⟨(24, 19184143581440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 19192465080576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 19192867733568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record007_result⟩)
 (.leaf ⟨(24, 19245255704704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 19247402139776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 19280670834816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record010_result⟩)
 (.leaf ⟨(24, 19281865638144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 19281865703424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 19285890105600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record013_result⟩)
 (.leaf ⟨(24, 19286158508288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 19286158573568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 19286160589056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record016_result⟩)
 (.leaf ⟨(24, 19289381802240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 19294480007424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 19294480072704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record019_result⟩)
 (.leaf ⟨(24, 19298105954368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(24, 19320182735104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 19320451137792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record022_result⟩)
 (.leaf ⟨(24, 19320451203072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(24, 19321594056960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 19328772636928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record025_result⟩)
 (.leaf ⟨(24, 19328772702208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(24, 19389170598144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 19389170663424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record028_result⟩)
 (.leaf ⟨(24, 19390311436544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(24, 19397357895936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 19397357961216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record031_result⟩)
 (.leaf ⟨(24, 19397492162560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(24, 19397756403712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 19398632935680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_result⟩)
 (.leaf ⟨(24, 19398903468096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 19435410685953), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 19451508490496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record037_result⟩)
 (.leaf ⟨(24, 19451516878848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 19457890123776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 19469758923008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record040_result⟩)
 (.leaf ⟨(24, 19471041298432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(24, 19475069927424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 19491125788672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record043_result⟩)
 (.leaf ⟨(24, 19499822907648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(24, 19499835197440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record045_result⟩)
 (.branch 47
 (.leaf ⟨(24, 19504121839616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record046_result⟩)
 (.leaf ⟨(24, 19512573493248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9655 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 9655 9703 :=
  block_of_table results 9655 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0163
