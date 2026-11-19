module
prelude
import GraphInputsRow31Part00085Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0873
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 17052135915520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record000_result⟩)
 (.leaf ⟨(31, 17052664332800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 17052672720896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record002_result⟩)
 (.leaf ⟨(31, 17060721655808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 17061258461184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record004_result⟩)
 (.leaf ⟨(31, 17061489672192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 17068200169488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record006_result⟩)
 (.leaf ⟨(31, 17068234178560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(31, 17120016531456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record008_result⟩)
 (.leaf ⟨(31, 17179886551296), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record009_result⟩))
 (.branch 11
 (.leaf ⟨(31, 17181219815424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record010_result⟩)
 (.leaf ⟨(31, 17190078119936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(31, 17197049186320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record012_result⟩)
 (.leaf ⟨(31, 17197066420224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record013_result⟩))
 (.branch 15
 (.leaf ⟨(31, 17197603225600), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record014_result⟩)
 (.leaf ⟨(31, 17198122795524), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26179 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 26179 26195 :=
  block_of_table results 26179 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0873
