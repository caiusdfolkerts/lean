module
prelude
import GraphInputsSix0Part00085Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1050
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 32712781991936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 32713178353664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record001_result⟩)
 (.leaf ⟨(32, 32715051639040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(32, 32715060547584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record003_result⟩)
 (.leaf ⟨(32, 32715324788736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record004_result⟩))
 (.branch 6
 (.leaf ⟨(32, 32716142739456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record005_result⟩)
 (.leaf ⟨(32, 32717718684176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(32, 32725001043968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record007_result⟩)
 (.branch 9
 (.leaf ⟨(32, 32728053714976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record008_result⟩)
 (.leaf ⟨(32, 32729127191072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(32, 32730200932880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record010_result⟩)
 (.leaf ⟨(32, 32748190367744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record011_result⟩))
 (.branch 13
 (.leaf ⟨(32, 32780282003712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record012_result⟩)
 (.leaf ⟨(32, 32780352290816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(32, 32780360613888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record014_result⟩)
 (.branch 16
 (.leaf ⟨(32, 32780550471680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record015_result⟩)
 (.leaf ⟨(32, 32780558794752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(32, 32780600016896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record017_result⟩)
 (.leaf ⟨(32, 32781069721600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record018_result⟩))
 (.branch 20
 (.leaf ⟨(32, 32782411792640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record019_result⟩)
 (.leaf ⟨(32, 32783216935424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 32787797647616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record021_result⟩)
 (.leaf ⟨(32, 32787881328640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 32788334518272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record023_result⟩)
 (.leaf ⟨(32, 32788335558656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(32, 32788351033344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record025_result⟩)
 (.leaf ⟨(32, 32788854219008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record026_result⟩))
 (.branch 28
 (.leaf ⟨(32, 32789458059776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record027_result⟩)
 (.leaf ⟨(32, 32804960342048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00085.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34860 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 34860 34889 :=
  block_of_table results 34860 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1050
