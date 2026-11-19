module
prelude
import GraphInputsRow30Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0757
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 15842542649344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record000_result⟩)
 (.leaf ⟨(30, 15842546810880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 15842658254848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 15851247895040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record003_result⟩)
 (.leaf ⟨(30, 16128415891456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 16493834699008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 16493834764288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record006_result⟩)
 (.leaf ⟨(30, 16494977618176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 16494977683456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 16494985482256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record009_result⟩)
 (.leaf ⟨(30, 16495002257424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(30, 16495109738752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 16496075997185), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record012_result⟩)
 (.leaf ⟨(30, 16496476585984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(30, 16502952562688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 16511499518080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record015_result⟩)
 (.leaf ⟨(30, 16511501631488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(30, 16512673386624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 16527189610752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record018_result⟩)
 (.leaf ⟨(30, 16531606079504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(30, 16531623247873), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record020_result⟩)
 (.branch 22
 (.leaf ⟨(30, 16531891716096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record021_result⟩)
 (.leaf ⟨(30, 16532675559680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(30, 16532948287488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record023_result⟩)
 (.leaf ⟨(30, 16533212430336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record024_result⟩))
 (.branch 26
 (.leaf ⟨(30, 16533220753408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record025_result⟩)
 (.branch 27
 (.leaf ⟨(30, 16536188227584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record026_result⟩)
 (.leaf ⟨(30, 16537373179904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(30, 16537381502976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record028_result⟩)
 (.branch 30
 (.leaf ⟨(30, 16544885379200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record029_result⟩)
 (.leaf ⟨(30, 16632420827136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(30, 16640391512064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 16648436220160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record032_result⟩)
 (.leaf ⟨(30, 16648572567552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(30, 16648580890624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record034_result⟩)
 (.branch 36
 (.leaf ⟨(30, 16648704688128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record035_result⟩)
 (.leaf ⟨(30, 16648713011200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(30, 16649173352448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record037_result⟩)
 (.branch 39
 (.leaf ⟨(30, 16650111812112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record038_result⟩)
 (.leaf ⟨(30, 16678037487616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(30, 16720379052032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record040_result⟩)
 (.branch 42
 (.leaf ⟨(30, 16721114038272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record041_result⟩)
 (.leaf ⟨(30, 16769851359488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(30, 16769863389184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record043_result⟩)
 (.branch 45
 (.leaf ⟨(30, 16769995509760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record044_result⟩)
 (.leaf ⟨(30, 16770253996160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00029.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24462 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 24462 24508 :=
  block_of_table results 24462 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0757
