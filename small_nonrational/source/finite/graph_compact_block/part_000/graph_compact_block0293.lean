module
prelude
import GraphInputsRow25Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0293
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 4521136848896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 4553943646464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record001_result⟩)
 (.leaf ⟨(25, 4658498142464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(25, 4953754140704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record003_result⟩)
 (.leaf ⟨(25, 4958047010848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record004_result⟩))
 (.branch 6
 (.leaf ⟨(25, 4966632751136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record005_result⟩)
 (.leaf ⟨(25, 5025405935872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(25, 5025674395680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record007_result⟩)
 (.leaf ⟨(25, 5089830445312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record008_result⟩))
 (.branch 10
 (.leaf ⟨(25, 5104109453312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record009_result⟩)
 (.leaf ⟨(25, 5123505979392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(25, 5138460737792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record011_result⟩)
 (.leaf ⟨(25, 5140677459968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record012_result⟩))
 (.branch 14
 (.leaf ⟨(25, 5140685783040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record013_result⟩)
 (.leaf ⟨(25, 5140950024192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(25, 5279332696065), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 5317987409920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record016_result⟩)
 (.leaf ⟨(25, 5363946520832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(25, 5397029388544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record018_result⟩)
 (.leaf ⟨(25, 5397186412544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record019_result⟩))
 (.branch 21
 (.leaf ⟨(25, 5397297791232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_result⟩)
 (.leaf ⟨(25, 5397310081024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(25, 5535820710144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record022_result⟩)
 (.leaf ⟨(25, 5537901084928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record023_result⟩))
 (.branch 25
 (.leaf ⟨(25, 5571135242272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record024_result⟩)
 (.leaf ⟨(25, 5829088509953), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(25, 5829549948928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record026_result⟩)
 (.leaf ⟨(25, 5863448256512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record027_result⟩))
 (.branch 29
 (.leaf ⟨(25, 5877817999616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record028_result⟩)
 (.leaf ⟨(25, 5877826387968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(25, 5878334128384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 5899137745152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record031_result⟩)
 (.leaf ⟨(25, 5899406213120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(25, 5899414536192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record033_result⟩)
 (.leaf ⟨(25, 5899942887936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record034_result⟩))
 (.branch 36
 (.leaf ⟨(25, 5899951276032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record035_result⟩)
 (.leaf ⟨(25, 6051116122368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(25, 6051116187648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record037_result⟩)
 (.leaf ⟨(25, 6051218854144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_result⟩))
 (.branch 40
 (.leaf ⟨(25, 6065781477632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record039_result⟩)
 (.leaf ⟨(25, 6066141233152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(25, 6067324981264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record041_result⟩)
 (.leaf ⟨(25, 6086531252480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record042_result⟩))
 (.branch 44
 (.leaf ⟨(25, 6086531317760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record043_result⟩)
 (.leaf ⟨(25, 6086534893824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record044_result⟩)))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf ⟨(25, 6087587823872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record045_result⟩)
 (.leaf ⟨(25, 6087587889152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record046_result⟩))
 (.branch 48
 (.leaf ⟨(25, 6099416170496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record047_result⟩)
 (.leaf ⟨(25, 6099537233936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(25, 6100610973697), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record049_result⟩)
 (.leaf ⟨(25, 6339585640464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record050_result⟩))
 (.branch 52
 (.leaf ⟨(25, 6378844323840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record051_result⟩)
 (.leaf ⟨(25, 6379100340480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record052_result⟩))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf ⟨(25, 6379368808448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record053_result⟩)
 (.leaf ⟨(25, 6379377131520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record054_result⟩))
 (.branch 56
 (.leaf ⟨(25, 6379905483264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record055_result⟩)
 (.leaf ⟨(25, 6379913871360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record056_result⟩)))
 (.branch 59
 (.branch 58
 (.leaf ⟨(25, 6413204062208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record057_result⟩)
 (.leaf ⟨(25, 6425565003776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record058_result⟩))
 (.branch 60
 (.leaf ⟨(25, 6425825018112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record059_result⟩)
 (.leaf ⟨(25, 6425837307904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record060_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12411 + i))) 0 61 :=
  interval_of_check _ 0 61 (by decide +kernel)

public theorem complete : Block 12411 12472 :=
  block_of_table results 12411 61 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0293
