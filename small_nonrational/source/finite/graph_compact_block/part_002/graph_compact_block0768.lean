module
prelude
import GraphInputsRow30Part00040Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0768
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 25375809765632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record000_result⟩)
 (.leaf ⟨(30, 25375946113024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 25375954436096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 25376078233600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record003_result⟩)
 (.leaf ⟨(30, 25376086556672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 25376350797824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record005_result⟩)
 (.leaf ⟨(30, 25376546897920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 25377620115456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 25432684560640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record008_result⟩)
 (.leaf ⟨(30, 25433320521728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 25444529225984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record010_result⟩)
 (.leaf ⟨(30, 25444663492608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 25444671815680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 25445066096640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record013_result⟩)
 (.leaf ⟨(30, 25445132156928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 25445569413376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record015_result⟩)
 (.leaf ⟨(30, 25446205374464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 25447715848448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 25513248751616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record018_result⟩)
 (.leaf ⟨(30, 25570491039744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 25576564867328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record020_result⟩)
 (.leaf ⟨(30, 25582106574848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 25582302674944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record022_result⟩)
 (.branch 24
 (.leaf ⟨(30, 25583375892480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record023_result⟩)
 (.leaf ⟨(30, 25642097770496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 25659277574144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record025_result⟩)
 (.leaf ⟨(30, 25659409694720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 25702227263744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 25704441905152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record028_result⟩)
 (.leaf ⟨(30, 25704978710528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(30, 25706522279936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record030_result⟩)
 (.leaf ⟨(30, 25706662723584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record031_result⟩))
 (.branch 33
 (.leaf ⟨(30, 25707059085312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 25719407132672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record033_result⟩)
 (.leaf ⟨(30, 25722593755136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(30, 25739757944832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record035_result⟩)
 (.branch 37
 (.leaf ⟨(30, 25739898388480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record036_result⟩)
 (.leaf ⟨(30, 25740294750208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(30, 25740410355712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record038_result⟩)
 (.branch 40
 (.leaf ⟨(30, 25769821618432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record039_result⟩)
 (.leaf ⟨(30, 25771970199552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00040.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24891 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 24891 24932 :=
  block_of_table results 24891 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0768
