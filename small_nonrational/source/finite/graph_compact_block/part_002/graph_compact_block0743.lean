module
prelude
import GraphInputsRow30Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0743
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 7598074103808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record000_result⟩)
 (.leaf ⟨(30, 7598082360064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 7598355054592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 7598363377664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record003_result⟩)
 (.leaf ⟨(30, 7598602453512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 7598602780672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record005_result⟩)
 (.leaf ⟨(30, 7607200776192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 7611241988096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 7611353432064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record008_result⟩)
 (.leaf ⟨(30, 7614977179904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 7615782322688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record010_result⟩)
 (.leaf ⟨(30, 7620079386624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 7623566950916), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 7623567082496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record013_result⟩)
 (.leaf ⟨(30, 7623843774464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(30, 7624103952384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 7699980910848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record016_result⟩)
 (.leaf ⟨(30, 7702127345920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(30, 7735412556032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 7749876350976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record019_result⟩)
 (.leaf ⟨(30, 7753087615232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record020_result⟩))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 7784168980480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record021_result⟩)
 (.leaf ⟨(30, 7785299869952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 7821953335296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record023_result⟩)
 (.branch 25
 (.leaf ⟨(30, 7890538594304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record024_result⟩)
 (.leaf ⟨(30, 8019387613184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record025_result⟩))))
 (.branch 29
 (.branch 27
 (.leaf ⟨(30, 8027964965504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record026_result⟩)
 (.branch 28
 (.leaf ⟨(30, 8041454141696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record027_result⟩)
 (.leaf ⟨(30, 8045883032320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(30, 8046164049920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record029_result⟩)
 (.branch 31
 (.leaf ⟨(30, 8156822372352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record030_result⟩)
 (.leaf ⟨(30, 8165540233216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record031_result⟩)))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf ⟨(30, 8173465370624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record032_result⟩)
 (.leaf ⟨(30, 8173993852928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record033_result⟩))
 (.branch 35
 (.leaf ⟨(30, 8184337072128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record034_result⟩)
 (.branch 36
 (.leaf ⟨(30, 8184873877504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record035_result⟩)
 (.leaf ⟨(30, 8189034627072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record036_result⟩))))
 (.branch 40
 (.branch 38
 (.leaf ⟨(30, 8197083561984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record037_result⟩)
 (.branch 39
 (.leaf ⟨(30, 8197356126208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record038_result⟩)
 (.leaf ⟨(30, 8197752487936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(30, 8247570891008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record040_result⟩)
 (.branch 42
 (.leaf ⟨(30, 8247570956288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record041_result⟩)
 (.leaf ⟨(30, 8247970894080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00015.record042_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24030 + i))) 0 43 :=
  interval_of_check _ 0 43 (by decide +kernel)

public theorem complete : Block 24030 24073 :=
  block_of_table results 24030 43 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0743
