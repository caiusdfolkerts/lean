module
prelude
import GraphInputsRow16Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0009
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 15213579735072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record000_result⟩)
 (.leaf ⟨(16, 15213596778496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 15213597818880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 15213919404032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record003_result⟩)
 (.leaf ⟨(16, 15213927597056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(16, 15214124867584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record005_result⟩)
 (.branch 7
 (.leaf ⟨(16, 15214125777920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record006_result⟩)
 (.leaf ⟨(16, 15256892047360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(16, 15256958042368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record008_result⟩)
 (.branch 10
 (.leaf ⟨(16, 15256958107648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record009_result⟩)
 (.leaf ⟨(16, 15256961163520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(16, 15257092308992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record011_result⟩)
 (.branch 13
 (.leaf ⟨(16, 15257354469376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record012_result⟩)
 (.leaf ⟨(16, 15257360711680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(16, 15259551170816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 15260132051200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record015_result⟩)
 (.leaf ⟨(16, 15260305654016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(16, 15260313001984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record017_result⟩)
 (.branch 19
 (.leaf ⟨(16, 15260574121984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record018_result⟩)
 (.leaf ⟨(16, 15260577243136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(16, 15260585037856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record020_result⟩)
 (.branch 22
 (.leaf ⟨(16, 15264490981632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record021_result⟩)
 (.leaf ⟨(16, 15264869072896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(16, 15264870048000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record023_result⟩)
 (.branch 25
 (.leaf ⟨(16, 15264870113280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record024_result⟩)
 (.leaf ⟨(16, 15269162918144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(16, 15277484417280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record026_result⟩)
 (.branch 28
 (.leaf ⟨(16, 15278021287936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record027_result⟩)
 (.leaf ⟨(16, 15278022328320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(16, 15285823406080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record029_result⟩)
 (.branch 31
 (.leaf ⟨(16, 15285830688768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record030_result⟩)
 (.leaf ⟨(16, 15285831599104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(16, 15286327051264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record032_result⟩)
 (.branch 34
 (.leaf ⟨(16, 15290243317760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record033_result⟩)
 (.leaf ⟨(16, 15292786835712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 15293443277056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 15294655563776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record036_result⟩)
 (.leaf ⟨(16, 15310623145984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(16, 15310895710208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record038_result⟩)
 (.branch 40
 (.leaf ⟨(16, 15510548840448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record039_result⟩)
 (.leaf ⟨(16, 15523427450880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(16, 15570676318208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record041_result⟩)
 (.branch 43
 (.leaf ⟨(16, 15579134099456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record042_result⟩)
 (.leaf ⟨(16, 15579603804160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(16, 15579670904832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record044_result⟩)
 (.branch 46
 (.leaf ⟨(16, 15579860762624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record045_result⟩)
 (.leaf ⟨(16, 15579869085696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00009.record046_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (721 + i))) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

public theorem complete : Block 721 768 :=
  block_of_table results 721 47 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0009
