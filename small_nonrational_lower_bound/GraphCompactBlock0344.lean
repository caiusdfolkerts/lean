module
prelude
import GraphInputsRow26Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0344
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 17461227356160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 17461995372544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record001_result⟩)
 (.leaf ⟨(26, 17464620482560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 17466156122112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 17469821419520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record004_result⟩)
 (.leaf ⟨(26, 17470349901824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 17493422833664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 17493695397888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record007_result⟩)
 (.leaf ⟨(26, 17494207365120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 17498368114688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 17501991927808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record010_result⟩)
 (.leaf ⟨(26, 17519171731456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 17523483640064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 17523752108032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record013_result⟩)
 (.leaf ⟨(26, 17523760431104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 17524272138240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 17532056635648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record016_result⟩)
 (.leaf ⟨(26, 17532593506304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 17532610150912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 17549236371972), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record019_result⟩)
 (.leaf ⟨(26, 17557847343104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 17566441406464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record021_result⟩)
 (.leaf ⟨(26, 17566969888768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 17583596240896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record023_result⟩)
 (.leaf ⟨(26, 17583612887040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(26, 17636819812736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 17702322274432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record026_result⟩)
 (.leaf ⟨(26, 17703123353856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(26, 17703127515392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 17703127580672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record029_result⟩)
 (.leaf ⟨(26, 17703255474432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(26, 17703263862784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 17704149926272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record032_result⟩)
 (.leaf ⟨(26, 17706415915264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(26, 17706617225344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 17708833931296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record035_result⟩)
 (.leaf ⟨(26, 17739633738048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(26, 17748219478336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record037_result⟩)
 (.branch 39
 (.leaf ⟨(26, 17748220518720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record038_result⟩)
 (.leaf ⟨(26, 17775135375616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(26, 17777551310880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record040_result⟩)
 (.branch 42
 (.leaf ⟨(26, 17783721115904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record041_result⟩)
 (.leaf ⟨(26, 17783725326400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(26, 17786737819904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 17787778007296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record044_result⟩)
 (.leaf ⟨(26, 17839761162496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(26, 17856395903232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record046_result⟩)
 (.leaf ⟨(26, 17856395968512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record047_result⟩))
 (.branch 49
 (.leaf ⟨(26, 17856532119808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record048_result⟩)
 (.leaf ⟨(26, 17856941031424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00028.record049_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15520 + i))) 0 50 :=
  interval_of_check _ 0 50 (by decide +kernel)

public theorem complete : Block 15520 15570 :=
  block_of_table results 15520 50 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0344
