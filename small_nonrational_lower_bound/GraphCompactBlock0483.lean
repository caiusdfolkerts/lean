module
prelude
import GraphInputsRow29Part00049Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0483
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 8521370571008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 8526064288000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record001_result⟩)
 (.leaf ⟨(29, 8526076317696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 8534905913344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 8538533529616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record004_result⟩)
 (.leaf ⟨(29, 8538949173376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 8538954928128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 8539066339456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record007_result⟩)
 (.leaf ⟨(29, 8539883962368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 8540139815552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 8543495258640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record010_result⟩)
 (.leaf ⟨(29, 8547790766080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 8615704559872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 8615842873344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record013_result⟩)
 (.leaf ⟨(29, 8616509702656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 8684424020224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 8727398844416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record016_result⟩)
 (.leaf ⟨(29, 8727910549512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 8727927194120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 8727935844352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record019_result⟩)
 (.leaf ⟨(29, 8731945402368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(29, 8736525516800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record021_result⟩)
 (.branch 23
 (.leaf ⟨(29, 8740803706880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record022_result⟩)
 (.leaf ⟨(29, 8744574451712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(29, 8745090418688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record024_result⟩)
 (.branch 26
 (.leaf ⟨(29, 8745358983168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record025_result⟩)
 (.leaf ⟨(29, 8749125206016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(29, 8757975187456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record027_result⟩)
 (.branch 29
 (.leaf ⟨(29, 8834083029248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record028_result⟩)
 (.leaf ⟨(29, 8836163404032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(29, 8840458354944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record030_result⟩)
 (.branch 32
 (.leaf ⟨(29, 8840726757632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record031_result⟩)
 (.leaf ⟨(29, 8840733098048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(29, 8870522093824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record033_result⟩)
 (.branch 35
 (.leaf ⟨(29, 8874682843392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record034_result⟩)
 (.leaf ⟨(29, 8874817044736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(29, 8874821206272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record036_result⟩)
 (.branch 38
 (.leaf ⟨(29, 8883406946560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record037_result⟩)
 (.leaf ⟨(29, 8906432610560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(29, 8910324957440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record039_result⟩)
 (.branch 41
 (.leaf ⟨(29, 8910593360128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record040_result⟩)
 (.leaf ⟨(29, 8910593425408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(29, 8912875036928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record042_result⟩)
 (.branch 44
 (.leaf ⟨(29, 8918914859264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record043_result⟩)
 (.leaf ⟨(29, 8918914924544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(29, 8919183294592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record045_result⟩)
 (.branch 47
 (.leaf ⟨(29, 8919317495936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record046_result⟩)
 (.leaf ⟨(29, 8921464971392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00049.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21158 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 21158 21206 :=
  block_of_table results 21158 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0483
