module
prelude
import GraphInputsRow26Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0326
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 6927650160640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 6927654322176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record001_result⟩)
 (.leaf ⟨(26, 6929069932544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 6929730535424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 6929734696960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record004_result⟩)
 (.leaf ⟨(26, 6933362802688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 6936483364864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 6936545263616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record007_result⟩)
 (.leaf ⟨(26, 6936549425152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 6968695619584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 6968757518336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record010_result⟩)
 (.leaf ⟨(26, 6968889638912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 6975316582656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 6977312950528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record013_result⟩)
 (.leaf ⟨(26, 6977338048512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 6977470169088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 6977858046080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record016_result⟩)
 (.leaf ⟨(26, 6979616604160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 6979669985536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 6979880845312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record019_result⟩)
 (.leaf ⟨(26, 6979938420864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 6982287228929), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 6983830735104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record022_result⟩)
 (.leaf ⟨(26, 6984173715456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(26, 6986447978497), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 6998930228224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record025_result⟩)
 (.leaf ⟨(26, 6999454515840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(26, 7003078557952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 7003082784768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record028_result⟩)
 (.leaf ⟨(26, 7003086946304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 7003090977792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 7003487339520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record031_result⟩)
 (.leaf ⟨(26, 7003615265408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(26, 7003883700736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 7033120129024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record034_result⟩)
 (.leaf ⟨(26, 7033186189312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 7046575425664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 7048655800448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record037_result⟩)
 (.leaf ⟨(26, 7055167471616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(26, 7072076791808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 7072605274112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record040_result⟩)
 (.leaf ⟨(26, 7074016722944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(26, 7074025046016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 7074148843520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record043_result⟩)
 (.leaf ⟨(26, 7074157166592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(26, 7074617507840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record045_result⟩)
 (.branch 47
 (.leaf ⟨(26, 7089460101120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record046_result⟩)
 (.leaf ⟨(26, 7147985928576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00010.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14571 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 14571 14619 :=
  block_of_table results 14571 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0326
