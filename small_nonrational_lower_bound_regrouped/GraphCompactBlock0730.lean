module
prelude
import GraphInputsRow30Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0730
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 1174210183424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record000_result⟩)
 (.leaf ⟨(30, 1174283583520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 1214009868544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 1255818756160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record003_result⟩)
 (.leaf ⟨(30, 1347147596032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 1364327464960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 1422317944832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record006_result⟩)
 (.leaf ⟨(30, 1484318114048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 1507739107328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 1587196002560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record009_result⟩)
 (.leaf ⟨(30, 1689411191040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 1689679593728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record011_result⟩)
 (.leaf ⟨(30, 1689679659008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 1693972463872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 1697195757824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record014_result⟩)
 (.leaf ⟨(30, 1702289801472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(30, 1702293963008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 1702294028288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record017_result⟩)
 (.leaf ⟨(30, 1723972223232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(30, 1723972288512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 1725247262976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record020_result⟩)
 (.leaf ⟨(30, 1727864570112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 1728265093376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record022_result⟩)
 (.leaf ⟨(30, 1728265158656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 1729408012544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record024_result⟩)
 (.branch 26
 (.leaf ⟨(30, 1736454537216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record025_result⟩)
 (.leaf ⟨(30, 1736586592512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(30, 1736586657792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 1736850898944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record028_result⟩)
 (.leaf ⟨(30, 1737729511680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(30, 1774639382529), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 1805171851520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record031_result⟩)
 (.leaf ⟨(30, 1859322446080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(30, 1861402820864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record033_result⟩)
 (.branch 35
 (.leaf ⟨(30, 1874285592832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record034_result⟩)
 (.leaf ⟨(30, 1876774879232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(30, 1877718663168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record036_result⟩)
 (.branch 38
 (.leaf ⟨(30, 1894646874112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record037_result⟩)
 (.leaf ⟨(30, 1894886211840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(30, 1907521257728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record039_result⟩)
 (.branch 41
 (.leaf ⟨(30, 1907525484544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record040_result⟩)
 (.leaf ⟨(30, 1907649153024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(30, 1912065753856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record042_result⟩)
 (.branch 44
 (.leaf ⟨(30, 1912090918912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record043_result⟩)
 (.leaf ⟨(30, 1919850578176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23617 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 23617 23662 :=
  block_of_table results 23617 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0730
