module
prelude
import GraphInputsRow30Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0745
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 8332513511440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 8332799148032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record001_result⟩)
 (.leaf ⟨(30, 8334119862272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 8334128185344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 8402713444352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record004_result⟩)
 (.leaf ⟨(30, 8402837241856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 8474784169984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 8526076317696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record007_result⟩)
 (.leaf ⟨(30, 8538533529616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 8539066339456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 8539883962368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record010_result⟩)
 (.leaf ⟨(30, 8547790766080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 8727398844416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 8727910549512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record013_result⟩)
 (.leaf ⟨(30, 8727927194120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 8727935844352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 8731945402368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record016_result⟩)
 (.leaf ⟨(30, 8736525516800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 8740803706880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 8744574451712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record019_result⟩)
 (.leaf ⟨(30, 8745090418688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(30, 8745358983168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 8749125206016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record022_result⟩)
 (.leaf ⟨(30, 8874817044736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(30, 8910593425408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record024_result⟩)
 (.branch 26
 (.leaf ⟨(30, 8918914924544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record025_result⟩)
 (.leaf ⟨(30, 8919183294592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(30, 8921464971392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 8943402303744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record028_result⟩)
 (.leaf ⟨(30, 8979310804992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(30, 8987632304128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 8990050230400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record031_result⟩)
 (.leaf ⟨(30, 9024544186400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(30, 9118899249280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record033_result⟩)
 (.branch 35
 (.leaf ⟨(30, 9125067063296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record034_result⟩)
 (.leaf ⟨(30, 9423465548032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(30, 9441156010016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record036_result⟩)
 (.branch 38
 (.leaf ⟨(30, 9502225080448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record037_result⟩)
 (.leaf ⟨(30, 9505580519456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(30, 9530134036480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record039_result⟩)
 (.branch 41
 (.leaf ⟨(30, 9530142359552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record040_result⟩)
 (.leaf ⟨(30, 9539940253697), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(30, 9634429538336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record042_result⟩)
 (.branch 44
 (.leaf ⟨(30, 9794964488192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record043_result⟩)
 (.leaf ⟨(30, 9821118005248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(30, 9935679225856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record045_result⟩)
 (.leaf ⟨(30, 9941114949888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record046_result⟩))
 (.branch 48
 (.leaf ⟨(30, 9974602366976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record047_result⟩)
 (.leaf ⟨(30, 10010104954881), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00017.record048_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24092 + i))) 0 49 :=
  interval_of_check _ 0 49 (by decide +kernel)

public theorem complete : Block 24092 24141 :=
  block_of_table results 24092 49 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0745
