module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00021Data
public import GraphInputsRow16Part00021Frames
public import GraphInputsRow16Part00021Leaves
public import GraphInputsRow16Part00021Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5766400890382581760, 6755399441055744, 18014471523926016, 1008806316530991104, 36028797018963968]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6827542929318346752, 17596481011712, 2252899593748480, 1688849860263936, 4503599644147712]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5908804138568777728, 18014471523926016, 578713651628736512, 5066549866004480, 325385073077518336, 21990232555520]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1736805084064382976, 4611686027017322496, 325385073077518336, 104152956928, 162129586585337856]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5766963843557228544, 5066549580791808, 1008806316530991104, 18014468302700544, 37154696925806592]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5766962709266432000, 104152956928, 1688849860263936, 576461851815051264, 4503600046800896, 486388759756013568]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4616838356217626624, 578713651628736512, 1152921506754330624, 37172289111851008, 108447924224, 450359962737049600]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5764690118707249152, 7318349662912512, 1008806316530991104, 54060792009457664, 1130297986908160]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1064006231628185600, 103087603712, 7318349662912512, 5764607523105538048, 3298669101056, 70368744177664]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1062880434775392256, 1688849893818368, 5764607523105538048, 3298937536512, 4573968371548160, 2251799813685248]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4618541503990464512, 1008806316530991104, 1152921506754330624, 1693247940329472, 104152956928, 54043195528445952]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1722999669522432, 4573968371548160, 5764607523034234880, 578712552117108736, 486388759756013568, 71949090816]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [306274598305923072, 5764607523101343744, 37159094972317696, 720575940379279360, 4573968371548160, 2814749767106560]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5764634047942754304, 4573968639983616, 3298534883328, 1693247906775040, 486388759756013568, 578712552117108736]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2219180633547079680, 105235087360, 5066549849227264, 4611756387242868736, 2199023255552]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1190669969134714880, 450359962737049600, 4611756387242868736, 3298803318784, 578712552117108736, 105235087360, 4503599627370496]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c26 c11
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c27 c10
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c29 c4
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002
def vertexColumn : Fields := ⟨10, (certNat% 2)⟩
def kindColumn : Fields := ⟨3, (certNat% 3)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 1153068839164968960, 27303072774488064, 61572919590912, 2341871806232657920, 72057594591576064]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4693612855675584512, 1170940301162840064, 2341880602325680128, (certNat% 5), 35600983916544, 142936511610880]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 4612248968380809216, 2216337342464, 1170935903116328960, 281474976710656]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2423143695114043392, 1152923707925069824, 154627211264, 18295873620410368, (certNat% 7), 4612248968380809216]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [108148510070669312, (certNat% 8), 3458905251308896256, 4612248968380809216, 27303072774488064, 6597203984384]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3476988279394402304, 117093590848503808, 17414750208, (certNat% 9), 4612248968380809216, 281474976710656]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 2491081031680, 117093590848503808, 3458905251308896256, 18295873653964800, 4398046511104]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4648339884413550592, (certNat% 8), 3458905251308896256, 81064793292668928, 6597203984384, 18295873519747072]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3458973945884049408, 117093590311632896, 18295873620410368, 21474836480, (certNat% 11), 2814749767106560]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 18004502904832, 2341871806232657920, 27303072774488064, 1152923707925069824, 4415360598016]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2344308401602822144, 81064793829539840, (certNat% 13), 18038862643200, 844424963686400, 1170940301162840064, 2220632309760]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006
def vertexColumn : Fields := ⟨10, (certNat% 14)⟩
def kindColumn : Fields := ⟨3, (certNat% 15)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6825768453668864, 54183967376539648, (certNat% 16), (certNat% 17), 3857014849536, 30856118796288, 132120576]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010
def vertexColumn : Fields := ⟨10, (certNat% 18)⟩
def kindColumn : Fields := ⟨3, (certNat% 19)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1179952390585974784, 108156759801069568, 432909063936802816, 1795162112, 175921860444160, 5629499534213120]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1226289720795856896, 481036337152, 5136918324969472, 63050403373121536, 432346113983381504]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1162078310453215232, 420906795008, 54043195528445952, 76666746781564928, 432909063936802816, 1125899906842624]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [438609426132238336, 1152930300699869184, 63050394783186944, 72092778410016768, 140737488355328]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [510702057464791040, 9007345283629056, 149533623320576, 54043195528445952, 1152921504942391296, 671088640]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1153493253165678592, 246290638176256, 63050403373121536, 364791569817010176, 144115943990099968, 1125901517455360, 275012124672]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019
def vertexColumn : Fields := ⟨10, (certNat% 20)⟩
def kindColumn : Fields := ⟨3, (certNat% 21)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [639514461186555904, 1225119836133130240, 4612249019920416768, 481036337152, 288283702465658880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4621257258955702272, 3298669101056, 54043195528445952, 175924007927808, 2017630225248026624, 72057598332895232]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [63050395194228736, 2017630225248026624, 4612249011334676480, 72198337968734208, 481086668800, 3865537675264, 35184372088832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record019
