module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00020Data
public import GraphInputsRow16Part00020Frames
public import GraphInputsRow16Part00020Leaves
public import GraphInputsRow16Part00020Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 3623990325149696, (certNat% 3), 1649267441664, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 9227468800, (certNat% 6), 299616918568960, 571746046443520, (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 7), (certNat% 9), 4787290807205888, (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 2392640381255680, 6322191859712, (certNat% 4), 4503599627370496]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 153122387330596864, (certNat% 13), 6896136929411072, 873012232454144, 36421322670080]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4215510233251840, (certNat% 7), 27021597764222976, (certNat% 14), (certNat% 15), 4787273627336704]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9007199221186560, (certNat% 16), (certNat% 7), (certNat% 4), (certNat% 17)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4219874020687872, (certNat% 18), (certNat% 19), 4785108963819520, (certNat% 4), (certNat% 6)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), 301815941824512, 1688918579740672, 6755442390728704, (certNat% 23)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064
def vertexColumn : Fields := ⟨10, (certNat% 24)⟩
def kindColumn : Fields := ⟨3, (certNat% 25)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), 13220446208, 6768868458496, 765328946626560, 6826336228212736]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record068
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068
def vertexColumn : Fields := ⟨10, (certNat% 28)⟩
def kindColumn : Fields := ⟨3, (certNat% 29)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4694031233796014080, 148620986726481920, 288247976927690752, 54043487586222080, 844562369085440, 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [220969329632477184, 288247968337756160, 4947802324992, 9147937816838144, 54641329853956096, 4612811918334230528]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [257706181672304640, 10133100503760896, 18049604356407296, 4899916394713317376, 558345748480, 17592186044416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [235039205347033088, 13651536370466816, 36072794663944192, 4899916394713317376, 1143492092887040, 8589934592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4901386055598473216, 18014677682356224, 36591746972385280, 220678580764409856, 9147937816838144, 4432943120384]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [230697503706578944, 54043487586222080, 4948607631360, 4612811918468448256, 288230384741646336, 35188667056128]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [221725459161808896, 288230384741646336, 4432943120384, 10133099161583616, 54043487586222080, 4611686568183201792]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4901518001288773632, 36600543065407488, 18014673387388928, 220678580764409856, 4432943120384, 9007200328482816]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [221118531561848832, 4899916394981752832, 36635727437496320, 10133100235325440, 18014694862225408, 4432943120384, 549755813888]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record068
