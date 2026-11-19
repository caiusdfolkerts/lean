module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00168Data
public import GraphInputsRow24Part00168Frames
public import GraphInputsRow24Part00168Leaves
public import GraphInputsRow24Part00168Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 34635086036992, (certNat% 5), 257698037760, 211119117434880]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004
def vertexColumn : Fields := ⟨10, (certNat% 6)⟩
def kindColumn : Fields := ⟨3, (certNat% 7)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), 28587306516480, (certNat% 11), 54043195578777600, 127506841600]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005
def vertexColumn : Fields := ⟨10, (certNat% 12)⟩
def kindColumn : Fields := ⟨3, (certNat% 13)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 506906804224, (certNat% 17)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 15), (certNat% 16), 506973913088, (certNat% 17)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 1037939211501568, (certNat% 21), 432345564227567616]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 546457279004672, (certNat% 24), (certNat% 25), (certNat% 26)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 1037939211501568, (certNat% 28), 432345564227567616, 235149459456]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 21), (certNat% 30), (certNat% 31), 432345564462448640, 235149459456, 1108307720798208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006
def vertexColumn : Fields := ⟨10, (certNat% 32)⟩
def kindColumn : Fields := ⟨3, (certNat% 33)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 206708186021888, (certNat% 35), 13546827679130451968, (certNat% 36), (certNat% 37)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 15765897230680064, (certNat% 39), 12898309332789100544, 288234776347803648, 193514096820224]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 216176080648667136, (certNat% 41), (certNat% 42), 193514046488576, 12682136550675316736]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46), 16888498602639360, (certNat% 47)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), 7036874417766400, 3674937295934324736, (certNat% 50)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 285873023221760, (certNat% 52), (certNat% 49)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 57174604644352, (certNat% 52), (certNat% 49)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 50), (certNat% 52), (certNat% 55)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), 53876069761024, 2533274790395904, (certNat% 52), (certNat% 49)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 59), 57174606741504, 3458764513820540928]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 52), (certNat% 49), 7036874417766400, (certNat% 61)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 21990234652672, (certNat% 63), (certNat% 59), 3458764513820540928]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 2522015791327477760, (certNat% 52), (certNat% 49), (certNat% 61)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 49), 2255098348568576, 3674937295934324736, (certNat% 61)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 45), 202310139510784, 19140298416324608, (certNat% 68), 15765897230680064]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 68), (certNat% 36), 196812581371904, 576469548396445696, 12682136550675316736]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 12898309332789100544, (certNat% 72), 15765897230680064, (certNat% 61)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 44), (certNat% 74), 15765897230680064, 193514046488576, 12898309332789100544]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 50), (certNat% 76), 56075093016576, 6755399441055744]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), 56075093016576, (certNat% 80), (certNat% 81)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), 15765897230680064, 3458764513822638080, 193514046488576, (certNat% 68)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 85), 16888498602639360, (certNat% 86), 4035225266123964416, (certNat% 68), 196812581371904]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c33 c26
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c34 c25
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c35 c24
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c36 c23
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c37 c22
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c38 c3
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c39 c3
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c40 c2
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c41 c1
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c42 c0
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c43 c0
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007
def vertexColumn : Fields := ⟨10, (certNat% 87)⟩
def kindColumn : Fields := ⟨3, (certNat% 88)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 90), 527765585526784, 17293822569102704640, (certNat% 91), (certNat% 92)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010
def vertexColumn : Fields := ⟨10, (certNat% 93)⟩
def kindColumn : Fields := ⟨3, (certNat% 94)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 96), (certNat% 97), 4363343175352320, (certNat% 98), 4362076160, 61573053808640]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record010
