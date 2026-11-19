module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00012Data
public import GraphInputsRow24Part00012Frames
public import GraphInputsRow24Part00012Leaves
public import GraphInputsRow24Part00012Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record070
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070
def vertexColumn : Fields := ⟨10, hexnat% "e61743713c1f392b4b8a3ab1aa699a36966c5956358ce1b91e2785eb44e9c6699365391e715355351d4cd4b46d4749d1743db0f2338f13a4e5334f0ba2ccb4acab1ae1b46c9b16f0731d2785d1725c5743c8f13c1f4b11c4a9261990e0ba9134499194550b41da0cc318c8b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6da6db49b4da4db4d34924934d34d249369b49b692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10808a7c012044c00000", hexnat% "4000400080000002000000", 714684705538048, 824650498048, hexnat% "90000200400000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [585058815251054592, hexnat% "10800000000040000000", hexnat% "4000000200000000000000", hexnat% "4000a0000000000000", hexnat% "98000200000000000", 18014398509481984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10c982ce2b2445c00000", 140739635838976, 580964351930793984, hexnat% "4000000020000002000000", 824633720832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108082cc212045c00000", 9007749044109312, hexnat% "4000400000000000000000", 714684705538048, hexnat% "90810000000000000", 292057776128]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1080824c8160c7c00000", 45036546029518848, hexnat% "4000400000000000000000", hexnat% "90810000000000000", 609146621657088]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10800048000041800000", hexnat% "4000000204000000000000", 962072674304, 149535795970048, hexnat% "98810000000000000", 601450040262656, hexnat% "4000a0000002400000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00012.record070
