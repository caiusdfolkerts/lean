module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00063Data
public import GraphInputsRow24Part00063Frames
public import GraphInputsRow24Part00063Leaves
public import GraphInputsRow24Part00063Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020
def vertexColumn : Fields := ⟨10, hexnat% "2d4ad29c2f2b2a695a2eb46a9a9695a362d876a394e4b8ae8789e1783eb4559b1695954d52d4756354d4b49d1743da4e5354cb31cd4b4acab46c9b16e8791d2729c6785c9715c3723c4f07cb82b2520ea465190e0b8b12a4990e5452950d2342d50c530cd0b0ac1b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db49b4db6926da6db6d349269a4924924d249b492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48600060183cf8000000", 41658296553177088, 457946592968704, 7696581394432, 144185556820033536, hexnat% "880110000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8881102b44518e8000000", 422349904019456, hexnat% "400040108010000000", hexnat% "200000080000000000", hexnat% "40000000000400000000", 37383395344384]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "801000f46f9838000000", 422352051503104, hexnat% "210000000000000000", hexnat% "400000100000000000", hexnat% "808000200000040000000", hexnat% "40000000000400000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c8710255b5b0d8000000", 45035996810575872, 10995116277760, 70403103916032, 17179869184]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c85102140534d8000000", 70403640786944, 457946592968704, 63050394783186944, hexnat% "200000080000000000", 19791209299968]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8480102f50130f8000000", 175939040313344, hexnat% "600000000000000000", hexnat% "80100000440800000000", 29137058136064]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "848000011a1bcf8000000", 63050394783186944, 28587302322176, 145315854773387264, hexnat% "600000000000000000", hexnat% "80110000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "848400010013410000000", 457948740452352, 63050395320057856, hexnat% "80100004440800000000", hexnat% "10200000048000000", hexnat% "200000080000000000", 19791209299968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record020
