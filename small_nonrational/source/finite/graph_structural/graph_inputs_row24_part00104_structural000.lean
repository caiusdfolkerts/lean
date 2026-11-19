module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00104Data
public import GraphInputsRow24Part00104Frames
public import GraphInputsRow24Part00104Leaves
public import GraphInputsRow24Part00104Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00104.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019
def vertexColumn : Fields := ⟨10, hexnat% "5b2b29c8f26a96a3aa9a369668d8b61d94e4b8ae1b91e27ab19c4f16a5693a699365658d4b51d54d4b4ad1b51d27723a8da398d6338e9394cd38ccb31ce8b62d4b32d2b2ac6b86d1b26c5b51e2749ca719e1745c9715c3743c8f13c2f07c5ca8a922685a498661590e1381ea869126459494651550d1341d"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6da49b4934926db6926d24d24d36da6db6db6db6d26d34db4d34d1249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "428010a21000328aa00000", hexnat% "600800000000000000", hexnat% "400810020000000000000000", hexnat% "18020000000000000000000", hexnat% "11000000000000000", hexnat% "440000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "404ed013a21000328aa00000", hexnat% "201800000000000000", hexnat% "10000400000000000000000", hexnat% "8020000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "404c9013ba1000328aa00000", hexnat% "240000000000000000000", hexnat% "600000000000000000", hexnat% "18020000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40089003021000328aa00000", hexnat% "10000400000000000000000", hexnat% "201800000000000000", hexnat% "10a000000000000000", hexnat% "4600000000000000000000", hexnat% "8060000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40489012221000328aa00000", hexnat% "200008000000000000000", hexnat% "400010000000000000000", hexnat% "600800000000000000", hexnat% "18020000000000000000000", hexnat% "40001000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40089002221000328aa00000", hexnat% "118000000000000000", hexnat% "600800000000000000", hexnat% "4600000000000000000000", hexnat% "18020000000000000000000", hexnat% "40001000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400810020200000288000000", hexnat% "4400110000000000000000", hexnat% "10000400010002000000000", hexnat% "28000a000000000000000", hexnat% "8000200000001000200000", hexnat% "20000800000000000000", hexnat% "40001000000002800000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00104.record019
