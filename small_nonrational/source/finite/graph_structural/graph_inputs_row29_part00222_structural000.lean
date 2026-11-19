module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00222Data
public import GraphInputsRow29Part00222Frames
public import GraphInputsRow29Part00222Leaves
public import GraphInputsRow29Part00222Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00222.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000
def vertexColumn : Fields := ⟨10, hexnat% "9d1aa5a8ea6695a36a6695a2e4b8ae1b91e2785ecc6b16c6715c4f15a4e96655936665956354d4b51d62d4b4ad4749d17723a8da398d6338f13a4e5354cd352ccb8ad2b2ac6b46c9b16e4789d2729c6745c9783d0f23c2f07da81b19262a161584e68591625292a46989465854551342d60e1344c9314d0b22c4b81c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6d36d36d369b4db4936926d249b4da6da49249a492493692492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000c73c804dfe6f80000000", hexnat% "820001000000000000000", hexnat% "24000000000000000000000", 121597258658480128, hexnat% "12000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20082728904dfe7f80000000", 121597189939003392, hexnat% "c0140000000000000000", hexnat% "24000000000000000000000", hexnat% "12000000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000608004dfc3f80000000", hexnat% "c0140000000000000000", hexnat% "801200000000000000000", 121597189939003392, hexnat% "2004020008000000000000000", hexnat% "10020000001000024000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20248272080007c4580000000", hexnat% "200000000040003000000000", hexnat% "10000000001001820000000000", 121597189939003392, 3377742670200832, hexnat% "c01c0000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c73c800dfe1f80000000", hexnat% "204000000000000000000000", hexnat% "10020000001000004000000000", hexnat% "2000020000000000000000000", 139611725887438848]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80124800dfc1f80000000", hexnat% "c0180000000000000000", hexnat% "2004020000000000000000000", 139611725887438848, hexnat% "10020000001000024000000000", hexnat% "200006000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000c73c807dfe4f80000000", hexnat% "820001000000000000000", hexnat% "24000000000000000000000", 108086597215322112, hexnat% "12000000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2008273c904c064700000000", 242665652224, hexnat% "c0000001c00000000000", hexnat% "24000000000000000000000", hexnat% "12000000000000000000000000", 121658762590158848]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c9
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "805208000000600000000", hexnat% "200002000040043080000000", hexnat% "2004020000000380000000000", hexnat% "c01c0000000100000000", hexnat% "10020000001001c24000000000", 121597189939003392, 3377734080266240]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c8
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c15 c5
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c4
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00222.record000
