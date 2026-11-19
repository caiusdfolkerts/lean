module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00216Data
public import GraphInputsRow29Part00216Frames
public import GraphInputsRow29Part00216Leaves
public import GraphInputsRow29Part00216Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00216.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003
def vertexColumn : Fields := ⟨10, hexnat% "1b47325c8f07c6c9ca96a3a1e9c669b1665a5655a364d8b61da8e63a4e538ce8b8ae1ba1e1783e6c5c9966391e5c569715656558d5352d475a358d9354d3362d1b61d1743d70da3c4d9394e334ccb31ce8b62e4b52ccb8ac6b86c5b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f550ac548aa544a96154529615454550d60d2344d0b58350ca384d1314c3382c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db4db6db6da6db6db69249249249249249249249249249369a6da693493493249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨96, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5f7ff0000e004200000000", hexnat% "2080000000010000000000", 571957152676052992, hexnat% "3f800000000000000", hexnat% "801000000000000502ce0000000", hexnat% "c0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fc04ff80e006c00000000", hexnat% "8010000000000005102e0000000", hexnat% "4002000040000000000000", 553942754166571008, hexnat% "29b00000000000000000", hexnat% "14000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60324c27fe0002e0000000", hexnat% "801000000000000516c00000000", hexnat% "3d800000000000000", hexnat% "da00000000000000000", hexnat% "17c0100000000000000000", hexnat% "800000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ebf4264e0104a0000000", hexnat% "4814000000000000000000", 85568402583715840, hexnat% "3d800000000000000", hexnat% "80080100000000000", hexnat% "801000000000000406800000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2015ffa6e406c00000000", hexnat% "1dc0000000000000000000", hexnat% "8010000000000001102e0000000", 400820366835974144, hexnat% "6012000000000000000000", hexnat% "2ca00000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fd9ddf7fe4106e0000000", hexnat% "26200000000000000000", hexnat% "20800006800000000", hexnat% "801000000000000100000000000", hexnat% "4000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff0e7fe500ae0000000", hexnat% "d0000000000000000", hexnat% "21800000400000000", hexnat% "801000000000000016000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dbff8e7fe5022e0000000", hexnat% "51000000000000000", hexnat% "240000000004c00000000", hexnat% "801000000000000010000000000", hexnat% "20800000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5fc873fffe006ee0000000", hexnat% "801000000000000510000000000", hexnat% "c0000000000000000", hexnat% "37800000000000000000", hexnat% "2000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5fc8f3fffe006ee0000000", hexnat% "c0000400000000000", hexnat% "801000000000000110000000000", hexnat% "37000000000000000000", hexnat% "2000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "548873fffe0002e0000000", hexnat% "37800000000000000000", hexnat% "c0000400000000000", hexnat% "b40000000002000000000", hexnat% "2000000000010000000000", hexnat% "801000000000000104c00000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5feff7fffe110c60000000", hexnat% "80000402000000000", hexnat% "2010000000000080000000", hexnat% "801000000000000004200000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88077ff7e010420000000", hexnat% "80080100000000000", hexnat% "6100000000000000000000", hexnat% "1640000000006800000000", hexnat% "8010000000000004002c0000000", hexnat% "3f800000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5d7340400000000000", hexnat% "2880e000000000000", hexnat% "6012000000000000000000", hexnat% "801000000000000116ee0000000", 337769972052787200, hexnat% "2da00000000000000000", hexnat% "1fc0000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c23 c2
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00216.record003
