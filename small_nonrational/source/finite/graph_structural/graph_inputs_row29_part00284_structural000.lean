module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00284Data
public import GraphInputsRow29Part00284Frames
public import GraphInputsRow29Part00284Leaves
public import GraphInputsRow29Part00284Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00284.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000
def vertexColumn : Fields := ⟨10, hexnat% "3e0f43b31c9715c3723c4f0bc1f0eac6a5a56a3a4e87a39b16959568d9361db0ea398e9394e33a2e4b8ae1ba1e4785e0f8f13a71996559366394e4b91e4e5c5655554d58d5352d475c368d6364d534cd8b52d2b46d8751d2745d0f4e3c4e5354e334cc73c2e8b62e4b52e2b4ac6b86d1b16c3bc1e8761e4751e2749c6785d1715c3783d0f23c4f0bc1f328aa318a6324a98651916439314a5855151543530ca382d0b22c4b0ae0741c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db69b6db4db6db6db4da6db6d24924924924926db69b4d26926db6d2492492492492492492493249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨119, by decide⟩, ⟨126, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408009020000000103ffd003e0000000", hexnat% "10004800000000000000000", hexnat% "1fe0000000000000000000000", 52759378264064, hexnat% "ff00000000000000000000", hexnat% "360000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "901feff04b60100800be0000000", hexnat% "40800002010000010004004000000000", 214835775974408192, 70042326663168]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "901feff04b601004007e0000000", hexnat% "40800002010000010004004000000000", 214906144718585856, 70059506532352]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40800903dbed04b701060063e0000000", hexnat% "241200000000000000000000", 144150372447944704, 70298375433486336, 34754875359232]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40800903dbed04b701050053e0000000", hexnat% "241200000000000000000000", 144150372447944704, 70579850410196992, 34823594835968]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40800900000000370100000080000000", hexnat% "ff00000000000000000000", hexnat% "1fe0000000000000000000000", hexnat% "2010004800000000000000000", 144150386943459328, 35167192219648, 71987225293750272]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00284.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00284.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008
def vertexColumn : Fields := ⟨10, hexnat% "3d0ec37332ac9b29c9723cb2aaa9aa9a96a3ab1aa699a9695a368e635a364d8b61d8ce8b92e2b86e8791e2785ecc6b16c6715c4f1ca6a96a6695a4e9c669966659564d9394d58d5352d4753362d4b4ad1b61d4749d17723a8da398d6338f13a4d9394d5334e334ccb31cf0ba2d8b92d4b32e2b4acab1ae1b46c9b16cc789d2785d170de0f43c2f07ca6198961588e138a5194951548d1362348ca318e1344c9314e0b42c8b12c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6da4da49b49b49b6db6db6db6db49b493693692492492492492492492492492492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0000000600000078020000000", hexnat% "c00000006000000780040000000", hexnat% "180000000c00001e0000200000000", hexnat% "184000000c20008200804000000000", 8725730720481280, 8935141712242671616, hexnat% "1f0000003000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00284.record008
