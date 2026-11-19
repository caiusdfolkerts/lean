module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00030Data
public import GraphInputsRow23Part00030Frames
public import GraphInputsRow23Part00030Leaves
public import GraphInputsRow23Part00030Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008
def vertexColumn : Fields := ⟨10, hexnat% "96a56359362d87663a4e538ce2b86e2785e0fa59954d54d4b51d58d9354d334ad1b49d1743da4cd38cd332cc73c2e8b62d4b32e2b2ac6b86c9b16c3b61e4751cc729c6785d1783c1f4b2529292a49896158364388e1382e946494a525254550d50d2344d0b64348e1324c530ce0b42c8b12c2b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f139820502007d0000000000", hexnat% "ec000000000020000000000", hexnat% "ac03c000000000000", 985162418487296, hexnat% "260200000000000000000", hexnat% "2000400500000000000000000", 4449556431842050048, hexnat% "1d800000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f0b8c10180803d0000000000", hexnat% "f4000000000020000000000", hexnat% "e403c000000000000", 1055531162664960, hexnat% "2000400700000000000000000", 4557642822898941952, hexnat% "1e800000000000000000", hexnat% "320000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a43c00703ffd030000000000", hexnat% "fc0000c0000000000", hexnat% "208000000000000000000", hexnat% "bc000000000000000000000", hexnat% "500000000000100000000000", hexnat% "17800000000000000000", 809240558043136, hexnat% "1e0000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2f14be27402005d0000000000", hexnat% "1d800000020000000000", hexnat% "1041000000009000000000000", hexnat% "bc004000000000000", hexnat% "2400000030000000000000", 738871813865472, 4449556431842050048, hexnat% "a8000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f179a2e5425bff0000000000", hexnat% "608000000000000000000", hexnat% "e8000000000000000000000", hexnat% "a8024000000000000", hexnat% "15100000000000000000", 4431542033332568064, hexnat% "40000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3b5330a64021bff0000000000", hexnat% "400080010000000000000000", hexnat% "c00100024000000000000", hexnat% "ac000000000000000", hexnat% "15800000000000000000", hexnat% "ac000000000000000000000", 4449556431842050048, hexnat% "60000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f079a08140407d0000000000", hexnat% "f8000000000020000000000", 985162418487296, hexnat% "e803c000000000000", hexnat% "240200000000000000000", hexnat% "408000000000000000000", 4575657221408423936, hexnat% "17500000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2f00180010000740000000000", hexnat% "10402080000090a0000000000", 4608309418218487808, hexnat% "ec000000000000000", hexnat% "17f00000000000000000", hexnat% "bf800000000000000000000", 703687441776640, hexnat% "60000000000000000000", hexnat% "400000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record008
