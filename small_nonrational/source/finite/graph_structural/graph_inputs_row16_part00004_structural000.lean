module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00004Data
public import GraphInputsRow16Part00004Frames
public import GraphInputsRow16Part00004Leaves
public import GraphInputsRow16Part00004Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00004.record065
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065
def vertexColumn : Fields := ⟨10, hexnat% "392d2b1a66a5a958b66386e2785ee4749c6599966552d58d1b49d17783d0f13a4d9394e332cf0b62e4b52d2b1ae1b46c9b16d8791cc729c6785c5743c8f0f03a258361382e07839254351342d0770360e4384c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a49b6db4d2492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400fbffe8f0000000", 216172782113783808, hexnat% "400800000200000000", hexnat% "180000000000000000", 90194313216, 1125899906842624]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [26458607813918720, 9570183567900672, hexnat% "400800000040000000", hexnat% "80100000000000000", hexnat% "100200000100000000", hexnat% "40080000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5c03fefa7ff0000000", 576460752303423488, 6047313952768, 281474976710656]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c027efa7ff0000000", hexnat% "400800000000000000", 6047313952768, 281474976710656, 108086391056891904]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c4 c2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10024ce27f70000000", hexnat% "400800000080000000", 32435593019392, 108086391056891904, hexnat% "c0000000000000000", 14355223812243456]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100204023130000000", hexnat% "4008008002c0000000", 17643725651968, hexnat% "40082000000000000", hexnat% "80100204000000000", 16045173184135168, 18098511149006848]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c1
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c10 c0
  c11
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00004.record065
