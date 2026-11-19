module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00013Data
public import GraphInputsRow16Part00013Frames
public import GraphInputsRow16Part00013Leaves
public import GraphInputsRow16Part00013Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010
def vertexColumn : Fields := ⟨10, hexnat% "31c8f31a36b16659362db0e3386e8791e2783ec64d98e715a55958d5352d70d934cd8b46d8751d2743dc4d9334d332cf0b32c6b86d1b26c5bc1d8751d2729c6785d1725c3783d0f23c1f0e8c61382ec46190e7053160d1342d30d1324c3312c2b06d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6d26da4d26db692493692493492492492692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "31001440fc91f000000", hexnat% "200a0000000000000", 432345564227567616, hexnat% "90002000000000000", 527766118203392, 233001975808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1100001843f7f000000", hexnat% "2000100088000000000", 109126529056768, 495395959010754560, hexnat% "90002000000000000", hexnat% "20004000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "31001000c3f7f000000", 495395959010754560, 529689726681088, hexnat% "90002000000000000", hexnat% "20004020000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3020001efd90f000000", hexnat% "90002000000000000", 270215977642229760, 164282499072, 297237575406452736, hexnat% "100004000030000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110025eddf77000000", hexnat% "a0000020000000000", hexnat% "3000000000000000000", 563087526592512, 270215977642229760, 288230376151711744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b06e407587d000000", hexnat% "3000000000102000000", 72066939886764032, 163208757248, 949978046398464, 140737488355328]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1100004045811000000", hexnat% "2000100080102000000", hexnat% "a0020020000000000", 529415385645056, 486388759957340160, hexnat% "10002002040000000", 25769803776]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00013.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00013.record010
