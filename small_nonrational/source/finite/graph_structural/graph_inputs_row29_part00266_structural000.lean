module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00266Data
public import GraphInputsRow29Part00266Frames
public import GraphInputsRow29Part00266Leaves
public import GraphInputsRow29Part00266Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00266.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003
def vertexColumn : Fields := ⟨10, hexnat% "1ca5a8ea568da8e87a719663995635a361d98e8b92e2ba1e4789e9c5c95a4e9564d91e5c5594e5554d51d70da358d4b4ad4749d70d6338d5334e3362d4b32e2b4acab1ae1b46c9b16d8751cc789d2729c6785d1725c5783e388d22c8703c1c83a0d90e2382e07a311c62986439896150d60d4348d0b41d50cc318c530cd0b22c2b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db49b6da4924924db6d36db492492492492492492492492492449249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400082080fffb8f00000000000", hexnat% "800000000003010000000000", hexnat% "7f00000008000000000", hexnat% "81240000000040080000000000", hexnat% "5b0000000000000000000000", 1132496976609280]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8082080fc0ff7f0000000000", hexnat% "40000000001800000000000000", hexnat% "7f00000008000000000", hexnat% "81240000000400800000000000", 2522015791327477760, hexnat% "5b0000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400082080ffbf80f0000000000", hexnat% "800000000003100000000000", hexnat% "7f00000008000000000", hexnat% "81240000000400800000000000", hexnat% "5b0000000000000000000000", 1231453023109120]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8082080fc78ff70000000000", hexnat% "40000000001800000000000000", hexnat% "7f00000008000000000", hexnat% "81240000000040080000000000", 2319353808095805440, hexnat% "5b0000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400082080ffbbe550000000000", hexnat% "800000000001000000000000", 187466732535808, hexnat% "7f00000000000000000", hexnat% "7f0000000000000000000000", hexnat% "81000000000440000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81248208c077f8998000000000", hexnat% "40800000000000000000000000", hexnat% "7300000000000000000", hexnat% "5b0000000000000000000000", 2082475023007744, hexnat% "f8800000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400082080fffbd330000000000", hexnat% "800000000002000000000000", 224850127880192, hexnat% "7f00000000000000000", hexnat% "7f0000000000000000000000", hexnat% "81000000000040000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8208005c88110000000000", hexnat% "c1800000000000000000000000", hexnat% "7f00000008000000000", hexnat% "f8003000000000000", 2553540988719071232, hexnat% "7f0000000000000000000000", 1387583674253312]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00266.record003
