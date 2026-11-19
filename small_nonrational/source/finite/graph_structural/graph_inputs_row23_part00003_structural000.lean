module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00003Data
public import GraphInputsRow23Part00003Frames
public import GraphInputsRow23Part00003Leaves
public import GraphInputsRow23Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027
def vertexColumn : Fields := ⟨10, hexnat% "2aa558ae17ba1d4731ca719a665956639c96a569565c55352b45da8d53a2ccb8ac6b86c9b0ed4731d2719d1725c3723c4f0bc1faa1542a85a29856c86a1c4551a26292a61916545494a54545528c5322c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44a78afe4080000000", hexnat% "25800000000000000", hexnat% "180004000340000000", hexnat% "10030000000000000", hexnat% "200001011000000000", 18014535948435456, 601295421440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22587529fc40000000", hexnat% "40380000000000000", hexnat% "180008000380000000", hexnat% "400002800000000000", hexnat% "18400000000000000", 2305847407260205056, 90159953477632]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5403da207480000000", hexnat% "200005010000000000", hexnat% "34020000000000000", 11817445422220181504, 598074195968, hexnat% "80000000000000000", 244091581366272, 1729382256910270464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44ff86fe1040000000", hexnat% "20021000000000000", hexnat% "280000000000000000", hexnat% "100008000380000000", 22519372526387200, hexnat% "10000000400000000", 721554505728]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50308afe1bc0000000", 2078764171264, hexnat% "280005000000000000", 175640385467449344, hexnat% "1c400000000000000", hexnat% "20800000000000000", hexnat% "40100000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdebd2e17c0000000", 72620543991349248, hexnat% "400000800000000000", 87960930222080, 2305843043573432320, 18015910337970176, 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc7ba2e1400000000", 1730789631793823744, 2305983746702049280, 18032128134479872, hexnat% "200000014000000000", hexnat% "500000000000000000", 70934606118912, 34359738368]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41008aac1000000000", hexnat% "280005000000000000", 16429131440647569408, hexnat% "40300000000000000", 31525197391593472, hexnat% "21800000000000000", 90176059604992, hexnat% "100000000000000000", 2113123909632]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record027
