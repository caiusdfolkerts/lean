module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00156Data
public import GraphInputsRow24Part00156Frames
public import GraphInputsRow24Part00156Leaves
public import GraphInputsRow24Part00156Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00156.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002
def vertexColumn : Fields := ⟨10, hexnat% "9713c9693a99966c5a9665a564da4e3392e2b86e8791e2785e0fa594e66559715a559595535934cd4b4ad8751d1743d98d63c4e9364e534ce4b32d2b2ae1b46c5b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f1b09c1a89a1a4999152519615454952344d0b41d90d2318e1344c9322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6da6d36da4924924924924924924924db4db4d249b6d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffc012003c04000000", 1046101750945153024, hexnat% "1200000000088038000000", 2396196476737814528, 11258999068426240, 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93fff803c04000000", hexnat% "7424000000000000000", hexnat% "1200000000088038000000", hexnat% "10a08000000000000000", hexnat% "140000000000000000", hexnat% "8000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c3ffff809c3c000000", hexnat% "1c0000000000000000", hexnat% "1200000000082000000000", hexnat% "18200000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c3ffff881c3c000000", hexnat% "1c0000000000000000", hexnat% "120000000000a000000000", hexnat% "18200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc3ffdf80bc0c000000", hexnat% "1c0000000000000000", 9007200060047360, hexnat% "1200000000080000000000", hexnat% "10200000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c3de87801c04000000", 2395923797854126080, hexnat% "80c0000000008000000", hexnat% "120000000000a030000000", 15762598695796736, hexnat% "10300000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14bfffff80803c000000", hexnat% "8400000000000000000", hexnat% "3000000001c00000000", hexnat% "1200000000082000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c7fc02300803c000000", 1159817641536258048, hexnat% "3800000001000000000", 2395923797854126080, hexnat% "1200000000002c00000000", 1045961013456797696]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43331ff88a010000000", hexnat% "10808000000000000000", 1008806436857184256, hexnat% "80c4000000008000000", hexnat% "3400000000000000000", hexnat% "1200000000000020000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "121c1df07b88bc3c000000", hexnat% "a20000000000000000", hexnat% "400080000000000000", 1081989810475761664, hexnat% "3000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fdff573083c1c000000", hexnat% "200004000000000000", hexnat% "1200000000008020000000", 2392537302040576, 756604737398243328]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7d3ef47001c0c000000", hexnat% "80c0000000000000000", hexnat% "10200000082010000000", hexnat% "1200000000008020000000", 15903336184152064, 1188950301625810944]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e5d5ed6808808000000", 11540474917552128, 2377909399344644096, hexnat% "1820000001000000000", hexnat% "1200000000002400000000", hexnat% "10208000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "121635f0fb88bc3c000000", hexnat% "8480000000000000000", hexnat% "1820000000000000000", 1081989810475761664]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7d3cfc7001c1c000000", hexnat% "80c0000000000000000", hexnat% "120000000008a020000000", hexnat% "10200000000000000000", 15903336184152064, 3458764513820540928]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "71130d2002018000000", hexnat% "8484000000000000000", 12807111507443712, hexnat% "10a08000000000000000", hexnat% "60000000000000000", hexnat% "1200000000089c20000000", 1080863910568919040]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c26 c11
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c27 c8
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c28 c1
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c29 c0
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00156.record002
