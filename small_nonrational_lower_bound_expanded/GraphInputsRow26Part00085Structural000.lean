module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00085Data
public import GraphInputsRow26Part00085Frames
public import GraphInputsRow26Part00085Leaves
public import GraphInputsRow26Part00085Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 34503619772416, 2261053303544610816, 2310065133864353792]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), (certNat% 5), (certNat% 6), 16911433728000, 1108131798937763840, 4222124650659840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 2307848518422757376, 34087007944704, 2260877381684166656]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 2308974418329600000, 34089155428352, 2260947750428344320]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 25707526750208, 1684592551241187328, (certNat% 14), (certNat% 3), 2310065133864353792]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 30105573261312, 1972822927392899072, (certNat% 14), (certNat% 3), 2310065133864353792]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 32304596516864, 2116938115468754944, (certNat% 14), (certNat% 3), 2310065133864353792]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 33404108144640, 2188995709506682880, (certNat% 14), (certNat% 3), 2310065133864353792]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 18), (certNat% 19), (certNat% 20)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c9 c7
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c12 c4
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c13 c3
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c14 c2
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "32cab1ac9723c4f0bc1f32aaa9aa96a3a4e8bac9aa669a568d9362db0ea398e9394e33a2e4b8ae8791e2785e0f9a98e5392e479696354d4b51d58d534cd8b52d2b46d8751d2745d0f5a38cd332cd8b52ccb8ad2b2ae1b46c9b0ed8751cc789d2729e1745c970de0f43c8f13c2f07e388d21a16a16159292a4590e525294550d45342c8b12c1b41c8711c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69b6db49b6da4db6db6db4da6924924936da4db6936da49a492492692493493449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 23), (facetIndex 76), (facetIndex 79), (facetIndex 92), (facetIndex 99)]))
 (.branch 2
 (.leaf ([(facetIndex 29), (facetIndex 53), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 39), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 43), (facetIndex 44), (facetIndex 91), (facetIndex 98)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 36), (facetIndex 37), (facetIndex 38)])))
 (.branch 6
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 46), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 27), (facetIndex 54), (facetIndex 59), (facetIndex 60), (facetIndex 106)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1800000c0000600000000000092489248006c00188005b4376d5240dc908dbz13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2]
def grouped2_0002 : List Nat := [3]
def grouped2_0003 : List Nat := [3, 4]
def grouped2_0004 : List Nat := [3, 4, 5, 6]
def grouped2_0005 : List Nat := [4]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6]
def grouped2_0008 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000" 40

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000" "{\"ridges\":[[32,518],[33,134],[34,262],[43,138],[44,266],[91,548],[98,552]],\"owners\":[[33,134,[77,83,86,87],[2,26,30,36,38,80,89,93,94]],[34,262,[78,84,86,88],[3,27,31,37,38,81,90,93,95]],[43,138,[77,83,86,87],[6,26,40,46,48,80,96,100,101]],[44,266,[78,84,86,88],[7,27,41,47,48,81,97,100,102]],[32,518,[82,85,87,88,94,95],[18,28,35,79,91,92]],[91,548,[61,109,110],[21,35,68,82,94,95,106]],[98,552,[61,109,110],[22,45,73,82,101,102,106]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-4,-1],[-4,-2],[-4,-3],[-5,-1],[-5,-2],[-5,-3],[-9,-1],[-9,-2],[-9,-3],[-10,-1],[-10,-2],[-10,-3],[-11,-1],[-11,-2],[-11,-3],[-15,-7],[-15,-12],[-16,-8],[-16,-13],[-17,-14],[-17,-15],[-17,-16],[-18,-14],[-18,-16],[-19,-14],[-19,-15],[-20,-1],[-20,-2],[-20,-3],[-21,-14],[-21,-16],[-22,-14],[-22,-15],[-23,-1],[-23,-2],[-23,-3],[-24,-14],[-24,-15],[-24,-16],[-25,-1],[-25,-2],[-25,-3],[-25,-14],[-25,-16],[-26,-1],[-26,-2],[-26,-3],[-26,-14],[-26,-15],[-28,-7],[-28,-8],[-28,-12],[-28,-13],[-28,-27],[-29,-7],[-29,-8],[-29,-12],[-29,-13],[-29,-27],[-30,-28],[-30,-29],[-31,-18],[-31,-19],[-31,-21],[-31,-22],[-31,-24],[-31,-25],[-31,-26],[-31,-27],[-31,-30],[-32,-14],[-32,-15],[-32,-16],[-33,-14],[-33,-15],[-33,-16],[-7,18,21,24,25],[-8,19,22,24,26],[-12,18,21,24,25],[-13,19,22,24,26],[-6,20,23,25,26,28,29],[-27,17,32,33],[-30,17,32,33],[-34,7,8,12,13,27,30],[-35,4,5,6,9,10,11],[-36,1,2,3,14,15,16,31],[-37,34],[-37,35],[-38,36],[-39,37],[-39,38],[-40,39],[40]],\"atoms\":[{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":30,\"b\":25},{\"tag\":\"incompatible\",\"a\":30,\"b\":26},{\"tag\":\"incompatible\",\"a\":30,\"b\":27},{\"tag\":\"incompatible\",\"a\":31,\"b\":25},{\"tag\":\"incompatible\",\"a\":31,\"b\":26},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":36,\"b\":25},{\"tag\":\"incompatible\",\"a\":36,\"b\":26},{\"tag\":\"incompatible\",\"a\":36,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":25},{\"tag\":\"incompatible\",\"a\":37,\"b\":26},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":38,\"b\":25},{\"tag\":\"incompatible\",\"a\":38,\"b\":26},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":59,\"b\":33},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":77,\"b\":54},{\"tag\":\"incompatible\",\"a\":77,\"b\":60},{\"tag\":\"incompatible\",\"a\":78,\"b\":54},{\"tag\":\"incompatible\",\"a\":78,\"b\":59},{\"tag\":\"incompatible\",\"a\":82,\"b\":25},{\"tag\":\"incompatible\",\"a\":82,\"b\":26},{\"tag\":\"incompatible\",\"a\":82,\"b\":27},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":60},{\"tag\":\"incompatible\",\"a\":84,\"b\":54},{\"tag\":\"incompatible\",\"a\":84,\"b\":59},{\"tag\":\"incompatible\",\"a\":85,\"b\":25},{\"tag\":\"incompatible\",\"a\":85,\"b\":26},{\"tag\":\"incompatible\",\"a\":85,\"b\":27},{\"tag\":\"incompatible\",\"a\":86,\"b\":54},{\"tag\":\"incompatible\",\"a\":86,\"b\":59},{\"tag\":\"incompatible\",\"a\":86,\"b\":60},{\"tag\":\"incompatible\",\"a\":87,\"b\":25},{\"tag\":\"incompatible\",\"a\":87,\"b\":26},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":54},{\"tag\":\"incompatible\",\"a\":87,\"b\":60},{\"tag\":\"incompatible\",\"a\":88,\"b\":25},{\"tag\":\"incompatible\",\"a\":88,\"b\":26},{\"tag\":\"incompatible\",\"a\":88,\"b\":27},{\"tag\":\"incompatible\",\"a\":88,\"b\":54},{\"tag\":\"incompatible\",\"a\":88,\"b\":59},{\"tag\":\"incompatible\",\"a\":94,\"b\":33},{\"tag\":\"incompatible\",\"a\":94,\"b\":34},{\"tag\":\"incompatible\",\"a\":94,\"b\":43},{\"tag\":\"incompatible\",\"a\":94,\"b\":44},{\"tag\":\"incompatible\",\"a\":94,\"b\":91},{\"tag\":\"incompatible\",\"a\":95,\"b\":33},{\"tag\":\"incompatible\",\"a\":95,\"b\":34},{\"tag\":\"incompatible\",\"a\":95,\"b\":43},{\"tag\":\"incompatible\",\"a\":95,\"b\":44},{\"tag\":\"incompatible\",\"a\":95,\"b\":91},{\"tag\":\"incompatible\",\"a\":98,\"b\":94},{\"tag\":\"incompatible\",\"a\":98,\"b\":95},{\"tag\":\"incompatible\",\"a\":106,\"b\":77},{\"tag\":\"incompatible\",\"a\":106,\"b\":78},{\"tag\":\"incompatible\",\"a\":106,\"b\":83},{\"tag\":\"incompatible\",\"a\":106,\"b\":84},{\"tag\":\"incompatible\",\"a\":106,\"b\":86},{\"tag\":\"incompatible\",\"a\":106,\"b\":87},{\"tag\":\"incompatible\",\"a\":106,\"b\":88},{\"tag\":\"incompatible\",\"a\":106,\"b\":91},{\"tag\":\"incompatible\",\"a\":106,\"b\":98},{\"tag\":\"incompatible\",\"a\":109,\"b\":54},{\"tag\":\"incompatible\",\"a\":109,\"b\":59},{\"tag\":\"incompatible\",\"a\":109,\"b\":60},{\"tag\":\"incompatible\",\"a\":110,\"b\":54},{\"tag\":\"incompatible\",\"a\":110,\"b\":59},{\"tag\":\"incompatible\",\"a\":110,\"b\":60},{\"tag\":\"mate\",\"ridge\":134,\"a\":33,\"owners\":[77,83,86,87]},{\"tag\":\"mate\",\"ridge\":262,\"a\":34,\"owners\":[78,84,86,88]},{\"tag\":\"mate\",\"ridge\":138,\"a\":43,\"owners\":[77,83,86,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":44,\"owners\":[78,84,86,88]},{\"tag\":\"mate\",\"ridge\":518,\"a\":32,\"owners\":[82,85,87,88,94,95]},{\"tag\":\"mate\",\"ridge\":548,\"a\":91,\"owners\":[61,109,110]},{\"tag\":\"mate\",\"ridge\":552,\"a\":98,\"owners\":[61,109,110]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[33,34,43,44,91,98],\"full_literals\":[-34,7,8,12,13,27,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,31,32,36,37,38],\"full_literals\":[-35,4,5,6,9,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[25,26,27,54,59,60,106],\"full_literals\":[-36,1,2,3,14,15,16,31]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "94 39 0 93 92 0\n95 37 0 94 90 0\n96 38 0 94 91 0\n97 34 0 95 87 0\n98 35 0 95 88 0\n99 36 0 96 89 0\n100 -1 28 29 0 98 1 4 7 10 13 27 34 40 45 85 81 0\n101 -14 0 97 20 23 25 30 32 37 43 48 71 74 82 83 77 79 78 80 84 0\n102 -28 0 97 50 51 52 53 54 60 84 0\n103 -29 0 97 55 56 57 58 59 61 84 0\n104 -1 0 103 102 100 0\n105 -31 0 97 62 63 64 65 66 67 68 69 70 77 79 78 80 84 0\n106 -2 0 98 103 102 2 5 8 11 14 28 35 41 46 85 81 0\n107 -3 0 98 103 102 3 6 9 12 15 29 36 42 47 85 81 0\n108 -15 0 97 16 17 21 26 33 38 49 72 75 82 83 78 80 84 0\n109 16 0 108 99 104 107 106 101 105 86 0\n110 -8 0 109 18 0\n111 -13 0 109 19 0\n112 -17 0 109 22 0\n113 -18 0 109 24 0\n114 -21 0 109 31 0\n115 -24 0 109 39 0\n116 -25 0 109 44 0\n117 -32 0 109 73 0\n118 -33 0 109 76 0\n119 -27 0 112 117 118 82 0\n120 -30 0 112 117 118 83 0\n121 -7 0 113 114 115 116 77 0\n122 -12 0 113 114 115 116 79 0\n123 0 119 120 97 121 110 122 111 84 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1accaaaa6aa5a69a366394e33a2e4b8ae8791e27b29aa5a9965a58d58d534cd8b52d2b61d4749dc8ea368e538cf0ba2d8b92d4b32e2b4acab46c9b61d4731e2719e1745c970de0f0bc5c8685a498a61590e2384e07a1916525294554348d1341d88d2328e1314e0b42c8b12c1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da4d24d24936d2692692492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 53), (facetIndex 58), (facetIndex 73), (facetIndex 88)]))
 (.leaf ([(facetIndex 37), (facetIndex 42), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 35), (facetIndex 41), (facetIndex 45), (facetIndex 72), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 83), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 80), (facetIndex 81)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "62483f9200030921fa48920db45b6d01ec5ed8a6z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 71)]))
 (.leaf ([(facetIndex 82), (facetIndex 86)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.branch 4
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 92)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "46d804004000248z37;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [2, 3, 4]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4]
def grouped3_0021 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002" "{\"ridges\":[[71,564],[74,424],[82,556],[89,424],[92,424]],\"owners\":[[82,556,[67],[]],[71,564,[86],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-4,-1],[-5,-1],[-7,-4],[-7,-5],[-9,-1],[-9,-7],[-10,-1],[-10,-7],[-11,-4],[-11,-5],[-11,-9],[-11,-10],[-13,-1],[-13,-7],[-13,-11],[-14,-1],[-14,-7],[-15,-1],[-15,-7],[-19,-11],[-19,-16],[-19,-17],[-20,-11],[-20,-16],[-20,-17],[-21,-2],[-21,-16],[-21,-17],[-21,-18],[-21,-19],[-21,-20],[-22,-19],[-22,-20],[-22,-21],[-23,-19],[-23,-20],[-23,-21],[-24,-19],[-24,-20],[-24,-21],[-25,-2],[-25,-3],[-25,-6],[-25,-8],[-25,-12],[-25,-18],[-26,-25],[-30,-11],[-30,-21],[-30,-27],[-30,-28],[-30,-29],[-31,-11],[-31,-21],[-31,-27],[-31,-28],[-31,-29],[-34,-33],[-38,-1],[-38,-11],[-38,-19],[-38,-20],[-38,-21],[-38,-26],[-38,-28],[-38,-29],[-38,-30],[-38,-31],[-38,-34],[-38,-36],[-38,-37],[-32,21],[-25,33],[-27,-35,-38],[-39,3,8,12,13,14,15],[-40,2,16,17,18,22,23,24],[-41,1,7,11,26,34],[-42,4,5,6,9,10],[-43,19,20,30,31],[-44,39],[-45,40,41],[-46,40],[-46,41],[-48,44],[-47,45],[-48,46],[-49,42,43],[-50,42],[-50,43],[-51,49],[-52,50],[-53,47],[-53,48,52],[-53,51],[53],[-54,21,25],[-55,32,33],[-56,27,28,29],[-57,35,36,37],[-58,38],[-59,54],[-59,55],[-60,57],[-60,58],[-61,56,60],[-62,56],[-62,60],[-63,59,62],[-63,61],[63]],\"atoms\":[{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":41},{\"tag\":\"incompatible\",\"a\":61,\"b\":35},{\"tag\":\"incompatible\",\"a\":61,\"b\":41},{\"tag\":\"incompatible\",\"a\":65,\"b\":45},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":45},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":37},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":42},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":71,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":45},{\"tag\":\"incompatible\",\"a\":81,\"b\":67},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":75},{\"tag\":\"incompatible\",\"a\":81,\"b\":76},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":92,\"b\":35},{\"tag\":\"incompatible\",\"a\":92,\"b\":45},{\"tag\":\"incompatible\",\"a\":92,\"b\":65},{\"tag\":\"incompatible\",\"a\":92,\"b\":66},{\"tag\":\"incompatible\",\"a\":92,\"b\":67},{\"tag\":\"incompatible\",\"a\":92,\"b\":72},{\"tag\":\"incompatible\",\"a\":92,\"b\":75},{\"tag\":\"incompatible\",\"a\":92,\"b\":76},{\"tag\":\"incompatible\",\"a\":92,\"b\":80},{\"tag\":\"incompatible\",\"a\":92,\"b\":81},{\"tag\":\"incompatible\",\"a\":92,\"b\":87},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"mate\",\"ridge\":556,\"a\":82,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":564,\"a\":71,\"owners\":[86]},{\"tag\":\"three\",\"ridge\":424,\"vertices\":[74,89,92]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,42,57,59,60,61],\"full_literals\":[-39,3,8,12,13,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[36,62,63,64,68,69,70],\"full_literals\":[-40,2,16,17,18,22,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,41,45,72,87],\"full_literals\":[-41,1,7,11,26,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[38,39,40,43,44],\"full_literals\":[-42,4,5,6,9,10]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[65,66,80,81],\"full_literals\":[-43,19,20,30,31]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,40,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,42,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-53,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-53,48,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[67,71],\"full_literals\":[-54,21,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[82,86],\"full_literals\":[-55,32,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[74,75,76],\"full_literals\":[-56,27,28,29]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[89,90,91],\"full_literals\":[-57,35,36,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[92],\"full_literals\":[-58,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,54,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,57,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,56,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,56,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "111 47 0 95 92 0\n112 51 0 95 94 0\n113 45 0 111 85 0\n114 49 0 112 90 0\n115 61 0 110 109 0\n116 -62 0 106 107 103 104 100 65 66 70 71 98 99 74 0\n117 59 0 116 110 108 0\n118 54 0 117 101 0\n119 55 0 117 102 0\n120 -38 0 118 114 95 59 60 61 62 63 64 67 68 69 96 79 43 89 87 91 93 86 83 77 3 4 6 8 78 0\n121 -58 0 120 100 0\n122 -60 0 121 104 0\n123 56 0 122 115 105 0\n124 -21 2 -40 0 27 28 29 34 37 40 76 0\n125 -13 -25 -41 0 73 58 47 13 14 15 77 0\n126 -7 6 -42 0 3 4 6 8 78 0\n127 -11 6 -42 0 9 10 11 12 78 0\n128 -25 -42 -41 0 43 47 73 58 126 127 77 1 2 5 7 78 0\n129 -21 -40 0 26 124 0\n130 -7 -48 0 118 86 83 82 129 96 125 45 44 42 84 80 17 19 75 0\n131 -11 -43 0 20 23 48 53 79 0\n132 -48 0 118 119 114 84 86 80 82 83 129 72 96 97 42 44 45 47 125 128 58 87 130 131 77 16 18 75 0\n133 52 0 132 95 93 0\n134 50 0 133 91 0\n135 42 0 134 88 0\n136 43 0 134 89 0\n137 -21 0 136 30 31 49 54 79 0\n138 25 0 137 118 96 0\n139 -2 0 138 41 0\n140 -18 0 138 46 0\n141 -41 0 138 135 128 0\n142 40 0 141 113 81 0\n143 -19 0 142 140 139 21 22 32 35 38 76 0\n144 -20 0 142 140 139 24 25 33 36 39 76 0\n145 -30 0 123 50 51 52 98 0\n146 31 0 145 136 144 143 79 0\n147 -27 0 146 55 0\n148 -28 0 146 56 0\n149 -29 0 146 57 0\n150 0 147 148 123 149 98 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c970dc6695a368d68d93633a2e4b8ae1ba1e4789e17b31ca719a65999655936695954d58d535a364d3352d2b46d8751d2745d64d5334e334cd8b52ccb8acab1ae1b46c9b16cc789d2729c6785d170de0f43c1f8b12a258562384e0ba294a625854951560d2344d0b52344c9314d0b22c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69b4924da4d36db6924d24924d2493492493492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 62), (facetIndex 77)]))
 (.leaf ([(facetIndex 34), (facetIndex 43), (facetIndex 51), (facetIndex 53), (facetIndex 54), (facetIndex 55)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 40), (facetIndex 79), (facetIndex 80), (facetIndex 90)]))
 (.leaf ([(facetIndex 32), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 63), (facetIndex 64), (facetIndex 65)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 31), (facetIndex 41), (facetIndex 42), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1006db60480000009242da2da2d2483ff0003fcdb6455fz17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 66), (facetIndex 78)]))
 (.leaf ([(facetIndex 88), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 58), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.branch 4
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 94)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "371b6090000d8002492400000000080000000002z21;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3, 4]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [4]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008" "{\"ridges\":[[9,19],[10,19],[11,19],[17,21],[17,81],[18,21],[18,145],[19,21],[19,529],[26,82],[27,146],[30,19],[43,273],[52,19],[52,562],[54,81],[54,273],[54,274],[55,145],[55,273],[55,274],[56,81],[57,145],[58,273],[59,529],[66,273],[71,216],[72,273],[73,81],[73,529],[74,273],[75,145],[75,529],[76,792],[78,816],[79,82],[80,146],[81,274],[82,538],[88,274],[89,562],[91,216],[92,274],[93,274],[94,216],[95,600],[96,664]],\"owners\":[[17,81,[9,41,53,54,71,72,73],[56,68,69]],[54,81,[17,56,68,69,71,73],[9,41,53,72]],[56,81,[9,53,54],[17,41,68,69,71,72,73]],[73,81,[9,17,53,54,68],[41,56,69,71,72]],[26,82,[9,41,53,54,91,92],[79,90]],[79,82,[9,53,54],[26,41,90,91,92]],[18,145,[10,42,53,55,71,74,75],[57,68,70]],[55,145,[18,57,68,70,71,75],[10,42,53,74]],[57,145,[10,53,55],[18,42,68,70,71,74,75]],[75,145,[10,18,53,55,68],[42,57,70,71,74]],[27,146,[10,42,53,55,91,93],[80,90]],[80,146,[10,53,55],[27,42,90,91,93]],[43,273,[66,78],[11,34,51,54,55,58,72,74,76]],[58,273,[11,51,54,55,78],[34,43,66,72,74,76]],[66,273,[11,43,54,55,72,74,76],[34,51,58,78]],[72,273,[11,34,51,55,66,78],[43,54,58,74,76]],[74,273,[11,34,51,54,66,78],[43,55,58,72,76]],[81,274,[11,51,54,55],[34,43,88,92,93]],[92,274,[11,34,51,55,88],[43,54,81,93]],[93,274,[11,34,51,54,88],[43,55,81,92]],[19,529,[44,52,73,75,76,78],[35,59,67,69,70]],[59,529,[52,78],[19,35,44,67,69,70,73,75,76]],[73,529,[19,35,52,67,70,78],[44,59,69,75,76]],[75,529,[19,35,52,67,69,78],[44,59,70,73,76]],[82,538,[44],[]],[52,562,[89],[]],[89,562,[52],[]],[95,600,[73],[]],[96,664,[75],[]],[76,792,[],[]],[78,816,[],[]]],\"edges\":[[31,[9,17,26,41,53,54,56,68,69,71,72,73,79,90,91,92,94,95]],[32,[10,18,27,42,53,55,57,68,70,71,74,75,80,90,91,93,94,96]],[33,[11,34,43,51,54,55,58,66,72,74,76,78,81,88,92,93]],[34,[19,35,44,52,59,67,69,70,73,75,76,78,82,89,95,96]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-14],[-18,-15],[-21,-19],[-21,-20],[-23,-21],[-24,-21],[-25,-21],[-27,-12],[-27,-16],[-27,-17],[-27,-26],[-28,-3],[-28,-22],[-28,-27],[-29,-2],[-29,-20],[-29,-22],[-29,-27],[-29,-28],[-30,-1],[-30,-19],[-30,-22],[-30,-27],[-30,-28],[-30,-29],[-35,-10],[-35,-11],[-35,-12],[-35,-13],[-35,-26],[-35,-27],[-36,-35],[-37,-35],[-38,-35],[-39,-35],[-42,-32],[-42,-40],[-42,-41],[-43,-42],[-44,-31],[-44,-40],[-44,-41],[-44,-42],[-44,-43],[-51,-27],[-53,-51],[-53,-52],[-54,-42],[-54,-44],[-57,-22],[-57,-33],[-57,-41],[-57,-42],[-57,-43],[-57,-44],[-57,-49],[-57,-50],[-57,-55],[-57,-56],[-58,-44],[-58,-57],[-59,-57],[-1,-3,-27],[-2,-3,-27],[-3,-9,-27],[-4,-5,-6],[-4,1,19,28,29,40,41,42],[-29,4,31,37,38,40,42],[-31,1,28,29],[-42,1,4,28,29,37],[-7,1,19,28,29,54,55],[-47,1,28,29],[-5,2,20,28,30,40,43,44],[-30,5,32,37,39,40,44],[-32,2,28,30],[-44,2,5,28,30,37],[-8,2,20,28,30,54,56],[-48,2,28,30],[-21,35,46],[-33,3,26,29,30,46],[-35,3,21,29,30,41,43,45],[-41,3,12,26,30,35,46],[-43,3,12,26,29,35,46],[-29,-35,-43],[-30,-35,-41],[-49,3,26,29,30],[-55,3,12,26,30,51],[-56,3,12,26,29,51],[-29,-51,-56],[-30,-51,-55],[-6,22,27,42,44,45,46],[-34,27,46],[-42,6,13,27,36,39,46],[-44,6,13,27,36,38,46],[-50,22],[-27,52],[-52,27],[-40,-54,-57],[-58,42],[-59,44],[-45],[-46],[-60,12,21,26,28,29,30],[-61,11,13,36,37,38,39],[-62,9,18,47,48,53],[-63,14,15,16,17],[-64,10,19,20,23,24,25],[-65,60],[-66,61],[-67,65,66],[-68,65],[-68,66],[-69,62],[-70,63],[-70,64],[-71,69],[-71,70],[-72,67],[-72,68,71],[72],[-73,27,35,46],[-74,51,52],[-75,22,33,40,41,42,43,44,45],[-76,49,50,54,55,56,58,59],[-77,57],[-78,73],[-78,74],[-79,76],[-79,77],[-80,75],[-80,79],[-81,78,80],[81],[1,4,7,19,28,29,31,37,38,40,41,42,47,53,54,55,57,58],[2,5,8,20,28,30,32,37,39,40,43,44,48,53,54,56,57,59],[3,12,21,26,29,30,33,35,41,43,45,46,49,51,55,56],[6,13,22,27,34,36,38,39,42,44,45,46,50,52,58,59]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":34},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":11},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":10},{\"tag\":\"incompatible\",\"a\":54,\"b\":42},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":9},{\"tag\":\"incompatible\",\"a\":55,\"b\":41},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":66,\"b\":31},{\"tag\":\"incompatible\",\"a\":66,\"b\":33},{\"tag\":\"incompatible\",\"a\":66,\"b\":34},{\"tag\":\"incompatible\",\"a\":66,\"b\":35},{\"tag\":\"incompatible\",\"a\":66,\"b\":51},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":56},{\"tag\":\"incompatible\",\"a\":75,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":52},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":73},{\"tag\":\"incompatible\",\"a\":91,\"b\":75},{\"tag\":\"incompatible\",\"a\":94,\"b\":44},{\"tag\":\"incompatible\",\"a\":94,\"b\":58},{\"tag\":\"incompatible\",\"a\":94,\"b\":72},{\"tag\":\"incompatible\",\"a\":94,\"b\":73},{\"tag\":\"incompatible\",\"a\":94,\"b\":74},{\"tag\":\"incompatible\",\"a\":94,\"b\":75},{\"tag\":\"incompatible\",\"a\":94,\"b\":81},{\"tag\":\"incompatible\",\"a\":94,\"b\":82},{\"tag\":\"incompatible\",\"a\":94,\"b\":92},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":75},{\"tag\":\"incompatible\",\"a\":95,\"b\":94},{\"tag\":\"incompatible\",\"a\":96,\"b\":94},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[9,11,52]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,11,52]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[11,30,52]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[17,18,19]},{\"tag\":\"mate\",\"ridge\":81,\"a\":17,\"owners\":[9,41,53,54,71,72,73]},{\"tag\":\"mate\",\"ridge\":81,\"a\":54,\"owners\":[17,56,68,69,71,73]},{\"tag\":\"mate\",\"ridge\":81,\"a\":56,\"owners\":[9,53,54]},{\"tag\":\"mate\",\"ridge\":81,\"a\":73,\"owners\":[9,17,53,54,68]},{\"tag\":\"mate\",\"ridge\":82,\"a\":26,\"owners\":[9,41,53,54,91,92]},{\"tag\":\"mate\",\"ridge\":82,\"a\":79,\"owners\":[9,53,54]},{\"tag\":\"mate\",\"ridge\":145,\"a\":18,\"owners\":[10,42,53,55,71,74,75]},{\"tag\":\"mate\",\"ridge\":145,\"a\":55,\"owners\":[18,57,68,70,71,75]},{\"tag\":\"mate\",\"ridge\":145,\"a\":57,\"owners\":[10,53,55]},{\"tag\":\"mate\",\"ridge\":145,\"a\":75,\"owners\":[10,18,53,55,68]},{\"tag\":\"mate\",\"ridge\":146,\"a\":27,\"owners\":[10,42,53,55,91,93]},{\"tag\":\"mate\",\"ridge\":146,\"a\":80,\"owners\":[10,53,55]},{\"tag\":\"mate\",\"ridge\":273,\"a\":43,\"owners\":[66,78]},{\"tag\":\"mate\",\"ridge\":273,\"a\":58,\"owners\":[11,51,54,55,78]},{\"tag\":\"mate\",\"ridge\":273,\"a\":66,\"owners\":[11,43,54,55,72,74,76]},{\"tag\":\"mate\",\"ridge\":273,\"a\":72,\"owners\":[11,34,51,55,66,78]},{\"tag\":\"mate\",\"ridge\":273,\"a\":74,\"owners\":[11,34,51,54,66,78]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[54,66,74]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[55,66,72]},{\"tag\":\"mate\",\"ridge\":274,\"a\":81,\"owners\":[11,51,54,55]},{\"tag\":\"mate\",\"ridge\":274,\"a\":92,\"owners\":[11,34,51,55,88]},{\"tag\":\"mate\",\"ridge\":274,\"a\":93,\"owners\":[11,34,51,54,88]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[54,88,93]},{\"tag\":\"three\",\"ridge\":274,\"vertices\":[55,88,92]},{\"tag\":\"mate\",\"ridge\":529,\"a\":19,\"owners\":[44,52,73,75,76,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":59,\"owners\":[52,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":73,\"owners\":[19,35,52,67,70,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":75,\"owners\":[19,35,52,67,69,78]},{\"tag\":\"mate\",\"ridge\":538,\"a\":82,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":562,\"a\":52,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":562,\"a\":89,\"owners\":[52]},{\"tag\":\"three\",\"ridge\":216,\"vertices\":[71,91,94]},{\"tag\":\"mate\",\"ridge\":600,\"a\":95,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":664,\"a\":96,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":792,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[34,43,51,53,54,55],\"full_literals\":[-60,12,21,26,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[33,35,67,68,69,70],\"full_literals\":[-61,11,13,36,37,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,40,79,80,90],\"full_literals\":[-62,9,18,47,48,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,37,38,39],\"full_literals\":[-63,14,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[31,41,42,48,49,50],\"full_literals\":[-64,10,19,20,23,24,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,65,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-72,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,68,71],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[52,66,78],\"full_literals\":[-73,27,35,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[88,89],\"full_literals\":[-74,51,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[44,58,71,72,73,74,75,76],\"full_literals\":[-75,22,33,40,41,42,43,44,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[81,82,91,92,93,95,96],\"full_literals\":[-76,49,50,54,55,56,58,59]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[94],\"full_literals\":[-77,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,73,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,76,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-80,75,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,78,80],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[9,17,26,41,53,54,56,68,69,71,72,73,79,90,91,92,94,95]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[10,18,27,42,53,55,57,68,70,71,74,75,80,90,91,93,94,96]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,34,43,51,54,55,58,66,72,74,76,78,81,88,92,93]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,35,44,52,59,67,69,70,73,75,76,78,82,89,95,96]}]}"
  "138 67 0 120 118 0\n139 -73 27 35 0 102 121 0\n140 -75 22 33 40 41 42 43 44 0 101 123 0\n141 3 12 21 26 29 30 33 35 41 43 49 51 55 56 0 101 102 136 0\n142 6 13 22 27 34 36 38 39 42 44 50 52 58 59 0 101 102 137 0\n143 -80 0 130 131 128 129 125 50 51 52 53 54 55 56 57 58 59 61 62 140 124 98 0\n144 78 0 143 133 132 0\n145 73 0 144 126 0\n146 74 0 144 127 0\n147 42 44 22 27 0 145 102 101 100 95 139 35 34 32 29 97 92 99 91 142 0\n148 -42 29 30 21 -35 0 138 101 30 32 34 33 29 27 35 104 109 110 108 28 103 12 38 39 81 0\n149 29 30 21 27 0 145 138 101 139 32 34 33 29 27 35 104 109 110 108 30 28 103 12 13 148 147 42 44 81 0\n150 -44 -29 30 27 0 145 102 19 15 139 34 33 32 29 40 41 43 76 94 68 66 0\n151 30 21 27 0 145 146 97 122 46 139 35 33 149 15 16 17 19 84 89 75 78 150 100 147 37 48 53 73 77 135 0\n152 44 -30 27 0 145 102 25 24 22 20 139 35 33 32 29 147 36 37 70 93 74 66 0\n153 -30 27 0 145 146 97 122 46 139 34 33 20 21 24 25 85 90 69 72 152 41 43 49 55 60 67 71 134 0\n154 27 0 145 120 139 26 27 29 32 33 34 35 104 109 112 119 117 115 153 151 3 4 5 6 7 107 0\n155 -12 0 154 8 0\n156 -16 0 154 9 0\n157 -17 0 154 10 0\n158 -26 0 154 11 0\n159 -28 0 154 14 0\n160 -29 0 154 18 0\n161 -30 0 154 23 0\n162 -35 0 154 31 0\n163 -51 0 154 45 0\n164 52 0 154 96 0\n165 -21 0 162 102 79 0\n166 -53 0 164 47 0\n167 -60 0 165 155 160 158 161 159 103 0\n168 -65 0 167 108 0\n169 -68 0 168 111 0\n170 71 0 169 120 119 0\n171 69 0 170 116 0\n172 70 0 170 117 0\n173 62 0 171 113 0\n174 63 0 172 114 0\n175 -18 0 174 157 156 1 2 106 0\n176 3 0 102 163 162 161 158 165 160 155 80 86 88 83 82 87 141 0\n177 -1 0 176 154 63 0\n178 -2 0 176 154 64 0\n179 -9 0 176 154 65 0\n180 -47 0 177 159 160 72 0\n181 -48 0 178 159 161 78 0\n182 0 181 179 166 173 175 180 105 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record008
