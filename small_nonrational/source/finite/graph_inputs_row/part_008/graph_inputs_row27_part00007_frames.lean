module
prelude
public import GraphInputsRow27Part00007Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x167a9f5149612062841e82cf7ddf3a4726db1782eb58ab1153a954f69dd2023a448869049f93ba73cda1a3332634ad1492704a08f91321c3c4760e51b6348668c817a2083e86c0d01782c8550a814c2904d0900dc1902a0500981181f03c0740e0140260400700a0120200380400600800800 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x4878fd1a22d43c85301df43b5752e8dcab856dad91abb4c66ccd18ab0f614bc5722e05bcb1d46a6c4c096926235450825021f93ca76ce89c93706a0cd99732a60ca5942272464851071ea3cc788ee1b034c660bd1722a4500941241ac348600a41402784b0940e81b03404808c1001f03c0480780e01a0280480800800c00800 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8758257ea7c47b57b176975b74e7206e26ae69568e63862c5ee5d75d05c05b45ad59759057b5745705094fc4ee4bd4824464294223c33b537a36035934833d33732131b3063002fc2d52c32a528927d26b24d23121f21220b20a1f21d91cb1be1b51a619d18b18217917415c14313511810f1050fc0ed0e40e30d30cd0c80c70c307b07907806f06e05c05b05805705604304104003703602402302001f01e } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x8ae22866148420e826047f9fa7b9e176dd7729c76edb56c5ad69da36799a65591639835f9775bd615414a519334bd2146d1744d0d421033fcfb3dcf43c4ee3ace4384de36cd433cc9310c32fcba2d8b32bca828c9c25c9223c8b218821e4741bc6b1905f1785814c4e1344a0ec390e0370d8310c02e0b42c0a026094230881c06c1906017 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0608.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0608.count (({ width := 9, code := 0x31383bede6ed74b85b2d165b056aab51a5d26893f9dce66b3196ca64b218f45a270f84c09f4f5793a5cee06d35daad2673258cc25faf172b75aac15aab54a913e9b4b2552690462250e83401f4f274389bcd8683197cb4582a144a04b23908823e198c86230178a85228138984421100783a170b0542813 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0608
    Papers.RationalityTen.SharedFrameCatalogue.group0608_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
def record013_frame004_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f38e936dd34ad9decd75f9af2173ab4156da98943ea0b4ae25211ce8a944b21910848303fb9f94f6a7a53cb9afcd28669306969ca5c4eb26b90a08283b31ba8d8866030e17e0b0c562281138898c478233112885c4242090fd87b43c41d40e6872c3781ae0d3868433218e0c385e02e216a0b1054c28a13e095849023811408484082000ed073037c1ba0d603d81e40f006f03701700b605802b815808604102000dc06c024011808003e01e } : Fields).get c.val)
theorem record013_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record013_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 4)
      (record013.inverseMaps 4) record013_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record013_frame004_links_0000 record013_frame004_links_0064)
theorem record013_frame004_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 4 :=
  of_group record013 4 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame004_indices record013_frame004_graph record013_frame004_links
def record013_frame005_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7557296f46cf6af6a366064d6406275f95ce5a859b55554f5255024f54df4ce4c94a449747946d4664254164063ed3bf39436b36131b3152eb2c52bc2a229428f26725c23c23222c20c2031f41e71e41db1ca1bb1b31a419c19a18a17917216e16715b15314613d13412e1241181121040fc0f40ef0e40dd0dc0cd0c50bd0bb0b507907707606d06c05a05905605505404304104003703602402302001f01e } : Fields).get c.val)
theorem record013_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record013_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record013) (record013.maps 5)
      (record013.inverseMaps 5) record013_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record013_frame005_links_0000 record013_frame005_links_0064)
theorem record013_frame005_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 5 :=
  of_group record013 5 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record013_frame005_indices record013_frame005_graph record013_frame005_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (Fin.cases (record013_frame004_supported hcells) (Fin.cases (record013_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c78d7c69a34299eecf0612afe97a4b7e5912c45560a9f53b29914249b64d2a51126690a47c23851a68cc45f22d515c8a244ca24911a7c63d01df4e526d736319c8cc26373131750b0457128e94309c44d125d12b494c49824792208fa47523791ac8223f31e28e687183721a48c806222e61690b00540281138098c4a6235113089042a1fa0f587a43ba1bd0cf06343001700a9050c28213208b842020c0f307603941bc0d703781b80d606a030017c0b805b01b80d8066032014009c048023 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f2ee906deb4c59e0cd85fb2f2d740b4156dab1d4bea4f51128393709594a4239d1ac8ab44c219d08a8334081fd8fc87cb3d91e88f306c234b99b0c1a5a72c994aca364ee26d121084a4141d98e886ee3641998c445fe2dc1610ac052e27e1370990478233112885c4242090fd87b43d01da0e9872c3781ae0d3868433218e0c386142fa1720b585a02c41530a284f8270130092847823811408484081fe0f307603941bc0d703781b80d606a030017c0b805b01b80d8066032014009c048023 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3399998bf65e5ae81682ac7527a8894249b84a4235915e8984069fe0fd07c83da1e98f2a6c234b99b0c1a59328d93b89bc48420a0e886f636416c8b1056829414009c84c2237119089042c20d10407e83d81e30ea87383901bb0cf06603121820be05b42ce15f0a204d425e12708c844c2160fe07403880de06b02f816c0b005502a00dc066027011808003a01c00d8054026012008803c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x303980cb7d5b82d8d606aa352528ed46a9cf4b524311fc8f6428a0f90608113ff1fc0fce7303921c5cd8065f30217e0be659e2a493e49de4e923411688a043921590848343bc1d70e386de35c1a70cb861e30417b0bc05c22b9133896c47a22d110880c3f41ec0d206082ee16b0a8851827412607c03a40de06b02f816c0b005502a00dc066027011808003a01c00d8054026012008803c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x75f75871a7086f96d66a066764964061b5e55ac59158354d54553e53152952251c4cc4b74a647d4454053e43dc3b037833831a30c2d82d02c92bd2b62b02ab27b27225b24723a23221a2041f31dd1d31ca1bc1a019718517b17015f15814a12e12011710c0fb0f00e60d80c40c106f06b05f05b05805505403703302702302001d01c01b01501301201100f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x27fce39852ee41c698a10820dbf27c8ec5d5ba46e4db1b2b596a6d31a33115feb2d572a951c9591fa39464821021fc3ea780ed1d433a5e4b31632c24fc9611d222434858e81b6318600b61602ac540a410c2103f8670cc1882c8570a61442684c06a0cc1902604a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xa2543e6b4bc9431ba35c5b83b022013ff7b4f35e2bb9760eadd335a676c8175ae85a6a553f2784ea96126a474788d518a2c414808f91e13b672cdc9b132a638c498429a5109d92b24a47c828f71de390638bb16c2c0548a20dc1b43485e0ba16c2a8540720dc1982704a08c0e81c0360540981202003c0700c0140200380500600800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6733331740b2a56328894249b847d22bd13088a40e1fe0fd07c73da1e98f2a66c2fb16489dc4de2420f186f63641ab0ba05882b41498a004e426111b88c844821610708043e61ec0ea873838e1c20c4860c2f616d0b3857c288135097849c2160fe07b03c01d00e203881bc0d605f02e816c0aa05401c80dc066027012808c03a01c00d8054026012008003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x77d7737166f36d668c6846616025d45c25bc57d56c56254c53e5325274cc49846641340b3eb3a538337837232e31730a2fb2ee2e62dd2af2a729127b27125c24723c21f21620e2071b91ad1a218b18117815213d1311250fc0eb0e30dc0d20ca06e06c06805c05a05805205103803603202702502301d01c01b01501301201000f00e00c00a008007005003002001000 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce35fb2d0558ea4f51326e12908e746b22ad08480d3fd1fa4f907b63ca9b08c1a59328d93c89084141d98e886ee30e16c8b1856a294141098446e23210688203f41ec0f187543901ad0cf066032018a0c105f02e81670af854828813d09a84bc24211908983f81d208d03501800b805b02c01580aa05401900a0048023010007803a01c00d80540260110078038016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2d0558ea4f4dc25211ac86442120c101a7e93e41edcf2a60d2c9946c9084141d10cc061c2fc16c8ad452828313088dc46420d0fd078c3901bb0d6869833c1980c506082f81750b3857c2a414409e84d425e12108c844c2180fe04902340de06a030016c0b005702b01540a803701900a004602000f807803a01c00d8054026011007002c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c6ac651326e123c8fa473a2ad11481c3fd1fa4f8e7b63ca96489e44841f50f187663771ab0ba058c2b51498a084c223711908384021f30f6075438e1b40c8062830617b0ba059c2be1520a204f426a12f09083f81ec0f007482340e206a03001740b805b02b01540a803901900a004a024011807803a01c00d80540260100078038018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x9792862dc1d7fef81ed3c6772ec9d333b640b4d4aa754b89612423c46e8b1052023b66e4c49842ea59ca71442764d49291f2264147e8f71de374640bb16c2c0438850dc1b43405f0ba16c2b8560aa1501c8370640a01282303e0780e81c0360540981001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5952b193708fa44520c10387e93e39edcf2a5f62c9121078c35617e0ba056a293141898446e23210707cc38e1c20da06983141830bd85d42ce15f0a9051027a13509784842180fe07b03c012408d03881bc0d406002e816c0ae05602a815007203701900a004a02300f807803a01c00d80540260100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce2596a93944a9b8456226910a86442120c10427f93e41edcf285f928d13c49083781b30d4466030e17e0bb458a294141898046e2320f207583a01c20dd86d035a1a60ce863c30617c0ba85982be1520a204f426a12f090844c2180f606d82340ee06a030016c0b405802b81580a803f01900a0046022010007c03c01c00d805402600e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c6b40544a899322948473a2ad11480c3fd1fa4fac7b63ca9830aaa4f222e90507663771ab0b6058c2b51510a084c223811588344101fa0f6075438e1b40cf865c32018a0ba059c2be1520a204f424211908983f81ec0f007482340da06a03081800b805b02b01540a803501900a4050024011807803a01c00d80500260110078038018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x199aa8c528284d2868fa460a2b113488a4181fa4fb67a53c99560a384df2078f1871a3781b30d585f82b515389c44be1fa0f987943bc1d60e8071c3841b40d3067c3141810b605942be1520a204f425e12108c84301ec0f006a824810206f03001740b605a02b81580aa04901b80a004a023011007c03c01d00d804c022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33ad9a0ac7510a84126a90f475235d15089d443a10901a7fa3f49f68f707a33c8964c9da4dc2008f6c76c3a31ba0da46a630e16c8b1856a2a614209bc4ba20d10407e83d81e50e8072035a1980c8062830417c0ba05642a414b0a204f426c12f090846021410307e03dc1d20d403c81a80d206803001600ac05502080c8062030014008003c01d00d804c02200f0070034016009004001c00c005002000c004000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa2aa148d58c47be7a879a79378377276375373e72a70e7036f06de6cb6b069d56f56248f4804744704634554474394284183ff3f83e93db3ca3b33a32bd2ac29628627526725a24923921a2091fa1e91ba1ae1a019118317316514613712b11c0f10e60d90cc0be0b207506d06806706605e05905803f03703203103002802302201b01300e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
def record051_frame002_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19eccee53ba9992168fa476a3a11c28da469a33118a8be45aa2c11528a244da249116638314138c9a64c626092e89664ad253127c93048f245120c8fa47723791a45b22c71548a6451427a135896c49822d10e88384001c60db069c32e1880bc05a429413a09584741ee0f007483881b60d403b81bc0d406903401800b605a01f80dc06403101800a004602200d804c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record051_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record051_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record051) (record051.maps 2)
      (record051.inverseMaps 2) record051_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record051_frame002_links_0000 record051_frame002_links_0064)
theorem record051_frame002_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 2 :=
  of_group record051 2 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record051_frame002_indices record051_frame002_graph record051_frame002_links
def record051_frame003_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19dacd3511a84115889a441a1e50ce855422a0cd0448103fb1fb0fb87cb3dd1e88f204ef26e0de06cc34f1a28ccc64231117f8bb85b82c215c0aa052e28613709703ac1d00e106ec3681ad0d3067c33018a0c185f02ea1590a9052c28813d09b04bc24211a08984301ea0ee07383801b20d303b81bc0d406903401800b605a01f80dc06403101800a004602200d804c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record051_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record051_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 3)
      (record051.inverseMaps 3) record051_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record051_frame003_links_0000 record051_frame003_links_0064)
theorem record051_frame003_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 3 :=
  of_group record051 3 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame003_indices record051_frame003_graph record051_frame003_links
def record051_frame004_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x64b63a55654c4a949e49449248647b46f46845c44d43743342941c4134023f631d31327026525b25624d24023822f2212141fe1fa1ed1e41da1c91bd16015d15414f14914313d13813212912511f11810a1051000fb0f60f00ea0e00da0d40cf0be0b80b30af0aa0a706f06806306206105905405303e03703203103002802302201b01300e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record051_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record051) (record051.maps 4) (record051.inverseMaps 4) record051_frame004_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record051) (record051.maps 4) (record051.inverseMaps 4) record051_frame004_indices (Fin.ofNat record051.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record051_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record051) (record051.maps 4)
      (record051.inverseMaps 4) record051_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record051_frame004_links_0000 record051_frame004_links_0064)
theorem record051_frame004_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 4 :=
  of_group record051 4 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record051_frame004_indices record051_frame004_graph record051_frame004_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (Fin.cases (record051_frame002_supported hcells) (Fin.cases (record051_frame003_supported hcells) (Fin.cases (record051_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2ad1518a62528289d41692147ea3a91888b044aa2290607fb2c01560a5c51c279935c7da3c91db0e406f83611ab0bf058e20810087e83e61ec0f287783ae1c70e106d034c19f0c886042e616c0b2857c2a414409e84bc250111085040c1f80f60780244102078037017c0ae05602a8124080036013807c03c01d00d8048022010007803801a00c0050024010005002000c004000 } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
def record054_frame002_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x28e94249f14f1270536690246f232914e89344221dd01e7db3191838bde5e12e116d0a2a4f7275133097e4b1253915c85e33a1920c5460c2f71740b645942af14e89e04c025211d08883fe1f20f2875436a19c0c805e42da142097848822c10807d8244102078037017c0ae05602a8124080036013807c03c01d00d8048022010007803801a00c0050024010005002000c004000 } : Fields).get c.val)
theorem record054_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record054) (record054.maps 2) (record054.inverseMaps 2) record054_frame002_indices (Fin.ofNat record054.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record054_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record054) (record054.maps 2)
      (record054.inverseMaps 2) record054_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record054_frame002_links_0000 record054_frame002_links_0064)
theorem record054_frame002_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 2 :=
  of_group record054 2 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record054_frame002_indices record054_frame002_graph record054_frame002_links
def record054_frame003_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x5cc5c05ae5a158d57952a51b50f4fa4ee4da4d54bb4a93f53e93d73cc3b53a034f33f3343213122fd2f92e02cd24023322721d2132081fb1f01da1d51c41b11a419117a16615d15314a13e12c12110c1010e30d60cd0c30bc0b808507b07406b05d05505405304703e03502701f01e01d01b01201101000f00e00d00c00a009008005004003002000 } : Fields).get c.val)
theorem record054_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record054) (record054.maps 3) (record054.inverseMaps 3) record054_frame003_indices (Fin.ofNat record054.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record054_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record054) (record054.maps 3)
      (record054.inverseMaps 3) record054_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record054_frame003_links_0000 record054_frame003_links_0064)
theorem record054_frame003_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) : Supported record054 3 :=
  of_group record054 3 (smallEmbedding record054) (small_cells_exact record054 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record054_frame003_indices record054_frame003_graph record054_frame003_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (Fin.cases (record054_frame002_supported hcells) (Fin.cases (record054_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x697b499a30d0a681b3d59d4b0356f2ad9546a7e52f265d2e494a49ba4491e48ed47423851b48d3466231517c8b745722ad13a8964479b24ce46392ba14749c84c925d12b494c498248922090847d23a91bc8d231c16e8b0856829913d09ac49823c11107f03dc1e00e886d832e1880b4856427e11908583f41f20f007483881b60d5057826c0ee06e034017c08003601980c8062027012008c04401200580280120080028010006002 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x9332223ec25829025ebbcc77eee5d4b9c71ee11bdb6f6cad61a4b45682b7d652bb4f49d9362614ba93919a2843c849049f63e279cf09db338648c117c2da568ab95028c4f89992b234438841021f43d4778e91c83786b8d118e2f85c0b11522904f097126228400640be1581e0340620c01782e04c094118220420680900b0140240400600a01001802 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x32418a6c37515a7b93a49874bf25c12c495b4a6a509280931491a47121c90747e23b51cc8df34c9964c785722b094f4a3050527092f4934477233910c8643ef1ef8f3c6062f21670aa452c27212708ac4101f80ea070c3001700b005542a01490a104ec26812d093047c22c10f085840c1f80f507803a01c40dc06b034813609103c01b8080036018009c04c024011808804001f00f0074036012008803c01c00d0058028012008 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x82280f6e46bc5ec5bd59c59359058858057857056856055754954653e53152a5223f23c33a22f62ce2b02ad2a529d29528d28527d27426626325b24e24723f1d81c31b41b11a91a219a19118918217a16e16a16315815014914213f13713012811f1171101080fc0f80f10e60de0d70d50d10cd0c90c50c10a909b09a09108e08d08c07807706e06b06a06904003002702402302201b01200f00e00d } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
def record059_frame002_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x73dc9675975b9665855f5795c5695855954549505354c52947515434611042ceb394de374db364d7354d3344cf330cb324c6310c22889c25494248902388c2288821883208801f47b1e4771d8741c8701b86c1a868194641885f1745b1685916057158551384811c3e0ec3a0e4330c829098250901e074140441003c0e0140200400 } : Fields).get c.val)
theorem record059_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record059_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record059) (record059.maps 2)
      (record059.inverseMaps 2) record059_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record059_frame002_links_0000 record059_frame002_links_0064)
theorem record059_frame002_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 2 :=
  of_group record059 2 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record059_frame002_indices record059_frame002_graph record059_frame002_links
def record059_frame003_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x88a1c7c1ea705b86c5af6b9ab6a1a56899f67199651936418c62988575545352d49d2047d1c4651644d104350a41504404fd3ecf9364d3330cb320c5308bf2f0b92d8b12c0ad2a4a7294a32889f27099258932408d22087210801f87c1ec7a1e4781dc761bc691a05f1705b1685414c4a11c46114350c027090230881b0480f0380d } : Fields).get c.val)
theorem record059_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record059_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record059) (record059.maps 3)
      (record059.inverseMaps 3) record059_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record059_frame003_links_0000 record059_frame003_links_0064)
theorem record059_frame003_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 3 :=
  of_group record059 3 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record059_frame003_indices record059_frame003_graph record059_frame003_links
def record059_frame004_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x95b26a18c1c774e79c4b81700de9bab6f6d6d95ae354690d1da0b38668cbd60aa55209291aa1e43885d08a0d410800fc9f13ca78cef1d53a2730c517b2e25b8b49622b6554a714627c4cc9892a23c4648990d2164107e8f71e23a4710da19e330630ba16a2bc568a71402744c8951162144207f0f81ec3d06d0d8190310610c00f81702604808c1101b02403c0700d } : Fields).get c.val)
theorem record059_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record059) (record059.maps 4) (record059.inverseMaps 4) record059_frame004_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record059) (record059.maps 4) (record059.inverseMaps 4) record059_frame004_indices (Fin.ofNat record059.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record059_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record059) (record059.maps 4)
      (record059.inverseMaps 4) record059_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record059_frame004_links_0000 record059_frame004_links_0064)
theorem record059_frame004_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 4 :=
  of_group record059 4 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record059_frame004_indices record059_frame004_graph record059_frame004_links
def record059_frame005_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0653.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0653.count (({ width := 8, code := 0xd0ccc4c0b9b4b1afaeadacabaaa8a6a4a1a09f9d9c9b948f8c8884807f7e7d7c7b7977757271706e6d6c6864605f5e5d5c5b5957555251504e4d4c4a494847464543413f3c3b3a3837363534333231302d2a29242322211e1d1817161512110c0b0a090803020100 } : Fields).get c.val)
theorem record059_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record059) (record059.maps 5) (record059.inverseMaps 5) record059_frame005_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record059) (record059.maps 5) (record059.inverseMaps 5) record059_frame005_indices (Fin.ofNat record059.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record059_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record059) (record059.maps 5)
      (record059.inverseMaps 5) record059_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record059_frame005_links_0000 record059_frame005_links_0064)
theorem record059_frame005_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 5 :=
  of_group record059 5 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0653
    Papers.RationalityTen.SharedFrameCatalogue.group0653_facts record059_frame005_indices record059_frame005_graph record059_frame005_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (Fin.cases (record059_frame002_supported hcells) (Fin.cases (record059_frame003_supported hcells) (Fin.cases (record059_frame004_supported hcells) (Fin.cases (record059_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc3260eb00d7dcbe25da2e79540a7f5342981474a24508a6112588ea46a23210e283440fa038fec7dc3e31ebcd3e69934419f0cd666132b1910c646212d1165caf65652ac14d8a5051528413a89a44c4251125090447322f91408803aa1c60db06c433d1948c5c6062e31610ae0528281137897448e23411108383fe1b90c305d82c6150087040019205c02d81680ae05602a812407e026012008c04402100f807803a010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
def record060_frame002_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x2c4afeb8ac6aea9ea499a5e9625593e4c926358821684e12801f87d9f47bdec7a9e86b1ab6a1a668da167d9c669986017e5e5745c96d5ad665915d559545354b5214650d414fd0f414f93d0ea394e2378d9340ca314bf2f4bc2e0b52c4ad2a89522c89210801c86f19443108410f83d0f0370c0230842007c1e0701b0681003c0e0340b028090200400c0200400 } : Fields).get c.val)
theorem record060_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record060_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record060) (record060.maps 2)
      (record060.inverseMaps 2) record060_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record060_frame002_links_0000 record060_frame002_links_0064)
theorem record060_frame002_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 2 :=
  of_group record060 2 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record060_frame002_indices record060_frame002_graph record060_frame002_links
def record060_frame003_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xcba658b29192cc8f640b1e95b8ace5602ae5556aa454ea6c52a691b48523f914086842ba13508a83d41b20bccf467533799a0cc265a3299930c8a63f2ba95b0aa253529314289f84e826f931095049923e91bc8ca46122d91588a236a1a78cc063e2fe1770b745922ae14789f84ba24d11e08c845422310e08544101a20b5055c28a13b08403f81a405c02d81680ae05602a812407e026012008c04402100f807803a010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record060_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record060) (record060.maps 3) (record060.inverseMaps 3) record060_frame003_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record060) (record060.maps 3) (record060.inverseMaps 3) record060_frame003_indices (Fin.ofNat record060.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record060_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record060) (record060.maps 3)
      (record060.inverseMaps 3) record060_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record060_frame003_links_0000 record060_frame003_links_0064)
theorem record060_frame003_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 3 :=
  of_group record060 3 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record060_frame003_indices record060_frame003_graph record060_frame003_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (Fin.cases (record060_frame002_supported hcells) (Fin.cases (record060_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x5c6ad6569ea3a50927c53c49c14daa4c518e890442a1c908c8204079fb0fb67d23e11e40efa76b3191838bde5e12e116d8a7a4e725e12c8944481232115c87842f213106c7ea3e71ed8d3867431517b8ba05942bf14e8a284f026d130094848e23a11888883fe1f20f2875436a19c0c805e42da1640ab05102100c803b81700b605a02c015c0ac05501f8090046022010007c03c01d00d804401e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
def record061_frame002_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x8510720c3cb784ee9dabad752e21b235169ad1d9e32f64ec798b312614be978ae852aa253ea794da9a52522a43485d092063f47d0f59e53c4774e79c9386638c41762ca580a794b2824f49a9312524949091922a434818fc1ea3b8708d419a3105e8ba1662b0490720ac118228440841042003f0660841001f03a0700d81a0300440780e01a0300580a0120200280400600800800 } : Fields).get c.val)
theorem record061_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record061) (record061.maps 2) (record061.inverseMaps 2) record061_frame002_indices (Fin.ofNat record061.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record061_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record061) (record061.maps 2)
      (record061.inverseMaps 2) record061_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record061_frame002_links_0000 record061_frame002_links_0064)
theorem record061_frame002_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 2 :=
  of_group record061 2 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record061_frame002_indices record061_frame002_graph record061_frame002_links
def record061_frame003_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0xac6a7a926196e5594a4c926338821684e0e82a04801fc7e1f67cdec7a9e86ada66859f6699860d745b56b59d61569565454d52d4a50d414fd10431003d0f1394e2370d934cd0328c8314bf2f4ba2d4b12b4a82889a2549022c89218811d06514843108410fc3e0f43c0c0210801f0741c06c1a0601103c0e0340c02c0a024080140400c0200400 } : Fields).get c.val)
theorem record061_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record061) (record061.maps 3) (record061.inverseMaps 3) record061_frame003_indices (Fin.ofNat record061.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record061_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record061) (record061.maps 3)
      (record061.inverseMaps 3) record061_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record061_frame003_links_0000 record061_frame003_links_0064)
theorem record061_frame003_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 3 :=
  of_group record061 3 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record061_frame003_indices record061_frame003_graph record061_frame003_links
def record061_frame004_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x695b39199aab454629894a0a27509a5211ce8ad44d22150c88424182034ff67e93ed9ed4f4a7932c01560a5c51c279937c8283b31bc8d986a23301870bf05b22c715a8a9c50227112f88344101fa0f607943ae1d00e106ec3681ad0d3067c3301910c506042e616c0b2857c2a414409e84bc25012108c844c1ec0d503b81700b605a02c015c0ac05501f8090046022010007c03c01d00d804401e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record061_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record061) (record061.maps 4) (record061.inverseMaps 4) record061_frame004_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record061) (record061.maps 4) (record061.inverseMaps 4) record061_frame004_indices (Fin.ofNat record061.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record061_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record061) (record061.maps 4)
      (record061.inverseMaps 4) record061_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record061_frame004_links_0000 record061_frame004_links_0064)
theorem record061_frame004_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) : Supported record061 4 :=
  of_group record061 4 (smallEmbedding record061) (small_cells_exact record061 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record061_frame004_indices record061_frame004_graph record061_frame004_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (Fin.cases (record061_frame002_supported hcells) (Fin.cases (record061_frame003_supported hcells) (Fin.cases (record061_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1920c5361fa8ad3dc9da4c125f52de9614ad253128a93d498248923690d48323fd1d08e146d1a64cb26442b91584a7a51828293849a24bd24d11dc8ce443219108c7de3df1e78c0c5e42ce1548a584e426212708ac4101f80ea070c3681800b8058029e1480a084e826612c092847822e10a07783440d005e02e016c0b405802b81580aa0300130090046022010007c03c01d00d804401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
def record062_frame002_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a56ce4666a98944ea134a224c92188e746a22b5134887432210906080d3fd9fa4f6a7a53c994b89e64df2080ff87b03b31d00de46cc3531980c385f82d91638ad450227112f88344101fa0f607943ae1d00e406ec35a1a60cc06443141730b605942b21520a5851027a13609784a024211307b83540d005e02e016c0b405802b81580aa0300130090046022010007c03c01d00d804401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record062_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record062_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record062) (record062.maps 2)
      (record062.inverseMaps 2) record062_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record062_frame002_links_0000 record062_frame002_links_0064)
theorem record062_frame002_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 2 :=
  of_group record062 2 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record062_frame002_indices record062_frame002_graph record062_frame002_links
def record062_frame003_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x9865493a1e8460b799e577dd9759d0735c9715bf6f1b66cdb0695a267d765a5634f93d4dd314b92849521475174510e42d083f4fa3dcd9360d2330c930cc02f0b82c8af2a4a628c98254922408f2388d2308b22889220862087d15c4d12c4a1244711845110300982408c220801f0781d06c1103c0e0340b02809020060140400c0200400 } : Fields).get c.val)
theorem record062_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record062_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record062) (record062.maps 3)
      (record062.inverseMaps 3) record062_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record062_frame003_links_0000 record062_frame003_links_0064)
theorem record062_frame003_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 3 :=
  of_group record062 3 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record062_frame003_indices record062_frame003_graph record062_frame003_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (Fin.cases (record062_frame002_supported hcells) (Fin.cases (record062_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x68533d59dcab053c299928890c47d23b51d08e146d234d1988c545f22dd1608a9451226512488b33918e4c5051d272134c98c4c125d12cc95a4a624f926092248a24191f48ea46f2348c645b42c71548a6451427a135896c49823c116887441c1c60db069c32e1880bc05a42b214a09d04ac1ee0f007483881b60d403b81ac0d406903401700b605a01f80cc064031018009004602200d803c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
def record063_frame002_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x698b3a99a6a5f51228411ce8ad44d220d0f286742aa1150668224081ff8fd87dc3e59ec8f4479029593c09b83b31bc8d9869e3451998c846222ff1770b705942b81540a5c4fc26e12e07b03ae1d00e106ec3681ad0d3067c3301910c5060c2f81590a9052c28813d09b04bc25012108d044c1ea0ee07383801b20d303b81ac0d406903401700b605a01f80cc064031018009004602200d803c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record063_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record063_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 2)
      (record063.inverseMaps 2) record063_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record063_frame002_links_0000 record063_frame002_links_0064)
theorem record063_frame002_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 2 :=
  of_group record063 2 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record063_frame002_indices record063_frame002_graph record063_frame002_links
def record063_frame003_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa55a28a149038d68c47f77bf7a879a79378377276375373e72a7167036f06de6c36b069d59d5705624bd4904804744704634554474394284184073f83e93db3c23b33a32e72be2ac29628627526725a24923922821a2091fa1ba1ae1a019118317316515614613712b0f10e60d90cc0be0b207506906806706605a05905803f03303203103002402302201b00f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record063_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record063_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record063) (record063.maps 3)
      (record063.inverseMaps 3) record063_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record063_frame003_links_0000 record063_frame003_links_0064)
theorem record063_frame003_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 3 :=
  of_group record063 3 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record063_frame003_indices record063_frame003_graph record063_frame003_links
def record063_frame004_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x67164963a57655754c4cb4aa49e49449248647b46f46845c44d43f43342941c40b4023f633d31e31329227126525b25624d24023822f2212142061fa1ed1e41d21c91bd17116115d15414f14914313d13813212d12912511f10a1051000fb0f60f00ea0e50e00da0d40be0b80b30af0aa0a706f06406306206105505405303e03303203103002402302201b00f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record063_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record063) (record063.maps 4) (record063.inverseMaps 4) record063_frame004_indices (Fin.ofNat record063.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record063_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record063) (record063.maps 4)
      (record063.inverseMaps 4) record063_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record063_frame004_links_0000 record063_frame004_links_0064)
theorem record063_frame004_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 4 :=
  of_group record063 4 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record063_frame004_indices record063_frame004_graph record063_frame004_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (Fin.cases (record063_frame002_supported hcells) (Fin.cases (record063_frame003_supported hcells) (Fin.cases (record063_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x84580076e7666ea6e46cd68c62f6296025c155653351b51649c49548c48646d42c4023f23d23c83bf3b939134b3353253072de2d92c52bc2aa28d28627325c22520d1c11ba1b61af1a719e18f16d16914413d13312c12711e1070ed0e20cf0ca0bd0b706905a05105003e03d03903403102d02c02a02502201600d00a008007003002001 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
def record068_frame002_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xd0b9d30860fb8d70adcd90aab52a96cf490d13a1041b7c2f79eb3d078ae6dbeb796d8d9dae352682c5d843045f0afd5e2a252e9f5352604ac921112123b8744e51bf3666a0cc9792e4548a39372584888b8ff1d636c670c413e2603185609a1301e03b06e0d01882d0580a81282202c0340500800e00c01001 } : Fields).get c.val)
theorem record068_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record068_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record068) (record068.maps 2)
      (record068.inverseMaps 2) record068_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record068_frame002_links_0000 record068_frame002_links_0064)
theorem record068_frame002_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 2 :=
  of_group record068 2 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record068_frame002_indices record068_frame002_graph record068_frame002_links
def record068_frame003_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xad956e8cd1699b32260c958c9186244227bcef5d2ba16aad49a4345672c417b2f05ccb856e2d557aa4d442824ec9592aa444748ad0b20f4087cce61bb3025e8bb16e2cc57caa93926a4708a10a2043f07a8dd19a3085b8b11362583385a0a21401f03d0720d01882d0580a81282202c0340500800e00c01001 } : Fields).get c.val)
theorem record068_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record068_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record068) (record068.maps 3)
      (record068.inverseMaps 3) record068_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record068_frame003_links_0000 record068_frame003_links_0064)
theorem record068_frame003_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 3 :=
  of_group record068 3 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record068_frame003_indices record068_frame003_graph record068_frame003_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (Fin.cases (record068_frame002_supported hcells) (Fin.cases (record068_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x2b856eabf53aa3d46a7949284cfb9d92de5b4908eb14613418812fedfa3ef7d0f51e83c075ce9db8b6b6ccd81a6b36662c357d2e95b4b1d51a9050c9f52e24c4608b5029fa3886f0d319c30c5dcaf15228c4b49211520e3c4730cc17e2e8538a013825c4788c0ee1d83705d06e08c0f81e01a02000800 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
def record076_frame002_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x812037fdfb7e9f97e1f67c9ee7b1de775d071dbc6bda968d9f6759b6659665190635896057f5f57b5dd705b5625695554d4f5093a4d9324b1284811d42d063c4eb394e2358cf308ba2cca728498240851fc721a8661745a15c531344c10c420fc380901d06c1a02c0700400 } : Fields).get c.val)
theorem record076_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record076_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record076) (record076.maps 2)
      (record076.inverseMaps 2) record076_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record076_frame002_links_0000 record076_frame002_links_0064)
theorem record076_frame002_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 2 :=
  of_group record076 2 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record076_frame002_indices record076_frame002_graph record076_frame002_links
def record076_frame003_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0116.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0116.count (({ width := 9, code := 0x349a3d0e7f3d9dce66b2d94c961b0b7dbbdced566b157abb5aac552a54fa6d2a87419f4f27334994ae4d2290c7e2f12874320b017e3edd2e66933590c45c2c5489f4ca4118873f9d8e26a31980ac5428938964a211047a3711874361a0601c0200 } : Fields).get c.val)
theorem record076_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record076_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0116.localPairCheck (smallEmbedding record076) (record076.maps 3)
      (record076.inverseMaps 3) record076_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record076_frame003_links_0000 record076_frame003_links_0064)
theorem record076_frame003_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 3 :=
  of_group record076 3 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0116
    Papers.RationalityTen.SharedFrameCatalogue.group0116_facts record076_frame003_indices record076_frame003_graph record076_frame003_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (Fin.cases (record076_frame002_supported hcells) (Fin.cases (record076_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x11020640b804ffdf43e778ae8dcdb8c6acd1198b225a0b2d63ac457eaf55cab355eaad3f27b4c49852da1641e808fe1ef388704d99ad340668ca9913005ecb996f2d6598ae15429a5149e121238434830fd1d83a46b8ce1802e8578a813a234448800f81dc2d84f0921201b0340560a00e80a01000c01000 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
def record080_frame001_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65c328d922b04578a9d94749dc4e526913269804b6a46d1f88c33f49ed8f4e7953c21dbceba5d02de9508a0c4a824b11c08be44c21c8f9c79038f15a8a084e626112a893848a23e11c88c045222210d881c3e21dc0d986b033c1970c505ec2e816e0b385602a214a0a184f426a12e094048422410507f03a40fe05c02b01540a8047012007803a01c00d006403001700a805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record080_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record080_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 1)
      (record080.inverseMaps 1) record080_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record080_frame001_links_0000 record080_frame001_links_0064)
theorem record080_frame001_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 1 :=
  of_group record080 1 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record080_frame001_indices record080_frame001_graph record080_frame001_links
def record080_frame002_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x67166b6655e25dd5b159156655e54f54653f5395104fe4da46e45044843d43542f4293a63a137235332a32131230a3032fd2d42be29b2322142092001f91f11ea1e31dd1d61cf1cb1c81ba1a418c16a16415414e14013913413012911d11911310c1070ff0f80f30ed0e50db0d50c407e05b05505405304702401e01d01c01a01901801701501401000f009008007004003002001000 } : Fields).get c.val)
theorem record080_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record080) (record080.maps 2) (record080.inverseMaps 2) record080_frame002_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record080) (record080.maps 2) (record080.inverseMaps 2) record080_frame002_indices (Fin.ofNat record080.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record080_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record080) (record080.maps 2)
      (record080.inverseMaps 2) record080_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record080_frame002_links_0000 record080_frame002_links_0064)
theorem record080_frame002_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 2 :=
  of_group record080 2 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record080_frame002_indices record080_frame002_graph record080_frame002_links
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (Fin.cases (record080_frame001_supported hcells) (Fin.cases (record080_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa009fc9f79dd9d799699297f93392a91e9118a689a88887d86e85f7f77927827717627387246c76b46a269869469067466d63362f6195d05c75bd5af54c54453652c5215144bd46f4624544464224123c63b73a839f39839238737c37536835b34e32731a30d2fd2ed2a329e28e27e27024223220f2001f21e11d11bf1b31a719818817816a15b14b1151041020f60eb0df0d10ba0ae06f06e05a05905305203903802402301d01c } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
def record082_frame002_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5c92e29708b655b02c25600ae3544a9f54e4a664f7a7a13889b44d3a65d2588b2450223d0fa85c4231f74f8e7b13d31e78f2c76d3b41c78e246f134b9a18cf46692fe97e0bba5d12e316e8aca50a27d93b09ba4c125711808a244221b90a08364142040fe07d43dc1e70e907263841b98d946182fd1760b705962a0145898c4a023d11588603ea1e70ec07283761b40d006302f813b095849c23010807b83a81a20c303881c00b805b02a8150072038012008c03a01c } : Fields).get c.val)
theorem record082_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record082_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record082) (record082.maps 2)
      (record082.inverseMaps 2) record082_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record082_frame002_links_0000 record082_frame002_links_0064)
theorem record082_frame002_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 2 :=
  of_group record082 2 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record082_frame002_indices record082_frame002_graph record082_frame002_links
def record082_frame003_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0xa6d2e9549a451e8d45a250e85419c4de6933994c6612691c823b198b43e190883412070280c01fefe7ebf1f6fa78bc1daec75ba9d2df6e365acd267b218ac15f2e96eb357ab154a85329144a04f2712a9247a31128542204fe7d3d1dce670369a8ce6430978b8582b958a650269288a421e0ec6833168b050271007c3218 } : Fields).get c.val)
theorem record082_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record082) (record082.maps 3) (record082.inverseMaps 3) record082_frame003_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record082) (record082.maps 3) (record082.inverseMaps 3) record082_frame003_indices (Fin.ofNat record082.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record082_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record082) (record082.maps 3)
      (record082.inverseMaps 3) record082_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record082_frame003_links_0000 record082_frame003_links_0064)
theorem record082_frame003_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 3 :=
  of_group record082 3 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record082_frame003_indices record082_frame003_graph record082_frame003_links
def record082_frame004_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65c328d922c3560f2e356f4b3f5592a79514a754ee27293489934c025b51ce878433215108881c4051ed8f4c7953c21dbceba7013751964c8c60b2bf15a8aac54125412588e045f22610e47663441990c806202e816b0a084e426112b093c49424311d08d445c22711008284061fc0fa87b43941c50df06dc36019c0ca86102fa1770b805a02b61540a6851827c13809884a424410908103fc1f20f2075038c1b00d203881c00b805b02a8150072038012008c03a01c } : Fields).get c.val)
theorem record082_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 4) (record082.inverseMaps 4) record082_frame004_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 4) (record082.inverseMaps 4) record082_frame004_indices (Fin.ofNat record082.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record082_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 4)
      (record082.inverseMaps 4) record082_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record082_frame004_links_0000 record082_frame004_links_0064)
theorem record082_frame004_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 4 :=
  of_group record082 4 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record082_frame004_indices record082_frame004_graph record082_frame004_links
def record082_frame005_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x822068160480dfc7edfa7d1f37c9f1795e477ddd76dd9741ba6d9b26b9a96959864d8d6298861d866157e5f57a5c9705b96c5615754d52545505293c4e1344c12a495194550f42d07411003f0f83d4f23bcea39ce4384de348ce328c6308ba2dcb02b4aa294a0264952448d224852007b1e06d1a86918c5f16c571404b1003f0d8350bc2e0a8290801f06418 } : Fields).get c.val)
theorem record082_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record082) (record082.maps 5) (record082.inverseMaps 5) record082_frame005_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record082) (record082.maps 5) (record082.inverseMaps 5) record082_frame005_indices (Fin.ofNat record082.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record082_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record082) (record082.maps 5)
      (record082.inverseMaps 5) record082_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record082_frame005_links_0000 record082_frame005_links_0064)
theorem record082_frame005_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 5 :=
  of_group record082 5 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record082_frame005_indices record082_frame005_graph record082_frame005_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (Fin.cases (record082_frame002_supported hcells) (Fin.cases (record082_frame003_supported hcells) (Fin.cases (record082_frame004_supported hcells) (Fin.cases (record082_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
def record083_frame001_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0270.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0270.count (({ width := 9, code := 0x2c95aaa5369948a3cf677399c4d6672b9448e431f8ec6e31138843e1d078340a00f87abcde4ef76399c4dd6db65aed468b3996c96330178b6552a54c9b4c2491c8b44215047d3e1e4ea71379b0d26631980ba5a2a950a04d249208c43200f472371b0d4662f158a450271309446210e8643017 } : Fields).get c.val)
theorem record083_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record083_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record083) (record083.maps 1)
      (record083.inverseMaps 1) record083_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record083_frame001_links_0000 record083_frame001_links_0064)
theorem record083_frame001_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 1 :=
  of_group record083 1 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0270
    Papers.RationalityTen.SharedFrameCatalogue.group0270_facts record083_frame001_indices record083_frame001_graph record083_frame001_links
def record083_frame002_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c34d4865c2e356f4b2658aaa294e09dc4e5267d30092047ba1e10cc8544222070ff47c53d31e54f0865932317c8bc255629e12a092c46b2260fb07863441990c806202e81630a444e426112b093c49424311788b444e2040fe07c03941c50df06dc36019c0cc864c3081790b805a02b61540a6851827c138092848822a10d08103fc1f20f2075038c1b00d204301f40e206c030016c0aa0540270114072034014008c03a01c } : Fields).get c.val)
theorem record083_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record083_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 2)
      (record083.inverseMaps 2) record083_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record083_frame002_links_0000 record083_frame002_links_0064)
theorem record083_frame002_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 2 :=
  of_group record083 2 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record083_frame002_indices record083_frame002_graph record083_frame002_links
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (Fin.cases (record083_frame001_supported hcells) (Fin.cases (record083_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd4865c2c554e09dc4e5267d30092047ba1990887fa3e29e98f2a7842f094f095049623591307d83c31990c4058c29113909844aa24e12288f84542220ff87e43721ab0cf066032016d0b385602a214a0a184f426a12108904301fc0ef074838810c07d03601800b605502a013808a034014008c03a01c00d006403001700a804c02000e005802000e0040018008002000 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record084_frame001_links_0000 record084_frame001_links_0064)
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32e17eab0451da7713949a44c0246d1f88ad43320fcfd27ca3c99e10d825d028392a092c4702260f9c7903791990c2c56a29612f895449c24511f08c04442070f887903bc1d70dc86cc33c1980c505e82ca1580a8852828613d09a84a024211208283bc1d20d503f81cc0b805a02b015408e03b012008803c01d00d006403001700a804001e00d00580240100040018008002000 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
def record086_frame002_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6586255e85b459759057f56953952e5094ea4d64a949b48b4854383de3a338337e36c35632631d2fd2de2cd2a729c29028a28127927425e24822420b1fd1ef1e81c21bf1a619818a17b16c15814e14613c13712a11610b0f60e70cc0c40ae07907105a05805405304503b02402201e01d01a01901801701501000f00d00b009008004003002001000 } : Fields).get c.val)
theorem record086_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record086) (record086.maps 2) (record086.inverseMaps 2) record086_frame002_indices (Fin.ofNat record086.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record086_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record086) (record086.maps 2)
      (record086.inverseMaps 2) record086_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record086_frame002_links_0000 record086_frame002_links_0064)
theorem record086_frame002_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 2 :=
  of_group record086 2 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record086_frame002_indices record086_frame002_graph record086_frame002_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (Fin.cases (record086_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd4a646b1b98a8be95c92c3960aafd57b2b6d584a8753829654809ee4f4270934a95b49c2460e127003721b28d0666632097f8bf05df2e41630ae0510279134c99c4a524b91908aa43d20d10447e63d71c50da867a2fb16f8b6857c2b91590a5c50827212208e444e20b0f4877c3981c20dc869430c1760a8050826406703281880b403d01d80d006202200c805c02000d002000c004001 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
def record088_frame001_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x352991ac6e62a2fa55eca8753829013e09e84e326a52b69383d31c6ce1e7073801b7cd8a6833331948c825fc2fc1764b8458c2b8155ca064e526992fc94a49724391908aa43d20c90447e23d51c50da867a2df15f0ae452e284139091047222710587ac3be1ce0e106e43501860bb054028413202d00f807a03c01d80e406803101780b405402200c805c02000d002000c004001 } : Fields).get c.val)
theorem record088_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record088_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record088) (record088.maps 1)
      (record088.inverseMaps 1) record088_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record088_frame001_links_0000 record088_frame001_links_0064)
theorem record088_frame001_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) : Supported record088 1 :=
  of_group record088 1 (smallEmbedding record088) (small_cells_exact record088 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record088_frame001_indices record088_frame001_graph record088_frame001_links
def record088_frame002_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x129e4047a8eb1320d3fb7eaf95e53c4772ec5cbb8d620b8d6fadc5b2b41622ac53ea5548a774ea9b13324e4808cd0da0f40a7f0fa9ed3ca764e71c23706bcd419d3045e8b695428c50c9a93024a4508910a2003e47a8ef1d038c700d61a031c610bc0ac0f81e83c0760e41a03105e0b41502203205c0800d00800c01001 } : Fields).get c.val)
theorem record088_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record088) (record088.maps 2) (record088.inverseMaps 2) record088_frame002_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record088) (record088.maps 2) (record088.inverseMaps 2) record088_frame002_indices (Fin.ofNat record088.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record088_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record088) (record088.maps 2)
      (record088.inverseMaps 2) record088_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record088_frame002_links_0000 record088_frame002_links_0064)
theorem record088_frame002_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) : Supported record088 2 :=
  of_group record088 2 (smallEmbedding record088) (small_cells_exact record088 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record088_frame002_indices record088_frame002_graph record088_frame002_links
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (Fin.cases (record088_frame001_supported hcells) (Fin.cases (record088_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
def record089_frame001_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xd099532964cc858af0fe02b9b726e3dc3b776cac9587ae35baa8d46a754ae824f29792c25349e92721637c6089b0f61741f838f8df03db7aaf2de13a172adfdbdb626b0d31a1b24632bd175ae25b2b3d632b755aa794a28a4f89e93aa6b4c294d2321f4207f8fc14f2884e4971232324247f8ed1ca36c3f0560440680c81802e0540800d00800c01001 } : Fields).get c.val)
theorem record089_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record089_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record089) (record089.maps 1)
      (record089.inverseMaps 1) record089_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record089_frame001_links_0000 record089_frame001_links_0064)
theorem record089_frame001_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) : Supported record089 1 :=
  of_group record089 1 (smallEmbedding record089) (small_cells_exact record089 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record089_frame001_indices record089_frame001_graph record089_frame001_links
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (Fin.cases (record089_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1918c84634b13d81cbf45c92be95e8ad155c29f94cea4c4f5259928690945422150e883c4139ff8fcc7d03d41e98e146e93679970bfa5f72ee9718b1056c2a2943c9e24d4266929c93246622b90e886242220c10447dc3d21c50da86a233d1770b345742a114309d04c223b11488203b61be0dd066c3121790a6051426a11c07c83b01be0cf04601d80e807103480b8058025011006803201800b805402000d } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (smallEmbedding record090) (small_cells_exact record090 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
def record090_frame002_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x2845069fb3d671cdb98323a454838f91a22fc56877025fd3e377eecdd739f730e29c0b796d6da19b32662ab81602bc564aa149a8e5069ad2f25549c8fd1ba2643e84907a0c412814fb1e638c6e4d69a631e600bb16e2c656ca91422724b48c10920a3dc768e51a633c638bc15a2a45289d0f81a8348670c00ac150240420680c81802e0540800d } : Fields).get c.val)
theorem record090_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record090) (record090.maps 2) (record090.inverseMaps 2) record090_frame002_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record090) (record090.maps 2) (record090.inverseMaps 2) record090_frame002_indices (Fin.ofNat record090.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record090_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record090) (record090.maps 2)
      (record090.inverseMaps 2) record090_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record090_frame002_links_0000 record090_frame002_links_0064)
theorem record090_frame002_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) : Supported record090 2 :=
  of_group record090 2 (smallEmbedding record090) (small_cells_exact record090 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record090_frame002_indices record090_frame002_graph record090_frame002_links
def record090_frame003_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7f17ee7de7ce7ad79f76b7016f96f16e86c66b269f66d62060d5e45ac5995895715675535455395245214b94a34894343f93f13e13ce3ab3a338c36b35333f33531d30f2f52ea2da2d42ca2bf2b72a528f25a24523222a2021ee1de1d01c61bc1b019b18f17f16114d14813312711c1030ff0f70e90d60cd0c40bc08607207106e06602d02c02502201a01901801701501000d } : Fields).get c.val)
theorem record090_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record090) (record090.maps 3) (record090.inverseMaps 3) record090_frame003_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record090) (record090.maps 3) (record090.inverseMaps 3) record090_frame003_indices (Fin.ofNat record090.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record090_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record090) (record090.maps 3)
      (record090.inverseMaps 3) record090_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record090_frame003_links_0000 record090_frame003_links_0064)
theorem record090_frame003_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) : Supported record090 3 :=
  of_group record090 3 (smallEmbedding record090) (small_cells_exact record090 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record090_frame003_indices record090_frame003_graph record090_frame003_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (Fin.cases (record090_frame002_supported hcells) (Fin.cases (record090_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1724afa57a2b45570a7e533a9313de9e74e2269d2ae934480a1c906e8223f09f2cf587a63839c04dbe6c534399a8ca45fd2fb9774b8c5882b615149a64a524b91908aa43d21b90a08364141fc0f707283741ae0d0c5da2eb1660b285762a014409d84c625111e08a840e1f50ec87603781bb0da067831817c0a5851c26e11a07d03b41c00d003b01d00e206903301900ba05a01f00f007203101700b004a022 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
def record091_frame002_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x245c5289f11e1ec2783502dfbbf17d8f81e2bbb752e19bbb706c2d69a9350602bf97c2f15aeb295d2a353aa5d46a6e4ca95519a2543e841052024027f4fc9f33d2760d91a0318618b51692b6568aa1482864f49b1312544848a9112064087a0f21d238c6e0d31883085e0b31542904f0990ce1983205d0b816c2a85206e0d81a02d0580ac12822 } : Fields).get c.val)
theorem record091_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record091) (record091.maps 2) (record091.inverseMaps 2) record091_frame002_indices (Fin.ofNat record091.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record091_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record091) (record091.maps 2)
      (record091.inverseMaps 2) record091_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record091_frame002_links_0000 record091_frame002_links_0064)
theorem record091_frame002_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 2 :=
  of_group record091 2 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record091_frame002_indices record091_frame002_graph record091_frame002_links
def record091_frame003_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1970b635aa2ca1600a9f53b29313b89c64d226012388f8460a0ccffc7ec3dd1ea8f207843179880be85cc2b59508a304a824911c08983e81e20e345fe2ca15c0a184ec25c12b093c49424311a889c4081f60f3877c37e1bd0d886bc34e19c0c9062c30817e0bb05bc2c815b0a7853428213e09c04c0252122088043420c0fb07603941bc0d703b01d00e206903301900ba05a01f00f007203101700b004a022 } : Fields).get c.val)
theorem record091_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 3) (record091.inverseMaps 3) record091_frame003_indices (Fin.ofNat record091.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record091_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 3)
      (record091.inverseMaps 3) record091_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record091_frame003_links_0000 record091_frame003_links_0064)
theorem record091_frame003_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 3 :=
  of_group record091 3 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record091_frame003_indices record091_frame003_graph record091_frame003_links
def record091_frame004_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x260c8e91520e3e4688bf15a1ec3785908a003f37beeb5cf397700de1b6b68664cb98eb0e5e8bb16e2c0578ac95429351ca0d2a23e46c8950f21442283905a073f87ace61be35e6a0c718d2fe5f8bb96d2c8570aa14c2864e89612522e458841062023e4778e61a4340640bb15c2a85309e0d41a4338600ba16c2a0510740e01a82d0560a812021 } : Fields).get c.val)
theorem record091_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record091) (record091.maps 4) (record091.inverseMaps 4) record091_frame004_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record091) (record091.maps 4) (record091.inverseMaps 4) record091_frame004_indices (Fin.ofNat record091.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record091_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record091) (record091.maps 4)
      (record091.inverseMaps 4) record091_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record091_frame004_links_0000 record091_frame004_links_0064)
theorem record091_frame004_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 4 :=
  of_group record091 4 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record091_frame004_indices record091_frame004_graph record091_frame004_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (Fin.cases (record091_frame002_supported hcells) (Fin.cases (record091_frame003_supported hcells) (Fin.cases (record091_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x602b89702dbdacb1d606a8d46a754ae824f291f1ae2e439855071ebbd178eef5ceb906c4d61a6343648c65662b4554a4543a7a4ea9ad30a5348c87d081fe3f0778e99c73786d0d519931c5ecb916729e5109c92e246464848ff1da3946d87e0c6158298520a21401882203e0780e81c0340640c01702a0400680a0120200380400600800800 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65c2fd5608a9e4ee2729348980456a19907e7e93db1e9cf086c12e815a895049623811306f23321858ad450427312a893848a23e118088840e2000f2075c3721b30cf066031417c0ba05b82b01510a5050c27a135094048420a0ef07482300e606902e01680ac05502a00ec062024011007803a01c00d006403001700a803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1970bf5582277138c9a44c0247515a8413f49ed8f4e784360974095049223811307d23791868ad450427312a893848a23e118088840e2000f2075c3661ac0cf06282e816e0ac052827a13509784a024211308283c01d208c03481980c805c02d01580aa05401880b8058024011007803a01c00d006403001700a803c01a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (smallEmbedding record094) (small_cells_exact record094 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
def record094_frame002_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6586255e859758f57f56953a5094d74a94944904854383de38337d36c3563272fd2ce2a729729428a28127927425e24822421d1fd1e81bf1b81a618a17517115814613712a12011610b0f70e70cd0c408606706406205a05805405305203102e02c02402201e01d01c01a01901801701500f00d009008007005004003002001000 } : Fields).get c.val)
theorem record094_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record094) (record094.maps 2) (record094.inverseMaps 2) record094_frame002_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record094) (record094.maps 2) (record094.inverseMaps 2) record094_frame002_indices (Fin.ofNat record094.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record094_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record094) (record094.maps 2)
      (record094.inverseMaps 2) record094_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record094_frame002_links_0000 record094_frame002_links_0064)
theorem record094_frame002_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) : Supported record094 2 :=
  of_group record094 2 (smallEmbedding record094) (small_cells_exact record094 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record094_frame002_indices record094_frame002_graph record094_frame002_links
def record094_frame003_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x246c5e84ef71eabce786ea1c436868ecd1973235e6af53926b4c69691f2193f4774e41c33726d0d81ae344660c217f2d456c9f13925a460851041f23bc730e21be368698c717c2bc5587a0bc16c2d0530a21342604b05e0b4158240440780e81c0340640c01702a03c0680901001c0280400600800800 } : Fields).get c.val)
theorem record094_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record094) (record094.maps 3) (record094.inverseMaps 3) record094_frame003_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record094) (record094.maps 3) (record094.inverseMaps 3) record094_frame003_indices (Fin.ofNat record094.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record094_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record094) (record094.maps 3)
      (record094.inverseMaps 3) record094_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record094_frame003_links_0000 record094_frame003_links_0064)
theorem record094_frame003_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) : Supported record094 3 :=
  of_group record094 3 (smallEmbedding record094) (small_cells_exact record094 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record094_frame003_indices record094_frame003_graph record094_frame003_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (Fin.cases (record094_frame002_supported hcells) (Fin.cases (record094_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007
