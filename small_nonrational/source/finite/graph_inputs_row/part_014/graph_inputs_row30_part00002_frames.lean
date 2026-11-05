module
prelude
public import GraphInputsRow30Part00002Data
public import RawFrameSupport
public import SharedFrameGroups044Checked
public import SharedFrameGroups058Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe6172a3915c60e016ea354da78ce9640306d82ac065ea2e796e2ae755aaa1d4aaa4451aa7f9332934486a3d90ec8303f81f9cfbe7d03dc9ea0f187843b69d70e807383929c74d3a66f31e1838bfc5f32e2968cada54e28c13e89e84e924211948a0436210906874036e1a00c385fc2f015b09dc4b024d11e88784262030fd064424c0f8074829c14205f02d81540a803d01c00d004e02300e807002c01200700280100070018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe6172a3915c40df16ea3709b78d926b334fd82ac055ea2e796e2a4451a25e922a8f64399f9cf867ab3bb9d7ce6a72635d9a54cb463430217f8be85c62c8160caf055a29d94b8a4650527c93d09d64ba243119489843620e90687d23b01d00e4c6e43501a00ccc62430517f0bc857627d12c08e443c1ff0fd06302d815b09d84a824c0f9071824411a06e035018c0be05b02b01540a8053027812407003400e80700100070020008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7347267056db6c76a36986826766676626425f95b65a259358458153a51f4fd4e84e14c84af49048a47d47747146c46a45f44844243142941c3fb3f63d73cf3c23af39b39138337d37135633b30c2ec2b52a829729427925523c22e2101ef1de1d51b81a018217d1711691661620ef0dc0c90ba0aa09f08907c07606d06905d05905305204a03402702502302001d01c01200e008007003002001000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x44a8790de164057eef89ebbc873cdddaa33f676c5d82aff5bcb6d63ac257ead5582ab540a5d49a874ec9b53125349090519a2d43c869081fe3e87c4f69c835e66cc91852f85a8b29582844e49a12f1a23005107d0f81903185f0b815c2b0520a21402784d09210c1c0320620ac140230440780e81c02c04c0700d0120200380400600800800 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xff97a5bbe1c9cd56688b2f58c2b6d566aa3946aa054eaa64d29c937490244517c87b42620bcfd27d33d39e24e5a6392cc9568a024d1250917c8344031f60f7471434718c0bec56a29f13988fc4521ff0d2865c31417b0b7054425c128090844821810507482b012e09004601e80d206302d01580aa05402100c405602200f007403801900b005002000d004802000e0040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf4b75bba0dbcad97688b2f58c2b9455fa8e140a9d54ac253926e920488a26511e87b433215cfd07d33e29e24e5a6602c594109a24a121210688063ec1ee8d946b63471990c8c56829f14888fc42a1ff0ef073c3721980c4854425011208604141de0e907102e015809004601b00d206302f81680aa05401a00c4056027011007403801900b004802000d005802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7b37a577b77074b7076fb6d96d06a169b68a66664662f6215f45e95df5b359b58456e54652b5254f94ee4c84be4b14734003ee3ba33f33531d2ff2f92f42cc2c62bc2af2a229326825c24422921a20d1e11d01b01aa18816614d1351201130ec0d20c60c10b50ad08708608507c06805905405204b03703103002802302201e01d01c01900e00b009007004003001000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xe457183805ba8d3f663b17982ac065f92ef170cb6e5ac2c1d5ecae7553aa5950ea4a52228d53f29c14cda57126c90c47b21050608013f81f9cfa07b93c21db4e7072538e9a74c785fe2f9960ca5c4f427492d48ca45d22810d885c42120d10487cc3c41d90e807123641a90d0065230617f0bc056c25812688f443c21310187e832416c09d84981d208403f017c0b605702a815007a03801a009c04601f00e807002400e005002000e0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1c8ae30700b751a7ecc762f305580cb71573aa1d488a3547b21050608013f81f9cf867b23bb9d98e6a72238e9c14d766b134e9968ca063c30217f8be65c02c8160cade53b29714689f24f427492d48ca45d22810d885c42120d0f907603a01c58d4068032b1828bf85e02b612c093447a21e109880c3f41920b604ec24c0e902f816c0ae05502a014c09e04c024811807a03801a009c04601f00e807002400e005002000e0040018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe636d1b3b198cc88619b00d746b4f57fabb55b4aa454829a946e9e34c9a6052dc93849223f91968ac44d224d11487142d20a8fa47a53849a94c926272da15409e84d225292408ec47022a912486640e1e30eac6f236f1aa8d186162ec1640a604d624d11488344001f20f086d431016a0a304a823a10f07f0368190091046022c10205702b0150084036018809c04401f00f00740380190080028012007002000c002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x81c3f2de3cec16f6363dac0d1566632a9924c5e61c2f45728b395852b29572a9e548a949424993473a2610cc80a3f41ed8f4c7953bb1d78e5470434e9980c0a5d62cb1614ad455d28f13788be3b31b20cc85ac2b414109c84c222910e88003d81ce0dc86242f81740b6859c2a213d09704a01fc0ef074838817c07002f81700b605502a00e004e024011807403801900a004801e00e005802000e0040018008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x277ce799f2c63f4588810be09bd66d8d759eb30634c4d86b03600bd9792e25a8b2963ac255caa151a8e5009d13325a4ae93922a3a44c859029e13a4730e31c1364694d09962fe5d8b71682b051c9492423c41c818f31ac2ec578a413e2703e8670b8164298520a213c2604808c0f41c03305209c1182003a0700900f01c0280400700600800800 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3329938c456022f296ceb2c58b2c1153ea3550827713489934c0248117c89a4181fecfd27b73b41c44da069631997e0bc45d02b594049b84a8238117c8983ec1c50d985f82c715a8a0c4a425112508d846a22e11388444081fc0fa079c3b61d10e206f436c1a70d0866832418b0bf05d82d61640ad855029a13e09c04c425212208a84342040fb073037c1b00d2046823011608703d01a80d205b02d015c0ac05502a014c09e04201900c404602200f807803a01c } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x33b5990c7761bafe5746b6b5ac2d215daa8653328dd3fe9ec4ee26052348fa465a2d915e89a4322034faa79f3a69c60e126f93529924c505f82e196d0b4855027a134c94a49024491d88a445121d0fe87f23e01e48e246c234c19a0c3c5ce2cf1588a84522270131895048623310b08183d61de0e706f835c18d0c005c42c0150099848c2100fb073037c1b00d2046823011608703d01a80d205b02d015c0ac05502a014c09e04201900c404602200f807803a01c } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8087f57dd7c17a477575074573a7066c56af68a65f65264760d5c25a556e55554c5345124fa4de4c149046545844d4133c83ab38736235734c3182d72c128b27226925123923823121d21c2162101fc1ef1e81e01d31c71be1b21ab1a419218b18417b17316515d14f1481401391321201191121091010f30eb0dd0d60cb0c70c30bf08d08c08b08707a06a06905b05a05705605505405304f04203203102302201f01e01d01c } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0xc8d8f30be01b8d656bf572a9f4ca7f4cd98b26a49c8e91118e2f4588a90ee1441982703a04b1661ec1d7c2d856caa13da664888cd0ea1942a841021f23b26dcd117c2ce4f49a1242344588810a2083f4760d01963045b0b215e2584887f0ee190308600be16c2a85408e0f41a03304e0941182003a0700900f01c0280400700600800800 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6f16e96c26b16826626376225f45d05a258157d53352751f5124e14dc4d04c84a548a47d47747146c37d37a37335833a31630c2ec2d22b52a829a29729429027825423b2091f31d51b118617d17116616215d1521471381190ef0e60dc0c90c00ba09f09908907e06906306005d05905305204503c03403302702502302001d01c01200f00e00a008007003002001000 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc5357fa7e93de9dc4dc26912f67c73db1e9cf2a71f2e593189764a824211c088e29314109cc4c224c12288dc46020e10386cc33c17b0ba05b82ce15f0ac052828813d09a84bc25010507f03c01d20a2048822c10807f03701980be05d02e01580aa054029813008e036017009c04a02400f007403801b00d0064030015009004001e009004001c00a0040018008002000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0709.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0709.count (({ width := 9, code := 0x196c95fef978b9dc6d32993c96471f8dc220b017ebede8cc65b2992c460af576af56a79309147a351686411ecf276389bcd8602e960aa4a2491c8843200f872371b0d06632188b85a2a1408c42200f074381b0d0643015090401e090401c0a04018080200 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0709.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0709
    Papers.RationalityTen.SharedFrameCatalogue.group0709_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
def record035_frame003_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0708.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0708.count (({ width := 8, code := 0x878581807e7d7c797271706f6d6b67666463625f58575655535251504e4d494744434241403f3d3c3b3a3938363534333231302d2c2b2a272625242322211e1d1c1b1817161514131211100f0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record035_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0708.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0708.localPairCheck (smallEmbedding record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0708.localPairCheck (smallEmbedding record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0708.localPairCheck (smallEmbedding record035) (record035.maps 3)
      (record035.inverseMaps 3) record035_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame003_links_0000 record035_frame003_links_0064)
theorem record035_frame003_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 3 :=
  of_group record035 3 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0708
    Papers.RationalityTen.SharedFrameCatalogue.group0708_facts record035_frame003_indices record035_frame003_graph record035_frame003_links
def record035_frame004_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0684.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0684.count (({ width := 7, code := 0x58af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record035_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0684.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0684.localPairCheck (smallEmbedding record035) (record035.maps 4) (record035.inverseMaps 4) record035_frame004_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0684.localPairCheck (smallEmbedding record035) (record035.maps 4) (record035.inverseMaps 4) record035_frame004_indices (Fin.ofNat record035.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record035_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0684.localPairCheck (smallEmbedding record035) (record035.maps 4)
      (record035.inverseMaps 4) record035_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record035_frame004_links_0000 record035_frame004_links_0064)
theorem record035_frame004_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 4 :=
  of_group record035 4 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0684
    Papers.RationalityTen.SharedFrameCatalogue.group0684_facts record035_frame004_indices record035_frame004_graph record035_frame004_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (Fin.cases (record035_frame003_supported hcells) (Fin.cases (record035_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f84f39781bb15ca8e146f33589a34cd0630b121818bcd54fa8413ee9f24efa6ed34e9834a824551fa8dd46222750c68303fd9fa4f927a33c89cb4e286d834c95ac9b84c325f12ac90e47322790707c23c91d48e406d232f17e0b1c56a29513789743fe1f30ef07403741a60c886282f61750a204f425e12809084442060fc078035015c06a03481980ae05602a80c806202e00f807803a019008003801a00a004802000e005002000c004000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x32a992cc7c6333159884c206022f25740b6c5a7ac6d5f4ada5652ae152ea7753328a53e29c14daa6bd29893348ca41d1d68b4442a1e50bc84e4189ff4fa47b03ca1df4ed66152ff97bcba45c22db16c4b3a5782aa94389e84c925911f48c843c213101c7f23e71ed8f4075e3871b78c845ee2ca15f8a1c4c023a11888543fe1f20f287703941b70d186002c814109803e01d40c803281880b605a02b015408e03d012808c04402000f007401e00e00680280120080018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x191b1e632c4985f07e01bd7726de5a5b2d5fab9568ab953ea3532a47406784d799d31653c9a92723a444778cb17a2c45489b0ee14c1b82b03603b4b682ce594b2062ec3d83af85c0ad95428c4fa9992da4446889510a18426841021f23c26dcd11862fc59cab93d26a4a090119228440851041fa3b06e8d01962d8590a50c21802d85a0ac1542383d04a08c1102003c0740780e01a0280480800600800800 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x14f29ad2ca4747e8c511a113d675cdd99f2f259caa94727e4b48f9111d63245889f12a13c1681f02a013eb7aef49e53c4778e95c8b89702dddb7b035f4bd175ae65beb6d6a2c9572a5145a764ce93922a2f44084906a043f67d8f41dd3a86bccc9893045a4aa1432764bc9211d22a440849021f239c6c8cd18e2bc548990be1742b8560a41442283d04a08c1102003c0740780e01a0280480800600800800 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
def record039_frame004_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x37a5ba8dac6c0b541a76d1367432b193ac8863d30757fcbd45d82ded6b8b325872b3d572aa454eaa5d3d29ae4cca6352ea93f48523ed1cc8da46122310ae84641f20d905e66d3309968c9864531f98e8c485eb2db156ca8651827e133896c48b23791808b845622891248383da1d70d3063e2ee16e8aac4fc24d11e08ac44621c10a88303ee1e20e306202ae13909803f01e60d203281880b605a02b015408e03d012808c04402000f007401e00e00680280120080018008002000 } : Fields).get c.val)
theorem record039_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record039_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record039) (record039.maps 4)
      (record039.inverseMaps 4) record039_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record039_frame004_links_0000 record039_frame004_links_0064)
theorem record039_frame004_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 4 :=
  of_group record039 4 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record039_frame004_indices record039_frame004_graph record039_frame004_links
def record039_frame005_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6f16e96d66cd6c26bc6b169e68767b66c66363762260c6035f45e65d05c05a659558658257d54953352751f5124f34e24dc4d04c84ba4a548b48147947046b39d39439038638237e37a37335833e31630c2f72ed2d22c82b52a92a029c29629329027825423f2091f31dc1d61b119e18617e17316b16516115d1521471381191010ef0e60c90c00b006306005905805405304503c02502302202001e01d00f00e00d00a009008003002001000 } : Fields).get c.val)
theorem record039_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record039) (record039.maps 5) (record039.inverseMaps 5) record039_frame005_indices (Fin.ofNat record039.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record039_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record039) (record039.maps 5)
      (record039.inverseMaps 5) record039_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record039_frame005_links_0000 record039_frame005_links_0064)
theorem record039_frame005_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 5 :=
  of_group record039 5 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record039_frame005_indices record039_frame005_graph record039_frame005_links
def record039_frame006_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x178aecdd1b816cad65a0b1b5c2b054fa8b4be92d19a173e677ce59af2f654c9792522e3545889d1262042e82f03e03bff7ecf91e6bc1774ed1d8330652c918cb1361cc2580af05b4ac95529650e9ad2f2454648890fa19424839001ef3be6c0ce9802ee584aa13e26c4a09091e22e448859041fa3b06d0cf1922bc5609b0c21802c8580a814c2383d04a08c1102003c0740780e01a0280480800600800800 } : Fields).get c.val)
theorem record039_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record039) (record039.maps 6) (record039.inverseMaps 6) record039_frame006_indices (Fin.ofNat record039.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record039_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record039) (record039.maps 6)
      (record039.inverseMaps 6) record039_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record039_frame006_links_0000 record039_frame006_links_0064)
theorem record039_frame006_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 6 :=
  of_group record039 6 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record039_frame006_indices record039_frame006_graph record039_frame006_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (Fin.cases (record039_frame004_supported hcells) (Fin.cases (record039_frame005_supported hcells) (Fin.cases (record039_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x36059d0c7a5662b01572aab5522a753de90a42ba11507c8364179f20f787ae3c79dfceb471e3891c10dca6d535819b4cc265a3261914c7e5af2bd15b4aa052527e13b49c04c324c11bc8c245c22b114487e42f20c8fbc7ae3ab1980c7c5fc2ee16e8a3c4fc25d12688f045422310e08544101f40e4862c2ae13b09803f81e60d203f81d40b605a02b01540a604701e80b4054023011007803a019008003c01c00d00580280120080018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1786b4e550aa054cca2b502275136c9894b1a5352128cc44aa21d0907d23d89e58ef47683919c58e146ef3719b34d4867f32f9858bf85cf2da9638ad2554287939c9784b2241909880c3f61da8ea471a3811b68c7c6102f916d8b305802b014409dc4da25112388c441e2020f8879038a1b40d3864030816d0b2051425a12108a83e81d60c5046823011605602a814c08e03401900c4048023011007803a01c00d806803201800a802c012008002000c004000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
def record041_frame002_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x72f7076a169668165764162360d5f45e45d65ac59057056254651d51150a4ff4f84da4d64d24c54bb4af49348346c4384224013ee3d73c43b337f36334033531d2f42e62e02c22b82a829b28425023f23421c20f1ff1f11e11d71d01bc1b419f18417f17116515414d14313512811710b0f40e80dd0d10c60c10af08708608505405305104503303103002402302201e01d01c01b01a01901801500b009008004003002000 } : Fields).get c.val)
theorem record041_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record041_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record041) (record041.maps 2)
      (record041.inverseMaps 2) record041_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record041_frame002_links_0000 record041_frame002_links_0064)
theorem record041_frame002_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 2 :=
  of_group record041 2 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record041_frame002_indices record041_frame002_graph record041_frame002_links
def record041_frame003_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x249c758931021bc2082b011fc3e87c2f65e13b0744e69c3b626b4d51a5343664cb99432263ec5983afb5e0b4161aaf542a3d452804c09291c2314407ecf89ec3ae744e51c6378664c79862f25c4b415f2a2534a594127a4c89191e22842c7e0f61e2398708dc1ae32c5f8b6160298500920f61e83c8520a213c228330620c0120230440780e81c0360680c81802a02c0480800800c01000 } : Fields).get c.val)
theorem record041_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record041_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record041) (record041.maps 3)
      (record041.inverseMaps 3) record041_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record041_frame003_links_0000 record041_frame003_links_0064)
theorem record041_frame003_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 3 :=
  of_group record041 3 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record041_frame003_indices record041_frame003_graph record041_frame003_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (Fin.cases (record041_frame002_supported hcells) (Fin.cases (record041_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xe397033755afcd50694332d878bd45d0adc1632aeb561a9993ae9c74e326fd3629aa4ce26192f29714b4a5712a894649ca4c925691c48b241d2008f3475a3811b26d532098a4c4060d2f4175cb6254d29593d09a249923390c88464011f88ee876239e1bc8da06842de15e0a144c422a0fc070c3681920c105602a21470a184ec26812e093047c23010908283f01ea0ea07103701ac0d0057023411808b03501a4064031017009404602200f807803a01c00c804001c00d0050024010007 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
def record042_frame002_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xc9663e319986cc146022ef969cb05572ab2952ea77533288136899c4cda6412ea96a4a7a4e521c8f547122f9156888434a1490788164041f88faa7b63cd9de0ecc61c2da9684b3a5912bc15b0aaa51027a132496448022b90bc84c4081fb8f0c7763af1c98e1c6de3221830b6457e28913008e846221210087743981b00d586783241880bd85bc2ca13f09a04802280fe073036c1a20c3055023411808b03501a4064031017009404602200f807803a01c00c804001c00d0050024010007 } : Fields).get c.val)
theorem record042_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record042) (record042.maps 2) (record042.inverseMaps 2) record042_frame002_indices (Fin.ofNat record042.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record042_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record042) (record042.maps 2)
      (record042.inverseMaps 2) record042_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record042_frame002_links_0000 record042_frame002_links_0064)
theorem record042_frame002_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 2 :=
  of_group record042 2 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record042_frame002_indices record042_frame002_graph record042_frame002_links
def record042_frame003_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x60f5fc5f25d75c95c15a657655b54f53d52451750c4f14c14b64b54af4a449e49348847b47346a45b45244443943242c41e41840a4043f83f03e53de35e32c32131f31930a3052f72cd2c22a829827d26c25725223e23621c21a2152072011f21c81b91a119317816115114d13913111e11810f10c1050ff0fb0f40ee0ea0dd0d90d10cc0c40bc0b80b50b009d08308208106706603203102e02502302201f01e01d01c01901000e00d00a009008007 } : Fields).get c.val)
theorem record042_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record042) (record042.maps 3) (record042.inverseMaps 3) record042_frame003_indices (Fin.ofNat record042.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record042_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record042) (record042.maps 3)
      (record042.inverseMaps 3) record042_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record042_frame003_links_0000 record042_frame003_links_0064)
theorem record042_frame003_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 3 :=
  of_group record042 3 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record042_frame003_indices record042_frame003_graph record042_frame003_links
def record042_frame004_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x74873c72b7107026f46d86b369468767164e63e62d60a5e55dc5db5d25c65bc5ac58457056a55b54853651f5084fc4f64e04d44b84ab49548f48447d3e63c33bb3b93b13a439838735734832d31b3022ed2cf2c62b82b42a229f29728927d2692382262091f41dd1c41a519918b18717616b15e15b14913d13312211610a0f00ec0e00d40c60bb0b20a60a109308108007f06406303203102e02502302201f01e01d01c01901000e00d00a009008007 } : Fields).get c.val)
theorem record042_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record042) (record042.maps 4) (record042.inverseMaps 4) record042_frame004_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record042) (record042.maps 4) (record042.inverseMaps 4) record042_frame004_indices (Fin.ofNat record042.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record042_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record042) (record042.maps 4)
      (record042.inverseMaps 4) record042_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record042_frame004_links_0000 record042_frame004_links_0064)
theorem record042_frame004_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 4 :=
  of_group record042 4 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record042_frame004_indices record042_frame004_graph record042_frame004_links
def record042_frame005_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x5d9ba3702d3d9cb1b5b6a2529a4142e77ce59af2ea48c899112123f4788dd16e25c4487b0ca14c19815005fd3ee7d0f61e7bc2776ecdd7b3261ac0d80af95e0ba16d2b3554a5943a6c4b08f51922343c82102a003ea7bcef9b1348628bb9622a84f89b12624444c861022023e87a8f01d23886d8cd19830c5e0b31542984f89a1181e83c8780cc1941903105c0941182203e0780e81c0320400700d01402404007 } : Fields).get c.val)
theorem record042_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record042) (record042.maps 5) (record042.inverseMaps 5) record042_frame005_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record042) (record042.maps 5) (record042.inverseMaps 5) record042_frame005_indices (Fin.ofNat record042.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record042_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record042) (record042.maps 5)
      (record042.inverseMaps 5) record042_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record042_frame005_links_0000 record042_frame005_links_0064)
theorem record042_frame005_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 5 :=
  of_group record042 5 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record042_frame005_indices record042_frame005_graph record042_frame005_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (Fin.cases (record042_frame002_supported hcells) (Fin.cases (record042_frame003_supported hcells) (Fin.cases (record042_frame004_supported hcells) (Fin.cases (record042_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xccd622b025794b675962c114269fa4f7a7713709a44c024711f48c144d218d0607fb3f49e94f2671136a9a58c665f82e8137c98c4bb25412108e044c1f40f1871a3661978bf058e2b5138897c49824511b88c044420e0ff87e43e61e40ef07403821ba0d9869833c1910c505b02ca15f0ac052828813d09a84bc25012108603c01aa08b03301740b605a02b81580aa053017009404602200f807803a01b00d0064030015008003801a00a004802000a0040018008002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xb4f582ab95594a9753ba99936a9a14ca26252dc9634a6a3f51b68a4442a11501e7db3e91df4ed67163779b34d3067332f96d8b4859a2c715d4ad255428813d09924b2240115c85e4261f38f6c76a3a91c68e046da34f1910c5060c2e716c8afc53828913b89804a223a11887c83ca1d50e2869c3381900c205e42da16409883ec19008b03301740b605a02b81580aa053017009404602200f807803a01b00d0064030015008003801a00a004802000a0040018008002000 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
def record043_frame003_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x67864e6376236035f05e257d57456e56655654f53f5114fd4d94c34a949247546e44643b4113fd3e73c73b43a634133833132a31a3123032d52bd29a28726d24f2392322071fe1ef1ea1db1d61cb1c01b21ad1a619518e17f17817116a15d15414714012e12712211d11310d1070ff0f90f30ed0e00ca0b308906505c05a05905605505405202e02502302201f01e01d01b01a01901801501000e00d00a009008005004003002001000 } : Fields).get c.val)
theorem record043_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record043) (record043.maps 3)
      (record043.inverseMaps 3) record043_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame003_links_0000 record043_frame003_links_0064)
theorem record043_frame003_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 3 :=
  of_group record043 3 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record043_frame003_indices record043_frame003_graph record043_frame003_links
def record043_frame004_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6b469468767164e63e62d5e65dd5d45cb5c05b65a756c5555305194f84da4b24a548748046545a4464254174083c43bc3b73af3a239638535734832d31b3022ed2cf2c62af2aa29b29328427826424423822f2262112091f41e31dd1d41c41b61a519918117a17116615414613a12d11f1131070eb0c50a207f06005905705605305205104f02e02502302201f01e01d01b01a01901801501000e00d00a009008005004003002001000 } : Fields).get c.val)
theorem record043_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record043) (record043.maps 4) (record043.inverseMaps 4) record043_frame004_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record043) (record043.maps 4) (record043.inverseMaps 4) record043_frame004_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record043) (record043.maps 4)
      (record043.inverseMaps 4) record043_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame004_links_0000 record043_frame004_links_0064)
theorem record043_frame004_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 4 :=
  of_group record043 4 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record043_frame004_indices record043_frame004_graph record043_frame004_links
def record043_frame005_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x40f7fafe1f6bdb7a6f25c838b712e21c0b7c6e6d7dabb47678cb58f309606bb173ad75a2b15582aa5409a5322624c29692aa4c46c8ad0c20c3fe7ccf09dc38a700dc9b735e6a4cf98f30c604bd96e2cc560a61472844d49792023241c819001f63c4768e61c0364688cd176290468750b41482804f09812c2504805a0941182203e0780e81b0340640c0150200380680a0120200280400600800800 } : Fields).get c.val)
theorem record043_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record043) (record043.maps 5) (record043.inverseMaps 5) record043_frame005_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record043) (record043.maps 5) (record043.inverseMaps 5) record043_frame005_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record043) (record043.maps 5)
      (record043.inverseMaps 5) record043_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame005_links_0000 record043_frame005_links_0064)
theorem record043_frame005_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 5 :=
  of_group record043 5 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record043_frame005_indices record043_frame005_graph record043_frame005_links
def record043_frame006_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x4c094725a474818f11b21d43285708a0b40e808f71e7bb8756e49beb686c2d0d9eb2362ac357daf25d0add582ab548a6d4a28b4dc9992b24c4728a90da1740c80cfa9ec3bc754e49b434867ccd98d3105f8b69662c2558a814628049c9211f22e42c810fb1e43a4710dc1902c04d8810c816c2c8580aa1502985105c0941182203e0780e81b0340640c0150200380680a0120200280400600800800 } : Fields).get c.val)
theorem record043_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record043) (record043.maps 6) (record043.inverseMaps 6) record043_frame006_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record043) (record043.maps 6) (record043.inverseMaps 6) record043_frame006_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record043) (record043.maps 6)
      (record043.inverseMaps 6) record043_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame006_links_0000 record043_frame006_links_0064)
theorem record043_frame006_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 6 :=
  of_group record043 6 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record043_frame006_indices record043_frame006_graph record043_frame006_links
def record043_frame007_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x3ba746e65c9388702dcda4342682cf59c33565ec698ab07602bc573ad45a0af55caa552ca3d41a7c4e69292224347e8e91ba31434841009f93d6780eb1d237a6ecda1ad33c664c61772d658cb115129c50c9c13125a4908e1112123c8770ec1d23886e0d71a4330638c3166278448790b814c2905109c1342604a05a0901102103e0780e81b0340640c0150200380680a0120200280400600800800 } : Fields).get c.val)
theorem record043_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record043) (record043.maps 7) (record043.inverseMaps 7) record043_frame007_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record043) (record043.maps 7) (record043.inverseMaps 7) record043_frame007_indices (Fin.ofNat record043.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record043_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record043) (record043.maps 7)
      (record043.inverseMaps 7) record043_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record043_frame007_links_0000 record043_frame007_links_0064)
theorem record043_frame007_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 7 :=
  of_group record043 7 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record043_frame007_indices record043_frame007_graph record043_frame007_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (Fin.cases (record043_frame003_supported hcells) (Fin.cases (record043_frame004_supported hcells) (Fin.cases (record043_frame005_supported hcells) (Fin.cases (record043_frame006_supported hcells) (Fin.cases (record043_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1cbad9d6b635adacad596a93511a32d046772eed768ba65c0adb9696a66527a921474a15501277d1f48f0474a37d1b68d3466231917c8b745822891368924459d98ec07503961c6cdf8628308982cbf65d72e3169c9a64c926112e09684ad253128093049124511f48ee46f2348b1c4f426b12608f045a20e100065c3101690ac852825611d07803a41c40db06a030815c07503501a40cc05b02d00f4064031017008c044019007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x19acc66625b129880c2860f301976eb835a8aaad548a9a54229e94ce9b44cf265d3169714b2a53910a87e4342105076823409201cfde7de3e99eb8f2a77b3b49aacd4e69b34119d8cc05b52d09674b225782b615549644ae24d91f08f046722d114087e43221390307f43e51ec8afc4da26012388e846221310086703201790b6859028813107c83a41bc0d406302e015407503501a40cc05b02d00f4064031017008c044019007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbf6ba2b87b86b84b7fb73b62b1baf4abca38a37a33a22a16a0694e93f93892f91f9128fd8248178077f67f37d77c37b779978477074572e70f6f968268067c66f6626515b95ac5a95a05905825704c44bb4ac49a49748547a47045c44d4404204123f93eb2d82932862652552462252151b51a818717816b1451350f50e80da0cb0bd0b30a707506a06906605b05a03d03203102e02302201900e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
def record044_frame004_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7a376e75b75a75875475074972b71c7086a56a26a069968f6836085fa5f95f55ef5e75d855d55554e54454253c53753252a52451e5105095014fa49849548d48547b46f3ee3df3de3d93cd3c63b633532c32531b31931230d3093012fb2f52e82e22da2d41fc1d01c71b41a919f18817e13b13511f11710b0f30ec0c50c00bc0b60b00a609b07306806706405905803b03103002d02302201900e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record044_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record044) (record044.maps 4) (record044.inverseMaps 4) record044_frame004_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record044) (record044.maps 4) (record044.inverseMaps 4) record044_frame004_indices (Fin.ofNat record044.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record044_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record044) (record044.maps 4)
      (record044.inverseMaps 4) record044_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record044_frame004_links_0000 record044_frame004_links_0064)
theorem record044_frame004_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 4 :=
  of_group record044 4 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record044_frame004_indices record044_frame004_graph record044_frame004_links
def record044_frame005_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f7eeb8739b9c9cc2e36710b7cdac8d1c669ae116f8b6a5a22cbd60ea104fba7c93be9bb4d3a60d13489043fa17d0b6845419a09d0207fe3f61f2cf747a23c81940c9063630817ecba64dc26192f8956487239913c6cc35c1a58cac64e31117f8bcc5b82ca15c0a5c50c26e12e074035a1a60cc064431417c0ba851027a12f094048422610c077039c1c00d9069830815c07503501a40cc05b02d00f4064031017008c044019007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record044_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 5) (record044.inverseMaps 5) record044_frame005_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 5) (record044.inverseMaps 5) record044_frame005_indices (Fin.ofNat record044.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record044_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 5)
      (record044.inverseMaps 5) record044_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record044_frame005_links_0000 record044_frame005_links_0064)
theorem record044_frame005_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 5 :=
  of_group record044 5 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record044_frame005_indices record044_frame005_graph record044_frame005_links
def record044_frame006_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x7246f56e16e06de6d86d66d06ad69367a60b60a6055f75f25e357c57156f5685575515404c34c04b84a54a349b49448d48147746f45e4544444393cf3ce3c93bb3b63a734033533232c31b31430428728427c26926725b25124a24223b2332222182051fc17f16515d14f14714013a13510d1070f90f30ed0e60e00c80c20bd0b70b10aa0a507406906806505a05903d03203102e02302201900e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record044_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record044) (record044.maps 6) (record044.inverseMaps 6) record044_frame006_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record044) (record044.maps 6) (record044.inverseMaps 6) record044_frame006_indices (Fin.ofNat record044.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record044_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record044) (record044.maps 6)
      (record044.inverseMaps 6) record044_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record044_frame006_links_0000 record044_frame006_links_0064)
theorem record044_frame006_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 6 :=
  of_group record044 6 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record044_frame006_indices record044_frame006_graph record044_frame006_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (Fin.cases (record044_frame004_supported hcells) (Fin.cases (record044_frame005_supported hcells) (Fin.cases (record044_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record044_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00002
