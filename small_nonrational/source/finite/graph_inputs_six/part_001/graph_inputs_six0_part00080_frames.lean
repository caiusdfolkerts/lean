module
prelude
public import GraphInputsSix0Part00080Data
public import RawFrameSupport
public import SharedFrameGroups018Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups027Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x623c418730be10c0d7eafb5f1bcf78ee4dc6b896eedadacb4d67acad8eb155cab6d6b98320e2ec3c8710860dbfa7e0f49e73b0758dd1b2b596aad1988aec5c8b0157aa94fe9d52ea5447c8e9042043fc788ea1a633a5f0bc9662c6548a693f2664b08e9182224347f0f81d0354630ba16c2c0558a91081fc3a8670b21602a05109a1302103304e0941202003a0700981201e0380400700800800800 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (embedding record001) hcells Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3137861a00cede73137f9ba4d8a4ad23d90f480e3df15e8a3bb01bdcdba69eb395986bcf5db2c254f6a2350527cd34a98948823cd1aa8ae451215908c8203fb9fc0f8e7b73d09e48d366822ea951c9de4d625f91c48aa3dc1df8e846f436e1910c485d82c315e0a4c50626d12f08c83c81de0eb06782f61750b005642a413409304682180fd07b83c01b40af05002340de06902e815c0a8037018809403e01c00a804c02000d005002000e0060028010002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1927c8b61430736e8b65da7ed1549ca23501677939d9c24d8e5d92d195e49324672228ca45f22e315089cc4ba048ee26f13559a8ad0f671ac1d51ca72529289930691147e236515684c41fa064ff47e93e99f14f6c7a73ca974cab453e28f13c889e3dd1e40e946ee3181858b9458c2b514f8a4450427313088043e21d50cc06403141740b7059c28613d090844820a0fe07783a412e09404801cc0d806002e01580aa05401d80d005002400f0074038017009804001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x583abf757cab451128534049f4ca4250f26f909480a3d310c87bc38a12f08683ac025fecfe37ecbf0df5ad2b65eb2958fcc525632961480a194f6a5d92cc94a490a4151fe8f0474a38d1b886b40f9cd8d7c6ae33f9960b5c54f29f94a4a0e4df24291d88a4431211903c8023f01f08f4467e2e01680ae853027010b081c3c61c20da06803241810b90588290133092845c1fa0f6074838c0c806002e81700ac05502a00f007203501600a004a02400f0074038017009804001e009004001c00a0040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (embedding record009) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1996c51e18afc979cbadd27288d4059de4e767093639764b4657924c919c88a32917c8b8c54227312e6a2b38d88cbf65822a2d4e4a4f513260121c8fc46b22ad07e7fa3f49f14f6c7a73ca9c48d845d02ab94f8a364f22260f687903a21bb8c2c58c2b51488a084e626112708c844420f10408043f01f10f1875436619e0cc06403141820ba05b82ce14a0a184f426a12108c844820a0fe07783a40e606c03001700ac05502a00ec068028012007803a01c00c005c02a013008804001e00b004802000e0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x607bcb76ee75cdb855ceb355caa5536a5d45a754e697d1ca3145282d049fb3e27a4f29151ea3345e86f06208c077f8f65dd3b4752e79bdb676c4d5da8b4d68ccbd902f0594b055b2a950096929a4446c851001fb3e27b0f41e33b2720de1aa340668c998b2f85b4a694127a4dc9912c238458870f11d6398708d71a23245c8b214c280340630b6160290510a00e4198280480780e81c03005c0a8130220400780b0120200380400600800800 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x5a9b31652c8d90b195a2b1d5eab3562abd52a9752aa353da774e69752da5749e93525937222394668830820dc11804f85ddbb574ce59b9b54694cfd9c33465ac6d872e6580ad954a9d4f89752a24747a860fd1f23cc780ed9d53946ecd89a3338658c918a2fc5c0ab1452824e89912e23e464888f81e63ac718d41a03245d8b214e2842e8570a0130230450880d4178270480780e81c03005c0a8130220400780b0120200380400600800800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32c994ac2860e6ea769cb43d96e8b54469cd4e066d92c795e49324672228a9c4f22610b8851c26604ee126aa3521a1ea91538294930690647ba3650ae84440c9f4cf8a7b73d31e54aba53c28f113c7a43c31d28c8c6202e514f8a4450627213086ec3561980ba85b42ce14309e848422410c07f03bc1c40a104a024812007d03781b00c005b02b81540a804501b80d005002300f8074038017009804001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x188f01e02bcd756ea5cdaf15daba55cab555aa3d45a834da9a5329bf33e2bc486a6d2da233e642bc1662c05169a52e23744684907a0b40e810e519d31e58ca713a2684b4941252243ec748dc1902f8580a411c2203b06d0c41782d8590aa14c2904608a0e41b8350580a01282303e0740e0170260400700a01001c0280400600800800 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x597eaf9568a52cffe7c93b98cdc6162df09784341d5fb6fc77d8bdd9edaf6466031f94b6a1947823a91c48dc4341d80d7867f2d714e8a0e48a229103c8023f11f00f4467e2cb14c086c3c61a00c906082e21620a404cc24a11708203d81d20dd05002480fa06f03201800ba05b02b81540a804602280e406e03501600a004a02300f8074038017009804001c00a004001c00a0040018008002000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x1d5b8e718dd9b3364ec0caf95328e25c41872fb5f2bdb756e95cfa5945a454726d4d8dacb51658ba15a2a24d893120a1940a7a4f29e03b6758d69822de5309d92a2484848d1162083d0738dc1983105b8ae11c2103b06d0c41782d8590aa14c2904608a0e41b8350580a01282303e0740e0170260400700a01001c0280400600800800 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x665b303976c84628f0c57e4baddc1acf166eae05682b0b560a2d511a7353819b64b1e57924c919c88a2a713c89842e21470996a4310d4e0a4f4c024251ee8d64221f14f6e7a63ca9c3ca7851b2260f547863a21880a445062721308938464222107878c3761ab0cf06603041750b6859c29414309e84d424211908904301fc0ef07102480fc07d03781b00c005b02b81540a804602280dc068028011807c03a01c00c005c02a013008804001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65ef2e1846c17dc86e1d69cb43d97e923476a274fe27b73c0982cafa4a1237914c6b22f31598a144a217d0a984839adc2ad516a234359c4bcd541a9cd4aaa2548a23ed19c8ac432216507c8243fc9f4cf907b73d21e50d3254f29f94849e23e01e38e686f03301928c285e02c514f8a5050627013007c83ac1d00dd869831e17c0ba85982a4142097844c218104070836c16a09e04801cc0d406002d01600ae05401d80c8050022010007c038017009803801a00b005002400e0050020008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2c81628ad1d642aef563a52cffe7c93b992d493e47510f880c3b1fb6fc77d8bdd9edaf6466032918fca5b51fa8652ce93049024351e28ea4712370f5876035e1ab4cfe5ae29d14a8a0e49a24511d48a444320790087e23e01e88cfc5962bb14c08ac4362060f187503401930c105c42c4148099849422e10a08203d81ba09203781900c005b02c015c0aa05402300e406e03501600a004602000f8074038017009803801600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xccb656f283908c316167045819bf25d6ee0d678b375702b41585ab052368e545a979cb6258f15389e44c21710a384cb5054eaa4f4c024251f28d6432210101a7c83db9e98f2a54128d91307aa3c51d10cc06182d914a0a0c4e426112708c84441f20f186ec35619e0cc06082f81750b6859c2a414a09e84d425e12108c844c2180fe07102480fc06f03201800b605802b81540a804601b80b0050023010007c03a01c00c005c02a013008803801600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1996cb0e51f211862c0de04afc9794b81dbaed9d670b3358d2c33600af5d74eb8159eac1d5d2a8f52ea92535299545aa1d50c680b2c795e49324672228da459e2ab13e88f42e21470996a4339953aa7051125f12168f7457a11103c7f83e29ed0f4c7952b494f09dc4481eb8f0c6f63101750b10522280139098449c23211108043f21ec0ea86ec35619e0cc05b42ce143093848423411208583f81ee0ef07403880fa06f03601ac0ca06202d81540a804501b80d006602d015008c03a01c00c005c02a013008003c01c00b005002000e0060018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record024_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record024_frame001_links_0000 (interval_append _ 64 128 133 record024_frame001_links_0064 record024_frame001_links_0128))
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1610afed2f2963446a15cf5e79333398e4a1e4df12c88cc3de1c4ff67f1bf0df5ad24652b1e589aabf52028513d09c44d426712ee96b4ae2551292926492244521090047ca3cd1d88e446c9cf4d5c6532d8953ca524f424191d889e43121190047e03e11a10b8057428510a081c3c01c20da06483021720a4850c272134097049823a118084840c1fc0f507883a81c80dc06b034013809704a02300f207403881a408203101600a004a024011007803a01c00b804c02000f0068024010007 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (embedding record025) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x304dffbef7a2eedd8ba5742e25b9b656a2cfd99b2964ac858cb15622b9d66ab954aa6d4ba8b4ea9cd2fa394628a505a093f67c4f49e52864547a871045fe3da768e79c037b6e0d9db13576a2d35a33065deb0554a894fe94d1b2144007ecfb9f13d87a0f19bd33462cb694c2804f49b932238458870f01d6398700d71922e4590ab14c2804087f0d018c2d8580a41442803a0720e01982c0520a01202103c0740e0170260400780b0120200380400600800800 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record026_frame001_links_0000 (interval_append _ 64 128 130 record026_frame001_links_0064 record026_frame001_links_0128))
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x2a3d46a8b5029cd37a6b4c694526a4747e8c514a1741e83503a013fe7bcf09db3aa73ce49b935e6b4d299732663cc297d2ea5bcb395f1c22bc43818fc1ef3b171add9af35969ad019c329642c65892df588a7d46a6d4cc90115a073e67b0f19dc3ac730e219d3065e8b494d2724cc96923220424810ef1d038c700d018e2f05b8b215a2a0418810d81982d8580a41442803c0760e41a02d0540a01202103c0740e0170260400780b0120200380400600800800 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (embedding (N := 44310) record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record026_frame002_links_0000 (interval_append _ 64 128 130 record026_frame002_links_0064 record026_frame002_links_0128))
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0421.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0421.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0421.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0421.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0421.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0421.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0421.localPairCheck (embedding (N := 44310) record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record026_frame003_links_0000 (interval_append _ 64 128 130 record026_frame003_links_0064 record026_frame003_links_0128))
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0421
    Papers.RationalityTen.SharedFrameCatalogue.group0421_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
def record026_frame004_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0343.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0343.count (({ width := 8, code := 0x81807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record026_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0343.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0343.localPairCheck (embedding (N := 44310) record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0343.localPairCheck (embedding (N := 44310) record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0343.localPairCheck (embedding (N := 44310) record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record026_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0343.localPairCheck (embedding (N := 44310) record026) (record026.maps 4)
      (record026.inverseMaps 4) record026_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record026_frame004_links_0000 (interval_append _ 64 128 130 record026_frame004_links_0064 record026_frame004_links_0128))
theorem record026_frame004_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 4 :=
  of_group record026 4 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0343
    Papers.RationalityTen.SharedFrameCatalogue.group0343_facts record026_frame004_indices record026_frame004_graph record026_frame004_links
def record026_frame005_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0284.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0284.count (({ width := 9, code := 0x26731974a64d2491c86391b8cc5e271187432170a83c160702803f1f2f679bc1deec74ba1cae270379b8db6d359a8d16733194c86230578ba5cadd6ab459ac15caa532853c9a4ba4d1c8540a00fc7c3d9e4ec72381b0d2633017cba5c2d15cac50271309647221047e3d1e0ec6e361a8cc6431168b056251208c401f0e87034180a85026120803c1c0b048200e04018080200 } : Fields).get c.val)
theorem record026_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0284.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0284.localPairCheck (embedding (N := 44310) record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0284.localPairCheck (embedding (N := 44310) record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0284.localPairCheck (embedding (N := 44310) record026) (record026.maps 5) (record026.inverseMaps 5) record026_frame005_indices (Fin.ofNat record026.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record026_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0284.localPairCheck (embedding (N := 44310) record026) (record026.maps 5)
      (record026.inverseMaps 5) record026_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record026_frame005_links_0000 (interval_append _ 64 128 130 record026_frame005_links_0064 record026_frame005_links_0128))
theorem record026_frame005_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 5 :=
  of_group record026 5 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0284
    Papers.RationalityTen.SharedFrameCatalogue.group0284_facts record026_frame005_indices record026_frame005_graph record026_frame005_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (Fin.cases (record026_frame004_supported hcells) (Fin.cases (record026_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xccb64db245911c2ce0930217e4baddc0edcd6c9b3d5992b3557fab4d526a6151ea6152ba939428a0b50165d52cf962492a4632278ca45f22e315089cc4b9bd2d42671ac014eca264c024791f08ab427a1050387fa3f49f1cf6c7a73ca9730a844f22260fa878837718d8c345d02c615a8a4c504273130893846422210087c43aa1ac0c8062830617b0ba05b82ce1520a504f426a12f09084141fc0f607803a40e807103201800ba05c02b01540a803c01c80b0050025012007803a01c00c005c02a013008003c018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record027_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record027_frame001_links_0000 (interval_append _ 64 128 132 record027_frame001_links_0064 record027_frame001_links_0128))
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xdbfb43676c6d57a9f4ee97d139eb3c670cbf95729e51c9190f20e38c578ab1461dc3986b03604c037e6fb5f3bc978aefddbbb1756d4d89ae54a2824ea95f21a3844f837041ff3ef7ccf3de03b574ed759d3215deb255d2a14ea9bd2ea534968dd15a2242e824fa9eb3966f8d397b2c8574ac94c2824e89911321c4047e0f61d832c618b815e298320620ac150288500941242403806c0a8140250480780e81c03005c0a81302003c0600901001c0280400600800800 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record027_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record027_frame002_links_0000 (interval_append _ 64 128 132 record027_frame002_links_0064 record027_frame002_links_0128))
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
def record027_frame003_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x8430720c4178250460740c81100e00bfe7f8fe5fc3f77e6fc5f83ec7cef99f2bdd7b6f69e6bcb792f19e23c1772ee1db3b3762eb9c5b706becd18db055cab3d62aae528a4942a7c4e89ad322614b68cd0b2053c8738e01ae32663cc01792e65a4b215f2b4548a494325e49c8a9011e03ac750e51c03706b8c818a3005d8ba16428c4f89b13024c338640b0150288500941242403b0700b0140250480780e81c03005c0a81302003c0600901001c0280400600800800 } : Fields).get c.val)
theorem record027_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record027_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record027_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record027) (record027.maps 3)
      (record027.inverseMaps 3) record027_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record027_frame003_links_0000 (interval_append _ 64 128 132 record027_frame003_links_0064 record027_frame003_links_0128))
theorem record027_frame003_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 3 :=
  of_group record027 3 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record027_frame003_indices record027_frame003_graph record027_frame003_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (Fin.cases (record027_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb4059eece1656b2558caa9d549a9e526691146d9a34cbe63130c97acb7a521287937c84a4051e988643de1c509784341d6012ff67f1bf65f86fad69432958a4ac352027b53869a74cba5d92cc94a494248522690547fa3c11d28e346e1ce8d5c65830d9748b5454f294937c90e47622a10c48464011f80f847a23ac1b18cec5c02ba138086040e1e50e106d03241810b905882ac14f0a404cc24a11708803f41ec0ef074838c0ca06403101800ba05c02b01540a802d01600a8050025012007803a01c00c005c02a013008003c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame001_links_0000 (interval_append _ 64 128 136 record028_frame001_links_0064 record028_frame001_links_0128))
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcd5668332d96bca8e4daffb7f1bf25c9ae27703acc55f6ae5547a9754929854aea4e50a282d4059754b3e58924a918c89e32917c8b8c54227312e6f335099c6b0453b28993da9a24be24791f08ab428a10503c7fa3f49f1cf6c7a73ca9740a844f225c91b88903ea1e20ddc63a30d1750b1856a29314109cc4c224e11908884021f10ea86cc35819e0c806282f61740b7059c2c01590a904f425e12108d04141fc0f707803a40ca06403101800ba05c02b01540a802d01600a8050025012007803a01c00c005c02a013008003c012008003801800a0040018008002000 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame002_links_0000 (interval_append _ 64 128 136 record028_frame002_links_0064 record028_frame002_links_0128))
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
def record028_frame003_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x8670ca18c3085f0ba1242384507a0d4167ecfcdf83ec7d2f99f2be47c6f7deebdb784ef9dd3af756e9dd33a5748e8dd13a169ecbd8b2c4548a2d3d26e4cc96528a4546e8d11722844c87d0e21a42e740d819730c5e8b91652ba544a19402744d09912b2504989191d2224247e0f41d03686b8d1196324610bf17a2e85b8b616a2c8580ae15a2a8548a814e2982f85e0b81682b8560a013c2702d0580a8140250480780e81c03005c0a81302003c0480800e0180280400600800800 } : Fields).get c.val)
theorem record028_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (embedding (N := 44310) record028) (record028.maps 3)
      (record028.inverseMaps 3) record028_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame003_links_0000 (interval_append _ 64 128 136 record028_frame003_links_0064 record028_frame003_links_0128))
theorem record028_frame003_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 3 :=
  of_group record028 3 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record028_frame003_indices record028_frame003_graph record028_frame003_links
def record028_frame004_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x9bb36a6bcd499f32a54ca794b26249c8e8ad146264478870fe1f43c8750d619c3182503a053fe7f2fd1f73eb7d0f9df33e570ed7da2aea584aa14b28a5049d536a614a6941252444848ed1c236466790de1a2320610be16f2ce56ca694a2884f89e1352644c09692723644c830fe1e4390708db1aa34c660c918e310608c017e2f05d0b816e2d0598b21622c0318620c01782d85a0a814c2902d0580a8140250480780e81c03005c0a81302003c0480800e0180280400600800800 } : Fields).get c.val)
theorem record028_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record028) (record028.maps 4)
      (record028.inverseMaps 4) record028_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame004_links_0000 (interval_append _ 64 128 136 record028_frame004_links_0064 record028_frame004_links_0128))
theorem record028_frame004_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 4 :=
  of_group record028 4 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record028_frame004_indices record028_frame004_graph record028_frame004_links
def record028_frame005_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xf91f1fe2fc3f85f03ce798f29df7be77be7bcef9c72de57ca78ff1be2fc1381f02da7b47676b4d65ac3556a6d47a734c695c81877065acb035aaad538a5340a784cf9412623fc6a8b911e1c42a842ef5c83756ced29a0b2262ebfd6dad2584acd5529a520a1d3f2754aa91910a103e671cde1aa330638bd9712ce574ac15028a48c890ff1ec36c698cc1842d82f85e0b816c2c8580a41442802d0580a8140250480780e81c03005c0a81302003c0480800e0180280400600800800 } : Fields).get c.val)
theorem record028_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (embedding (N := 44310) record028) (record028.maps 5)
      (record028.inverseMaps 5) record028_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame005_links_0000 (interval_append _ 64 128 136 record028_frame005_links_0064 record028_frame005_links_0128))
theorem record028_frame005_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 5 :=
  of_group record028 5 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record028_frame005_indices record028_frame005_graph record028_frame005_links
def record028_frame006_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0xc738df1b635c678c70ae13c2381b02e02bad756e9dcab8f716dedb9b6d6b6d65a9b0f616c1d70add5b2b1d5fabb55ea95509e735260c6186908608bfa7e2f5de4bb0728e29c03746dad71aab4d68cba1622af53ea193d25d4aa8f90fa1b4167f8fb1e83c476cea1cd36869cc597d2cc540a59412664b48f918224434851082063c4710d619c2ec5b0b315c2a42e05b0b21602a85409c1342602c0560a4138250480780e81c03005c0a81302003c0480800e0180280400600800800 } : Fields).get c.val)
theorem record028_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (embedding (N := 44310) record028) (record028.maps 6)
      (record028.inverseMaps 6) record028_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame006_links_0000 (interval_append _ 64 128 136 record028_frame006_links_0064 record028_frame006_links_0128))
theorem record028_frame006_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 6 :=
  of_group record028 6 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record028_frame006_indices record028_frame006_graph record028_frame006_links
def record028_frame007_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0630.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0630.count (({ width := 8, code := 0xcbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a3a1a09b9998969391908e8b8887858382817f7e7d78767573706e6d6b68656462605f5e5c5b5a58555352504d4a494745444341403f3e3d3c3b3a383735343332312c2b2a2928272423221e1d1c1b1a1916151411100f0e0d0c09080706050403020100 } : Fields).get c.val)
theorem record028_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0630.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0630.localPairCheck (embedding (N := 44310) record028) (record028.maps 7) (record028.inverseMaps 7) record028_frame007_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0630.localPairCheck (embedding (N := 44310) record028) (record028.maps 7) (record028.inverseMaps 7) record028_frame007_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0630.localPairCheck (embedding (N := 44310) record028) (record028.maps 7) (record028.inverseMaps 7) record028_frame007_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0630.localPairCheck (embedding (N := 44310) record028) (record028.maps 7)
      (record028.inverseMaps 7) record028_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame007_links_0000 (interval_append _ 64 128 136 record028_frame007_links_0064 record028_frame007_links_0128))
theorem record028_frame007_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 7 :=
  of_group record028 7 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0630
    Papers.RationalityTen.SharedFrameCatalogue.group0630_facts record028_frame007_indices record028_frame007_graph record028_frame007_links
def record028_frame008_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xdc7b876fedadabb434de99d2fa133fe7aca594327642c818fb15e2ac518770e61ac0d81300df9bed7cef25e2bbf76eec5d5b51626b9529a093aa67cb895d21a3844f839041ffbef7ccf3de03b574ed799d321614bdd772c9574a853ba6f4be94d25a374568890ba093ea7ace59be34e5fcbd96d2c8574a61412744c89391b2264047b0ec1ce32c618b915e2982b8560aa150288500941242402b0540a4140250480780e81c03005c0a81302003c0480800e0180280400600800800 } : Fields).get c.val)
theorem record028_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record028) (record028.maps 8) (record028.inverseMaps 8) record028_frame008_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record028) (record028.maps 8) (record028.inverseMaps 8) record028_frame008_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record028) (record028.maps 8) (record028.inverseMaps 8) record028_frame008_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record028) (record028.maps 8)
      (record028.inverseMaps 8) record028_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame008_links_0000 (interval_append _ 64 128 136 record028_frame008_links_0064 record028_frame008_links_0128))
theorem record028_frame008_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 8 :=
  of_group record028 8 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record028_frame008_indices record028_frame008_graph record028_frame008_links
def record028_frame009_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0xc4d89712622c3d862fddfabf37cef85ebba173ae5dc5b85702da5b2b5f6a2d3da4b1d632c5587b0b612bb574ae55beb756ca113aa6ac888d115e21c3284f025fcbdd778ed1d2b97722e1dbfb796e2c897cae55a6b0d5ba955129b5242444688a110213414818fe9ec3b8748d81a030e584ae14c2844ec9612523e45c871072023c4720d91a830c5e8b61602a82f85e0ba1702c8580a41442802d0580a8140250480780e81c03005c0a81302003c0480800e0180280400600800800 } : Fields).get c.val)
theorem record028_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (embedding (N := 44310) record028) (record028.maps 9) (record028.inverseMaps 9) record028_frame009_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (embedding (N := 44310) record028) (record028.maps 9) (record028.inverseMaps 9) record028_frame009_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (embedding (N := 44310) record028) (record028.maps 9) (record028.inverseMaps 9) record028_frame009_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (embedding (N := 44310) record028) (record028.maps 9)
      (record028.inverseMaps 9) record028_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame009_links_0000 (interval_append _ 64 128 136 record028_frame009_links_0064 record028_frame009_links_0128))
theorem record028_frame009_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 9 :=
  of_group record028 9 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record028_frame009_indices record028_frame009_graph record028_frame009_links
def record028_frame010_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0822.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0822.count (({ width := 9, code := 0x9cce26f369acd2673298cc25f2e96cb2572a94ca24f2692c92472290c823f1e8ec72371a8cc622f168ac3e150780bf1f2f77abc1d8e670379b6d86bb51a2cf66b2d8ac05eaed72b4582a948a24fa7136984aa4d228f46a2d0c823e1d8e871371b4d4673298cc2602f970b4582b950a652289407e3e1e8f07238190c460271309448211006832180b05428130803c1208038180a04018080200 } : Fields).get c.val)
theorem record028_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0822.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (embedding (N := 44310) record028) (record028.maps 10) (record028.inverseMaps 10) record028_frame010_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (embedding (N := 44310) record028) (record028.maps 10) (record028.inverseMaps 10) record028_frame010_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (embedding (N := 44310) record028) (record028.maps 10) (record028.inverseMaps 10) record028_frame010_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0822.localPairCheck (embedding (N := 44310) record028) (record028.maps 10)
      (record028.inverseMaps 10) record028_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame010_links_0000 (interval_append _ 64 128 136 record028_frame010_links_0064 record028_frame010_links_0128))
theorem record028_frame010_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 10 :=
  of_group record028 10 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0822
    Papers.RationalityTen.SharedFrameCatalogue.group0822_facts record028_frame010_indices record028_frame010_graph record028_frame010_links
def record028_frame011_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0823.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0823.count (({ width := 8, code := 0xdcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b7b6b4b0afada9a7a5a4a2a09b9a9896959391908f8d8c8a868482817f7d7877757372706e6d6c6a68666563615c5b595756545251504f4e4d4b49484744434241403534333231302b2a292221201f1e1d181716131211100f0e09080706050403020100 } : Fields).get c.val)
theorem record028_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0823.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0823.localPairCheck (embedding (N := 44310) record028) (record028.maps 11) (record028.inverseMaps 11) record028_frame011_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0823.localPairCheck (embedding (N := 44310) record028) (record028.maps 11) (record028.inverseMaps 11) record028_frame011_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0823.localPairCheck (embedding (N := 44310) record028) (record028.maps 11) (record028.inverseMaps 11) record028_frame011_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0823.localPairCheck (embedding (N := 44310) record028) (record028.maps 11)
      (record028.inverseMaps 11) record028_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame011_links_0000 (interval_append _ 64 128 136 record028_frame011_links_0064 record028_frame011_links_0128))
theorem record028_frame011_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 11 :=
  of_group record028 11 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0823
    Papers.RationalityTen.SharedFrameCatalogue.group0823_facts record028_frame011_indices record028_frame011_graph record028_frame011_links
def record028_frame012_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0427.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0427.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0427.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0427.localPairCheck (embedding (N := 44310) record028) (record028.maps 12) (record028.inverseMaps 12) record028_frame012_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0427.localPairCheck (embedding (N := 44310) record028) (record028.maps 12) (record028.inverseMaps 12) record028_frame012_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0427.localPairCheck (embedding (N := 44310) record028) (record028.maps 12) (record028.inverseMaps 12) record028_frame012_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0427.localPairCheck (embedding (N := 44310) record028) (record028.maps 12)
      (record028.inverseMaps 12) record028_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame012_links_0000 (interval_append _ 64 128 136 record028_frame012_links_0064 record028_frame012_links_0128))
theorem record028_frame012_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 12 :=
  of_group record028 12 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0427
    Papers.RationalityTen.SharedFrameCatalogue.group0427_facts record028_frame012_indices record028_frame012_graph record028_frame012_links
def record028_frame013_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0425.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0425.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0425.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0425.localPairCheck (embedding (N := 44310) record028) (record028.maps 13) (record028.inverseMaps 13) record028_frame013_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0425.localPairCheck (embedding (N := 44310) record028) (record028.maps 13) (record028.inverseMaps 13) record028_frame013_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0425.localPairCheck (embedding (N := 44310) record028) (record028.maps 13) (record028.inverseMaps 13) record028_frame013_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0425.localPairCheck (embedding (N := 44310) record028) (record028.maps 13)
      (record028.inverseMaps 13) record028_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame013_links_0000 (interval_append _ 64 128 136 record028_frame013_links_0064 record028_frame013_links_0128))
theorem record028_frame013_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 13 :=
  of_group record028 13 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0425
    Papers.RationalityTen.SharedFrameCatalogue.group0425_facts record028_frame013_indices record028_frame013_graph record028_frame013_links
def record028_frame014_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0426.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0426.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0426.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0426.localPairCheck (embedding (N := 44310) record028) (record028.maps 14) (record028.inverseMaps 14) record028_frame014_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0426.localPairCheck (embedding (N := 44310) record028) (record028.maps 14) (record028.inverseMaps 14) record028_frame014_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0426.localPairCheck (embedding (N := 44310) record028) (record028.maps 14) (record028.inverseMaps 14) record028_frame014_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0426.localPairCheck (embedding (N := 44310) record028) (record028.maps 14)
      (record028.inverseMaps 14) record028_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame014_links_0000 (interval_append _ 64 128 136 record028_frame014_links_0064 record028_frame014_links_0128))
theorem record028_frame014_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 14 :=
  of_group record028 14 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0426
    Papers.RationalityTen.SharedFrameCatalogue.group0426_facts record028_frame014_indices record028_frame014_graph record028_frame014_links
def record028_frame015_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0423.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0423.count (({ width := 8, code := 0xc2c1c0bfbdbcb8b7b6b5b4b2afaeadabaaa9a7a5a4a3a2a09d9c9b99989795949391908f8b8a8986858482807e7a78767574737271706f6e6d6a696866625f5e5c5a5958575655545352514e4b484744434241403f3e3d3c3b3a383634312f2d2c29282726252221201f1e1d1c1b1a1817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0423.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (embedding (N := 44310) record028) (record028.maps 15) (record028.inverseMaps 15) record028_frame015_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (embedding (N := 44310) record028) (record028.maps 15) (record028.inverseMaps 15) record028_frame015_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (embedding (N := 44310) record028) (record028.maps 15) (record028.inverseMaps 15) record028_frame015_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (embedding (N := 44310) record028) (record028.maps 15)
      (record028.inverseMaps 15) record028_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame015_links_0000 (interval_append _ 64 128 136 record028_frame015_links_0064 record028_frame015_links_0128))
theorem record028_frame015_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 15 :=
  of_group record028 15 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0423
    Papers.RationalityTen.SharedFrameCatalogue.group0423_facts record028_frame015_indices record028_frame015_graph record028_frame015_links
def record028_frame016_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0424.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0424.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0424.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0424.localPairCheck (embedding (N := 44310) record028) (record028.maps 16) (record028.inverseMaps 16) record028_frame016_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0424.localPairCheck (embedding (N := 44310) record028) (record028.maps 16) (record028.inverseMaps 16) record028_frame016_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0424.localPairCheck (embedding (N := 44310) record028) (record028.maps 16) (record028.inverseMaps 16) record028_frame016_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0424.localPairCheck (embedding (N := 44310) record028) (record028.maps 16)
      (record028.inverseMaps 16) record028_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame016_links_0000 (interval_append _ 64 128 136 record028_frame016_links_0064 record028_frame016_links_0128))
theorem record028_frame016_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 16 :=
  of_group record028 16 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0424
    Papers.RationalityTen.SharedFrameCatalogue.group0424_facts record028_frame016_indices record028_frame016_graph record028_frame016_links
def record028_frame017_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0288.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0288.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0288.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0288.localPairCheck (embedding (N := 44310) record028) (record028.maps 17) (record028.inverseMaps 17) record028_frame017_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0288.localPairCheck (embedding (N := 44310) record028) (record028.maps 17) (record028.inverseMaps 17) record028_frame017_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0288.localPairCheck (embedding (N := 44310) record028) (record028.maps 17) (record028.inverseMaps 17) record028_frame017_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0288.localPairCheck (embedding (N := 44310) record028) (record028.maps 17)
      (record028.inverseMaps 17) record028_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame017_links_0000 (interval_append _ 64 128 136 record028_frame017_links_0064 record028_frame017_links_0128))
theorem record028_frame017_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 17 :=
  of_group record028 17 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0288
    Papers.RationalityTen.SharedFrameCatalogue.group0288_facts record028_frame017_indices record028_frame017_graph record028_frame017_links
def record028_frame018_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0286.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0286.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record028_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0286.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0286.localPairCheck (embedding (N := 44310) record028) (record028.maps 18) (record028.inverseMaps 18) record028_frame018_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0286.localPairCheck (embedding (N := 44310) record028) (record028.maps 18) (record028.inverseMaps 18) record028_frame018_indices (Fin.ofNat record028.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record028_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0286.localPairCheck (embedding (N := 44310) record028) (record028.maps 18) (record028.inverseMaps 18) record028_frame018_indices (Fin.ofNat record028.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record028_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0286.localPairCheck (embedding (N := 44310) record028) (record028.maps 18)
      (record028.inverseMaps 18) record028_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record028_frame018_links_0000 (interval_append _ 64 128 136 record028_frame018_links_0064 record028_frame018_links_0128))
theorem record028_frame018_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 18 :=
  of_group record028 18 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0286
    Papers.RationalityTen.SharedFrameCatalogue.group0286_facts record028_frame018_indices record028_frame018_graph record028_frame018_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (Fin.cases (record028_frame003_supported hcells) (Fin.cases (record028_frame004_supported hcells) (Fin.cases (record028_frame005_supported hcells) (Fin.cases (record028_frame006_supported hcells) (Fin.cases (record028_frame007_supported hcells) (Fin.cases (record028_frame008_supported hcells) (Fin.cases (record028_frame009_supported hcells) (Fin.cases (record028_frame010_supported hcells) (Fin.cases (record028_frame011_supported hcells) (Fin.cases (record028_frame012_supported hcells) (Fin.cases (record028_frame013_supported hcells) (Fin.cases (record028_frame014_supported hcells) (Fin.cases (record028_frame015_supported hcells) (Fin.cases (record028_frame016_supported hcells) (Fin.cases (record028_frame017_supported hcells) (Fin.cases (record028_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2b9d5ba8fcc78230b16f8b1455225f11c8304139f9cfb86eab4a1940c4f61e2dc1586a3b4f5275d3889a84ce25c52ca95c4aa253928c92b492247122c90348023cd1d68e046c9acccaa6212e91504a4850427a138091847b22a10047e23db1d90d8c5a42b514a8a144e221d10607943241820b6055c2a01490a204f425612608e844421210507f83d41e00ea071037c1ac0d0050024811a08c03e81bc0d406901b80c4054028012808803e01d00e00540260100068028010007 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x1ca790efcde5ad73be72cc99672be54ca392b20626c4385708602bef7baf55d7b9d736915078ff19228c36800fc9f1bd275ce91ca37e6d4d8dabb4e620b7157a98524a253b24d4808e10ba1341c820fb1e53c074ce41b730a5e8b69682c852ca313c2484848c10f2124107f0f81d83806b8cc19030c5e8b71582a44707f0da19c2d8550a41141b8320620b41602504607c0f01c02a04c0800d0140200380600a01000800 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332d90bc2ce0930217e4bb75d6ec01549a98547a73137f9ba492a4632278a9c4f22610b8851c265654a8a4c021510387c73db9e98f2a5f62ab11306402e81498a0c4e426112708c84441f90e106c830617b0ba85b42ce1520a504f426a12f09084301fc0f6078038814009203e81c40de06403001740b605702a815008a03901b80b0050025011807c03a01c00c005c02a013008003801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x665afc9766bb1d802a8f52ea92514a89d3989bfcdd25892be92548c644f1598a144a21750a5849b51d608a714f8268921a8f6429a10d03c7c73db9e90f2a5d029e92f08dc3d91e10c7c61e2ea1498a0c4e026112708c84441f90d986b034c19e0c505ec2ea1670b005642a41490a104bc23410c08203f81ee0f007082480fa06f03501880c005d02b81540a804501b80c8054028012807c03a01c00c005c02a0130080038014009004001c00c0050020008002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x5e3bb572ee4d97adf5bab4d58aaf5529dd34a3b4668bd06a053e67acf19b53666b4ac94f24244c838f3049fdbb373ee19c1b7a6e6d99ac352698d158b3065f2b21612b5550a5944a594a49091ba2b44a87d0ca134127fcfb9f23da79cf11bd3185b8b395229851ca193624c474868f71e63a8700de1943085c0ab13625c340620b61582a0530a00e81c8310520a01102104007c0e0170260380680b0140240380500800800800 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x665b0d5859bf25dbaeb748da39516a7f13db9e04caa62330592848de4531d18dc46b22a713c89835059c4bca5bd2cb5514a7552728953008f945622690c88544202084ff27c83db9e98f2869632317e4aac54128d13c48983c51bc0d986603201860bb458a29414189c84c024e11908883f21f20f207583a01c90e106ec3641ab0ce863c30617c0ba85b42cc1520a504f426a12f090844c2180f6071036c0c806002d81680b005702a00b0050023011008003e01c00c005c02a013007003401800b005001c00a0040018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
def record037_frame002_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x1b7f5a6abd2fa4b44e26c4b88b0c617c2983305e08bf57e2fadeabd379aee5dabaf622b8d48a7d4c686d039ef3a657c718a11221341f81f009f73d0782ed1d337e6e8d9d9fb39654c8177abb544a6d4027a4dc989292384588850b2093ea7ace29bf3646a0d099931c618bf17a2d858cac94d2844e49891321c4047e0f61d8374698b81402682b05409e1382604b0900a8140230440800f81c03005c0a81301c0340600b01401c0280400600800800 } : Fields).get c.val)
theorem record037_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record037_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (embedding (N := 44310) record037) (record037.maps 2)
      (record037.inverseMaps 2) record037_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record037_frame002_links_0000 record037_frame002_links_0064)
theorem record037_frame002_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 2 :=
  of_group record037 2 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record037_frame002_indices record037_frame002_graph record037_frame002_links
def record037_frame003_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x10860a41281902a043e47c4f7decbd67a8f45e83ce78ef15e1bbe77aeedda3b2760dbdaf34767eced8fb1a622c1172ac655eaa94da97522a213da6c4ca9812d24647c8e50f21541a810f21c135e6a4cd19631c60cbc16a2ca578ac95229250c9692823e4588890f21641c819001ec3bc750e61c236c6b0c818a3005d8ba1642b45409b11c2282c05409e1382604b0900b0140230440800f81c03005c0a81301c0340600b01401c0280400600800800 } : Fields).get c.val)
theorem record037_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record037_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (embedding (N := 44310) record037) (record037.maps 3)
      (record037.inverseMaps 3) record037_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record037_frame003_links_0000 record037_frame003_links_0064)
theorem record037_frame003_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 3 :=
  of_group record037 3 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record037_frame003_indices record037_frame003_graph record037_frame003_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (Fin.cases (record037_frame002_supported hcells) (Fin.cases (record037_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332d7e4bb35d8ede76d6b5f5712a9b534a9352468ed44e9fc4f6e78130595f494246f2298d645e62b314289442fa1530906a23389794a73512a7c134490d47da34d158864429a0f8ff27c83db9e90f2869629f93c497846e1ec8f1c73e3781980c7c6142c514a0a0c4e026012708c84441f90f907903ac1d00dd86cc34c18f0be05d42cc1600ac8548292142097846822610c08203dc1c20db03981a80c406002d01600ae05401d80c8054028011008003e01c00c005c02a013007003401600a004801c00c0050020008002000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x30a1839ba95b8ed8d65ca4e516a88d30f92648ce4451988c045ce1730a484d3781b0ed0f5852bc153aa524bc24451f88d942ba1110327fb3f41f4cf8a7952eb16f0ad251e2220f747903a51918c405ca2c715a0a7c52226110e08043e21bb0d586603221890b3850c27a12808904141fc0ef071029c12809004701b00d605f02e015c0aa05401a00cc04e02400f8074038017009004001e00b005002000e0040018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x59dacd757cab4529287d4239dd4a4250f26f8a2c4e224b10e87ec3a21b50c8857c25e10d075805bfe9fcef777b73d95a5cc7e564a8653229764b324191fc8f046e21ace686e433f96a4b3054f29f94a4a0e48a22910c884440f2008f446743291700b4057429810d878c3861b30d006482c4148099849423c0fd07b03a41ba08e03581900be05d02e015c0aa05402600e406a033016009c04a02400f8074038017009004001e00a004001c00a0040018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6423147862bce5d6ee096b7b56d7a2ba1576ab052728b5446987c9324672228cc46022e70b9852426988caf054ea93d2f690e47e23590887fb3f41f14f2a7122de15a4a364471ed0f207443101638ad0522261127087041e20810087e03e21e30dd86ac33c1980c886243041670a5050c27a135094046422410507f03bc1c408e04201b00d605f02e015c0aa05402600d0066027012007c03a01c00c005c02a012008804001e00b005002000e0040018008002000 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1465a31d0d6865377997ccb630d1828b5be75f06f7173436a1a4ad00600ad3966eae0562aa894d09e24e5a5d12b293647e23811848bd45b229914288c3d31bfcdd06993411990c545aa2c99510a5a50f26a92e493849724812008f846a1d38cac6322c514c89e049823c11608383e21e40db06542d21590a484ac21c10104a024011c06b02e01600ae05502a00cc04802000f8074038017009003c01c00b005002000e0050020008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1888c38e11b05f752b71db1a92945aa2746ca2e71697e5bb11b0ed0f5e8ac295e0a9153aa9494249864b624511f68d944e219103280d3fd9f4cf9079534e9758b7855d2a094789bc45221c0f8078e3a51b40cc05ca2d91638a7c52826110e07c83d81ce0dd86ac3301910c485f02da1670a9050825e128090044c2080fe04a024011c06b02e01600ae05502a00cc04802000f8074038017009003c01c00b005002000e0050020008002000 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x97897797497396495895792c92b9298fc8f88f68cd8928398197a874072f6ff6ee6d86b164d63a6055f25d75a758656455e55554253c5254c545344040b3f83dd3ad3523413113002ea2c32a328127b27225f2592422061de1d81bb1a819718117917016215214c13612510f1070fe0f00e00da09409008e06b05c05805705505403302402001f01d01c01701200f00e00b00a008007005004002001000 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x534e97744fa1dd07a81534098bcc0630d1828b5be75f06f715fa2cdd58aa9f534272d2b293347e238117a8b6450a230f326e83411984c5459329694309aa4b924b92408f846a2220e9c6d432b18c8c0858a29913c096849823c116087041c1f10f206d832a1770b48564292139095843820208e04201f80d605c02c015c0aa0540260118066024010007c03a01c00c005c02a012008803c01c00b005002000e0050020008002000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc2360beeb171eb85d2468ed44e983caae51926e92848de4531ae8bbc5a5f94e6b6f9361da1abd05862a394aaa114c325b119c8ad432216507c8243f59f4cf9079434e1760ab452126e914887039a1bc8cc064a30a1780adc53e29413008703ae1cf0dd869831017c0b705982a414209784a0240113070836c13c09004701cc0d605c02d01600ae05401d80cc048022010007c038017009003c01a00b005002400e0050020008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x642f1fb859c126042f2976eb70db12d5b5f1aecd5aeac9549a98547a98f4b3a274b1a55b28e933492a4632278d945ce2d2afe54528492d891e47b22710387fb3e39e54b9455626f10e07d43c21b40ba058e29313089384382010fc87b039c1c20d906443121830bd85b42ce1520a104d425e12809004101fc0f6078023810807d03881ac0ba05c02b81540a804c02280e4066025012007c03a01c00c005c02a012008003c01c00c005002000e0050020008002000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (embedding record050) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x28af43ca10ceda6192f596f4a4e5172738a4425e10d0758213ffdfd8d2d6553105590a454ee25d92269064782370e6a6a934b18fcc3c5a82cd153ca7c52726992248f045421910808023de1e88ebc67232b1700b3c57026410d08243ca1c30d886482de1620ab053c29012508f04401ec0ef07482380d606202e81700ae05502a013008a03601980c8054025012007c03a01c00a804001e00a004001c00c0050020008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (embedding record051) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa83d1968a343d997cc6660727e90848063e51868c145adf3af837b8ad3966eac5534278939695947e23811848bd45b228511875e3799ba0d246823151824b3c59329e94b49aa4c726012e492e49024111f08d43b91d38cac6322c514c8a304f025812608f045820e0f8879036c1a90ca85d42d21590a484ac21c10107b025011c06b02e01600ae05502a0130072033015009004202000f8074038017009003c01c00b005002000e0050020008002000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1908c4261b70c5794bb1db7ed856b7af85762ae9563aa3d4baa49494a2d513a3651738b4abc14eaa124f825e92d890d47da2710c881e4069fecf907952de15049bc4bc22310e07b23c71b40cc05d42d91638a504c224e10e07e43e41ec0e706ec35619e0cc064431217c0b6859c2c01590a9052428412f094048023411308203f81ee08e04201ac0c405c02c015c0aa05402600cc054024010007c03a01c00c005c02a012007803801600a004001c00c0050020008002000 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (embedding record056) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x334999ac356166edd75bb7e5afed5b627b0655d6ad348da39516a65d315983cbfe5c92cd952ca1a4eb25091bc8a63a91bb8d742f615109c5bd29392f696a456a2650c88544202084f90794323146888e4361bc8d946603201860bb452826012708703c81d70e787243841bb0d906ac33a1830be05982a414a09e84d425e12808984141ec0e206d823810806b032017c0b805a02c015c0a804c01980b004e024011008003e01c00c005c02a012007803401800b005001c00a0040018008002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1766bb1dc6ee116fcb17584eae556caa6d4d2a4d491a3b513a60f2ab94649ba4a1237914c6ba2ef169508a7c12f496c469a2b50c885341f1facf9079426e92f088c4381cf8de466031f1850adc52826012708703c81d70e786ec3661a60c405f02dc1660b005642a41490a104bc25012008d044c1ee0e106d823810807303581880b805a02c015c0a804c01d80cc054024011008003e01c00c005c02a012007803401600a004801c00c0050020008002000 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x649f22d786bbadc7ae176e3b63598e93947ba30511a6112ec968caf22c114989b430e15d09e6f13629a18ce4583aa814aca3b513a60d2228fc46722b509883f4182064ff67e93ee9f28f6a7932e995b0a44507279913c7ba3c81cd0de463030b17e0b9458e2b51548a5850225f10087c43bc1d70dd86983301910c505e82e61650a184f425012108904141de0d504f025c12807302e01680ae05602a80ec04802200f807803a017008003c01a00b00500240100040018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x160eafdd742b794d5a6251ee8c143ea11cf02521287937c95247f22a8d0c65a30113e89644662190f7871437a1a10b784ec2420fefdf7e9bef5ef4f717b434ad904c5356328753dc9764b3254d29892148da4191fe8e846d21ace6c6e733e1964b5c54f29f94a4a044f427092148ec46722910c88464141f78f3c67e2e01680ae8526285139085840e1f80f1870c3681a50c00580290133092847822e0fd07483440c805d02e01680ae05602a810c078039016009404802200f807803a017008003c01a00a004802000a0040018008002000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record061_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record061_frame001_links_0000 (interval_append _ 64 128 129 record061_frame001_links_0064 record061_frame001_links_0128))
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xccb618b05179cbb35d6ee39709b5bdab6cff57aaaad4f2a2349ca3dd18288d3089764b465791608a4c4da1870ae84f339188cb0455028ed44e98048723f11a28ad41fa0c0ff67e93e51ed4f267122e815b0a0e4f32260f6879039d1bc8c2c5f82c715a8a5850225f127088841e20810087e03e21de0eb86ec3661a60cf066032218a0bd05cc2ca14a0a184f426a128090846422410507783540f607302e01680ae05602a810c076024011007c03c01d00c005c02a011008003c01a00b00500240100040018008002000 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x62230e371eb85db8ed8d494a48d1da89d3ab9c94dea60b2f896ecafa4af23e9163f31cd6d8a6b334319c8bcd583aa494c4a56513a84d2288fb46722b50c885941f206501a7fb3ee9ed4f5279334c974cabc52e29113cc9be3e01e38e686f23301928c285ca2d91638aa450227512f87c83d81d70e806ec34c1980c886282e616c0b2854828412f094044c2080e106a827812807302e01680b005702a80ec048022010007c03a017007803801a00b00500240100050020008002000 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332d8fdc316167033766b8e5c26d6f6adb3fd8b6c255b7ab15556a79511a4a52468ed44e9d5ce4a6f530597c4b7657d25791f48b19c8bc6582298944ea1347da34515a86441f2034ff67b53d49e4cd245d029713cc9be3c71ce8de466030a16c8b1c50227512f89384442080f907b03ae1d00dd86cc34c19e0cc06443141730b605942a414209a84bc25011908984101c20d503f01ec0e605c02d01600ae055023010c076024011008003e01d00c005c02a011007803801a00b00500240100050020008002000 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record067_frame001_links_0000 record067_frame001_links_0064)
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (embedding record067) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
def record072_frame001_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xccb6403137862c0de04af29766bb1dc6ee116fcb6fdb0ad6ece45e52c11540a6f53128ed44ea13486a34d15a85340f1fecf947b53d49e4cd2c5d02b614eca5c507279937c7b239f1bc8c7c5d42c714b0a044ea25f12708884021f90f607903bc1d70e806ec3661a60cf066032218a0bd05cc2d81650ac852425011a08904101ee0ef07083540fa07303101700b405702a811407602a012008803e01d00c005c02a010007803801a00b00500240100060020008002000 } : Fields).get c.val)
theorem record072_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record072_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record072) (record072.maps 1)
      (record072.inverseMaps 1) record072_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record072_frame001_links_0000 record072_frame001_links_0064)
theorem record072_frame001_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) : Supported record072 1 :=
  of_group record072 1 (embedding record072) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record072_frame001_indices record072_frame001_graph record072_frame001_links
def record072_frame002_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa84d2d28f544ea11502e74f3739b54d2666131a986cbd25bcc815d82c3959cabe55caaad548a9d4bba4fd2368c444621a108a83d41ba0bceb46b0337997ccb464c32298fcaa4525285131493047d230916c8ae4512168e9c69e33e18f8c345fc2ee16e8ab853a27e136097449a23c115088c4382150f907282d414809d84902160fe07383480fa07303101700b405702a811407602a012008803e01d00c005c02a010007803801a00b00500240100060020008002000 } : Fields).get c.val)
theorem record072_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record072) (record072.maps 2) (record072.inverseMaps 2) record072_frame002_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record072) (record072.maps 2) (record072.inverseMaps 2) record072_frame002_indices (Fin.ofNat record072.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record072_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record072) (record072.maps 2)
      (record072.inverseMaps 2) record072_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record072_frame002_links_0000 record072_frame002_links_0064)
theorem record072_frame002_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) : Supported record072 2 :=
  of_group record072 2 (embedding record072) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record072_frame002_indices record072_frame002_graph record072_frame002_links
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (Fin.cases (record072_frame001_supported hcells) (Fin.cases (record072_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa66d2d672937f9b74d5a6373059604a7e4672198d946822e315a85142260a10396b4b511a3ed1368233f19eab44564aa714f09d84aea4c12188e846c23511988c345ba2c11528a344ca2511166fc35199fcc986392d39538a544f727212e89684ab253128093049124511ec8ea4712348f0465c2da14289dc4d625611e08b44161f20d106503101730ac852825010f07c83c41d20e206d83500e807103581a40ca06202e016807603401980c4058025012008801e00d0050024010007002000c004001 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record074_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080
