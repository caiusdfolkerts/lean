module
prelude
public import GraphInputsRow24Part00030Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030
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
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x333191ea124dc25a91f28e744c22290387fb3f41e98f2a75b26f121086c3c51d98d906ac2e81638ad04e426112688dc44821c0f907b039c1c70e106443121830b6859c2be15209e84d425e12808983f81ec0f007102380e206b032017c0b805b02b81540a803901980b004e024011807c03a01c00d805c02a012007803801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
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
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x32c591ec8163daae5548a9b4eba6bd2ca91b483a3f116486842a213507a8374179eece226753341968ca664531e9678aee56c2a21498a144f9275137c96e49923e91b08ca45b22b914472836f1978c7c5dc2ce14709f849a232111887042a2030f006d42f816a0ab051427812408403fc1ce0d203c01b80b805a02b81540800360180098048022010807c03a017009003c01c00d00500240100050020008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6ff6cf6bb69968b68666e6216125e45dc5d65b65525284fa4d04a349b44042c4173f13d23c83c63aa3a134233f3173152fb2f72f02c82c62ae2a52a229c29125724123621e2081eb1e51e11b91b119419118717b16d0f60e70cc0c40ae0a70a306105a05404804104003803602b02401e01601000f00b009004003001000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6ff6c76bb69168b6856676216125e45dc5d65b653b5284d84d049a43f4374173f03dd3c83c73a73a434233e3173092fb2f72ef2c82ba2ae2a52a129d2912362302081f41e51e11d91b119d19118718317d16d0f20e70c80c40ae0a70a306105b05a05605404804204003903602b02401e01600f009004003001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1dc6dec6dc3465a10cf56392e1d6a6ab4551aa4141a9764afa4892348ef414a070f9676e39c1c28e0867c33b9604af651627e13749a44c5233112c86641f20a101c7a63121860a9c51a26e13189583ee1dc0e206c034a1980b204201fa0e7071834418c0be03181740b805802b012808604101c80d805602400f005801e009002000c002000 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6ef6b167f6175d95a754351f50b5024db4c74bf4a649e46e46245543742340d4013ee38737435c35532a32530c3062fb2d32ce2b22ab29c27b24922721e2171ec1e71d11c31bd19519017516915e14610a0f60f00e50de0d70d10c50bf0ba0b509c08206805f05204f04a04403a03503303202902802401f01c01401200e009007005002001000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x88b0f20dbfc782ebdd538b6e0d69a0b3c666cb989b0a60abfd762e5578abd50a854f69c537a2b448831039f43de790f09da37c6d0d59a8344644bf9682c0578a11402644a48d11120e4087c8f21d2380640c41822f85d8b81622b0540a313c2684b0810e0178260470840f81b02f05c0a0130240440740d0140240380580900e00800800 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x7056e06a06796345f05da5bf5b05ad57754c54751c5195134c84a549f48047146c43c40b3e03de3b33b23ab37035f33d33732f2eb2d22cf2b72ad2aa27c24d24a21b2192111ac1911851741641131060f30ee0e00bc0b00a80a006c06b06906706405d05a05503a03703202b02902802502301601300e00a009008007004003002001 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x13c26e4c095f2223144c8790c214bff7b4f5ddb3b174eda1a8b4c676cd59932560cb856f2bd570ab93ba654a09251d2053dc7a4ec1d239e6f0d29a3312618c014a26c4b4909161bc348610bd16427c4e0981281a0338650c61842d0570a40e01a8300540a0138250460580980e0140240400700800c01001 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record029_frame002_links_0000 record029_frame002_links_0064)
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x85d8227c679873b6f36dc6be6a569e66263262e5f25ec5e158456a56554252f5294f14a846c4674374314233d63ba3a539c38b33a31530d2f32e32df2b327927423b23422b1d21ba1a919818112e11a1050fd0eb0d10c80c00b806f06e06c06a06706005d05803903603102b02902802502301601300e00a009008007004003002001 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record029_frame003_links_0000 record029_frame003_links_0064)
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x7056e06a06795da5b05af54c51c5134c84a549f48047146c4394023f93e03d53c43b33b03ab37e37035f35633d33733532f2eb2d22cf2b72ad2aa24d21b2182111ad1911861741641131060f30ee0e00bc0b00a80a006c06906405d05a05504904603a03903703503202b02902802502301601300e00a009008007004003002001 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6b669a6756615da5aa5a353b50b4fc4ba4a84a34914894844604294223ff3f83e63d33c83bf38637b35c35533c33032931d2df2cc2c72b82b22af24e21220a1fd1a11861791681551090f60e20d80c50b20ab0a409e06f06c06706105e05904d04703903803603403102b02902802502301601300e00a009008007004003002001 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x2b054fa694765247e8f70e20ac0f7bef2de43b4752ea1b9b3f676c8d8eb095fabd578ad0586abd5429551aa2940a5b4969291ca2f45c780d81ab34257ca714126a494760dd19a3205d8a814226c4b06f0da1a03105f0b613c2483a0720dc1a8320560a4140250460580980e0140240400700800c01001 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x801bc09b6cd58687b04568eadd566a9494749be4aba5391cc8d9461a0bd0327fa3f49f4cf2a6dd30996a4b3251e283122884641a1d90e9471e2fb1728b1856a29f13088ac4281f30f5877034a1970c806282f6167097048422410c07f03a412809004681a80c606002d81580aa05401900ac05002300f007403801600a004c02000e004802000e0040018008002000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record031_frame001_links_0000 record031_frame001_links_0064)
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
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6fe6a465e6516105a657556e5294fd4f14de4bd4b64634584394304253fb3d736d33c32a2f02c42b829c28a27822a2102001f71e01c21ad18f18c17016d16712911811010d0f50ed0e70e40e00d70d10c50b409409007f06b06806305b05705404f04e04d03a03703202902502301e01d01c01601300e00a009008007003002001000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x780b8d1ab0d0a607ae7d68eadd523a8413809944a5a3991b88c2457223505e8264071ff0fa679236d99acc265a9289937091846020b8ec875038e1bd0d645f62f216d0b2053e25e11588503d61dd0eb074034a1970c806282a4144096849822610c07e83c01d20da059024011a06a034818c0b605602a00c806202b011807803801600a004c01c00d004802000e005002000c002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
def record041_frame002_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x6dab471946c8b5f4ae2968eae8557aa71478a064d7a54928e92e48e23f113e89443da1a509282e3ca1cccdd468932818f8bde5c62bf14d0a5a51928593c494e4a024611f88c64501e00df063c2fd1768b744fa25c12608f03c01b70bd05a027813108b83fc1e80da059024011a06a034818c0b605602a00c806202b011807803801600a004c01c00d004802000e005002000c002000 } : Fields).get c.val)
theorem record041_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record041_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record041) (record041.maps 2)
      (record041.inverseMaps 2) record041_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record041_frame002_links_0000 record041_frame002_links_0064)
theorem record041_frame002_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 2 :=
  of_group record041 2 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record041_frame002_indices record041_frame002_graph record041_frame002_links
def record041_frame003_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0xdcfb174ee8bc8585efc5ccb4163ab254aa533de794e49b73264ac909031de2fc49824f99e439d6e2d7d9ab1b5f4b1960ab2550a513125d49e9191821a3e4784db9a834266cb695e2ae5449591e214414790eb1b632c620b4144230448680ce1842c8540a40c81882b0460780e01602804c0700d0120200380500800c00800 } : Fields).get c.val)
theorem record041_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record041_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record041) (record041.maps 3)
      (record041.inverseMaps 3) record041_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record041_frame003_links_0000 record041_frame003_links_0064)
theorem record041_frame003_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 3 :=
  of_group record041 3 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record041_frame003_indices record041_frame003_graph record041_frame003_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (Fin.cases (record041_frame002_supported hcells) (Fin.cases (record041_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x24dc878d113e1c4337f6fa1e73af748e55c7b646acd31a1b34628c3d852fe5dcb7163aad50a9892da4c4848a1042043f27c8e89c83706d4d0193306594a51422704d08c10a20c408770d31983085c8b11522804e0940ea1ac2e85c0ae1482784a0900d81883005608c1001e0380580980e01a0240400700800c00800 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x6072e11648aad545a9e94309b84a0a47d21c8c2457a230f6672336c9b14cde64e31d9738b0857028d13e49cc4b224492088d44001e98e446ae32c1770b6057626a12c092c47622d10687fc3c81d80c385d42d01580a504a823810107b025011a07c035016c0ac05502a013c08803901900a804602100f007403801600a004c02000f00700240100070018008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf0171a37a9a54d0a667303d73cb47530a91d41e9c04b7252d1ca8dc461226d11a82f4132038fca7d33db1e9cf246db335184ca5a51326d92308744171d88ea071c3671ac8bec5e42da1588a7c50427312f087442a1ea0ee875c39e1a50cb85d02dc1520a204b423e11308283f41e00e906d02c812006e034818c0b805602a00d806202b012007803801600a004801e00d004802000e005002000c002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030
