module
prelude
public import GraphInputsRow27Part00002Data
public import RawFrameSupport
public import SharedFrameGroups003Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups057Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0825.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0825.count (({ width := 11, code := 0x39171cdcdb135c682ce18caff5f0bd577ae958caa94ea8f5069f93aa6e4bc9612023b4067f8fb9f63de7a4d79a9338644c41762e859cae1572ac54ca5111220430840ff1dc3ac678ca192318610bc16a2c858899128234448860fe1982f05d0b81602784e06c0c81882f05008c1100e01a0240400700c00c01001 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0825.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0825
    Papers.RationalityTen.SharedFrameCatalogue.group0825_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x281ce79531f6344568a110e1741b82f031f93e4756ea1beb676c2d1d9530b5febe16eaca578aa552a9351c9591ca36420818f29d53a46d4ce18c2f058cb095a2a85189f9342584748c91121a42c849041e03a0630b61682bc4f09a12a1ac338590ae14c1d03304c094118160240380500800e00c01001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
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
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x113e1341681efede73a4742e61c6b756c8d3d9d3345eabb956aa052ea152da5849a901162283d2744dd9ac340640b295e2944e09a128230418810ee1d63946b8c317e2e4500750e81742e05209e138250490900c4180230440800f01d0380580980e01a0240400700600800800 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332973eb66595ab754209c94c9256d13488a3f499acc645f72d4937092a45e2138d986ac2b512308fc46222a10a07ac3ac1d00e387003681a50cf86403141830af854028813c097849c24211307b03c011a08c04581a80d205b02d01580aa05402980c8062023011007803a01c00d8068032016009803801a00c004802000e0050018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3addcf8e3d717b8a1bd8daa6c2b54da22cec65d3291922c7c6102f2d744b7e594ac015b8ac0556aa7d5249b14cea6211fc8ea46aa13508a8363c29dc8db66c832a1934c7a5db2c615c4a5a50b27c139094047e235919c8ac4521e40e046a63041778b6456426312708e045821c10b06882620f4069033818e0be02d8158080036011807801c009002000c002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
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
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x7763b25d12e5b7163825b92d9b6a93509a50d1867fb3a99aabeb5e3ae116dcb5854929794b6a1850127b124c8f2474a33118c8b7457225911e82a3c91dccd986b9352994cc4261e2bb9590aa04fe266130894c48c24211dc8de46c1d68cbc5f22d114c09ac49e22710787b83d01b50c405b028812c08584141d20e206e83541900b2057827813606e02f80c80460190050024008003 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x79078877d77276875f75274872a71e7076fb6e26cf6c666d66264363762b5ca5b85b659058657c51e50c4ff4d64cc4bc4ae48e48345741d4123b73ab39f37a3683663062fc2f22ce2bc2af28625e2532432352331ef1be1ac1a419017d16e15814b1351321221131070f70ed0dd0da0c70c10bd0b60af0a70a409e09b06e05f03202301900a009004003 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0295.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0295.count (({ width := 7, code := 0xb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0295.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0295.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0295.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0295.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0295
    Papers.RationalityTen.SharedFrameCatalogue.group0295_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
def record024_frame004_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0294.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0294.count (({ width := 7, code := 0xb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record024_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0294.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0294.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0294.localPairCheck (smallEmbedding record024) (record024.maps 4) (record024.inverseMaps 4) record024_frame004_indices (Fin.ofNat record024.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record024_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0294.localPairCheck (smallEmbedding record024) (record024.maps 4)
      (record024.inverseMaps 4) record024_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record024_frame004_links_0000 record024_frame004_links_0064)
theorem record024_frame004_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 4 :=
  of_group record024 4 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0294
    Papers.RationalityTen.SharedFrameCatalogue.group0294_facts record024_frame004_indices record024_frame004_graph record024_frame004_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (Fin.cases (record024_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0xa9f526a0d38a5d4aa905149892fa4e4838fb19a29c438850ce164297d2f35d6b9e728de9b935e682ce5802fc5e8b61622a6526a3d402744a88e112a1b432840cf1902ea560a9935262464820f81c0310600ac15028c4d89311e234448870d419c3285605c0ac1202201402402003 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0830.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0830.count (({ width := 7, code := 0x9f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0830.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0830.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0830.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0830.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0830
    Papers.RationalityTen.SharedFrameCatalogue.group0830_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0433.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0433.count (({ width := 7, code := 0x9f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0433.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0433.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0433.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0433.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0433
    Papers.RationalityTen.SharedFrameCatalogue.group0433_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x91b17226c047f8f2dd2b9d6a6d259b30f5eebc9702dc564aad4da924da9992824948c8b90aa033c470cd59932fc5e0b81492824988b9091b0314600b50f81e43105e0ac14c2704d09812c2303f0680c81702604a08c0f01d03804c0900f01c0240400700600800800 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x5d19cb22e3645885d01df2332612bc1552964dc88d071ef3665509f12222442c820ec19e2b0468820fa1e83c86f0d2198328600ba1642c0540a6148200360640c4138250460880f01d0380480700d0140240400700600800800 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 65 :=
  interval_of_check _ 64 1 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 65 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x80ef59c72df5629d53625d47a8c8fa1d834266ca79462664547f8f91e8390688c817e2a85288a1001e43b0750d4190308600ac1482884d09812c2503c0680c01782d04c0941102103a0700d8190240380680b0120200380400600800800 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x5fb2fa9780bb45c52dd9604af55512a55486a3c4c725f5252918482a3f91467e73eb9f24f1c77d3a11ca8d7e6b032f193cbfe5f92b29560a2050327a13bc94e41a2048f3c77a3ad1cf0df06da35d1a68cf863830d17e8bd85c02cc15089a04b424c11708804241fa0db068c3221760b5858028a13a09784982340e904502240aa054029014403a01c00d806803001700b005002601000780300100070018008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xaa8aa5a95a90a81a64a1fa139d59c696e95f8e68d688887884d8397ec6fe6f16ee6e06db6cb6ab66c65f62961b5d65ca55f5525105034e34d54923f03e43c63bc3ad3a438637936a35734d32f31d2f82e82c52b529f2752642542342242141f21c31b41a718617716b1441341251151030dc08a08905505405205101d01c01b01a01801701601401301000f00c008007003002001000 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0xbc577aeadd2b93706d0d9aaf15d2a5d46a093de67cc796f2c647c1982503a024007ecfb5e6bc5746e81bbb72666ca5822fc5e0bb56626f4d294125a444828b110a1b42a844fd9f43ca784e91c937a680cd1903025e0ba1622824c89311521a418790ed1c836c680af0f41e42784e09812c0e81c0360680c01702c0500981001e0300400700600800800 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
def record044_frame004_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0171.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0171.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record044_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0171.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0171.localPairCheck (smallEmbedding record044) (record044.maps 4) (record044.inverseMaps 4) record044_frame004_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0171.localPairCheck (smallEmbedding record044) (record044.maps 4) (record044.inverseMaps 4) record044_frame004_indices (Fin.ofNat record044.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record044_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0171.localPairCheck (smallEmbedding record044) (record044.maps 4)
      (record044.inverseMaps 4) record044_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record044_frame004_links_0000 record044_frame004_links_0064)
theorem record044_frame004_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 4 :=
  of_group record044 4 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0171
    Papers.RationalityTen.SharedFrameCatalogue.group0171_facts record044_frame004_indices record044_frame004_graph record044_frame004_links
def record044_frame005_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0040.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record044_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0040.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0040.localPairCheck (smallEmbedding record044) (record044.maps 5) (record044.inverseMaps 5) record044_frame005_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0040.localPairCheck (smallEmbedding record044) (record044.maps 5) (record044.inverseMaps 5) record044_frame005_indices (Fin.ofNat record044.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record044_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0040.localPairCheck (smallEmbedding record044) (record044.maps 5)
      (record044.inverseMaps 5) record044_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record044_frame005_links_0000 record044_frame005_links_0064)
theorem record044_frame005_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 5 :=
  of_group record044 5 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0040
    Papers.RationalityTen.SharedFrameCatalogue.group0040_facts record044_frame005_indices record044_frame005_graph record044_frame005_links
def record044_frame006_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x659b2898dac5860faf7d680b2b5632ac9474a264b6a56d1f88e9461a2bd0a87953bf9db8e727243759aacc185f72c915f8a0c4f221c909c7903b51c78dec6402611298900470231115886c42820e10388043e21ea0ee075438e1c00d9067c32e1900c185ec2e81670a5050c27812e093848422410b08283f81ec0e204502240aa054029014403a01c00d806803001700b005002601000780300100070018008002000 } : Fields).get c.val)
theorem record044_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 6) (record044.inverseMaps 6) record044_frame006_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 6) (record044.inverseMaps 6) record044_frame006_indices (Fin.ofNat record044.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record044_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record044) (record044.maps 6)
      (record044.inverseMaps 6) record044_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record044_frame006_links_0000 record044_frame006_links_0064)
theorem record044_frame006_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 6 :=
  of_group record044 6 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record044_frame006_indices record044_frame006_graph record044_frame006_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (Fin.cases (record044_frame004_supported hcells) (Fin.cases (record044_frame005_supported hcells) (Fin.cases (record044_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0847.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0847.count (({ width := 11, code := 0x19e723643c79862f15b1b495dea6d48a6b4be92d049d931e52c9d8db18a21c3282f051eebd97acf49bb3716c8d7199afc5c8b6d672bf56aa893ea6b4ba9512822c3e8798f11d93a0718cb9922f45c4b095b2a44f09912622a418768e41aa31c5e0a41381f03d0790be1501c0330620880e81c02e0580a00f01a00c01001 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0847.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0847
    Papers.RationalityTen.SharedFrameCatalogue.group0847_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a8ace362c2dd1682b0453928993b899f4c023f115683f3fd1fa4f8a7b63d39e54e486403069740a7c4f225411ac8983c81bb8c2c58c2b51488a084e626112c092c49423c117889c42220a10107d83b41cb0db06a83421990c9862c2f21770b785a02b614d0a304f8270125091045421210607f83c81d40df06c034811408603981b00c005c02b01540a805202700ec068028012007803a01c } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
def record049_frame002_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x24547a8d911e20437822ff1f43df7b2ed1cf37b6ced89abb5169ad199a3045f6bc160aa951ea1d4025346c851001fb3e27b0f41e33c0750e99cc3866f8d79a5338644b99642a0524a293f2744cc9112122e440808f51dc3a0720da1b03385f0bb1662a05109912a2443c0770d018c2d8580a41442804e0980e4198280480780e81c } : Fields).get c.val)
theorem record049_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record049_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (smallEmbedding record049) (record049.maps 2)
      (record049.inverseMaps 2) record049_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record049_frame002_links_0000 record049_frame002_links_0064)
theorem record049_frame002_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 2 :=
  of_group record049 2 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record049_frame002_indices record049_frame002_graph record049_frame002_links
def record049_frame003_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x24dc888ef14a25c41837009f9bec7c2ed5cb3736a8d299fb38668cb58fafa5e0b995b29d514a113e25447a860fd1f23cc780ed9d53a2720e39c03726ccd299e330640bb1692b6544a514427c4d49212323644c840fd1ee3b8740d81ae3345f8bd1682a451899126240350690ba15c2804c08c114220420820d4178270480780e81c } : Fields).get c.val)
theorem record049_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record049_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record049) (record049.maps 3)
      (record049.inverseMaps 3) record049_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record049_frame003_links_0000 record049_frame003_links_0064)
theorem record049_frame003_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 3 :=
  of_group record049 3 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record049_frame003_indices record049_frame003_graph record049_frame003_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (Fin.cases (record049_frame002_supported hcells) (Fin.cases (record049_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x1702d4589ae556e94d049d537a65cca9892d258ca292b2263dc5a847066033f87d2f61e4bba758ce990b1360ac117faf25e0b255d2a14de94d25a374568890ba1040880cfe1f03da72cdf1a72f6590ae94c2824e89912c240450889032043fc7b8ee1da360670cc1882c85489c12c234428840e41c41502804a0900f01d03805c0981001e02404007 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
def record050_frame002_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x392da50ca56292f99586a404f6a7353809bf4d8a6913389864bfa5dd2d694f495a49122c90848023cd1d88e446e9ab8cb063430b1834bd05cc2d8953ca524df23b10c48464011f80f847a23c51d38e786f235d1a10b8057427010387083681920c085c82c41580a8852428613909a04b824c11d08c04242060fe07b83a81c80dc06b034015a0a90450218058028012809003c01d00e005c0260100078024010007 } : Fields).get c.val)
theorem record050_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record050) (record050.maps 2) (record050.inverseMaps 2) record050_frame002_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record050) (record050.maps 2) (record050.inverseMaps 2) record050_frame002_indices (Fin.ofNat record050.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record050_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record050) (record050.maps 2)
      (record050.inverseMaps 2) record050_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record050_frame002_links_0000 record050_frame002_links_0064)
theorem record050_frame002_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 2 :=
  of_group record050 2 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record050_frame002_indices record050_frame002_graph record050_frame002_links
def record050_frame003_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0709.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0709.count (({ width := 9, code := 0x697439dcd65f278ac1e06f579ba5bed761aed66a94aa1cfe733297caa51269244e190a81c09fcf97b3a9ccdf6bb3d9ccc65b2992c861b097cba5bab152a24e251269147a35168942a04fc783b9d0e06b35190c4612f164ac522813c9a4c231144e24108803c1d0e05c2610078241007 } : Fields).get c.val)
theorem record050_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0709.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record050) (record050.maps 3) (record050.inverseMaps 3) record050_frame003_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record050) (record050.maps 3) (record050.inverseMaps 3) record050_frame003_indices (Fin.ofNat record050.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record050_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0709.localPairCheck (smallEmbedding record050) (record050.maps 3)
      (record050.inverseMaps 3) record050_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record050_frame003_links_0000 record050_frame003_links_0064)
theorem record050_frame003_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 3 :=
  of_group record050 3 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0709
    Papers.RationalityTen.SharedFrameCatalogue.group0709_facts record050_frame003_indices record050_frame003_graph record050_frame003_links
def record050_frame004_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0679.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0679.count (({ width := 8, code := 0xd7d6d5d4d2d1d0cfcecbcac7c4c2bebcbab7b5b3b1afadaba7a5a3a19c9b9a979693908e888786848281807f7e7d7c7a797674726a6968656261605f5e5d5c595653504f4d4a48474342413f3c3a3837363534302f1e1d1a19171615100e0b0a080706 } : Fields).get c.val)
theorem record050_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0679.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0679.localPairCheck (smallEmbedding record050) (record050.maps 4) (record050.inverseMaps 4) record050_frame004_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0679.localPairCheck (smallEmbedding record050) (record050.maps 4) (record050.inverseMaps 4) record050_frame004_indices (Fin.ofNat record050.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record050_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0679.localPairCheck (smallEmbedding record050) (record050.maps 4)
      (record050.inverseMaps 4) record050_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record050_frame004_links_0000 record050_frame004_links_0064)
theorem record050_frame004_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 4 :=
  of_group record050 4 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0679
    Papers.RationalityTen.SharedFrameCatalogue.group0679_facts record050_frame004_indices record050_frame004_graph record050_frame004_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (Fin.cases (record050_frame002_supported hcells) (Fin.cases (record050_frame003_supported hcells) (Fin.cases (record050_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xa794367549d8ab11e1f4387fef91ddbae738e25c2b7b6e6da1a7b3d5d8ba16eac35089cd36a26428815019f83da780e41b93465f0ad15129c524a293d26e4a8909112023f87d0eb1c6368620ba1682c4570aa14e2904407d0d819c2f8570aa1001b83604a08c100160260380680a01000c00800 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
def record056_frame002_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0496.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0496.count (({ width := 9, code := 0xdeee769a7ce6532590c1de2e771b658abf5babd468938984b6532089c3a1b017dbd9e6ee74b91b0cc61add5ca952a893e9c4d259248b41200fa773a1c0ca5e2d15cac53281348c411f0ec6e32180a44e260e870341208030160a0400c0200 } : Fields).get c.val)
theorem record056_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record056) (record056.maps 2) (record056.inverseMaps 2) record056_frame002_indices (Fin.ofNat record056.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record056_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record056) (record056.maps 2)
      (record056.inverseMaps 2) record056_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record056_frame002_links_0000 record056_frame002_links_0064)
theorem record056_frame002_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) : Supported record056 2 :=
  of_group record056 2 (smallEmbedding record056) (small_cells_exact record056 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0496
    Papers.RationalityTen.SharedFrameCatalogue.group0496_facts record056_frame002_indices record056_frame002_graph record056_frame002_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (Fin.cases (record056_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x53ca1b39661c9e88f0fa1c422825029ff3e47b4f51e13bb75ce6dc636e6d2d55a833e5d0b7561a9450c9cd36a4144c859049df38e6e8d197c2b454ca293d26e4a89090e216414810fe1f43ac718d71a633c620bb1702cc530a30fa1b03385f0ae0dc1b033052094118160260380500800e00c01001 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (smallEmbedding record057) (small_cells_exact record057 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x29e50d9cb30e4f44b814ff9f43c2736da5a833e660c5972ad959cb2161ab053ea51432704d29752b24146e8ad1321640c7a0ef9d038e6e8d217c2b454c9f1362544848710b20a4087c8ec1c635c698cf1882ec5b8b314c28c3385709a0f41e03706c0cc1782d052094118160260380500800e00c01001 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (smallEmbedding record058) (small_cells_exact record058 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19fcca2622a8d93ae957473230d0147fa3e29e98f2a76e38894089464231d90e3c5ac2c614889c84c225312608e046222b10a08383f21f30f587703901900b6859c2b014a097048422410c07f03bc1d20e204481c00d8063030016c0aa05402880e006802b014008c03a01c00d806803001600a004c02000e005802000e0040018008002000 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x83b8287f47e37b57ab72e6ea69b65d64d62f5d05a258757656855a54b4f54ec4e24a049144c43e4303ee3e83cc3c437f35d34f3213103043012f32e51e71de1d41a719418f1721671561271141070f20e00d60c80c40c10b009809107c05504404203802902001d01600f00e00d00a008003002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x2e56eb4da2cf65a9d3e9746a1cf6491d8b45629127b3c9dce973381bedd6c35d9cc25eae164ae56aa94ea3502793698492451e8c44a19047c3d9dce06f36198c25e2d960a853269288c45221047e3e1e0e86630160a8522612088401e } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
def record064_frame002_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1680ac651aa7fd3de9d74159ff8fd87ba3d51e40c18592280932c9764a317b8b2857028613b09704b025112208ec4221db0e606fc3621a30d0066832418b0c205f82ec16f0b205882b61530a6851427412c094848822010d08303ec1d80e506f035c18009d04481e80ec07403901a40c606102e81680a204201f00f007403101580a404a022 } : Fields).get c.val)
theorem record064_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 2) (record064.inverseMaps 2) record064_frame002_indices (Fin.ofNat record064.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record064_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 2)
      (record064.inverseMaps 2) record064_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record064_frame002_links_0000 record064_frame002_links_0064)
theorem record064_frame002_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 2 :=
  of_group record064 2 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record064_frame002_indices record064_frame002_graph record064_frame002_links
def record064_frame003_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6265f25b459859358b4c84aa49d47e47245f3ec3b837a35e35935128e26d26224123722522421c21120b1e31ac19b18d17c16f16d16816115915014c14413b12f12e12a12411e11810f1051030fb0eb0ea0e30d70cc0c40bc0b60aa09708507807407207006706105f05b05804f04203e03c03a03102b029025022 } : Fields).get c.val)
theorem record064_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record064) (record064.maps 3) (record064.inverseMaps 3) record064_frame003_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record064) (record064.maps 3) (record064.inverseMaps 3) record064_frame003_indices (Fin.ofNat record064.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record064_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record064) (record064.maps 3)
      (record064.inverseMaps 3) record064_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record064_frame003_links_0000 record064_frame003_links_0064)
theorem record064_frame003_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 3 :=
  of_group record064 3 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record064_frame003_indices record064_frame003_graph record064_frame003_links
def record064_frame004_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0477.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0477.count (({ width := 9, code := 0x2271087432170a7c3c5dce772389b0d46833998cb5e2dd68af562a950a6512853c994b2491e8c45a250c823f1f0f275381bcda6a34194c45f2f168a8532792488401e0e06831168b0562a148a04a2411888401f0f07438190c05c2c15 } : Fields).get c.val)
theorem record064_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0477.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0477.localPairCheck (smallEmbedding record064) (record064.maps 4) (record064.inverseMaps 4) record064_frame004_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0477.localPairCheck (smallEmbedding record064) (record064.maps 4) (record064.inverseMaps 4) record064_frame004_indices (Fin.ofNat record064.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record064_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0477.localPairCheck (smallEmbedding record064) (record064.maps 4)
      (record064.inverseMaps 4) record064_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record064_frame004_links_0000 record064_frame004_links_0064)
theorem record064_frame004_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 4 :=
  of_group record064 4 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0477
    Papers.RationalityTen.SharedFrameCatalogue.group0477_facts record064_frame004_indices record064_frame004_graph record064_frame004_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (Fin.cases (record064_frame002_supported hcells) (Fin.cases (record064_frame003_supported hcells) (Fin.cases (record064_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2e7d718a60511a7bd2b689a4192034ff07c83d319accb052c27792ec84e36617f0b64588294139094c49823110a07e43d61d60e807203821bb0d206602f81750b6857c29414409e04bc24e12108983a01c408c04481bc0d205b02d01600aa05402880dc062023011008003a01c00d8068030016009803801a00b005002000e0050018008002000 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
def record068_frame002_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x11562840a7f2fa9e138f6e6d99b0b4d682bb173a945049c920a0c3da784ed9c937a6c4d51942f859cad14e29250c9f93b25448c8810b20a3f0768e91c6364698cf18c2b85507e0fa19c310570ac1502885009a0d8180230440800e81c0360680c0160260380680b0140200380500600800800 } : Fields).get c.val)
theorem record068_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record068_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record068) (record068.maps 2)
      (record068.inverseMaps 2) record068_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record068_frame002_links_0000 record068_frame002_links_0064)
theorem record068_frame002_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 2 :=
  of_group record068 2 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record068_frame002_indices record068_frame002_graph record068_frame002_links
def record068_frame003_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x310c32e9b7ad5b02909f2739c6619622a899f779ddc729aa6598d6297a5c56558953509324a11f4651543d0c3fcf6394df370d130cc02ecb42c0a828089210621845113446114431003f0f82f0ac23088200741c06c1a0601604c0e0340b0280801c0500c0200400 } : Fields).get c.val)
theorem record068_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record068_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record068) (record068.maps 3)
      (record068.inverseMaps 3) record068_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record068_frame003_links_0000 record068_frame003_links_0064)
theorem record068_frame003_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 3 :=
  of_group record068 3 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record068_frame003_indices record068_frame003_graph record068_frame003_links
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
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x724b915c80e337143875c08df96f7369daf6d526a5b511a4ccec66e3315906c7362e2f7d752b855b8ada5684b0956e2b21552a7c53424111fe8f7427a11106480f4021fc8f4a7593989c94e2e6e735b9a5cce265631b18409ea4ee27511ac8b645221e10b08462ff17b8bc04bc24e11e08904282020b905a42be14109c04b824c10407b03a01ba0d303081740b0028012007c02400e0048008002000 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
def record070_frame002_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x7603ad5d54e8573d39bdcace517263851bcadb46d4b649a98d1b68833e5972cb2655314181cbeb5dc2e7d6d8b4958b2bf55b8ac856024ad24090c43c21b50b284441fa0dcfe67b13c39d84e6870736e9adcd146763349968a3a50827f12408f6471231116c8ae3021780b6c4c224f11d08b044821c0bb059c2ac13709704902300fa078839c1b60d203081740b0028012007c02400e0048008002000 } : Fields).get c.val)
theorem record070_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record070) (record070.maps 2) (record070.inverseMaps 2) record070_frame002_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record070) (record070.maps 2) (record070.inverseMaps 2) record070_frame002_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record070) (record070.maps 2)
      (record070.inverseMaps 2) record070_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame002_links_0000 record070_frame002_links_0064)
theorem record070_frame002_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 2 :=
  of_group record070 2 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record070_frame002_indices record070_frame002_graph record070_frame002_links
def record070_frame003_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x809005ff3f77e8fc5f63e97ccf81ee3d77aaf41e23bf77aee1d5ba9748e59c7b886fcde5b936b6c2d71aab4b68cbc9782ea57caf15b2ac554a914d28a4f89d5362634aa93922a3e46e8b8f41e33c26f0db9b535e6a8d41462824ec851051fe3e47a0ee1863045d8ac1542904f092120228420810a613c250260440740900e01200800800 } : Fields).get c.val)
theorem record070_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record070) (record070.maps 3) (record070.inverseMaps 3) record070_frame003_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record070) (record070.maps 3) (record070.inverseMaps 3) record070_frame003_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record070) (record070.maps 3)
      (record070.inverseMaps 3) record070_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame003_links_0000 record070_frame003_links_0064)
theorem record070_frame003_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 3 :=
  of_group record070 3 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record070_frame003_indices record070_frame003_graph record070_frame003_links
def record070_frame004_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1060.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1060.count (({ width := 10, code := 0x96257956529464f9324b9264590e408fa3c8d2318be2d8922288216852128320780e017edf67c9ec79dbe6f5b8685a066d936498d6157d5d9725ad655795a54d4e529434791a46504400ff3e4f53d0c3300bb28ca026c972508f1e8781dc6e1b06b1a46117c5e1705b118420f4240801b0480e0240200400 } : Fields).get c.val)
theorem record070_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record070) (record070.maps 4) (record070.inverseMaps 4) record070_frame004_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record070) (record070.maps 4) (record070.inverseMaps 4) record070_frame004_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record070) (record070.maps 4)
      (record070.inverseMaps 4) record070_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame004_links_0000 record070_frame004_links_0064)
theorem record070_frame004_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 4 :=
  of_group record070 4 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1060
    Papers.RationalityTen.SharedFrameCatalogue.group1060_facts record070_frame004_indices record070_frame004_graph record070_frame004_links
def record070_frame005_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xac757eaed57aab546a754ca954ae9251ba2f4427fcf79e73ba6d4d799d26a4948c8fb1e236c658b91562543e86aeddda3ac6f0dd9b73626bcd61a5b3f660c918eb1560cc0179aeb5bcb452da544a086506a083f47ccf817c2e45989f9382644a09111b1ce3886e0cf19c324628b61642c4560a60ba1642a0270460780900e01200800800 } : Fields).get c.val)
theorem record070_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record070) (record070.maps 5) (record070.inverseMaps 5) record070_frame005_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record070) (record070.maps 5) (record070.inverseMaps 5) record070_frame005_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record070) (record070.maps 5)
      (record070.inverseMaps 5) record070_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame005_links_0000 record070_frame005_links_0064)
theorem record070_frame005_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 5 :=
  of_group record070 5 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record070_frame005_indices record070_frame005_graph record070_frame005_links
def record070_frame006_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6fe6fc6fa6f46f16f06eb6e96e76ce6c46b86b26ac69968668368066c66665f60c5fd5f45e65dc5c95c05b05a559457d5734a94a449945344c4404284234184033f43e83de3cf3bf3b33a83953853753622a529529124e23e2382232152101a519e19416715f15514e14613d1040fc0f80e80e00dd0d90ca0c20bd0b80b205b05705202802401f01200e009002001000 } : Fields).get c.val)
theorem record070_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record070) (record070.maps 6) (record070.inverseMaps 6) record070_frame006_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record070) (record070.maps 6) (record070.inverseMaps 6) record070_frame006_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record070) (record070.maps 6)
      (record070.inverseMaps 6) record070_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame006_links_0000 record070_frame006_links_0064)
theorem record070_frame006_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 6 :=
  of_group record070 6 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record070_frame006_indices record070_frame006_graph record070_frame006_links
def record070_frame007_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0846.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0846.count (({ width := 11, code := 0x90b20e4147f8f91ee3bc748e717e2d4558a513e21c3e8790e616c2c851009fe3f67e0fb1f2bdd7acf41e23bb766cfd9eb38622c3582af85e8ba96d2d65a0b2d62abf56aabd4f298526a210da154267b0f09dc3a4728e295f2b65549892824045c891081ac340660bf1762d8588a613c2644a8900ac1482682804807c0900e01200800800 } : Fields).get c.val)
theorem record070_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record070) (record070.maps 7) (record070.inverseMaps 7) record070_frame007_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record070) (record070.maps 7) (record070.inverseMaps 7) record070_frame007_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0846.localPairCheck (smallEmbedding record070) (record070.maps 7)
      (record070.inverseMaps 7) record070_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame007_links_0000 record070_frame007_links_0064)
theorem record070_frame007_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 7 :=
  of_group record070 7 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0846
    Papers.RationalityTen.SharedFrameCatalogue.group0846_facts record070_frame007_indices record070_frame007_graph record070_frame007_links
def record070_frame008_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0836.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0836.count (({ width := 7, code := 0xbf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record070_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0836.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0836.localPairCheck (smallEmbedding record070) (record070.maps 8) (record070.inverseMaps 8) record070_frame008_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0836.localPairCheck (smallEmbedding record070) (record070.maps 8) (record070.inverseMaps 8) record070_frame008_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0836.localPairCheck (smallEmbedding record070) (record070.maps 8)
      (record070.inverseMaps 8) record070_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame008_links_0000 record070_frame008_links_0064)
theorem record070_frame008_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 8 :=
  of_group record070 8 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0836
    Papers.RationalityTen.SharedFrameCatalogue.group0836_facts record070_frame008_indices record070_frame008_graph record070_frame008_links
def record070_frame009_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0782.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0782.count (({ width := 9, code := 0x91486411f8f476391b8d4622f158a44e251087c3a1b0b84bf9fafb7d3e5f0f67abd1e6ee7635dacd463b1988c1602f976ba5c2dd6cb559ac962af55a9d2a9248a1504813f1f0f66c3519cb85a2b954a65122108803e1e8f0763a1c8e06e36160a84a1d0d054220d040080200 } : Fields).get c.val)
theorem record070_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0782.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record070) (record070.maps 9) (record070.inverseMaps 9) record070_frame009_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record070) (record070.maps 9) (record070.inverseMaps 9) record070_frame009_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0782.localPairCheck (smallEmbedding record070) (record070.maps 9)
      (record070.inverseMaps 9) record070_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame009_links_0000 record070_frame009_links_0064)
theorem record070_frame009_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 9 :=
  of_group record070 9 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0782
    Papers.RationalityTen.SharedFrameCatalogue.group0782_facts record070_frame009_indices record070_frame009_graph record070_frame009_links
def record070_frame010_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0771.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0771.count (({ width := 7, code := 0xbf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record070_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0771.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0771.localPairCheck (smallEmbedding record070) (record070.maps 10) (record070.inverseMaps 10) record070_frame010_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0771.localPairCheck (smallEmbedding record070) (record070.maps 10) (record070.inverseMaps 10) record070_frame010_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0771.localPairCheck (smallEmbedding record070) (record070.maps 10)
      (record070.inverseMaps 10) record070_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame010_links_0000 record070_frame010_links_0064)
theorem record070_frame010_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 10 :=
  of_group record070 10 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0771
    Papers.RationalityTen.SharedFrameCatalogue.group0771_facts record070_frame010_indices record070_frame010_graph record070_frame010_links
def record070_frame011_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0767.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0767.count (({ width := 7, code := 0xbf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record070_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0767.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0767.localPairCheck (smallEmbedding record070) (record070.maps 11) (record070.inverseMaps 11) record070_frame011_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0767.localPairCheck (smallEmbedding record070) (record070.maps 11) (record070.inverseMaps 11) record070_frame011_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0767.localPairCheck (smallEmbedding record070) (record070.maps 11)
      (record070.inverseMaps 11) record070_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame011_links_0000 record070_frame011_links_0064)
theorem record070_frame011_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 11 :=
  of_group record070 11 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0767
    Papers.RationalityTen.SharedFrameCatalogue.group0767_facts record070_frame011_indices record070_frame011_graph record070_frame011_links
def record070_frame012_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0756.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0756.count (({ width := 9, code := 0xa4d228f46a2d128742a0cfe7d3c9dcea73379b4d669329847a3b1b8d46631168ac52270d85bc1deed7037dbad96c359a6d26833d9ccd65b2992c7612f54ca351259269247231167c3d1dcd86a33990c460299449e4d2612c94492411c8c45198c4581f0e05c240e048080200 } : Fields).get c.val)
theorem record070_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record070) (record070.maps 12) (record070.inverseMaps 12) record070_frame012_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record070) (record070.maps 12) (record070.inverseMaps 12) record070_frame012_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0756.localPairCheck (smallEmbedding record070) (record070.maps 12)
      (record070.inverseMaps 12) record070_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame012_links_0000 record070_frame012_links_0064)
theorem record070_frame012_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 12 :=
  of_group record070 12 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0756
    Papers.RationalityTen.SharedFrameCatalogue.group0756_facts record070_frame012_indices record070_frame012_graph record070_frame012_links
def record070_frame013_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0748.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0748.count (({ width := 7, code := 0xbf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record070_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0748.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0748.localPairCheck (smallEmbedding record070) (record070.maps 13) (record070.inverseMaps 13) record070_frame013_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0748.localPairCheck (smallEmbedding record070) (record070.maps 13) (record070.inverseMaps 13) record070_frame013_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0748.localPairCheck (smallEmbedding record070) (record070.maps 13)
      (record070.inverseMaps 13) record070_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame013_links_0000 record070_frame013_links_0064)
theorem record070_frame013_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 13 :=
  of_group record070 13 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0748
    Papers.RationalityTen.SharedFrameCatalogue.group0748_facts record070_frame013_indices record070_frame013_graph record070_frame013_links
def record070_frame014_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0734.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0734.count (({ width := 7, code := 0xbf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record070_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0734.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0734.localPairCheck (smallEmbedding record070) (record070.maps 14) (record070.inverseMaps 14) record070_frame014_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0734.localPairCheck (smallEmbedding record070) (record070.maps 14) (record070.inverseMaps 14) record070_frame014_indices (Fin.ofNat record070.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record070_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0734.localPairCheck (smallEmbedding record070) (record070.maps 14)
      (record070.inverseMaps 14) record070_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record070_frame014_links_0000 record070_frame014_links_0064)
theorem record070_frame014_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 14 :=
  of_group record070 14 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0734
    Papers.RationalityTen.SharedFrameCatalogue.group0734_facts record070_frame014_indices record070_frame014_graph record070_frame014_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (Fin.cases (record070_frame002_supported hcells) (Fin.cases (record070_frame003_supported hcells) (Fin.cases (record070_frame004_supported hcells) (Fin.cases (record070_frame005_supported hcells) (Fin.cases (record070_frame006_supported hcells) (Fin.cases (record070_frame007_supported hcells) (Fin.cases (record070_frame008_supported hcells) (Fin.cases (record070_frame009_supported hcells) (Fin.cases (record070_frame010_supported hcells) (Fin.cases (record070_frame011_supported hcells) (Fin.cases (record070_frame012_supported hcells) (Fin.cases (record070_frame013_supported hcells) (Fin.cases (record070_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x6fe6fc6fa6f36eb6c46c16bf69968166c66665f60c5fd5f45e65dc5bb5af5945044cd45144d43f4284234033f43e83de3cf3ae3a73852f32bb24f23c2372232151a519e19416315b15614e1461081000f70e80e00ca0c20be0b70b20a50a406a05705505203702402301f01200e008003001000 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (smallEmbedding record071) (small_cells_exact record071 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (Fin.cases (record071_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0496.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0496.count (({ width := 9, code := 0xdeee7419ecee4b218eb9dcae362afd6ea349a2502673298cb6411c8741202f679bb9c8dc6c3518ab957aad48a04fa71349246a2d0c803e9dce06932988b4572b14ca04d230f87637190c04e260e870341007834180a0400c0200 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (smallEmbedding record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0496
    Papers.RationalityTen.SharedFrameCatalogue.group0496_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3289920c7e62c2f7d6f2af24ee25651868ab4079f9cf8a7b63d39db8eb874a3921aacc8a5be254109471e37716d8acc522282139894c49824511c08c445622310e885841c20710087703aa1c80d986b432c1880ba05b82b014a09e84b822410507f03bc1d20db03601800be05c02b0150068028013809003c01c00d8068030014009804802000f005802400e0040018008002000 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
def record076_frame002_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x65264e64b64061e6095e15975585135084bb4a849949449047b47346e46142e40f3d43833433042fc2b52a629a29729428827f27926925f25524923f23722b22421e1ed1e71d41bf1b919618917517115814613711f0f60e70e00cc0c40b606a05e05d05a05405203402802702401e01c01b01a01801401301201000f00b009007004003002001000 } : Fields).get c.val)
theorem record076_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record076_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record076) (record076.maps 2)
      (record076.inverseMaps 2) record076_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record076_frame002_links_0000 record076_frame002_links_0064)
theorem record076_frame002_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 2 :=
  of_group record076 2 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record076_frame002_indices record076_frame002_graph record076_frame002_links
def record076_frame003_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x121a4147e8ef16623c237b8ee5c7b876acd199c33465cc758c31461abbd6e2b84e493d11a183d4770e71c83866dcd91b035268ccf199328644c5984300580ad14e27c4e8919172144107c8ef1cc378630be1742b8558a20c015c2b05309a12c1882804e0900f01c0360680c0140260480800f0160240380400600800800 } : Fields).get c.val)
theorem record076_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record076_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record076) (record076.maps 3)
      (record076.inverseMaps 3) record076_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record076_frame003_links_0000 record076_frame003_links_0064)
theorem record076_frame003_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) : Supported record076 3 :=
  of_group record076 3 (smallEmbedding record076) (small_cells_exact record076 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record076_frame003_indices record076_frame003_graph record076_frame003_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (Fin.cases (record076_frame002_supported hcells) (Fin.cases (record076_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce0665328988ab6751aa88d4209dc45f22b11348303f49edcedc71131994049de4dc2540e286f036617e0ad4506258128892847623411608443f81f40ed87643a21c40db069c33418e0c585f82ec16b0b2056c29a13e098849424411508684081f60e606f83601a409204682300f406f03501a40c005b02d015c0ac05502a010806e03201880a004602200f807803a01c } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
def record077_frame002_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x66666265463d60c5a65a259e58651050b5074c949e47f45f4494143a93a63a238f32e32c32a2ec2ce2b62a629928c27e27226624c23222620d20b2071f31d71bc1aa19619418317716816115113c1271191091080f90f00e30de0b90ad0a509d08107f07e07206906406305a05505405105004f04e04203703203102802302201f01e01d01c } : Fields).get c.val)
theorem record077_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record077) (record077.maps 2) (record077.inverseMaps 2) record077_frame002_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record077) (record077.maps 2) (record077.inverseMaps 2) record077_frame002_indices (Fin.ofNat record077.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record077_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record077) (record077.maps 2)
      (record077.inverseMaps 2) record077_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record077_frame002_links_0000 record077_frame002_links_0064)
theorem record077_frame002_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 2 :=
  of_group record077 2 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record077_frame002_indices record077_frame002_graph record077_frame002_links
def record077_frame003_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x80e8087f87dd7756c56bb6af68a5c25b55a556e54c5345154fa4903c83bb3ab3872d72cd2c128b26925123e23823122221b2141fc1e81e01c71c51be1b21a419218417517316515d14f1481401321201121031010f30eb0dd0d60cb0c70c30bf09208d08c07a06f06a06906005b05a05705605505404203703203102802302201f01e01d01c } : Fields).get c.val)
theorem record077_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record077) (record077.maps 3) (record077.inverseMaps 3) record077_frame003_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record077) (record077.maps 3) (record077.inverseMaps 3) record077_frame003_indices (Fin.ofNat record077.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record077_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record077) (record077.maps 3)
      (record077.inverseMaps 3) record077_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record077_frame003_links_0000 record077_frame003_links_0064)
theorem record077_frame003_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 3 :=
  of_group record077 3 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record077_frame003_indices record077_frame003_graph record077_frame003_links
def record077_frame004_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x339cd332cb309b7edeb66d3a6e96a427b9aa5d92e4588deb79de0769b06b5aa655835d5675916156d56545414d53048d2146d13429023e0f03bce7388d834ccf31cbe2d8ac2aca22749423c862047d1e46518c62160511384d1284611442104400fc350bc2c0ac2808c2207c1e0741c } : Fields).get c.val)
theorem record077_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record077) (record077.maps 4) (record077.inverseMaps 4) record077_frame004_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record077) (record077.maps 4) (record077.inverseMaps 4) record077_frame004_indices (Fin.ofNat record077.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record077_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record077) (record077.maps 4)
      (record077.inverseMaps 4) record077_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record077_frame004_links_0000 record077_frame004_links_0064)
theorem record077_frame004_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) : Supported record077 4 :=
  of_group record077 4 (smallEmbedding record077) (small_cells_exact record077 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record077_frame004_indices record077_frame004_graph record077_frame004_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (Fin.cases (record077_frame002_supported hcells) (Fin.cases (record077_frame003_supported hcells) (Fin.cases (record077_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
def record081_frame001_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6c966c65463d60b5fb5ef5d15be5a85615285144cc4b84a34a148c48246f46e45f4494163ff3ca39d39538f37033d32f31d3052ee2d12d02b82ac2ab29d29028927726c26424522c2242101e61ca1bb1b319719318c17616916614412f12611210a1070f20ef0e40e10c30b70ab0a308107f06e06d06906402902802502301b01a01801401301000e } : Fields).get c.val)
theorem record081_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record081_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record081) (record081.maps 1)
      (record081.inverseMaps 1) record081_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record081_frame001_links_0000 record081_frame001_links_0064)
theorem record081_frame001_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 1 :=
  of_group record081 1 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record081_frame001_indices record081_frame001_graph record081_frame001_links
def record081_frame002_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0491.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0491.count (({ width := 9, code := 0x6bf4ba2d06733599cb6572587c05fadd68afd7ab355a652e8d459f4e2612792c8e411f8f45e250e80c01f2f077ba5cee470379b8d86b3519ec460af972af562a1429a4ba2d08813e1d8e66f36194c4572993c9642208f4783a1c87c3c1d0e0542813088401c0c } : Fields).get c.val)
theorem record081_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (smallEmbedding record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (smallEmbedding record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record081_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (smallEmbedding record081) (record081.maps 2)
      (record081.inverseMaps 2) record081_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record081_frame002_links_0000 record081_frame002_links_0064)
theorem record081_frame002_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 2 :=
  of_group record081 2 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0491
    Papers.RationalityTen.SharedFrameCatalogue.group0491_facts record081_frame002_indices record081_frame002_graph record081_frame002_links
def record081_frame003_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0470.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0470.count (({ width := 9, code := 0x3ddeaf4793b9d6ea7439dcae06db65a6d066b3192c761b097ebe5c2d15eab54a9d4ca451a813c9c4ba59248e46a29128742a1106803f9f8f471379b8d6673318cbe5c2d950a04e251249044219007e3a1b8d0622d160a852281386832180b8542813088401c0c } : Fields).get c.val)
theorem record081_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0470.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0470.localPairCheck (smallEmbedding record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0470.localPairCheck (smallEmbedding record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record081_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0470.localPairCheck (smallEmbedding record081) (record081.maps 3)
      (record081.inverseMaps 3) record081_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record081_frame003_links_0000 record081_frame003_links_0064)
theorem record081_frame003_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 3 :=
  of_group record081 3 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0470
    Papers.RationalityTen.SharedFrameCatalogue.group0470_facts record081_frame003_indices record081_frame003_graph record081_frame003_links
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (Fin.cases (record081_frame001_supported hcells) (Fin.cases (record081_frame002_supported hcells) (Fin.cases (record081_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x65463d60b5fb5ef5d15be5a859658c58655d5245114ca4a549f48047146c45f4494134073f83da3c33ab39d39538f37033d32f2ed2d22cf2b72ad2aa2a629928c27e27226624c2322262132041e51c91bc1b41aa19619418d18317716816715f15114513c1301271111091080f10f00e30e20c40b80ac0a406e06d06906405b05a05705503e03c037032029028025023 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
def record082_frame002_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0xbcde2e772b8dbadb6ab459ecd64b1d82ab4ca5d1a813f9dcd64d249147637178ac52270d84411f0ef773a5c6e26fb75b6d76ab4d9ccb64b157ab8592c15aaa5228d409e4da55289147a311286421f0f077381bcd26830978b6582311486421f0f4783b160a8502711084401f } : Fields).get c.val)
theorem record082_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record082) (record082.maps 2) (record082.inverseMaps 2) record082_frame002_indices (Fin.ofNat record082.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record082_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record082) (record082.maps 2)
      (record082.inverseMaps 2) record082_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record082_frame002_links_0000 record082_frame002_links_0064)
theorem record082_frame002_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 2 :=
  of_group record082 2 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record082_frame002_indices record082_frame002_graph record082_frame002_links
def record082_frame003_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0471.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0471.count (({ width := 9, code := 0xa8d42994aa451689409e4ee75379a4c64d219046e2f1689c421105823fdfaf97abd1e6ef75391b0d36933592c86331184bf5eae96ab358aad449d4d2612a9247a39168943209027e3e1e4ee75391b0d46931988bc5d2b1489c4a1f8f8783b1c0dc6c35150a44c251007c3c1d } : Fields).get c.val)
theorem record082_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record082) (record082.maps 3) (record082.inverseMaps 3) record082_frame003_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record082) (record082.maps 3) (record082.inverseMaps 3) record082_frame003_indices (Fin.ofNat record082.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record082_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (smallEmbedding record082) (record082.maps 3)
      (record082.inverseMaps 3) record082_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record082_frame003_links_0000 record082_frame003_links_0064)
theorem record082_frame003_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 3 :=
  of_group record082 3 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0471
    Papers.RationalityTen.SharedFrameCatalogue.group0471_facts record082_frame003_indices record082_frame003_graph record082_frame003_links
def record082_frame004_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65131156c6b40594ab19510a3a4ffa7bd3b899147d22fd0667f63f61ee8f447983b71c44c5e60c2fa9648aa850626592ec95045d1e30e2c5fe2c215c0a184dc26412c094449423b11a08b04221fc0fa07843981bf0d8869c34019a0c7062c30817e0bb05ac2d01620ad854c29a14509f04b024a12208804342040ff07603941bc0d703b01d00de06a03081800ba05b01f00f006e03201480a004a023 } : Fields).get c.val)
theorem record082_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 4) (record082.inverseMaps 4) record082_frame004_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 4) (record082.inverseMaps 4) record082_frame004_indices (Fin.ofNat record082.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record082_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 4)
      (record082.inverseMaps 4) record082_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record082_frame004_links_0000 record082_frame004_links_0064)
theorem record082_frame004_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 4 :=
  of_group record082 4 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record082_frame004_indices record082_frame004_graph record082_frame004_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (Fin.cases (record082_frame002_supported hcells) (Fin.cases (record082_frame003_supported hcells) (Fin.cases (record082_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
def record083_frame001_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xe8471cb5f98d0c1f5ea2c654069cd4e326fd3609a94d0a6192e29694ab24e525691c487a40d2008f3475a3811ba66e31a1880c1a5c029593c88ce44221190047e23d11e28ec473c35115e0a0c3f01d30da06483041620ac054429214309d84d024811d08c042420a0fc07b83a81c40dc06b034012408d03781a806e03201480a004a02300f807803a01c00a004c02000e0050024010007 } : Fields).get c.val)
theorem record083_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record083_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record083) (record083.maps 1)
      (record083.inverseMaps 1) record083_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record083_frame001_links_0000 record083_frame001_links_0064)
theorem record083_frame001_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 1 :=
  of_group record083 1 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record083_frame001_indices record083_frame001_graph record083_frame001_links
def record083_frame002_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6f56e96c866c65463d60c5a859c59258857a56c56154a5335285144f94e24cc4b84a34a148c48246f46e3ab39f39739037033d32f2ec2db2ce2bc2b62a92a329628b2642242101b91a519117e17416415e15014413b12f12611210a1070f20ef0e40e10cc0ba0ae0a609e08107f06906403703202902802502301f01e01d01c01401301000e00a009008007 } : Fields).get c.val)
theorem record083_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record083_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record083) (record083.maps 2)
      (record083.inverseMaps 2) record083_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record083_frame002_links_0000 record083_frame002_links_0064)
theorem record083_frame002_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 2 :=
  of_group record083 2 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record083_frame002_indices record083_frame002_graph record083_frame002_links
def record083_frame003_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0x3f97e8f65d83a273ae09acb4d68ed059cb32656c6586b065ecb916cace588ae95caae552a7d4f24f4868f91ca2940c7d4e59c136e6a4d219c330648c69762b25248f9132103f87c8f01d63986f8da1a63385f0ba1722a4538a11402584788a10e2103886d0c01701b8320520a01282303e0780e81c02804c0800e01402404007 } : Fields).get c.val)
theorem record083_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record083) (record083.maps 3) (record083.inverseMaps 3) record083_frame003_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record083) (record083.maps 3) (record083.inverseMaps 3) record083_frame003_indices (Fin.ofNat record083.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record083_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record083) (record083.maps 3)
      (record083.inverseMaps 3) record083_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record083_frame003_links_0000 record083_frame003_links_0064)
theorem record083_frame003_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 3 :=
  of_group record083 3 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record083_frame003_indices record083_frame003_graph record083_frame003_links
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (Fin.cases (record083_frame001_supported hcells) (Fin.cases (record083_frame002_supported hcells) (Fin.cases (record083_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
def record084_frame001_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x65463d60c5a85865124c949e47f46b45f4494143ab38f3302ec2ce2b62a929d29028927726c26424522c2242101ec1d01b91a519117e17416414b1361251151060f50ee0e008107f06906405a05505105004f04e03703202802301f01e01d01c01b01a01801401301000e00a009008007004003002001000 } : Fields).get c.val)
theorem record084_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record084) (record084.maps 1) (record084.inverseMaps 1) record084_frame001_indices (Fin.ofNat record084.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record084_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record084) (record084.maps 1)
      (record084.inverseMaps 1) record084_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record084_frame001_links_0000 record084_frame001_links_0064)
theorem record084_frame001_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 1 :=
  of_group record084 1 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record084_frame001_indices record084_frame001_graph record084_frame001_links
def record084_frame002_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x666b1dd746a8b51ba47d1968af44d22310d680d3a69938bf04f925292248ec46a22c91088584021f48f4c6fc3401960bb8550289135892c45a20d100079038a1a60c405a029412a08e840412408d03781a80c005b02b81580aa05401b80c805002300f807803a01c00d8068030014009804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record084_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record084) (record084.maps 2) (record084.inverseMaps 2) record084_frame002_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record084) (record084.maps 2) (record084.inverseMaps 2) record084_frame002_indices (Fin.ofNat record084.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record084_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record084) (record084.maps 2)
      (record084.inverseMaps 2) record084_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record084_frame002_links_0000 record084_frame002_links_0064)
theorem record084_frame002_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 2 :=
  of_group record084 2 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record084_frame002_indices record084_frame002_graph record084_frame002_links
def record084_frame003_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x90f1e6253fd7cee69b935b690cf1983165b6a1d35a173d8758e19b83626a8d299a328638bc1672c25489f9342564888e10f2164087b8ed1c8360678c51842ec4207f0ce18c2d8570a61482885006c0c41402303e0780e81c0360680c0140260400700a0120200380400600800800 } : Fields).get c.val)
theorem record084_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record084) (record084.maps 3) (record084.inverseMaps 3) record084_frame003_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record084) (record084.maps 3) (record084.inverseMaps 3) record084_frame003_indices (Fin.ofNat record084.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record084_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record084) (record084.maps 3)
      (record084.inverseMaps 3) record084_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record084_frame003_links_0000 record084_frame003_links_0064)
theorem record084_frame003_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 3 :=
  of_group record084 3 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record084_frame003_indices record084_frame003_graph record084_frame003_links
def record084_frame004_indices (c : Fin record084.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65131156cea3a4ee230d0607e93db9e54edc711319941895038f17e0ad4506261129893048a23811888ac41c1f90f987703821b30d3065c31417b0ba859c2b014a09e84b824211208603f812408d03781a80c005b02b81580aa05401b80c805002300f807803a01c00d8068030014009804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record084_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record084.data.requiredEdges q = true := by decide +kernel
theorem record084_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 4) (record084.inverseMaps 4) record084_frame004_indices (Fin.ofNat record084.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record084_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 4) (record084.inverseMaps 4) record084_frame004_indices (Fin.ofNat record084.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record084_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record084) (record084.maps 4)
      (record084.inverseMaps 4) record084_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record084_frame004_links_0000 record084_frame004_links_0064)
theorem record084_frame004_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) : Supported record084 4 :=
  of_group record084 4 (smallEmbedding record084) (small_cells_exact record084 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record084_frame004_indices record084_frame004_graph record084_frame004_links
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (Fin.cases (record084_frame001_supported hcells) (Fin.cases (record084_frame002_supported hcells) (Fin.cases (record084_frame003_supported hcells) (Fin.cases (record084_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1a5cd2367533919c0bf05dd2e915f8a61520a89942695e49da4b91f48ef46ca1c906e8223f51f50f7c7873bd9dbcec87073791ac0d206733311964c926343119844c0a5fd2d71678b1e5822b9959ca7c53b296934c94a497234116489443321210646102f11680ae052628113787803861b90c305d81e40e506b02bc15c09d03080f807802900a00280120080028010006002 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x693d039ef27605b55656c7d88aff5d27c4e29b53464b47f8ed1b22a45089507dea37b6ccd81acb5068ab1d582a753a98d26a4547889510a1b426835039fd3a8714dc1a834466cc517b2dc578ac1512844f89d13425c4ac9211e23041c810f21962b82f85a0b21602a8540a60a41202304407c0f01d0360680c01401e0380680a0120200280400600800800 } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (smallEmbedding record090) (small_cells_exact record090 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994b6750827fd3de9dc460226906080c3fd9fa4f6e63326e132c9764a81c60d985f82d81638ad450625312609144701f90ee87403821b30d3065c32218a0ba857c2b01520a5051027a128090844c2180f004682300d4069030816c0b405702b01540a803201880a404602200f807803a01c00d80680300140070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (smallEmbedding record091) (small_cells_exact record091 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce666631f986aba05c628894249ef457a26101a7f83f41f20f687a63ca9d28e0266c32c13b89bc4bb1bd8d905b22c415a0a50500272130894c498245118888c42c2070fc87b03aa1ce0e407043761980c485f02da1670af852828812f093844c2160fe07403880de06b02f816c0b005502a00dc066027011808003a01c00d8068030013009003c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
def record092_frame002_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x75f7587437316f96f064964063159158354d54553e53152952251c5024e54a649e3e43dc3ca31a30c2d82d02c92bd2b62b02ab2a029528e27125a2472312192041dd1d31ca1c21bc19718517015f15814a13412e11710c0f00e60d80c40c106f06b05f05b05805505403703302702302001d01c01b01a01801301200f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record092_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record092_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record092) (record092.maps 2)
      (record092.inverseMaps 2) record092_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record092_frame002_links_0000 record092_frame002_links_0064)
theorem record092_frame002_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 2 :=
  of_group record092 2 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record092_frame002_indices record092_frame002_graph record092_frame002_links
def record092_frame003_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x49391b1f23845d8aeff5fbbef710df1a5b43676cc595b2563cc39812ef5d29f93ba6e428834ee9d439a70cde1b63606a4d199f32e63cc317d2e2598ae1572a4530a4130242460861061fe3c4768dd1aa3145f0b314e2843005c0a81402684a0920d0180270460800e81c0360680c01302403c0700b0140200380500600800800 } : Fields).get c.val)
theorem record092_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record092_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record092) (record092.maps 3)
      (record092.inverseMaps 3) record092_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record092_frame003_links_0000 record092_frame003_links_0064)
theorem record092_frame003_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 3 :=
  of_group record092 3 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record092_frame003_indices record092_frame003_graph record092_frame003_links
def record092_frame004_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xc0e6032f39730b635a9a8ed46aa0e47f23d90a283e4182044ffc7f03f39e88eac71738517e0be65d327793a48d045a22810e485642120d10247e83e01d68e346de34d1968c3c5ec2f01708b3457225b11e88844061fa0f606d83481770b5851827412607c03a40de06b02f816c0b005502a00dc066027011808003a01c00d8068030013009003c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record092_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record092) (record092.maps 4) (record092.inverseMaps 4) record092_frame004_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record092) (record092.maps 4) (record092.inverseMaps 4) record092_frame004_indices (Fin.ofNat record092.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record092_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record092) (record092.maps 4)
      (record092.inverseMaps 4) record092_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record092_frame004_links_0000 record092_frame004_links_0064)
theorem record092_frame004_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 4 :=
  of_group record092 4 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record092_frame004_indices record092_frame004_graph record092_frame004_links
def record092_frame005_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6da6d26b36936676605c15bb5ae51650e4c34b74b149f49148948146344441741037136b35e2c62be26f26125924a23e23823122922221b2051f51e71d41c41b61a71a319e19719116d15a14a13713112d11d1191060fe0ec0e40d90c80c306f06b05f05b05805505403703302702302001d01c01b01a01801301200f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record092_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record092) (record092.maps 5) (record092.inverseMaps 5) record092_frame005_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record092) (record092.maps 5) (record092.inverseMaps 5) record092_frame005_indices (Fin.ofNat record092.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record092_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record092) (record092.maps 5)
      (record092.inverseMaps 5) record092_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record092_frame005_links_0000 record092_frame005_links_0064)
theorem record092_frame005_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 5 :=
  of_group record092 5 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record092_frame005_indices record092_frame005_graph record092_frame005_links
def record092_frame006_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x49792120e3b4568a0fe1fa3ea72ce39b33616b4d35a3341678c9587aed5cea053f27242482cf09db3aa724e09bd3706c4d51a532861cbe9722ce56ca69482864fc9d923236440829021f83b4748d91a6318608bb15c2a8338640b415c2a0510a00d8190270460800e81c0360680c01302403c0700b0140200380500600800800 } : Fields).get c.val)
theorem record092_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record092) (record092.maps 6) (record092.inverseMaps 6) record092_frame006_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record092) (record092.maps 6) (record092.inverseMaps 6) record092_frame006_indices (Fin.ofNat record092.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record092_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record092) (record092.maps 6)
      (record092.inverseMaps 6) record092_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record092_frame006_links_0000 record092_frame006_links_0064)
theorem record092_frame006_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 6 :=
  of_group record092 6 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record092_frame006_indices record092_frame006_graph record092_frame006_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (Fin.cases (record092_frame002_supported hcells) (Fin.cases (record092_frame003_supported hcells) (Fin.cases (record092_frame004_supported hcells) (Fin.cases (record092_frame005_supported hcells) (Fin.cases (record092_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19dacd35c62de56cea2350827fd3de9dc45622690ce845419a040fec7ec3e59ee8f4479032c1914c664ef26e132c9764a81bc0d9866631117f8b705842b814b8a184dc25c129893048a2310fc87583a01c80e086ec3661ad0d3066031417c0ba857c2b01520a5051027a12f090844c2180ee07383801b20d303781a80d206002d816806e03201880a004602200d8068030013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
def record093_frame002_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19eccee5e0aec5746a77533295548aa37485a3e91c28d346622f916a8b0451226d12488b3b69d74e9a6383141860c105f8271934c9744ad253126091e48a23e91dc8de46922c91088583e91a00b6458e2b81540a6451227a135893045a20e100075438a1b60d3065c3101690a504ac23a0f007483881b60d403781a80d206002d816806e03201880a004602200d8068030013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record093_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record093) (record093.maps 2) (record093.inverseMaps 2) record093_frame002_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record093) (record093.maps 2) (record093.inverseMaps 2) record093_frame002_indices (Fin.ofNat record093.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record093_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record093) (record093.maps 2)
      (record093.inverseMaps 2) record093_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record093_frame002_links_0000 record093_frame002_links_0064)
theorem record093_frame002_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 2 :=
  of_group record093 2 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record093_frame002_indices record093_frame002_graph record093_frame002_links
def record093_frame003_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x66866461961160c5a259e59658c58650b5074e84d14ca4b44a549f48848047146a42441b4143a63a239d39538f32c32a30e2f62ed2de2d22cf2bf2b72ad2a829d29028926c22c20a2061fc1ec1dd1d01c11b91a619117f17415714b14213612d1251161060f60ee0c70bc0b00a80a006906406305a05505403703203102802302201b01a01801300e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record093_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record093) (record093.maps 3) (record093.inverseMaps 3) record093_frame003_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record093) (record093.maps 3) (record093.inverseMaps 3) record093_frame003_indices (Fin.ofNat record093.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record093_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record093) (record093.maps 3)
      (record093.inverseMaps 3) record093_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record093_frame003_links_0000 record093_frame003_links_0064)
theorem record093_frame003_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 3 :=
  of_group record093 3 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record093_frame003_indices record093_frame003_graph record093_frame003_links
def record093_frame004_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x23ac708750da18be07b8f65ea3ce700df1b83676c4d61a7b4e684cf199b2e5f6bdd792a053aa694aa8f4808f518a284468610720b4027ecf99ef3d2788ef1cb32c5ecba96e2cc578ab14e2924e8949182203f07b0f21d83a0720d919a3045d8a61402644988e0cc184300570a41441b8320620a0118220360680c01301c0340580a0120200380500800c01001 } : Fields).get c.val)
theorem record093_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record093) (record093.maps 4) (record093.inverseMaps 4) record093_frame004_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record093) (record093.maps 4) (record093.inverseMaps 4) record093_frame004_indices (Fin.ofNat record093.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record093_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record093) (record093.maps 4)
      (record093.inverseMaps 4) record093_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record093_frame004_links_0000 record093_frame004_links_0064)
theorem record093_frame004_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 4 :=
  of_group record093 4 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record093_frame004_indices record093_frame004_graph record093_frame004_links
def record093_frame005_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x24c4918a1132253f97e6fb5f53e7728e3dc0b776e8d9dafb5d69cd299fb3b5ceb7d6da824fa9d93926b420830fe9f23dc788ec9d8394714dd9b73626a8d29942ce538a494327e4ec9a13025648c8e1102163f07b8f31da3a4720d919e318610b215a2a4530a30ce18c3105b0ae1581b0310600a0118220360680c01301c0340580a0120200380500800c01001 } : Fields).get c.val)
theorem record093_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record093) (record093.maps 5) (record093.inverseMaps 5) record093_frame005_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record093) (record093.maps 5) (record093.inverseMaps 5) record093_frame005_indices (Fin.ofNat record093.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record093_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record093) (record093.maps 5)
      (record093.inverseMaps 5) record093_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record093_frame005_links_0000 record093_frame005_links_0064)
theorem record093_frame005_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 5 :=
  of_group record093 5 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record093_frame005_indices record093_frame005_graph record093_frame005_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (Fin.cases (record093_frame002_supported hcells) (Fin.cases (record093_frame003_supported hcells) (Fin.cases (record093_frame004_supported hcells) (Fin.cases (record093_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcc962c2de5470a0f4ee22b51327c53db1e9ce48645282136c9503791b28a44504273129893048a223107081c4021de0eb873c3901b30d686602e816e0ac052827a12808904141de0e904882300dc06c034817c0b805a02b01540a803601a00c404e024011007803a01c00d8068030012008003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (smallEmbedding record094) (small_cells_exact record094 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record099_frame001_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x87f0e61541e82101e013ff78ae8dc7b8c6accc5963225f2b4165ac7586aed5a2ae552a193f26e4c494511a0f4167bcf71cc3746ccd69a0334654c89732cc570a2938242448869061fa3b0748ce1943005d0af150274468891001f03b8680b613c248480860d81a02b0500740b00a01000c01000 } : Fields).get c.val)
theorem record099_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record099) (record099.maps 1) (record099.inverseMaps 1) record099_frame001_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record099) (record099.maps 1) (record099.inverseMaps 1) record099_frame001_indices (Fin.ofNat record099.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record099_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record099) (record099.maps 1)
      (record099.inverseMaps 1) record099_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record099_frame001_links_0000 record099_frame001_links_0064)
theorem record099_frame001_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) : Supported record099 1 :=
  of_group record099 1 (smallEmbedding record099) (small_cells_exact record099 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record099_frame001_indices record099_frame001_graph record099_frame001_links
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (Fin.cases (record099_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00002
