module
prelude
public import GraphInputsRow19Part00001Data
public import RawFrameSupport
public import SharedFrameGroups024Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups043Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups065Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001
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
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x182f01dbaa874d2774ba8cb1522444281d005d4396714cc97e2f654e9f53ba684a4919142113fa7c0d097e2e45a4a993f246448820f81e63745c0b414e2884d87c0c416c2d0550a814c2802c0460880b00e01a00c01001 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 63 :=
  interval_of_check _ 0 63 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ record017_frame001_links_0000
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x152a64c4a6ecdb9b53666b2d099fb1d630b796b2d259ab29452774888c0fd1f13bc76ceb19a310554a111c21a418810f21ca350610bc16c28c4e8790c61402784d0960c81883005808c0f01c03404c0680800e01800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 63 :=
  interval_of_check _ 0 63 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ record021_frame001_links_0000
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
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
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x9ad22e2a3ed666c59863085ceadd4a2784e49c1352674ac92922a2e4447ecf59e238e6e8dc1b03586a4d09913005b4af13823e430840f01b6330628b615c2ac4d8971261dc328510a00c41802c0520880f01d0380680b00f01a02404007 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0799.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0799.count (({ width := 10, code := 0x6a98b581484f13849912400fe3f4fb3d4f33bce438ce135cd2334cc328c7318c4308c02e8b92ccaa2a49d2689524c88200771d46d1b0681845d16853104310bc27090210801f07017058140380d0300a02007 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0799.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0799.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0799.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0799.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0799
    Papers.RationalityTen.SharedFrameCatalogue.group0799_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
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
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0xa071862bc12796ef1bcb5b6a4cdd8ab085e0b3d48a8c5109651822343e84cf79da3ae734db198318590ae15425e4748a10e2104146e8d71a2320618bd1642b0548a411c1b4288450800dc1b0300580941181e03404c0680a01001800800 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x15768fce899927e2ac4c894f61e93ca788e49bb36e6b6cc19331e632bed73adc5acb49452664a490511a17402800f89db310604b693f27c4a49111221a418810da1a83085e0b21582985009611a1f83c8680c6140278400600b01181a02603403001 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 71 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
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
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1808b59519a3550607f038217c4ba44c723a114088a4212040f346fa31d1720b2c57024d11e884c4061ef0ee868c2300f8074826c118078034817c0b605a02a81500a604001f00c404e023011008403a01c00c805c02400e00680280100070018008002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ record044_frame001_links_0000
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
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
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332973eb66595ab754209c94c9256d13488a3f499acc645f72d4937092a45e2138d986ac2b5129092448423411688643dc1d90e8873038a1b50d4068032618b0c205ac2c81620aa851427e130095048822810207d83e41e20df06c034811a08c04581a80d205b02d01580aa05402980c8062023011007803a01c } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
def record060_frame002_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x64a61660a5f95de57e56855653f4df4d54a24444354234033a538e37c3603022f92c62a629e29428627b2572191f41e71dd1d91c71b51a719418a17e15a14e14d14212f12510f1040fa0e70ca0be0bd0b90a80a109b08308208106706605905805405305205103103002302201e01d01c } : Fields).get c.val)
theorem record060_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record060) (record060.maps 2) (record060.inverseMaps 2) record060_frame002_indices (Fin.ofNat record060.n i)) 64 75 :=
  interval_of_check _ 64 11 (by decide +kernel)
theorem record060_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record060) (record060.maps 2)
      (record060.inverseMaps 2) record060_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 75 record060_frame002_links_0000 record060_frame002_links_0064)
theorem record060_frame002_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) : Supported record060 2 :=
  of_group record060 2 (smallEmbedding record060) (small_cells_exact record060 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record060_frame002_indices record060_frame002_graph record060_frame002_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (Fin.cases (record060_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x64bb0b9804b5d51928b11e88383fc1f98e086e13369830bc25aa2aa94008fa45f22690c083c4192030bbc5c02ca15d09a047622e10087b03b81c40bb857428c12c07d83ac1b80d2057826c0d205a029810007c03a01b00c806202e015809c04602200d80340180080038014004001 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (smallEmbedding record065) (small_cells_exact record065 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0xba351272c919171621741780ef91e6b3261ac25782aa52ca1d37232446838f79b32ee5509f136244448859041d8368678ac0f41e4330650c01642c0540a61481903104a08c1101e03a0700700d0140240400700600800800 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ record067_frame001_links_0000
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (smallEmbedding record067) (small_cells_exact record067 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a0da20cca5ca2d11420a054d3a26911e87b4332064fd266030813709a24731b30d6c68e3321728ad43a01b90d6866031417c0a884f425012108603bc1d209404682300d406902d81680ac05502a00c8062023011007803a01c00c803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (smallEmbedding record068) (small_cells_exact record068 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994b4150826911348663f498349b84701b30cc856a23711807903a01c80dc86b433c1980c505f02b015109e84d425012108603bc1d208d046022c0d406902d81680ac05502a014c064031011808803c01d00e006c03401900a803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
def record070_frame002_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7076966085e455d54651d4833ee3c433531d2f42a829b2251fc1f11e11d01bc1b419f18815414d13512811710b0ec0c60c108708608506806705905805405305205103103002302201e01d01c01b01a01901500e00d00b009008007004003002001000 } : Fields).get c.val)
theorem record070_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record070) (record070.maps 2) (record070.inverseMaps 2) record070_frame002_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record070) (record070.maps 2) (record070.inverseMaps 2) record070_frame002_indices (Fin.ofNat record070.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record070_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record070) (record070.maps 2)
      (record070.inverseMaps 2) record070_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record070_frame002_links_0000 record070_frame002_links_0064)
theorem record070_frame002_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 2 :=
  of_group record070 2 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record070_frame002_indices record070_frame002_graph record070_frame002_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (Fin.cases (record070_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1994a104fd26e134889a3f4937098c4842380d9856a23711807903a019e0c5057c2b014409e84d425e128090844c2180f0074823411808b03501a40cc05b02d01580aa05402980c806202e011808803c01d00e006c03401900a803801a009004001c00a0040018008002000 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (smallEmbedding record071) (small_cells_exact record071 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
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
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xbbb586a7544a0f2ea53c9d8870b6123fe7d0f7dea3d0798f0dc8b5569ccf9932d95a8b2d2323645c8a11318c30c604bc13625c4a0891091ea354670c816e2c0550a713c258430650ba1581f83606a0c8188270460880900901001401802 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
def record075_frame002_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0639.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0639.count (({ width := 9, code := 0xd1e471383be5b6cb5fa8d22873c99cba592a9449e3d118741dfcf579bc596c861b017ea150279388942204f6783899cc4602e15caa522893496401d0d8502612888421f0d8682409040140602 } : Fields).get c.val)
theorem record075_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record075_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record075) (record075.maps 2)
      (record075.inverseMaps 2) record075_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record075_frame002_links_0000 record075_frame002_links_0064)
theorem record075_frame002_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 2 :=
  of_group record075 2 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0639
    Papers.RationalityTen.SharedFrameCatalogue.group0639_facts record075_frame002_indices record075_frame002_graph record075_frame002_links
def record075_frame003_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0635.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0635.count (({ width := 9, code := 0xaad26873e9dcc657268e45a230b82c01fafc7dbe9e6ea7438dbad66a3495eab542994a8c45a250e73381b8d4683196cb0562913c9a4c25918863b1b8c84e24118803e1c0c05c2009040140602 } : Fields).get c.val)
theorem record075_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0635.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record075_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0635.localPairCheck (smallEmbedding record075) (record075.maps 3)
      (record075.inverseMaps 3) record075_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record075_frame003_links_0000 record075_frame003_links_0064)
theorem record075_frame003_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 3 :=
  of_group record075 3 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0635
    Papers.RationalityTen.SharedFrameCatalogue.group0635_facts record075_frame003_indices record075_frame003_graph record075_frame003_links
def record075_frame004_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x6542e456bab4b55ca7cd3869b246622551068123ef1f44f407883bb1cccd786283059778b6053d297145884a4001f28f647a42be1598a9051c2080f8879035c19c0bc84d824211507783781a80c905982ac13606e033017c08003601a80c806202701180880240090040014006002 } : Fields).get c.val)
theorem record075_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record075) (record075.maps 4) (record075.inverseMaps 4) record075_frame004_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record075) (record075.maps 4) (record075.inverseMaps 4) record075_frame004_indices (Fin.ofNat record075.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record075_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record075) (record075.maps 4)
      (record075.inverseMaps 4) record075_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record075_frame004_links_0000 record075_frame004_links_0064)
theorem record075_frame004_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 4 :=
  of_group record075 4 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record075_frame004_indices record075_frame004_graph record075_frame004_links
def record075_frame005_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0585.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0585.count (({ width := 8, code := 0xbdb6b4b2aea8a6a4a1a09d9c9b98979695938f8b8a86827e7d7c6b69656463575655544a46454443403a373533302e2d2c282725231f1816151312100e0d0a0807050302 } : Fields).get c.val)
theorem record075_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record075) (record075.maps 5) (record075.inverseMaps 5) record075_frame005_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record075) (record075.maps 5) (record075.inverseMaps 5) record075_frame005_indices (Fin.ofNat record075.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record075_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record075) (record075.maps 5)
      (record075.inverseMaps 5) record075_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record075_frame005_links_0000 record075_frame005_links_0064)
theorem record075_frame005_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) : Supported record075 5 :=
  of_group record075 5 (smallEmbedding record075) (small_cells_exact record075 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0585
    Papers.RationalityTen.SharedFrameCatalogue.group0585_facts record075_frame005_indices record075_frame005_graph record075_frame005_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (Fin.cases (record075_frame002_supported hcells) (Fin.cases (record075_frame003_supported hcells) (Fin.cases (record075_frame004_supported hcells) (Fin.cases (record075_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
def record078_frame001_indices (c : Fin record078.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x62c2eb96f4b4e55da93d3689ab48ea2150f88624241f48f766bb32496d4b5e52c25912b4930483213104c57e288136891c4622130da06402da16409883e81d609004682300d406902d81680ac05502a00c8062023011007803a01c00c803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record078_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record078.data.requiredEdges q = true := by decide +kernel
theorem record078_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record078_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record078_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record078) (record078.maps 1)
      (record078.inverseMaps 1) record078_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record078_frame001_links_0000 record078_frame001_links_0064)
theorem record078_frame001_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) : Supported record078 1 :=
  of_group record078 1 (smallEmbedding record078) (small_cells_exact record078 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record078_frame001_indices record078_frame001_graph record078_frame001_links
def record078_frame002_indices (c : Fin record078.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x741b561a22cca5ca2b29420a0549ba26911e87b4331fa4fa66602cb13709a24031b30d6c68e33215a8a7c3a01b90d6866031417c0a884f425012108603bc1d209004682300d406902d81680ac05502a00c8062023011007803a01c00c803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record078_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record078.data.requiredEdges q = true := by decide +kernel
theorem record078_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record078) (record078.maps 2) (record078.inverseMaps 2) record078_frame002_indices (Fin.ofNat record078.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record078_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record078) (record078.maps 2) (record078.inverseMaps 2) record078_frame002_indices (Fin.ofNat record078.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record078_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record078) (record078.maps 2)
      (record078.inverseMaps 2) record078_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record078_frame002_links_0000 record078_frame002_links_0064)
theorem record078_frame002_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) : Supported record078 2 :=
  of_group record078 2 (smallEmbedding record078) (small_cells_exact record078 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record078_frame002_indices record078_frame002_graph record078_frame002_links
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (Fin.cases (record078_frame001_supported hcells) (Fin.cases (record078_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
def record079_frame001_indices (c : Fin record079.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x8ff02e03bd673ee39adadf56aac53aa6c4ba9111ea323f67d0ec1a133657ca79462664848a8ff1f23d0720d11963205f8aa14a1d83a8610c01482884d09812c2503005e0b4128220420740e01b0320380680b0120200380400600800800 } : Fields).get c.val)
theorem record079_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record079.data.requiredEdges q = true := by decide +kernel
theorem record079_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record079_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record079_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record079) (record079.maps 1)
      (record079.inverseMaps 1) record079_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record079_frame001_links_0000 record079_frame001_links_0064)
theorem record079_frame001_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) : Supported record079 1 :=
  of_group record079 1 (smallEmbedding record079) (small_cells_exact record079 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record079_frame001_indices record079_frame001_graph record079_frame001_links
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (Fin.cases (record079_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
def record080_frame001_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7076666085b355d54651d44f3ee38c33531d2f42632572492261fc1f11e11d01b419f19018815414d13511710b0fc0ec0c60c108708608506806705905805405305205103103002302201e01d01c01b01a01901100e00d00b009008007004003002001000 } : Fields).get c.val)
theorem record080_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record080_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record080) (record080.maps 1)
      (record080.inverseMaps 1) record080_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record080_frame001_links_0000 record080_frame001_links_0064)
theorem record080_frame001_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 1 :=
  of_group record080 1 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record080_frame001_indices record080_frame001_graph record080_frame001_links
def record080_frame002_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x332958ea1049a22690cc7e92c993708003661990ad441a2060fd07943a01c80dc86b433018a0c105f02b015109e84a024211908603bc1d208d046022c0d406902d81680ac05502a014c064031011808803c01d00e006c034019008803801a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record080_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 2) (record080.inverseMaps 2) record080_frame002_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 2) (record080.inverseMaps 2) record080_frame002_indices (Fin.ofNat record080.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record080_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record080) (record080.maps 2)
      (record080.inverseMaps 2) record080_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record080_frame002_links_0000 record080_frame002_links_0064)
theorem record080_frame002_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) : Supported record080 2 :=
  of_group record080 2 (smallEmbedding record080) (small_cells_exact record080 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record080_frame002_indices record080_frame002_graph record080_frame002_links
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (Fin.cases (record080_frame001_supported hcells) (Fin.cases (record080_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
def record081_frame001_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb775368a4a693d0ee1b430852fe1c9b1060ea3543a7f4f49c92ca4146e830c918c3105f4b815728c4cc8910c20e3e0738e11a03005d8b60f81ec318620aa1502804f09c1341f8320620bc118220420780e81c0320380680b0120200380400600800800 } : Fields).get c.val)
theorem record081_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record081_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record081) (record081.maps 1)
      (record081.inverseMaps 1) record081_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record081_frame001_links_0000 record081_frame001_links_0064)
theorem record081_frame001_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 1 :=
  of_group record081 1 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record081_frame001_indices record081_frame001_graph record081_frame001_links
def record081_frame002_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x75d7076ab60860055d55454d54651d4993ee3e033532832131d3173072f42ed2cd1fc1ef1eb1e11d01b419f18816015214d13511710b0ec0cb0c60c108708606806705905805405305205103d03103002e02302202101e01d01c01900e00d00b009008007004003002001000 } : Fields).get c.val)
theorem record081_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record081) (record081.maps 2) (record081.inverseMaps 2) record081_frame002_indices (Fin.ofNat record081.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record081_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record081) (record081.maps 2)
      (record081.inverseMaps 2) record081_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record081_frame002_links_0000 record081_frame002_links_0064)
theorem record081_frame002_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 2 :=
  of_group record081 2 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record081_frame002_indices record081_frame002_graph record081_frame002_links
def record081_frame003_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0375.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0375.count (({ width := 8, code := 0xb2aca7a19f9997969591867c7a706e6d6c6b6a6766625856555453514f4d4a4948474443403e3d3c3635302f2b2a29282726241e1d1c161514131211100a09080706050403020100 } : Fields).get c.val)
theorem record081_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record081) (record081.maps 3) (record081.inverseMaps 3) record081_frame003_indices (Fin.ofNat record081.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record081_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record081) (record081.maps 3)
      (record081.inverseMaps 3) record081_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record081_frame003_links_0000 record081_frame003_links_0064)
theorem record081_frame003_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 3 :=
  of_group record081 3 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0375
    Papers.RationalityTen.SharedFrameCatalogue.group0375_facts record081_frame003_indices record081_frame003_graph record081_frame003_links
def record081_frame004_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0447.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0447.count (({ width := 8, code := 0xb2aca7a19f9997969591867c7a706e6d6c6b6a6766625856555453514f4d4a4948474443403e3d3c3635302f2b2a29282726241e1d1c161514131211100a09080706050403020100 } : Fields).get c.val)
theorem record081_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record081) (record081.maps 4) (record081.inverseMaps 4) record081_frame004_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record081) (record081.maps 4) (record081.inverseMaps 4) record081_frame004_indices (Fin.ofNat record081.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record081_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record081) (record081.maps 4)
      (record081.inverseMaps 4) record081_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record081_frame004_links_0000 record081_frame004_links_0064)
theorem record081_frame004_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) : Supported record081 4 :=
  of_group record081 4 (smallEmbedding record081) (small_cells_exact record081 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0447
    Papers.RationalityTen.SharedFrameCatalogue.group0447_facts record081_frame004_indices record081_frame004_graph record081_frame004_links
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (Fin.cases (record081_frame001_supported hcells) (Fin.cases (record081_frame002_supported hcells) (Fin.cases (record081_frame003_supported hcells) (Fin.cases (record081_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
def record082_frame001_indices (c : Fin record082.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33294209fa44d22290f07e926e13186cc3561a20ad43a01c70e006d033e18a0c1857c2b014409e84bc25012108984301ec0f0074823411808b03501a40cc05b02d01580aa05402980c806202e011808803c01d00e006c0340190070034018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record082_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record082.data.requiredEdges q = true := by decide +kernel
theorem record082_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record082_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 1) (record082.inverseMaps 1) record082_frame001_indices (Fin.ofNat record082.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record082_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record082) (record082.maps 1)
      (record082.inverseMaps 1) record082_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record082_frame001_links_0000 record082_frame001_links_0064)
theorem record082_frame001_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) : Supported record082 1 :=
  of_group record082 1 (smallEmbedding record082) (small_cells_exact record082 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record082_frame001_indices record082_frame001_graph record082_frame001_links
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (Fin.cases (record082_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0xa8f319febe176ee69c2b7d6c4d79ab33b608b45642b6564a2538a43456820f39da3a271cd21872be504950f61bc334638c317a2bc548a413c1e83285b0a01382604a0680cc1602704a0800e01302403c0500700600800800 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ record087_frame001_links_0000
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (smallEmbedding record087) (small_cells_exact record087 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x15e29dc4b6a2b4fd27b63d396f49504391bc8ad4504273129891447021b10387743ae1b30d6065c3141740b7056029414309e84b825012108283a411808a03481700b405602a81500a4031012008803c01d00e006c03401800b805001e00d004802000e0040018008002000 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (smallEmbedding record092) (small_cells_exact record092 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
def record093_frame001_indices (c : Fin record093.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1812b4551ca3ed0908334041fccfcc6f03701ab8c9a5e62e7170090a45922990a88484191f98bd45c82a0146092847c21010205dc2d21600a304e025e0fb07383701a40b004e01a40c805a029010407c03c01b80cc06202c01400900440170068024010007002800c004001 } : Fields).get c.val)
theorem record093_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record093.data.requiredEdges q = true := by decide +kernel
theorem record093_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record093_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record093) (record093.maps 1) (record093.inverseMaps 1) record093_frame001_indices (Fin.ofNat record093.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record093_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record093) (record093.maps 1)
      (record093.inverseMaps 1) record093_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record093_frame001_links_0000 record093_frame001_links_0064)
theorem record093_frame001_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) : Supported record093 1 :=
  of_group record093 1 (smallEmbedding record093) (small_cells_exact record093 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record093_frame001_indices record093_frame001_graph record093_frame001_links
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (Fin.cases (record093_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x14209ff47da2b10867fa3d213709963c71bc0c3c58c27012989144621f90f907583a01b30d6064031415f0ac054828412f08984302080f0074838411808a03501a40c005a02a81500a403201880a004401d00e006c03401800b804c01c00d004802000e0050020008002000 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
def record095_frame002_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1538a8d4b2a46916486741a98f8c6854428492dc8f845522010547a833e1978bb45ba29d14709304782050f8878036a17c09e04c42480ff07a039c11808a03501a40c005a02a81500a403201880a004401d00e006c03401800b804c01c00d004802000e0050020008002000 } : Fields).get c.val)
theorem record095_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record095_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record095) (record095.maps 2)
      (record095.inverseMaps 2) record095_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record095_frame002_links_0000 record095_frame002_links_0064)
theorem record095_frame002_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) : Supported record095 2 :=
  of_group record095 2 (smallEmbedding record095) (small_cells_exact record095 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record095_frame002_indices record095_frame002_graph record095_frame002_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (Fin.cases (record095_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record097_frame001_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xc90613b0354869fd4c0246d20a8ff4189fc4fce7c93be9ca8ce060f2ff97e4b7655427f93d09dc48122e114485a42220d0fd07bc3bd1d78dc46ba34f1888bf45ee2a212d08f84402040fd077036c18f0bb05a42c014509c04bc24c05602a81500a202b014009003c01d00e006c03001400800240100070018008002000 } : Fields).get c.val)
theorem record097_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record097_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record097) (record097.maps 1)
      (record097.inverseMaps 1) record097_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record097_frame001_links_0000 record097_frame001_links_0064)
theorem record097_frame001_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) : Supported record097 1 :=
  of_group record097 1 (smallEmbedding record097) (small_cells_exact record097 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record097_frame001_indices record097_frame001_graph record097_frame001_links
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (Fin.cases (record097_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
def record098_frame001_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xca262c2f7d5baa6151d28992b68e9461a2bcfd27a73ca9db8e486ab2d494b4a0c4f22138ed471e37b15a89cc4c225312608e046222b10a083840e2010f507703aa1b30d2865c32018a0bd85d02dc1670a504f025c127090844821610507f02240ac05502a014403c01d00e006c03401800b005002601000780240100070018008002000 } : Fields).get c.val)
theorem record098_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record098) (record098.maps 1) (record098.inverseMaps 1) record098_frame001_indices (Fin.ofNat record098.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record098_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record098) (record098.maps 1)
      (record098.inverseMaps 1) record098_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record098_frame001_links_0000 record098_frame001_links_0064)
theorem record098_frame001_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) : Supported record098 1 :=
  of_group record098 1 (smallEmbedding record098) (small_cells_exact record098 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record098_frame001_indices record098_frame001_graph record098_frame001_links
def record098_frame002_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xbea5da2dd956ca56521a8f12fa918482a3f90627f13f39f24efa72a338183cbfe5f92ac140c9e84ef22890888344091fa0ef475a39e1b68d7469a33e1868bf45ec2a213c096849823e11008484081fa0db06442ec16b0b0051427412f09302240ac05502a014403c01d00e006c03401800b005002601000780240100070018008002000 } : Fields).get c.val)
theorem record098_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record098) (record098.maps 2) (record098.inverseMaps 2) record098_frame002_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record098) (record098.maps 2) (record098.inverseMaps 2) record098_frame002_indices (Fin.ofNat record098.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record098_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record098) (record098.maps 2)
      (record098.inverseMaps 2) record098_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record098_frame002_links_0000 record098_frame002_links_0064)
theorem record098_frame002_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) : Supported record098 2 :=
  of_group record098 2 (smallEmbedding record098) (small_cells_exact record098 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record098_frame002_indices record098_frame002_graph record098_frame002_links
def record098_frame003_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xccd646b039648ab2545a9e937094648fa43915e89344621ad0447b336c99d0c9c63b2c2147c9f24e624491c08d445922110087d23d31c88df86d235718b8bb85b0289135092c47622d10687fc3e41e40d3061c2d01580a504a823810f08082240ac05502a014403c01d00e006c03401800b005002601000780240100070018008002000 } : Fields).get c.val)
theorem record098_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record098) (record098.maps 3) (record098.inverseMaps 3) record098_frame003_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record098) (record098.maps 3) (record098.inverseMaps 3) record098_frame003_indices (Fin.ofNat record098.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record098_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record098) (record098.maps 3)
      (record098.inverseMaps 3) record098_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record098_frame003_links_0000 record098_frame003_links_0064)
theorem record098_frame003_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) : Supported record098 3 :=
  of_group record098 3 (smallEmbedding record098) (small_cells_exact record098 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record098_frame003_indices record098_frame003_graph record098_frame003_links
def record098_frame004_indices (c : Fin record098.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7a678a7636e46ad69f6986375f05e15da59157556f56053650348444543342c3c237c36a36331c3012fb2f52ed2cb2ba2ad28027326225522821b2151de1c51b21ab1a318f18617e17714812f11c11310b0f90f20ea0e108905605505405101e01d01c01b01a01801601401301000f009008007003002001000 } : Fields).get c.val)
theorem record098_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record098.data.requiredEdges q = true := by decide +kernel
theorem record098_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record098) (record098.maps 4) (record098.inverseMaps 4) record098_frame004_indices (Fin.ofNat record098.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record098_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record098) (record098.maps 4) (record098.inverseMaps 4) record098_frame004_indices (Fin.ofNat record098.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record098_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record098) (record098.maps 4)
      (record098.inverseMaps 4) record098_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record098_frame004_links_0000 record098_frame004_links_0064)
theorem record098_frame004_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) : Supported record098 4 :=
  of_group record098 4 (smallEmbedding record098) (small_cells_exact record098 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record098_frame004_indices record098_frame004_graph record098_frame004_links
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (Fin.cases (record098_frame001_supported hcells) (Fin.cases (record098_frame002_supported hcells) (Fin.cases (record098_frame003_supported hcells) (Fin.cases (record098_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00001
