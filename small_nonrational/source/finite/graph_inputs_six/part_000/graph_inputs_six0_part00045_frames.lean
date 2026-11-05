module
prelude
public import GraphInputsSix0Part00045Data
public import RawFrameSupport
public import SharedFrameGroups005Checked
public import SharedFrameGroups007Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x91c8fd8b88ac88386b83a82b81e81381180e80c8087eb7dc7da7d77c27ab7a977977877376e76676275c73e6cb6c669d5e75e25b65365295174f44e74d44a94a147e4774454294153f33e03dd38137534834033c32631c2e72bc2b429528727f23422820f1f91f11e81de19b17e16b15714a13d1241171020e90de0d70d10bf0ba0ae09407a06005c05304704503d03b03802401f01d00e009008002001000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1563aa24af6553127851bbfdde8ee9770b931c78e31657b299922bb35cf2c455f8ac8559aa7531497d4b2a51d25c8d746522c912887b426a0fd06e8303d89e7cf0476c3ae9d18e0e6f536c1b08d6669c33b19a4cb465432298fcace55e2ac1510a5a51926d13449964b725012308ce45b22b91487263501978bf45ba2af147097047822410e08543b81b50bd04f025c12408b83fc1e20e706d0348146099017009003e01700a003801a0090040014002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x90e8f08bc8ba8b38b188686f84582e80a7f57e37be7b07a278d77e77877676c76a7607417006f969e67c62161a5b75a45315245114ed4e04a649e49949549249147f47046444a4463fd3ea3de3d937f37234e3283122ef2e82db2ce2a32852812742322251ff1ea1c91ab1a319c19016514c13b13611a10d0e10da0cf0c50bf0ba0b50ac09e09d08206805f05805203e03c02e02901f017014009005002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
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
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x918470a2b70e883a3f49f0ef7c7b0bcd5df4ece7083811b8cdba6beb5d1a96d4268730054caa61519a8353ba9894bea58d2ae94d4a3a4551dc8b74149fd4fa67823b81980cb063730d983cbc457e2ac9538a2245f21b909c8183ec1f00ebc7423871bc8dbc6d033418c0bac54428c13a09a849c244118887c4001f40f386c83321900bb05b42c812408c03f41bc0d406302000e8071036817007603801700b00520240078024010007002000c004001 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x12da93ec92a41f1dc8ac43960dafd07c2bdedec2f3577d3b39c20e046e336e9afad746a5b509a1cc01533a98547ea134f1a5f52ae9474149fd4fa67823b81d7cea074535a1a88cfa65e32c18acc366092ee1638afc5692ac9550a9c52428894109b245f21b909c8183ec1f00eb47423851bc8db86d033718b0ba453e28c13a89a849e24411888844001f40f386c83321900bb05b42c812408c03f41bc0d4063017009003c01d80e407003501700b00520240078024010007002000c004001 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x90dc6b5ff0fd97d6be39e26eac741b805b6edb06c635d9ab4d44601af5968ab3b59a2a7d4fea68521a53128c91946ea2990d482c3fc1f50f8a79c3c21dc8d3668b33b1998cc065930b97f8ba25552a793d899649a236111084c3f41f48f7475e39d1c38dd46de3671820b5c54e27f13109644782320fe07dc3d41ca0d1866c3001780b2050c26012408c04381d80dc069031012e09403f81940c4047019807803a01c00c805c028010007800c004001 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x4b2245d1c089bc412189091824c059fcafd67cd3e2ded2f026ce362dafad6a6acb52d800bc35d0adb54cca61513280d3a69894b1a534fa47913bf9db4ebe7503a2997ccb06162fd1734b1c5822b49574aa854f28793d899648323090e484c4061fb0fa47ba3a91d08e046f236d1b40ce464230716d0a304ee26a128891046221010007d03ce1c50d3864030816d0b204902300eb02e01580aa05402380ec070034012007803a01c00d006002a00f004802000e0040018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x4b7a50d2198d5c52a22d0d7851c172030ff77ec3eb1f1af2075cba55d00e466ce362dafad6a6acb52d808a60500a74531697b4b2a55529c94647e237514c7d23c89dfceda75f3a81d14cbe6592ff1744b145822b29574aa654f293143c9ec4cb238112084c3f61f48f7475a39d1c28dd46dc3671820b5c4d824611888484001f40f3870c3681a50cd86403041780b6859028612408c03ac0fe05c02b01540a804701780b405402400f007403801900b805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x64db14579dbb5dc16d7967bb32d5caad3524a8f515e77f39e9c2cd922a113989744161d90e165c328d922b04578a9d94749dc4e526913269804b6a46d1f88c33f49ed8f4e7953c21dbceba5d02de9508a0c4a824b11c08be44c21c8f9c79038f15a8a084e626112a893848a23e11c88c045222210d881c3e21dc0d986b033c1970c505ec2e816e0b385602a214a0a184f426a12e094048422410507f03a40fe05c02b01540a8047012007803a01c00d006403001700a805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x49863e7137882431212304980b3f95facf9a7c5bc81d72e957403919b38d8b6beb5a9ab2d4b5a2aced668a6653028053a29894bda58d2aa94d4a323f11ba8a63e91e44efe76d3af9d40e8a65f32c97f8ba258e2c115a4aba5542a7943c9ec4cb2130fd87d23dd1e48edc75239d1c78e046ea36d1b38ce46082d713b89b04a224611888484001f40f387143681a70cd86403081780b6859028612408c03ac0fe05c02b01540a8047012007803a01c00d006403001700a805002000f004802000e0040018008002000 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame002_links_0000 record040_frame002_links_0064)
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
def record040_frame003_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x84182f8108087fd7f57e67e17d27d07c47c27ad79979178d78375575375174f74c74a67166b6655e25dd5b159156655e54f54653f5395104fe4da46e45044843d43542f4293a63a137235332a32131230a3032fd2d42be29b2322142092001f91f11ea1e31dd1d61cf1cb1c81ba1a418c16a16415414e14013913413012911d11911310c1070ff0f80f30ed0e50db0d50c407e05b05505405304702401e01d01c01a01901801701501401000f009008007004003002001000 } : Fields).get c.val)
theorem record040_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record040_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record040) (record040.maps 3)
      (record040.inverseMaps 3) record040_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record040_frame003_links_0000 record040_frame003_links_0064)
theorem record040_frame003_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 3 :=
  of_group record040 3 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record040_frame003_indices record040_frame003_graph record040_frame003_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (Fin.cases (record040_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8bc4496165079823bfe5f44f547903b65d50e70714b7c5b82d8e6be35ddacad606a53265924c775b2ad09652afa57aa9812d894948c22b1148889440a17509c7e03e51da0e8872e3849c00cc258b2b79510a1c4f5278135c9924af23191508344121f98f887ae3c61b10ca462e2ef1700b3857e2b81568a584682220f907883aa1c50d2865428213108583f81e60e606c03240ec07403101680b203d01d80a4044020007803801a00a0048008002000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa9fa6aa40a339f89e39a499395494e92490c8d58c188d88685d85c85285083e7f87ad7316c86c369367f5fd5f85db5c855354f53951d4df47246342d41739638736234c2e12d72be2ac29028827526625e24f2041c01ba1b71af19c19418f15f15814513d13212c11c1141070e60d80d00ca0bd0b707607106b06506205b03d03803302c02902300f00e00a008007003002001 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x24447a8eb1ce2ec5788f1121842e841076054047e4fc1ecbd87a8f4de83c175eda9a634a672ccd7caf85d8b854fa9d51a9ed35a4f48a8ad131f43da780ed1a4336628be9722d8588ae1572a44c48c113222434800fb1f2388700d91a4330640bf1742cc5289f1382604608a0c81882e8580aa1381c03405e0ac1402301e0380500800e00c01001 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xd4ed44c40c36badb9db7cb71a009fc9f79dd9d799699297f93392a91e9118a689a88887d86e85f7f77927827717627387246c76b46a269869469067466d63362f6195d05c75bd5af54c54453652c5215144bd46f4624544464224123c63b73a839f39839238737c37536835b34e32731a30d2fd2ed2a329e28e27e27024223220f2001f21e11d11bf1b31a719818817816a15b14b1151041020f60eb0df0d10ba0ae06f06e05a05905305203903802402301d01c } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x78a3c0db94db96c335fdaded685c92e29708b655b02c25600ae3544a9f54e4a664f7a7a13889b44d3a65d2588b2450223d0fa85c4231f74f8e7b13d31e78f2c76d3b41c78e246f134b9a18cf46692fe97e0bba5d12e316e8aca50a27d93b09ba4c125711808a244221b90a08364142040fe07d43dc1e70e907263841b98d946182fd1760b705962a0145898c4a023d11588603ea1e70ec07283761b40d006302f813b095849c23010807b83a81a20c303881c00b805b02a8150072038012008c03a01c } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
def record046_frame003_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0xb5daab75aacd62af56a6d2e9549a451e8d45a250e85419c4de6933994c6612691c823b198b43e190883412070280c01fefe7ebf1f6fa78bc1daec75ba9d2df6e365acd267b218ac15f2e96eb357ab154a85329144a04f2712a9247a31128542204fe7d3d1dce670369a8ce6430978b8582b958a650269288a421e0ec6833168b050271007c3218 } : Fields).get c.val)
theorem record046_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record046) (record046.maps 3)
      (record046.inverseMaps 3) record046_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame003_links_0000 record046_frame003_links_0064)
theorem record046_frame003_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 3 :=
  of_group record046 3 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record046_frame003_indices record046_frame003_graph record046_frame003_links
def record046_frame004_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0149.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0149.count (({ width := 9, code := 0xa8d4283409fcfa7b3c99cca633097cba5b2c95caa53288fc7a371a8cc622f0d8541e09007ebd9e6ef76bb1d6ea74ba1cee672b91c6e26cb61aad469b49a2c7623057cba5bac15aa953a9546a14fa7536994ba55269147a350e85411fcf8783b9d0e470369a8cc6330174b4582a948a04c259288e44208f872361a8d05c2d138984a240f0742e16 } : Fields).get c.val)
theorem record046_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0149.localPairCheck (embedding (N := 44310) record046) (record046.maps 4)
      (record046.inverseMaps 4) record046_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame004_links_0000 record046_frame004_links_0064)
theorem record046_frame004_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 4 :=
  of_group record046 4 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0149
    Papers.RationalityTen.SharedFrameCatalogue.group0149_facts record046_frame004_indices record046_frame004_graph record046_frame004_links
def record046_frame005_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0229.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0229.count (({ width := 9, code := 0x83c19eef67abd1e6f277bb9daec75ba9d2e873b99cae47037dbadc6db69b2d569b459ecc653218cc36130580bf5f2f578bb5d2e570b759ac960af572b558a853291449f4ea6d32964aa4d228f46a2d128742a0d027f3e9ecea73381b4d46632988c05e2d960a8512712c9046219007c3a1c8e06a33188bc582a148a04e26108803e1e0e8702e16 } : Fields).get c.val)
theorem record046_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0229.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record046) (record046.maps 5) (record046.inverseMaps 5) record046_frame005_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0229.localPairCheck (embedding (N := 44310) record046) (record046.maps 5)
      (record046.inverseMaps 5) record046_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame005_links_0000 record046_frame005_links_0064)
theorem record046_frame005_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 5 :=
  of_group record046 5 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0229
    Papers.RationalityTen.SharedFrameCatalogue.group0229_facts record046_frame005_indices record046_frame005_graph record046_frame005_links
def record046_frame006_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xaa4d4c249b234882c3b21710a365c328d922c3560f2e356f4b3f5592a79514a754ee27293489934c025b51ce878433215108881c4051ed8f4c7953c21dbceba7013751964c8c60b2bf15a8aac54125412588e045f22610e47663441990c806202e816b0a084e426112b093c49424311d08d445c22711008284061fc0fa87b43941c50df06dc36019c0ca86102fa1770b805a02b61540a6851827c13809884a424410908103fc1f20f2075038c1b00d203881c00b805b02a8150072038012008c03a01c } : Fields).get c.val)
theorem record046_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 6) (record046.inverseMaps 6) record046_frame006_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 6) (record046.inverseMaps 6) record046_frame006_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record046) (record046.maps 6)
      (record046.inverseMaps 6) record046_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame006_links_0000 record046_frame006_links_0064)
theorem record046_frame006_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 6 :=
  of_group record046 6 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record046_frame006_indices record046_frame006_graph record046_frame006_links
def record046_frame007_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x8198137a179d78778477f77a69769368b67667163d63a6255e95e25d95d158d58757456b5625595254e94e14da4d04bd4af47a46e46445d45745443c4374034003eb3ae3a63a039935334d33933032a3212eb2ae2a429e29628327523d23322a22321b21421020a2051fd1f61ee1dc1d31cb1c21bb19919418c18317b16916315014b14513c13312a12511e11911210e1091030fb0e40dd0db0d60d20cb0c30b70b106f06e05a05905305203903802402301d01c } : Fields).get c.val)
theorem record046_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record046) (record046.maps 7) (record046.inverseMaps 7) record046_frame007_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record046) (record046.maps 7) (record046.inverseMaps 7) record046_frame007_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (embedding (N := 44310) record046) (record046.maps 7)
      (record046.inverseMaps 7) record046_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame007_links_0000 record046_frame007_links_0064)
theorem record046_frame007_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 7 :=
  of_group record046 7 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record046_frame007_indices record046_frame007_graph record046_frame007_links
def record046_frame008_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x8e2378a22789a2589223822068160480dfc7edfa7d1f37c9f1795e477ddd76dd9741ba6d9b26b9a96959864d8d6298861d866157e5f57a5c9705b96c5615754d52545505293c4e1344c12a495194550f42d07411003f0f83d4f23bcea39ce4384de348ce328c6308ba2dcb02b4aa294a0264952448d224852007b1e06d1a86918c5f16c571404b1003f0d8350bc2e0a8290801f06418 } : Fields).get c.val)
theorem record046_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record046) (record046.maps 8) (record046.inverseMaps 8) record046_frame008_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record046) (record046.maps 8) (record046.inverseMaps 8) record046_frame008_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record046) (record046.maps 8)
      (record046.inverseMaps 8) record046_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame008_links_0000 record046_frame008_links_0064)
theorem record046_frame008_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 8 :=
  of_group record046 8 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record046_frame008_indices record046_frame008_graph record046_frame008_links
def record046_frame009_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0228.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0228.count (({ width := 7, code := 0xefdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record046_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0228.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0228.localPairCheck (embedding (N := 44310) record046) (record046.maps 9) (record046.inverseMaps 9) record046_frame009_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0228.localPairCheck (embedding (N := 44310) record046) (record046.maps 9) (record046.inverseMaps 9) record046_frame009_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0228.localPairCheck (embedding (N := 44310) record046) (record046.maps 9)
      (record046.inverseMaps 9) record046_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame009_links_0000 record046_frame009_links_0064)
theorem record046_frame009_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 9 :=
  of_group record046 9 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group0228
    Papers.RationalityTen.SharedFrameCatalogue.group0228_facts record046_frame009_indices record046_frame009_graph record046_frame009_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (Fin.cases (record046_frame003_supported hcells) (Fin.cases (record046_frame004_supported hcells) (Fin.cases (record046_frame005_supported hcells) (Fin.cases (record046_frame006_supported hcells) (Fin.cases (record046_frame007_supported hcells) (Fin.cases (record046_frame008_supported hcells) (Fin.cases (record046_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xa9da68a3ea31a03a009e69d09b59ae99698796e95e95294c9349248d589588d88686e86c86686386085d8578548527807757316cb6c36005f856f56154b52952251c51750e5074e54df47046342d41739438736234c2f72e92bd2b62b02ab28e28827026625924f2312192041c21ba1af1a019418f15f15813d13412c1201141070e60d80c80c40c109106b05b05505403d03803302c02902302001d01c01a01801500f00e00a008007003002001000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
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
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0x3a7d1e873799cae471387c1e06ff7dbdde6ef75b8db6d759a9d36931987b958abd55a35067f329849643188a442190380be1e8ee76395c6df6db5daad16732186b85a29944994923d0a823d1d4d0652e968ae441e8e46a31180bc5429130904621100783a190c05c260f068241007018080200 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (embedding (N := 44310) record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (embedding (N := 44310) record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (embedding (N := 44310) record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (embedding record071) hcells Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (Fin.cases (record071_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x533696b3fe9fdccfe467219901c7d23691a2890c142072ff77f4bdfdedaf577a435a5a88d135b2ad115fcaf3564a9e93f29d84c9261d2ba90e46c23511868b0454a28d12888d38f1c20df869f33f98ecb925b32d39528a544e625a12ac94049824511ec8e246b21990707c83c11aa0cb85b02ad14d8a144ee25611d88b44161ff0f907903941b80d106502e61580a504a023810f08083e41e20e206d835010c07403881940c404701d80d0058025009803c012008003800c004001 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2aab4cba59cee27353859774b5e45f2158ffc7c23691a2890c19e0a10398033fddfd2f7f7b6bd5de90d0e5a42bcd592a7a4ee261d2ba90e46822bd13e8934462204e106f934f99fcc765b32d21528a544e624b92248e046a21610707743691aa0cb85b029b14489dc4b423b116882c3fe1f20f206e034c1940bb856029412808e043c2020ef04b023c10c05602a815009c04701d80d0058025010007803a01c00d006002a01300780240100070018008002000 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x36c6c7d63abf4b691d079db35661cb99231f62cc4f86708e07c017d2f55e5bc3772ebda3b41652b9d1aa0b40a7a4c89011662ac4183b06a0940e7fafd1ef3c971cde5b9b6b656bdd74aba556a4d43a844f49c12ea4547285d071fa3d8720da998322608bc9712d2594b194e2704808a90c20e404790e91aa3285e8b71662b0538a20f61b83685c0a814c2183b074094110200260380680a01200800800 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb18b05af2ad6aa6a89a5ea139f49d69c59a99859709378f18ea8d18a989e89688d8857fd7f672260f5fe5eb5af5a959e59457c5505284dc49448b42436a3563503453342fa2de2c22ba2a429225d2442202182041f91f31e91d21a518017416515814f1411050ea0e10d90d20ca0c10b90ab09808107206e06c06205805604403c03602c02502302001300e00d00a008003001000 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (embedding record077) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
def record078_frame001_indices (c : Fin record078.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xafdadbaa6a9ea8aa5ea339ee9d69c59b89aa97f93792c8f18ea8d18c58af8aa7fc7f77e47a57226ef6e86b968565361c6116085eb5d35b15a859c59657c56f5505345284dc49e48d48543f42440c3e83ab3a138236735735234333431a2fa2e82de2c22ba2a429225d2442202182091fc1ef1e41d21c31ba1a518a18016d16215d1541411241050fd0f40ea0e10d90d30c90c10b908107106e06405604403a02d02502001300e00d009008004001000 } : Fields).get c.val)
theorem record078_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record078.data.requiredEdges q = true := by decide +kernel
theorem record078_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record078_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record078) (record078.maps 1) (record078.inverseMaps 1) record078_frame001_indices (Fin.ofNat record078.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record078_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record078) (record078.maps 1)
      (record078.inverseMaps 1) record078_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record078_frame001_links_0000 record078_frame001_links_0064)
theorem record078_frame001_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) : Supported record078 1 :=
  of_group record078 1 (embedding record078) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record078_frame001_indices record078_frame001_graph record078_frame001_links
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (Fin.cases (record078_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
def record080_frame001_indices (c : Fin record080.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb18b05af2ad6a97a3aa1fa169d49ce9be9969739258f38ef8bf8b289c89788a8866c86bf6b765464560f5fe57b55a55252949448b4534403e63d73d03363272f82df2c22ba2a429225d2442041f91f31e91d21a019818b18117416515814f13a12511a1050eb0e50dd0c00b80ab09808107206e06c06205f05804403c03603302c02502301300e00a008007003002001 } : Fields).get c.val)
theorem record080_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record080.data.requiredEdges q = true := by decide +kernel
theorem record080_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record080_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record080) (record080.maps 1) (record080.inverseMaps 1) record080_frame001_indices (Fin.ofNat record080.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record080_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record080) (record080.maps 1)
      (record080.inverseMaps 1) record080_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record080_frame001_links_0000 record080_frame001_links_0064)
theorem record080_frame001_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) : Supported record080 1 :=
  of_group record080 1 (embedding record080) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record080_frame001_indices record080_frame001_graph record080_frame001_links
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (Fin.cases (record080_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
def record081_frame001_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xf99ec7a36eadafb334e696cfb9631c5fcba172ad1d98b1361ebf57b97125644459891065ef3bd750e91aab52666c41853005ccb85642c457aa693b2564aa9111d22e43484cff9f33986d8c097a2ec5b8af93926a4ac9291c228428810f51c8374668bb16e2c44d89611e2303685b09c1141f03d0720dc1a02d0580a8128230260380500800e00c01001 } : Fields).get c.val)
theorem record081_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record081_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record081) (record081.maps 1)
      (record081.inverseMaps 1) record081_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record081_frame001_links_0000 record081_frame001_links_0064)
theorem record081_frame001_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 1 :=
  of_group record081 1 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record081_frame001_indices record081_frame001_graph record081_frame001_links
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (Fin.cases (record081_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
def record083_frame001_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x26dcd98fd1f2334658c318221c30838ff9fd3e97cef69e7bb5764e8dcdb886f0d41a2b3e66ec8d8aafd5daba1722c2578a9951a935149c9382674c294d2422e44a87d0d2093fc7a4ef1da3aa738e49c23626c0d599331c610b69672bc554a613726a4bc9011221440c7d8f41dc3a0708dc19a330608bb1622c0550a2134248438820e01b4318610ac1442584a08c10c1b83305008c0e81c } : Fields).get c.val)
theorem record083_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record083_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record083) (record083.maps 1)
      (record083.inverseMaps 1) record083_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record083_frame001_links_0000 record083_frame001_links_0064)
theorem record083_frame001_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) : Supported record083 1 :=
  of_group record083 1 (embedding record083) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record083_frame001_indices record083_frame001_graph record083_frame001_links
def record083_frame002_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0270.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0270.count (({ width := 9, code := 0x30983bf5f6ed75ba5cec95aaa5369948a3cf677399c4d6672b9448e431f8ec6e31138843e1d078340a00f87abcde4ef76399c4dd6db65aed468b3996c96330178b6552a54c9b4c2491c8b44215047d3e1e4ea71379b0d26631980ba5a2a950a04d249208c43200f472371b0d4662f158a450271309446210e8643017 } : Fields).get c.val)
theorem record083_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (embedding (N := 44310) record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (embedding (N := 44310) record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record083_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (embedding (N := 44310) record083) (record083.maps 2)
      (record083.inverseMaps 2) record083_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record083_frame002_links_0000 record083_frame002_links_0064)
theorem record083_frame002_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) : Supported record083 2 :=
  of_group record083 2 (embedding record083) hcells Papers.RationalityTen.SharedFrameCatalogue.group0270
    Papers.RationalityTen.SharedFrameCatalogue.group0270_facts record083_frame002_indices record083_frame002_graph record083_frame002_links
def record083_frame003_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0127.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0127.count (({ width := 9, code := 0x377bad96c74fa6d2e9345a1cde2b1384c1dfaf974b9dc2dd6ab4572b558ab5529f4ba451a8933994b6592792c7639198bc4e230581c05fefd7c3d1e2ef75b95c2db65b298cbc5c2c54aa14f26d309349239148541200fa7a3b9d0e26d33194c45f2d164ae54289389448211047c3c1a8cc6230160ac50260f874361a } : Fields).get c.val)
theorem record083_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (embedding (N := 44310) record083) (record083.maps 3) (record083.inverseMaps 3) record083_frame003_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (embedding (N := 44310) record083) (record083.maps 3) (record083.inverseMaps 3) record083_frame003_indices (Fin.ofNat record083.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record083_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (embedding (N := 44310) record083) (record083.maps 3)
      (record083.inverseMaps 3) record083_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record083_frame003_links_0000 record083_frame003_links_0064)
theorem record083_frame003_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) : Supported record083 3 :=
  of_group record083 3 (embedding record083) hcells Papers.RationalityTen.SharedFrameCatalogue.group0127
    Papers.RationalityTen.SharedFrameCatalogue.group0127_facts record083_frame003_indices record083_frame003_graph record083_frame003_links
def record083_frame004_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2a9353092648ce20d0ed85c428dc34d4865c2e356f4b2658aaa294e09dc4e5267d30092047ba1e10cc8544222070ff47c53d31e54f0865932317c8bc255629e12a092c46b2260fb07863441990c806202e81630a444e426112b093c49424311788b444e2040fe07c03941c50df06dc36019c0cc864c3081790b805a02b61540a6851827c138092848822a10d08103fc1f20f2075038c1b00d204301f40e206c030016c0aa0540270114072034014008c03a01c } : Fields).get c.val)
theorem record083_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record083) (record083.maps 4) (record083.inverseMaps 4) record083_frame004_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record083) (record083.maps 4) (record083.inverseMaps 4) record083_frame004_indices (Fin.ofNat record083.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record083_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record083) (record083.maps 4)
      (record083.inverseMaps 4) record083_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record083_frame004_links_0000 record083_frame004_links_0064)
theorem record083_frame004_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) : Supported record083 4 :=
  of_group record083 4 (embedding record083) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record083_frame004_indices record083_frame004_graph record083_frame004_links
def record083_frame005_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x334e67c3585ef6debbc778ac856fa9343a854f59e33325dc9491d2063d45f89708a0c415816ff1f93d978ef01ddb7f6f8d79ad334658c11802ed5c6b215da90514a093fa6b4b69111ba3245a88d0da123ee7d8f79cb3866c8c69893005e0b815c2b454c9f93124a4708b10e2104087d0f61cc3906c8d218e318610bc16c2bc5209f0f61d4350660b41542784e09210c1c03405008c0e81c } : Fields).get c.val)
theorem record083_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record083) (record083.maps 5) (record083.inverseMaps 5) record083_frame005_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record083) (record083.maps 5) (record083.inverseMaps 5) record083_frame005_indices (Fin.ofNat record083.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record083_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record083) (record083.maps 5)
      (record083.inverseMaps 5) record083_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record083_frame005_links_0000 record083_frame005_links_0064)
theorem record083_frame005_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) : Supported record083 5 :=
  of_group record083 5 (embedding record083) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record083_frame005_indices record083_frame005_graph record083_frame005_links
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (Fin.cases (record083_frame001_supported hcells) (Fin.cases (record083_frame002_supported hcells) (Fin.cases (record083_frame003_supported hcells) (Fin.cases (record083_frame004_supported hcells) (Fin.cases (record083_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33d19c6ccb64230c5799b73db2acdf665b005702ae9560a92547a9cd40a963caf2499233911441a1db0e285c428e132d4865c2c554e09dc4e5267d30092047ba1990887fa3e29e98f2a7842f094f095049623591307d83c31990c4058c29113909844aa24e12288f84542220ff87e43721ab0cf066032016d0b385602a214a0a184f426a12108904301fc0ef074838810c07d03601800b605502a013808a034014008c03a01c00d006403001700a804c02000e005802000e0040018008002000 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (embedding record086) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x3f07cff67e8bbb765e9dcd775ed2d5ba7b45678cd793322dfdb9b716d95a8b2b64ea5548a7549e60cb392d1c624c2e845011fe3f57dcfa5eebc7778ecdd3ba46ded79aab52672cad9430e5e4bb9732e1576a954ea935129e93a26f4d2995302574928ed1c22d43484d021ef3906eccb98f3025e8bb16e2be554a693d2664908e1142144087c8db19a31c610ba1682b8548a213825c2604707c0f41c82d0580941082002403c0680a01000c00800 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
def record087_frame002_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0210.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0210.count (({ width := 8, code := 0xece8e7e5e2e1e0dfdbdad9d8d7d6d5d4d3cfcecdcac8c7c6c4c2c0bfb8b7b6b3aeadaba8a7a6a5a4a3a2a1a09f9e9d9c9b999695949391908d8b8887868483817f7d7a7877736f6c6a68646362605f5e5c59575452514d4b484543413e3b393834302d2b2a28262524232221201f1d1c1a1413110e0d0807050403020100 } : Fields).get c.val)
theorem record087_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0210.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0210.localPairCheck (embedding (N := 44310) record087) (record087.maps 2) (record087.inverseMaps 2) record087_frame002_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0210.localPairCheck (embedding (N := 44310) record087) (record087.maps 2) (record087.inverseMaps 2) record087_frame002_indices (Fin.ofNat record087.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record087_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0210.localPairCheck (embedding (N := 44310) record087) (record087.maps 2)
      (record087.inverseMaps 2) record087_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record087_frame002_links_0000 record087_frame002_links_0064)
theorem record087_frame002_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 2 :=
  of_group record087 2 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0210
    Papers.RationalityTen.SharedFrameCatalogue.group0210_facts record087_frame002_indices record087_frame002_graph record087_frame002_links
def record087_frame003_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0075.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record087_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0075.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0075.localPairCheck (embedding (N := 44310) record087) (record087.maps 3) (record087.inverseMaps 3) record087_frame003_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0075.localPairCheck (embedding (N := 44310) record087) (record087.maps 3) (record087.inverseMaps 3) record087_frame003_indices (Fin.ofNat record087.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record087_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0075.localPairCheck (embedding (N := 44310) record087) (record087.maps 3)
      (record087.inverseMaps 3) record087_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record087_frame003_links_0000 record087_frame003_links_0064)
theorem record087_frame003_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 3 :=
  of_group record087 3 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0075
    Papers.RationalityTen.SharedFrameCatalogue.group0075_facts record087_frame003_indices record087_frame003_graph record087_frame003_links
def record087_frame004_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0100.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record087_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0100.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0100.localPairCheck (embedding (N := 44310) record087) (record087.maps 4) (record087.inverseMaps 4) record087_frame004_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0100.localPairCheck (embedding (N := 44310) record087) (record087.maps 4) (record087.inverseMaps 4) record087_frame004_indices (Fin.ofNat record087.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record087_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0100.localPairCheck (embedding (N := 44310) record087) (record087.maps 4)
      (record087.inverseMaps 4) record087_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record087_frame004_links_0000 record087_frame004_links_0064)
theorem record087_frame004_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 4 :=
  of_group record087 4 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group0100
    Papers.RationalityTen.SharedFrameCatalogue.group0100_facts record087_frame004_indices record087_frame004_graph record087_frame004_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (Fin.cases (record087_frame002_supported hcells) (Fin.cases (record087_frame003_supported hcells) (Fin.cases (record087_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
def record099_frame001_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xabaab1a8ca829dc9c298c96a9579519289038d98b086585c85985081a7cd76e76672b6cd68667b64b6025d75bb58555653351b5174e149c49546d42741e3f83ea3d23c839136934632b3123072de2d92c02ae28f28827325c2282102061e21d81c11ba1b61af19e18f17316516215214413d13312c11e1070f30e90de0d20cf0ca0bd0b90a709d06b06905b05a03e03d03902d02c02a00a008003002 } : Fields).get c.val)
theorem record099_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record099) (record099.maps 1) (record099.inverseMaps 1) record099_frame001_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record099) (record099.maps 1) (record099.inverseMaps 1) record099_frame001_indices (Fin.ofNat record099.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record099_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record099) (record099.maps 1)
      (record099.inverseMaps 1) record099_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record099_frame001_links_0000 record099_frame001_links_0064)
theorem record099_frame001_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 1 :=
  of_group record099 1 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record099_frame001_indices record099_frame001_graph record099_frame001_links
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (Fin.cases (record099_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045
