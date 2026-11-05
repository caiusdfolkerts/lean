module

public import PaperVerification.ToricChartFaceLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

/-!
# Actual affine chart maps and their open images

The schemes are spectra of the semigroup subalgebras inside the character
ring. Every morphism is induced by their literal inclusion. Localization
therefore gives an actual open immersion, with its specified principal
open image. The final lemma is the categorical pullback statement for
two localizations with the same character denominator.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable (k : Type*) [CommRing k]
variable {G : Type*} [AddCommGroup G]

def monoidChartScheme (S : AddSubmonoid G) : Scheme :=
  Spec (CommRingCat.of (monoidChartAlgebra k S))

def monoidChartSpecMap {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartScheme k T ⟶ monoidChartScheme k S :=
  Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom)

@[simp] theorem monoidChartSpecMap_comp {S T U : AddSubmonoid G}
    (hST : S ≤ T) (hTU : T ≤ U) :
    monoidChartSpecMap k hTU ≫ monoidChartSpecMap k hST =
      monoidChartSpecMap k (hST.trans hTU) := by
  dsimp only [monoidChartSpecMap, monoidChartScheme]
  rw [← Spec.map_comp]
  congr 1

@[simp] theorem monoidChartSpecMap_self (S : AddSubmonoid G) :
    monoidChartSpecMap k (le_refl S) = 𝟙 (monoidChartScheme k S) := by
  have heq : CommRingCat.ofHom (monoidChartInclusion k (le_refl S)).toRingHom =
      𝟙 (CommRingCat.of (monoidChartAlgebra k S)) := by
    ext f
    rfl
  exact (congrArg Spec.map heq).trans (Spec.map_id _)

theorem monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap
    {S T : AddSubmonoid G} (hST : S ≤ T) (v : G) (hv : v ∈ S)
    (hloc : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST)) :
    IsOpenImmersion (monoidChartSpecMap k hST) := by
  letI : Algebra (monoidChartAlgebra k S) (monoidChartAlgebra k T) :=
    (monoidChartInclusion k hST).toRingHom.toAlgebra
  letI : IsLocalization.Away (chartCharacter k S v hv) (monoidChartAlgebra k T) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact IsOpenImmersion.of_isLocalization (chartCharacter k S v hv)

theorem monoidChartSpecMap_opensRange_of_isLocalizationMap
    {S T : AddSubmonoid G} (hST : S ≤ T) (v : G) (hv : v ∈ S)
    (hloc : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST))
    [IsOpenImmersion (monoidChartSpecMap k hST)] :
    (monoidChartSpecMap k hST).opensRange =
      PrimeSpectrum.basicOpen (chartCharacter k S v hv) := by
  letI : Algebra (monoidChartAlgebra k S) (monoidChartAlgebra k T) :=
    (monoidChartInclusion k hST).toRingHom.toAlgebra
  letI : IsLocalization.Away (chartCharacter k S v hv) (monoidChartAlgebra k T) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact SetLike.coe_injective
    (PrimeSpectrum.localization_away_comap_range (monoidChartAlgebra k T)
      (chartCharacter k S v hv))

/-- An actual square of chart inclusions is a pullback when its two
vertical arrows invert the same character before and after restriction.
No abstract replacement of any chart algebra is used. -/
theorem monoidChartSquare_isPullback
    {S T U V : AddSubmonoid G}
    (hST : S ≤ T) (hSU : S ≤ U) (hTV : T ≤ V) (hUV : U ≤ V)
    (v : G) (hv : v ∈ S)
    (hlocSU : (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hSU))
    (hlocTV : (Submonoid.powers (chartCharacter k T v (hST hv))).IsLocalizationMap
      (monoidChartInclusion k hTV)) :
    IsPullback (monoidChartSpecMap k hUV) (monoidChartSpecMap k hTV)
      (monoidChartSpecMap k hSU) (monoidChartSpecMap k hST) := by
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k hSU v hv hlocSU
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k hTV v (hST hv) hlocTV
  apply IsOpenImmersion.isPullback
  · simp only [monoidChartSpecMap_comp]
  · rw [monoidChartSpecMap_opensRange_of_isLocalizationMap k hSU v hv hlocSU,
      monoidChartSpecMap_opensRange_of_isLocalizationMap k hTV v (hST hv) hlocTV]
    change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (chartCharacter k S v hv) =
        PrimeSpectrum.basicOpen (chartCharacter k T v (hST hv))
    rw [SpecMap_preimage_basicOpen]
    rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory

variable (k : Type*) [CommRing k] {n : ℕ}

def coneChart (s : Finset (Lattice n)) : Scheme :=
  monoidChartScheme k (dualConeMonoid s)

def coneChartFaceMap {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    coneChart k t ⟶ coneChart k s :=
  monoidChartSpecMap k (dualConeMonoid_antitone hts)

@[simp] theorem coneChartFaceMap_comp {s t u : Finset (Lattice n)}
    (hts : t ⊆ s) (hut : u ⊆ t) :
    coneChartFaceMap k hut ≫ coneChartFaceMap k hts =
      coneChartFaceMap k (hut.trans hts) :=
  monoidChartSpecMap_comp k (dualConeMonoid_antitone hts) (dualConeMonoid_antitone hut)

@[simp] theorem coneChartFaceMap_self (s : Finset (Lattice n)) :
    coneChartFaceMap k (Finset.Subset.refl s) = 𝟙 (coneChart k s) :=
  monoidChartSpecMap_self k (dualConeMonoid s)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem coneChartFaceMap_isOpenImmersion (s t : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    IsOpenImmersion (coneChartFaceMap k hts) := by
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k s t hs hts
  exact monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc

theorem coneChartFaceMap_principal_open (s t : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s)
    [IsOpenImmersion (coneChartFaceMap k hts)] :
    ∃ (v : Lattice n) (hv : v ∈ dualConeMonoid s),
      (coneChartFaceMap k hts).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) := by
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k s t hs hts
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  exact ⟨v, hv, monoidChartSpecMap_opensRange_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc⟩

/-- The affine chart of the actual common face is the scheme-theoretic
overlap of two face charts inside the original chart. -/
theorem coneChart_faces_isPullback (q s t : Finset (Lattice n))
    (hq : q ∈ «Σ».cones) (hs : s ⊆ q) (ht : t ⊆ q) :
    CategoryTheory.IsPullback
      (coneChartFaceMap k (Finset.inter_subset_right : s ∩ t ⊆ t))
      (coneChartFaceMap k (Finset.inter_subset_left : s ∩ t ⊆ s))
      (coneChartFaceMap k ht) (coneChartFaceMap k hs) := by
  obtain ⟨v, hv, hneg, hclear, hclearInter⟩ :=
    «Σ».exists_intersection_character_denominator q s t hq hs ht
  apply monoidChartSquare_isPullback k
    (dualConeMonoid_antitone hs) (dualConeMonoid_antitone ht)
    (dualConeMonoid_antitone Finset.inter_subset_left)
    (dualConeMonoid_antitone Finset.inter_subset_right) v hv
  · exact monoidChartInclusion_isLocalizationMap k (dualConeMonoid_antitone ht)
      v hv hneg hclear
  · exact monoidChartInclusion_isLocalizationMap k
      (dualConeMonoid_antitone Finset.inter_subset_left)
      v (dualConeMonoid_antitone hs hv)
      (dualConeMonoid_antitone Finset.inter_subset_right hneg) hclearInter

end SmoothCompleteFan

end PaperVerification.ToricGeometry
