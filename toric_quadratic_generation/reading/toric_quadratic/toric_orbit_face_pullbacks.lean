module

public import PaperVerification.ToricOrbitChartMaps

@[expose] public section

/-!
# Actual pullback squares for orbit charts

The denominator removing a smooth cone face has pairing zero on the
retained rays and pairing one on the removed rays. If the orbit cone is
retained, the denominator descends to precisely the quotient-star face
denominator. If an orbit ray is removed, that denominator is killed by
the orbit quotient, so the preimage of the face chart is empty.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators

variable {n : ℕ}

theorem integerPairing_neg (u m : Lattice n) :
    integerPairing u (-m) = -integerPairing u m := by
  simp [integerPairing]

theorem integerPairing_nsmul (u m : Lattice n) (N : ℕ) :
    integerPairing u (N • m) = (N : ℤ) * integerPairing u m := by
  simp only [integerPairing,Pi.smul_apply,nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem exists_face_character_denominator_exact
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (hts : t⊆s) :
    ∃ v : Lattice n, v∈dualConeMonoid s ∧ -v∈dualConeMonoid t ∧
      (∀ u∈s,integerPairing u v=if u∈t then 0 else 1) ∧
      (∀ m∈dualConeMonoid t,∃ N : ℕ,m+N • v∈dualConeMonoid s) := by
  obtain ⟨b,J,rfl⟩ := «Σ».smooth s hs
  let I := basisRayIndices b t
  have hI : I.image b=t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I⊆J := by
    intro i hi
    have hbi : b i∈t := hI ▸ Finset.mem_image.mpr ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp (hts hbi)
    exact b.injective hji ▸ hj
  let v := faceDenominatorExponent (integralDualBasis b) I J
  refine ⟨v,?_,?_,?_,?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) I J
  · rw [← hI,dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) I J
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate,faceDenominatorExponent_repr]
    have hbit : b i∈t ↔ i∈I := by simp [I,basisRayIndices]
    by_cases hiI : i∈I
    · simp [hiI,hbit.mpr hiI]
    · have hnot : b i∉t := fun h => hiI (hbit.mp h)
      simp [hi,hiI,hnot]
  · intro m hm
    rw [← hI,dualConeMonoid_basis_eq] at hm
    obtain ⟨N,hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hIJ m hm
    exact ⟨N,(dualConeMonoid_basis_eq b J).symm ▸ hN⟩

end SmoothCompleteFan

variable (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

theorem projected_face_denominator
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t)
    (v : Lattice n) (hv : v∈dualConeMonoid s) (hnv : -v∈dualConeMonoid t)
    (hzero : ∀ u∈I.image b,integerPairing u v=0)
    (hclear : ∀ m∈dualConeMonoid t,∃ N : ℕ,m+N • v∈dualConeMonoid s) :
    faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I s) ∧
      -faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I t) ∧
      ∀ m∈dualConeMonoid (orbitQuotientCone b I t),∃ N : ℕ,
        m+N • faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I s) := by
  refine ⟨faceCharacterProjection_mem_quotientDualCone b I s ⟨⟨v,hv⟩,hzero⟩,?_,?_⟩
  · have hzneg : ∀ u∈I.image b,integerPairing u (-v)=0 := by
      intro u hu
      rw [integerPairing_neg,hzero u hu,neg_zero]
    simpa only [map_neg] using
      faceCharacterProjection_mem_quotientDualCone b I t ⟨⟨-v,hnv⟩,hzneg⟩
  · intro m hm
    have hlift := faceTangentLattice_mem_dualCone b I t ⟨m,hm⟩
    obtain ⟨N,hN⟩ := hclear (faceTangentLattice b I m) hlift
    have hz : ∀ u∈I.image b,
        integerPairing u (faceTangentLattice b I m+N • v)=0 := by
      intro u hu
      rw [integerPairing_add,faceTangentLattice_annihilates b I m u hu,
        integerPairing_nsmul,hzero u hu,mul_zero,zero_add]
    have hproj := faceCharacterProjection_mem_quotientDualCone b I s
      ⟨⟨faceTangentLattice b I m+N • v,hN⟩,hz⟩
    exact ⟨N,by simpa only [map_add,map_nsmul,faceCharacterProjection_tangent] using hproj⟩

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (k : Type*) [CommRing k]

theorem orbitQuotientChart_face_isPullback
    {s t : Finset (Lattice n)} (hs : s∈«Σ».cones) (hts : t⊆s)
    (hIt : I.image b⊆t) :
    IsPullback (orbitQuotientChartMap k b I t hIt)
      (coneChartFaceMap k (orbitQuotientCone_mono b I hts))
      (coneChartFaceMap k hts)
      (orbitQuotientChartMap k b I s (hIt.trans hts)) := by
  obtain ⟨v,hv,hnv,hpair,hclear⟩ :=
    «Σ».exists_face_character_denominator_exact s t hs hts
  have hzero : ∀ u∈I.image b,integerPairing u v=0 := by
    intro u hu
    rw [hpair u (hts (hIt hu)),if_pos (hIt hu)]
  obtain ⟨hp,hnp,hpclear⟩ := projected_face_denominator b I hts hIt v hv hnv hzero hclear
  let hloc := monoidChartInclusion_isLocalizationMap k (dualConeMonoid_antitone hts)
    v hv hnv hclear
  let hploc := monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
    (faceCharacterProjection b I v) hp hnp hpclear
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
    (faceCharacterProjection b I v) hp hploc
  letI : IsOpenImmersion (coneChartFaceMap k hts) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone hts) v hv hloc
  letI : IsOpenImmersion (coneChartFaceMap k (orbitQuotientCone_mono b I hts)) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
      (faceCharacterProjection b I v) hp hploc
  apply IsOpenImmersion.isPullback
  · exact orbitQuotientChartMap_naturality k b I hts hIt
  · rw [show (coneChartFaceMap k hts).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) from
      monoidChartSpecMap_opensRange_of_isLocalizationMap k
        (dualConeMonoid_antitone hts) v hv hloc]
    rw [show (coneChartFaceMap k (orbitQuotientCone_mono b I hts)).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k
          (dualConeMonoid (orbitQuotientCone b I s)) (faceCharacterProjection b I v) hp) from
      monoidChartSpecMap_opensRange_of_isLocalizationMap k
        (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
        (faceCharacterProjection b I v) hp hploc]
    change PrimeSpectrum.basicOpen
        (orbitQuotientAlgebraMap k b I s (hIt.trans hts)
          (chartCharacter k (dualConeMonoid s) v hv)) =
      PrimeSpectrum.basicOpen (chartCharacter k
        (dualConeMonoid (orbitQuotientCone b I s)) (faceCharacterProjection b I v) hp)
    apply congrArg PrimeSpectrum.basicOpen
    apply Subtype.ext
    rw [orbitQuotientAlgebraMap_character,dif_pos hzero]
    rfl

/-- A cone face omitting an orbit ray has empty preimage in the orbit
chart. This is proved by the literal denominator being mapped to zero. -/
theorem orbitQuotientChart_preimage_face_empty
    {s t : Finset (Lattice n)} (hs : s∈«Σ».cones) (hts : t⊆s)
    (hIs : I.image b⊆s) (hnot : ¬I.image b⊆t) :
    (orbitQuotientChartMap k b I s hIs) ⁻¹ᵁ
      ((coneChartFaceMap k hts).opensRange
        (H := «Σ».coneChartFaceMap_isOpenImmersion k s t hs hts)) = ⊥ := by
  letI : IsOpenImmersion (coneChartFaceMap k hts) :=
    «Σ».coneChartFaceMap_isOpenImmersion k s t hs hts
  obtain ⟨v,hv,hnv,hpair,hclear⟩ :=
    «Σ».exists_face_character_denominator_exact s t hs hts
  have hnonzero : ¬∀ u∈I.image b,integerPairing u v=0 := by
    intro h
    apply hnot
    intro u hu
    by_contra hut
    have he := hpair u (hIs hu)
    rw [if_neg hut,h u hu] at he
    norm_num at he
  let hloc := monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hnv hclear
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  rw [show (coneChartFaceMap k hts).opensRange =
      PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) from
    monoidChartSpecMap_opensRange_of_isLocalizationMap k
      (dualConeMonoid_antitone hts) v hv hloc]
  change PrimeSpectrum.basicOpen (orbitQuotientAlgebraMap k b I s hIs
    (chartCharacter k (dualConeMonoid s) v hv)) = ⊥
  have hmap : orbitQuotientAlgebraMap k b I s hIs
      (chartCharacter k (dualConeMonoid s) v hv)=0 := by
    apply Subtype.ext
    rw [orbitQuotientAlgebraMap_character,dif_neg hnonzero]
    rfl
  rw [hmap,PrimeSpectrum.basicOpen_zero]

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitQuotientChart_face_isPullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitQuotientChart_preimage_face_empty
