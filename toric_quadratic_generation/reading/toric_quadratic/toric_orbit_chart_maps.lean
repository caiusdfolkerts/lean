module

public import PaperVerification.ToricOrbitStarIndex

@[expose] public section

/-! # Naturality and gluing of actual orbit chart quotient morphisms -/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped Classical

variable (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M]

@[simp] theorem monoidChartAlgebraEquiv_single_character
    (S : AddSubmonoid M) (m : S) :
    monoidChartAlgebraEquiv k S (single m 1) = chartCharacter k S m.val m.property :=
  Subtype.ext (monoidChartMap_single k S m 1)

@[simp] theorem monoidChartAlgebraEquiv_symm_character
    (S : AddSubmonoid M) (m : M) (hm : m∈S) :
    (monoidChartAlgebraEquiv k S).symm (chartCharacter k S m hm) = single ⟨m,hm⟩ 1 := by
  apply (monoidChartAlgebraEquiv k S).injective
  simp only [AlgEquiv.apply_symm_apply,monoidChartAlgebraEquiv_single_character]

theorem chartAlgHom_ext_characters (S : AddSubmonoid M)
    {A : Type*} [Semiring A] [Algebra k A]
    (F G : monoidChartAlgebra k S →ₐ[k] A)
    (h : ∀ m (hm : m∈S),F (chartCharacter k S m hm)=G (chartCharacter k S m hm)) :
    F=G := by
  ext f
  obtain ⟨g,rfl⟩ := (monoidChartAlgebraEquiv k S).surjective f
  induction g using AddMonoidAlgebra.induction_on with
  | of m =>
      simpa only [AddMonoidAlgebra.of_apply,toAdd_ofAdd,monoidChartAlgebraEquiv_single_character] using
        h m.val m.property
  | add f g hf hg => simp only [map_add,hf,hg]
  | smul a f hf => simp only [map_smul,hf]

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} (k : Type*) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

theorem orbitQuotientAlgebraMap_character
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) (m : Lattice n)
    (hm : m∈dualConeMonoid s) :
    ((orbitQuotientAlgebraMap k b I s hIs (chartCharacter k (dualConeMonoid s) m hm) :
        monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I s))) :
          AddMonoidAlgebra k (Lattice (n-I.card))) =
      if h : ∀ u∈I.image b,integerPairing u m=0
      then single (faceCharacterProjection b I m) 1 else 0 := by
  simp only [orbitQuotientAlgebraMap,AlgHom.comp_apply,AlgEquiv.coe_algHom,
    monoidChartAlgebraEquiv_symm_character]
  by_cases h : ∀ u∈I.image b,integerPairing u m=0
  · have hmem : (⟨m,hm⟩ : dualConeMonoid s)∈orbitCharacterFace s (I.image b) := h
    rw [additiveFaceRetraction_single_of_mem k _ _ _ hmem,
      AddMonoidAlgebra.domCongr_single,dif_pos h]
    exact monoidChartMap_single k _ _ 1
  · have hmem : (⟨m,hm⟩ : dualConeMonoid s)∉orbitCharacterFace s (I.image b) := h
    rw [additiveFaceRetraction_single_of_not_mem k _ _ _ hmem,map_zero,map_zero,dif_neg h]
    rfl

theorem orbitQuotientCone_mono {s t : Finset (Lattice n)} (hts : t⊆s) :
    orbitQuotientCone b I t ⊆ orbitQuotientCone b I s :=
  Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) hts)

/-- Restriction along an actual cone face commutes with killing the
characters positive on the orbit cone. -/
theorem orbitQuotientAlgebraMap_naturality
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t) :
    (orbitQuotientAlgebraMap k b I t hIt).comp
        (monoidChartInclusion k (dualConeMonoid_antitone hts)) =
      (monoidChartInclusion k (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))).comp
        (orbitQuotientAlgebraMap k b I s (hIt.trans hts)) := by
  apply chartAlgHom_ext_characters
  intro m hm
  apply Subtype.ext
  simp only [AlgHom.comp_apply,monoidChartInclusion_character,
    monoidChartInclusion_coe,orbitQuotientAlgebraMap_character]

def orbitQuotientChartMap (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    coneChart k (orbitQuotientCone b I s) ⟶ coneChart k s :=
  Spec.map (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I s hIs).toRingHom)

instance orbitQuotientChartMap_closed (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    IsClosedImmersion (orbitQuotientChartMap k b I s hIs) :=
  orbitQuotientChartMap_isClosedImmersion k b I s hIs

set_option maxHeartbeats 2000000 in
@[reassoc] theorem orbitQuotientChartMap_naturality
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t) :
    coneChartFaceMap k (orbitQuotientCone_mono b I hts) ≫
        orbitQuotientChartMap k b I s (hIt.trans hts) =
      orbitQuotientChartMap k b I t hIt ≫ coneChartFaceMap k hts := by
  exact (Spec.map_comp
    (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I s (hIt.trans hts)).toRingHom)
    (CommRingCat.ofHom (monoidChartInclusion k
      (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))).toRingHom)).symm.trans
    ((congrArg (fun f : monoidChartAlgebra k (dualConeMonoid s) →ₐ[k]
        monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I t)) =>
          Spec.map (CommRingCat.ofHom f.toRingHom))
      (orbitQuotientAlgebraMap_naturality k b I hts hIt).symm).trans
      (Spec.map_comp
        (CommRingCat.ofHom (monoidChartInclusion k (dualConeMonoid_antitone hts)).toRingHom)
        (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I t hIt).toRingHom)))

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (hF : I.image b∈«Σ».cones)

/-- The actual quotient charts map compatibly into the actual fan scheme. -/
def orbitClosureCocone : Cocone («Σ».orbitChartDiagram b I hF k) where
  pt := «Σ».fanScheme k
  ι :=
    { app s := orbitQuotientChartMap k b I s.val s.property.2 ≫
        «Σ».fanChartMap k ⟨s.val,s.property.1⟩
      naturality := by
        intro s t f
        change coneChartFaceMap k (orbitQuotientCone_mono b I (leOfHom f)) ≫
          (orbitQuotientChartMap k b I t.val t.property.2 ≫
            «Σ».fanChartMap k ⟨t.val,t.property.1⟩) =
          (orbitQuotientChartMap k b I s.val s.property.2 ≫
            «Σ».fanChartMap k ⟨s.val,s.property.1⟩) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc,
          orbitQuotientChartMap_naturality k b I (leOfHom f) s.property.2,
          Category.assoc]
        exact congrArg
          (fun q => orbitQuotientChartMap k b I s.val s.property.2 ≫ q)
          («Σ».fanChartMap_naturality k
            (s := ⟨s.val, s.property.1⟩) (t := ⟨t.val, t.property.1⟩)
            (leOfHom f)) }

/-- The global morphism from the actual quotient-star scheme. Closedness
and its identification with the invariant orbit closure are proved using
the actual local quotient squares; they are not included in this definition. -/
def orbitClosureMap :
    («Σ».completeQuotientStarFan b I hF).fanScheme k ⟶ «Σ».fanScheme k :=
  («Σ».orbitChartColimitIsoFan b I hF k).inv ≫
    colimit.desc («Σ».orbitChartDiagram b I hF k) («Σ».orbitClosureCocone k b I hF)

@[reassoc (attr := simp)] theorem orbitClosureMap_chart
    (s : «Σ».OrbitConeIndex b I) :
    («Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s) ≫ «Σ».orbitClosureMap k b I hF =
      orbitQuotientChartMap k b I s.val s.property.2 ≫
        «Σ».fanChartMap k ⟨s.val,s.property.1⟩ := by
  rw [← «Σ».orbitChartColimitIsoFan_ι b I hF k s]
  change (colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫
      («Σ».orbitChartColimitIsoFan b I hF k).hom) ≫
    («Σ».orbitChartColimitIsoFan b I hF k).inv ≫
      colimit.desc («Σ».orbitChartDiagram b I hF k) («Σ».orbitClosureCocone k b I hF) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫ q)
      (Iso.hom_inv_id_assoc («Σ».orbitChartColimitIsoFan b I hF k)
        (colimit.desc («Σ».orbitChartDiagram b I hF k)
          («Σ».orbitClosureCocone k b I hF)))).trans
      (colimit.ι_desc («Σ».orbitClosureCocone k b I hF) s))

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.orbitQuotientAlgebraMap_naturality
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_chart
