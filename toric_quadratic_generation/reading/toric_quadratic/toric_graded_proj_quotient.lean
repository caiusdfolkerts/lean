module

public import PaperVerification.ToricProjectiveRatios
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

/-!
# Surjective graded homomorphisms and genuine closed Proj embeddings

A homogeneous element of a graded quotient has a homogeneous preimage:
take the required degree component of any preimage. Consequently the
degree-zero localized maps are surjective. The actual Proj morphism is
therefore a closed immersion on the standard affine open cover.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped Classical
open HomogeneousIdeal

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ→σ} {ℬ : ℕ→τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem graded_surjective_homogeneous_preimage (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) {d : ℕ} {b : B} (hb : b∈ℬ d) :
    ∃ a : A,a∈𝒜 d ∧ f a=b := by
  obtain ⟨a,rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a d,(DirectSum.decompose 𝒜 a d).property,?_⟩
  rw [f.map_directSumDecompose,DirectSum.decompose_of_mem_same ℬ hb]

theorem irrelevant_le_map_of_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) : ℬ₊≤𝒜₊.map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro d hd b hb
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_preimage f hf hb
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)

theorem homogeneousAway_map_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) {d : ℕ} {s : A} (hs : s∈𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨m,b,hb,rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_preimage f hf hb
  exact ⟨Away.mk 𝒜 hs m a ha,by simp⟩

/-- The literal Proj morphism of a graded quotient is a closed immersion.
The proof uses surjectivity of its actual affine coordinate homomorphisms. -/
theorem projMap_isClosedImmersion_of_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hf)) := by
  let h := irrelevant_le_map_of_surjective f hf
  let F := Proj.map f h
  let J := Σ d : {d : ℕ // 0<d}, {s : A // s∈𝒜 d.val}
  let U (j : J) := Proj.basicOpen 𝒜 j.2.val
  have hcover : (⨆ j,U j)=⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro d hd a ha
    exact Ideal.subset_span ⟨⟨⟨d,hd⟩,⟨a,ha⟩⟩,rfl⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U hcover
  intro j
  let eA := Proj.basicOpenIsoSpec 𝒜 j.2.val j.2.property j.1.property
  let eB := Proj.basicOpenIsoSpec ℬ (f j.2.val)
    (f.map_mem j.2.property) j.1.property
  let g := Spec.map (CommRingCat.ofHom (Away.map f j.2.val))
  letI : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective _
    (homogeneousAway_map_surjective f hf j.2.property)
  let r : (Proj.basicOpen ℬ (f j.2.val)).toScheme ⟶
      (Proj.basicOpen 𝒜 j.2.val).toScheme := F ∣_ U j
  have hsq : (eB.inv ≫ (Proj.basicOpen ℬ (f j.2.val)).ι) ≫ F =
      g ≫ eA.inv ≫ (U j).ι :=
    Proj.awayι_comp_map f h j.1.property j.2.val j.2.property
  have hcanonical : (Proj.basicOpen ℬ (f j.2.val)).ι ≫ F =
      (eB.hom ≫ g ≫ eA.inv) ≫ (U j).ι := by
    have h := congrArg (fun q => eB.hom ≫ q) hsq
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h
  have heq : r = eB.hom ≫ g ≫ eA.inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 j.2.val).ι).mp
    exact (morphismRestrict_ι F (U j)).trans hcanonical
  letI : IsClosedImmersion (g ≫ eA.inv) := IsClosedImmersion.comp g eA.inv
  have hclosed : IsClosedImmersion (eB.hom ≫ g ≫ eA.inv) :=
    IsClosedImmersion.comp eB.hom (g ≫ eA.inv)
  change IsClosedImmersion r
  exact heq.symm ▸ hclosed

variable {K : Type u} [Field K]

theorem homogeneousAwayEvaluation_gradedMap (f : 𝒜→+*ᵍℬ)
    (F : B→+*K) {d : ℕ} {s : A} (hs : s∈𝒜 d) (hne : F (f s)≠0) :
    (homogeneousAwayEvaluation ℬ F (f s) hne).comp (Away.map f s)=
      homogeneousAwayEvaluation 𝒜 (F.comp f.toRingHom) s hne := by
  ext z
  obtain ⟨m,a,ha,rfl⟩ := Away.mk_surjective 𝒜 hs z
  simp only [RingHom.comp_apply,Away.map_mk,homogeneousAwayEvaluation_mk]
  rfl

theorem projectiveFieldChart_gradedMap (f : 𝒜→+*ᵍℬ)
    (h : ℬ₊≤𝒜₊.map f) (F : B→+*K) {d : ℕ} {s : A}
    (hs : s∈𝒜 d) (hd : 0<d) (hne : F (f s)≠0) :
    projectiveFieldChart ℬ F (f s) (f.map_mem hs) hd hne≫Proj.map f h=
      projectiveFieldChart 𝒜 (F.comp f.toRingHom) s hs hd hne := by
  unfold projectiveFieldChart
  rw [Category.assoc,Proj.awayι_comp_map f h hd s hs,
    ← Category.assoc,← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (homogeneousAwayEvaluation_gradedMap f F hs hne)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.projMap_isClosedImmersion_of_surjective
