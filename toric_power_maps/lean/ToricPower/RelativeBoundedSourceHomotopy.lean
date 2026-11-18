module

public import ToricPower.RelativeHomPrecompQuasiIso

/-!
# Relative Hom assembly with a bounded source

The relative null-homotopy construction can start from a lower bound on
the source instead of a lower bound on the target. This is the version
needed for a finite Čech or cellular resolution and an arbitrary,
possibly unbounded coefficient complex.

All comparisons below are the actual signed Hom-complex maps. In
particular, no boundedness condition is imposed on the target complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive CochainComplex HomComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]

open Cochain.InductionUp in
/-- Row exactness contracts every map from a source with a lower bound,
even when the target has terms in arbitrarily negative degrees. -/
theorem nonempty_homotopy_zero_of_boundedSource_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q)) (f : K ⟶ L) :
    Nonempty (Homotopy f 0) := by
  let X (n : ℕ) : Set (Cochain K L (-1)) :=
    Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n+d-1))
  let x₀ : X 0 := ⟨0, fun p q hpq hp =>
    IsZero.eq_of_src (K.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
  let φ (n : ℕ) (α : X n) : X (n+1) :=
    ⟨_, (relativeHomotopyStep f α.1 (n+d-1) ((n+1 : ℕ)+d-1)
      (by lia) (hrow _) α.2).choose_spec⟩
  have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d+k) :=
    fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  let k₀ := (n-d+1).toNat
  rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n-1) (n+1) rfl (by lia),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n-1) (n+1) rfl (by lia),
    limitSequence_eqUpTo φ hφ x₀ k₀ n (n-1) (by lia) (by lia),
    limitSequence_eqUpTo φ hφ x₀ k₀ (n+1) n (by lia) (by lia)]

/-- The contraction kills actual morphisms in the homotopy category. -/
theorem homotopyHom_eq_zero_of_boundedSource_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q))
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) : f = 0 := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
  exact (HomotopyCategory.quotient_map_eq_zero_iff f).mpr
    (nonempty_homotopy_zero_of_boundedSource_rightHomExact K L d hrow f)

/-- Source shifts are transferred to the unrestricted target by the
actual shift adjunction. -/
theorem shiftedHomotopyHom_eq_zero_of_boundedSource_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q)) (n : ℤ)
    (f : ((HomotopyCategory.quotient C (.up ℤ)).obj K)⟦n⟧ ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) : f = 0 := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  letI : (shiftEquiv (HomotopyCategory C (.up ℤ)) n).functor.Additive :=
    inferInstanceAs (CategoryTheory.Functor.Additive
      (CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) n))
  let adj := (shiftEquiv (HomotopyCategory C (.up ℤ)) n).toAdjunction
  let e := (Q.commShiftIso (-n)).app L
  have eq := homotopyHom_eq_zero_of_boundedSource_rightHomExact K (L⟦-n⟧) d
    (fun q => hrow (q + -n)) (adj.homEquiv _ _ f ≫ e.inv)
  apply (adj.homEquiv _ _).injective
  rw [adj.homAddEquiv_zero]
  apply (cancel_mono e.inv).mp
  simpa only [zero_comp] using eq

/-- An actual augmentation cone with a lower bound and exact Hom rows
makes precomposition bijective for every target. -/
theorem cone_boundedSource_rowExact_precomp_bijective
    {K L : CochainComplex C ℤ} (ε : K ⟶ L)
    (X : CochainComplex C ℤ) (d : ℤ) [(mappingCone ε).IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact (mappingCone ε) (X.X q)) :
    Function.Bijective (fun f : (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj X =>
      (HomotopyCategory.quotient C (.up ℤ)).map ε ≫ f) := by
  let T := mappingCone.triangleh ε
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished ε
  constructor
  · intro a b hab
    change T.mor₁ ≫ a = T.mor₁ ≫ b at hab
    have closed : T.mor₁ ≫ (a-b) = 0 := by
      simpa only [comp_sub, sub_eq_zero] using hab
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT (a-b) closed
    have gz := homotopyHom_eq_zero_of_boundedSource_rightHomExact
      (mappingCone ε) X d hrow g
    apply sub_eq_zero.mp
    rw [hg, gz, comp_zero]
  · intro a
    have closed : T.invRotate.mor₁ ≫ a = 0 :=
      shiftedHomotopyHom_eq_zero_of_boundedSource_rightHomExact
        (mappingCone ε) X d hrow (-1) _
    obtain ⟨g, hg⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a closed
    exact ⟨g, hg.symm⟩

/-- The literal precomposition comparison for a bounded augmentation
cone and an arbitrary coefficient complex. -/
theorem augmentation_linearHomPrecomp_quasiIso_of_boundedSource
    (R : Type r) [CommRing R] [Linear R C]
    (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (Z : C)
    (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj Z) [Epi (ε.f 0)]
    (X : CochainComplex C ℤ) (d : ℤ) [(mappingCone ε).IsStrictlyGE d]
    (h : ∀ q, AugmentationHomExact K Z (X.X q) ε) :
    QuasiIso (linearHomComplexPrecomp R ε X) := by
  apply linearHomComplexPrecomp_quasiIso_of_homotopy_bijective
  intro n
  apply cone_boundedSource_rowExact_precomp_bijective ε (X⟦n⟧) d
  intro q
  exact rightHomExact_cone_of_single_precomp ε (X.X (q+n))
    (augmentation_single_precomp_bijective K Z (X.X (q+n)) ε (h (q+n)))

/-- Finite projective resolutions compute the actual Hom complex on
every row-acyclic coefficient complex, with no target truncation. -/
theorem projective_linearHomPrecomp_quasiIso_of_boundedSource
    (R : Type r) [CommRing R] [Linear R C]
    {Z : C} (P : ProjectiveResolution Z)
    (X : CochainComplex C ℤ) (d : ℤ)
    [(mappingCone (projectiveCochainAugmentation P)).IsStrictlyGE d]
    (h : ∀ q (n : ℕ), (projectiveCoefficientComplex R P (X.X q)).ExactAt (n+1)) :
    QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P) X) :=
  augmentation_linearHomPrecomp_quasiIso_of_boundedSource R (projectiveCochain P) Z
    (projectiveCochainAugmentation P) X d
    (fun q => projectiveCochain_augmentationHomExact R P (X.X q) (h q))

/-- Every cohomology class vanishes under the same bounded-source
condition, including classes in negative degrees. -/
theorem homClass_eq_zero_of_boundedSource_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q))
    (n : ℤ) (x : CohomologyClass K L n) : x = 0 := by
  apply (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).injective
  rw [map_zero]
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
    ((CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)) x)
  rw [← hf]
  apply (HomotopyCategory.quotient_map_eq_zero_iff f).mpr
  exact nonempty_homotopy_zero_of_boundedSource_rightHomExact K (L⟦n⟧) d
    (fun q => hrow (q+n)) f

/-- The whole signed Hom complex is acyclic. -/
theorem linearHomComplex_acyclic_of_boundedSource_rightHomExact
    (R : Type r) [CommRing R] [Linear R C]
    (K L : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q)) :
    (linearHomComplex R K L).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  haveI : Subsingleton (CohomologyClass K L n) :=
    ⟨fun x y => (homClass_eq_zero_of_boundedSource_rightHomExact K L d hrow n x).trans
      (homClass_eq_zero_of_boundedSource_rightHomExact K L d hrow n y).symm⟩
  haveI : Subsingleton ((linearHomComplex R K L).homology n) :=
    (HomComplex.homologyLinearEquiv R K L n).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end ToricPower

end
