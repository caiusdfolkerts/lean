import CommAlg.KoszulComplex.GradedTor

/-! # Completeness and independence of the genuine Tor multigrading

Every derived Tor class is a finite sum of the degree components defined in `GradedTor`.
The projections onto distinct components annihilate one another, so this is a genuine
internal grading of the actual derived tensor module.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Distinct multidegrees have orthogonal chain projections. -/
lemma homogeneousInclusion_retraction_ne (B : Family V) (a b : Exponent V)
    (hab : a ≠ b) :
    homogeneousInclusion (k := k) B a ≫ homogeneousRetraction (k := k) B b = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact Grading.projection_eq_zero (Ne.symm hab) z.property

/-- The chain endomorphism projecting to one degree and including it again. -/
def homogeneousProjector (B : Family V) (a : Exponent V) :
    underlyingComplex (k := k) B ⟶ underlyingComplex (k := k) B :=
  homogeneousRetraction (k := k) B a ≫ homogeneousInclusion (k := k) B a

@[simp] lemma homogeneousProjector_f (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousProjector (k := k) B a).f i =
      ModuleCat.ofHom (homogeneousProjection (k := k) B a i) := rfl

/-- Every actual Koszul homology class is a finite sum of its homogeneous projections. -/
lemma homogeneous_homology_decomposition (B : Family V) (i : ℕ)
    (x : (underlyingComplex (k := k) B).homology i) :
    ∃ s : Finset (Exponent V),
      ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i x = x := by
  let K := underlyingComplex (k := k) B
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance x
  let s := ((monomialCoefficientBasis (k := k) B i).repr (K.iCycles i z)).support.image
    monomialDegree
  have hz : ∑ a ∈ s, HomologicalComplex.cyclesMap
      (homogeneousProjector (k := k) B a) i z = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    rw [map_sum]
    calc
      ∑ a ∈ s, K.iCycles i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) =
          ∑ a ∈ s, homogeneousProjection (k := k) B a i (K.iCycles i z) := by
        apply Finset.sum_congr rfl
        intro a ha
        have h := congrArg (fun f : K.cycles i ⟶ K.X i => f z)
          (HomologicalComplex.cyclesMap_i (homogeneousProjector (k := k) B a) i)
        exact h
      _ = _ := homogeneous_decomposition B i (K.iCycles i z)
  refine ⟨s, ?_⟩
  calc
    ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i
        (K.homologyπ i z) =
        ∑ a ∈ s, K.homologyπ i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg (fun f : K.cycles i ⟶ K.homology i => f z)
        (HomologicalComplex.homologyπ_naturality (homogeneousProjector (k := k) B a) i)
    _ = K.homologyπ i
        (∑ a ∈ s, HomologicalComplex.cyclesMap
          (homogeneousProjector (k := k) B a) i z) := (map_sum _ _ _).symm
    _ = _ := congrArg (K.homologyπ i) hz

variable [Nontrivial k]

/-- A nonzero multigraded Betti component forces the genuine derived Tor module to be nonzero. -/
lemma derivedTor_nonzero_of_graded (B : Family V) (a : Exponent V) (i : ℕ)
    (h : GradedBettiNonzero (k := k) B a i) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) := by
  intro hz
  letI : Subsingleton (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  apply h
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply Subtype.ext
  exact Subsingleton.elim (α := finitePolynomialTor i
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) x.val y.val

end CommAlg.Koszul
