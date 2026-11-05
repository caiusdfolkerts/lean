import CommAlg.KoszulComplex.TorGrading

/-! # Every genuine derived Tor class is a finite sum of multigraded classes -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- A canonical component of a derived Tor element, regarded as a member of its true degree submodule. -/
def derivedComponent (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))))
    (a : Exponent V) : gradedTor (k := k) B a i :=
  ⟨toDerivedTor (k := k) B a i
    (HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i
      ((coefficientTorIso (k := k) B i).hom x)), ⟨_, rfl⟩⟩

/-- Completeness of the multigrading: every actual derived Tor class is a finite sum of its components. -/
lemma derivedTor_decomposition (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))) :
    ∃ s : Finset (Exponent V), ∑ a ∈ s, (derivedComponent (k := k) B i x a).val = x := by
  obtain ⟨s, hs⟩ := homogeneous_homology_decomposition (k := k) B i
    ((coefficientTorIso (k := k) B i).hom x)
  refine ⟨s, ?_⟩
  apply (coefficientTorIso (k := k) B i).toLinearEquiv.injective
  change (coefficientTorIso (k := k) B i).hom _ = _
  rw [map_sum]
  calc
    ∑ a ∈ s, (coefficientTorIso (k := k) B i).hom
        (derivedComponent (k := k) B i x a).val =
      ∑ a ∈ s, HomologicalComplex.homologyMap
        (homogeneousProjector (k := k) B a) i ((coefficientTorIso (k := k) B i).hom x) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [derivedComponent, toDerivedTor, ModuleCat.comp_apply,
        ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
        homogeneousProjector, HomologicalComplex.homologyMap_comp, Category.assoc,
        Iso.inv_hom_id_assoc, Category.comp_id]
    _ = _ := hs

/-- The actual degree submodules span all of derived Tor. -/
lemma iSup_gradedTor (B : Family V) (i : ℕ) :
    (⨆ a : Exponent V, gradedTor (k := k) B a i) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
  rw [← hs]
  apply Submodule.sum_mem
  intro a ha
  exact (le_iSup (fun a : Exponent V => gradedTor (k := k) B a i) a)
    (derivedComponent (k := k) B i x a).property

/-- Nonzero derived Tor has some nonzero multidegree, and conversely. -/
lemma derivedTor_nonzero_iff (B : Family V) (i : ℕ) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ↔
      ∃ a, GradedBettiNonzero (k := k) B a i := by
  constructor
  · contrapose!
    intro h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro x y
    have hx : x = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i x a) 0)
    have hy : y = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i y
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i y a) 0)
    exact hx.trans hy.symm
  · rintro ⟨a, ha⟩
    exact derivedTor_nonzero_of_graded (k := k) B a i ha

end CommAlg.Koszul
