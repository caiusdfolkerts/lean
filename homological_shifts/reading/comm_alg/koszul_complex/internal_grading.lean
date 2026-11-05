import CommAlg.KoszulComplex.DerivedDecomposition
import Mathlib.Algebra.DirectSum.Module

/-! # The multigraded pieces form an actual internal direct sum of derived Tor -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- The canonical projection from derived Tor onto a homogeneous homology group. -/
def fromDerivedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ⟶
      (homogeneousComplex (k := k) B a).homology i :=
  (coefficientTorIso (k := k) B i).hom ≫
    HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i

lemma toDerivedTor_from_same (B : Family V) (a : Exponent V) (i : ℕ) :
    toDerivedTor (k := k) B a i ≫ fromDerivedTor (k := k) B a i = 𝟙 _ := by
  simp only [toDerivedTor, fromDerivedTor, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp, homogeneousInclusion_retraction,
    HomologicalComplex.homologyMap_id]

lemma toDerivedTor_from_ne (B : Family V) (a b : Exponent V) (i : ℕ) (hab : a ≠ b) :
    toDerivedTor (k := k) B a i ≫ fromDerivedTor (k := k) B b i = 0 := by
  simp only [toDerivedTor, fromDerivedTor, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp,
    homogeneousInclusion_retraction_ne B a b hab, HomologicalComplex.homologyMap_zero]

/-- The genuine degree projection, as an endomorphism of actual derived Tor. -/
def derivedProjection (B : Family V) (a : Exponent V) (i : ℕ) :=
  (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i).hom

lemma derivedProjection_self (B : Family V) (a : Exponent V) (i : ℕ)
    {x} (hx : x ∈ gradedTor (k := k) B a i) : derivedProjection (k := k) B a i x = x := by
  obtain ⟨y, rfl⟩ := hx
  change (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i)
    (toDerivedTor (k := k) B a i y) = toDerivedTor (k := k) B a i y
  rw [← ModuleCat.comp_apply, ← Category.assoc, toDerivedTor_from_same, Category.id_comp]

lemma derivedProjection_other (B : Family V) (a b : Exponent V) (i : ℕ)
    (hab : a ≠ b) {x} (hx : x ∈ gradedTor (k := k) B b i) :
    derivedProjection (k := k) B a i x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i)
    (toDerivedTor (k := k) B b i y) = 0
  rw [← ModuleCat.comp_apply, ← Category.assoc,
    toDerivedTor_from_ne B b a i (Ne.symm hab), zero_comp]
  rfl

lemma gradedTor_independent (B : Family V) (i : ℕ) :
    iSupIndep (fun a : Exponent V => gradedTor (k := k) B a i) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hs a ha
  have h := congrArg (derivedProjection (k := k) B a i) hs
  rw [map_sum, map_zero] at h
  rw [Finset.sum_eq_single a] at h
  · rwa [derivedProjection_self B a i (hv a ha)] at h
  · intro b hb hba
    exact derivedProjection_other B a b i (Ne.symm hba) (hv b hb)
  · exact fun hnot => (hnot ha).elim

/-- The degree pieces used to define Betti support are a genuine internal direct sum of derived Tor. -/
theorem gradedTor_isInternal (B : Family V) (i : ℕ) :
    DirectSum.IsInternal (fun a : Exponent V => gradedTor (k := k) B a i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedTor_independent B i) (iSup_gradedTor B i)

end CommAlg.Koszul
