import Characterizations.Resolution.DeleteVariable

/-! Genuine linear free resolutions descend along a variable regular on the ideal quotient. -/
noncomputable section
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)

private lemma augmentation_variable_saturated (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    ∀ y : Unit → MvPolynomial V k,
      (X j : MvPolynomial V k) • y ∈ LinearMap.range (scalarFree P.augmentation) →
        y ∈ LinearMap.range (scalarFree P.augmentation) := by
  intro y hy
  obtain ⟨x,hx⟩ := hy
  have hmul : X j * y () ∈ I := by
    have hm : P.augmentation x ∈ I := (P.augmentationToIdeal x).property
    have he := congrFun hx ()
    change P.augmentation x = X j * y () at he
    rwa [← he]
  have hyI : y () ∈ LinearMap.range P.augmentation := by
    rw [P.augmentation_range]
    exact hI (y ()) hmul
  obtain ⟨z,hz⟩ := hyI
  refine ⟨z,?_⟩
  funext a
  cases a
  exact hz

/-- Evaluation at zero in one variable preserves exactness whenever that
variable is regular on the quotient by the resolved ideal. The resulting
object is again a literal exact complex of finite free modules. -/
def specializeQuotient {W : Type u}
    (φ : MvPolynomial V k →ₐ[k] MvPolynomial W k)
    (hφ : Function.Surjective φ) (j : V) (ht : φ (X j) = 0)
    (hker : ∀ p, φ p = 0 → ∃ q, p = X j * q)
    (hhom : ∀ {p : MvPolynomial V k} {d}, p.IsHomogeneous d → (φ p).IsHomogeneous d)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map φ.toRingHom I) d where
  Index := P.Index
  finite := P.finite
  differential n := specialize φ.toRingHom (P.differential n)
  augmentation := specializeScalar φ.toRingHom P.augmentation
  augmentation_range := specializeScalar_range _ hφ
    P.augmentation I P.augmentation_range
  exact_zero := by
    have h := specialize_exact φ.toRingHom hφ (X j) ht
      hker (P.differential 0) (scalarFree P.augmentation)
      (by simpa only [scalarFree_ker] using P.exact_zero)
      (P.augmentation_variable_saturated j hI)
    exact h.trans (specializeScalar_ker _ P.augmentation)
  exact_succ n := by
    apply specialize_exact φ.toRingHom hφ (X j) ht hker _ _ (P.exact_succ n)
    cases n with
    | zero =>
      exact saturated_range_of_exact (P.differential 0) (scalarFree P.augmentation)
        (by simpa only [scalarFree_ker] using P.exact_zero) (X j)
        (MvPolynomial.isRegular_X.left)
    | succ n =>
      exact saturated_range_of_exact (P.differential (n+1)) (P.differential n)
        (P.exact_succ n) (X j) (MvPolynomial.isRegular_X.left)
  linear n := by
    intro a b
    rw [specialize_single]
    exact hhom (P.linear n a b)
  augmentation_homogeneous b := by
    rw [specializeScalar_single]
    exact hhom (P.augmentation_homogeneous b)

def deleteVariable (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map (Resolution.deleteVariable (k:=k) j).toRingHom I) d :=
  P.specializeQuotient (Resolution.deleteVariable j) (deleteVariable_surjective j)
    j (deleteVariable_X j) (deleteVariable_kernel j)
    (deleteVariable_homogeneous j) hI

def descendAlong {W : Type u} (f : W → V) (hf : Function.Injective f)
    (j : V) (hrange : ∀ i, i ∈ Set.range f ↔ i ≠ j)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    LinearResolution (Ideal.map (MvPolynomial.killCompl hf).toRingHom I) d := by
  apply P.specializeQuotient (MvPolynomial.killCompl hf)
    (fun p => ⟨MvPolynomial.rename f p,MvPolynomial.killCompl_rename_app hf p⟩)
    j ?_ (killCompl_kernel_of_range f hf j hrange) (killCompl_homogeneous f hf) hI
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range hf 1 (a:=j)
  · simp
  · simpa only [hrange, ne_eq, not_not] using (rfl : j = j)

end LinearResolution

theorem HasLinearResolution.deleteVariable
    {I : Ideal (MvPolynomial V k)} (h : HasLinearResolution I) (j : V)
    (hI : ∀ p : MvPolynomial V k, X j * p ∈ I → p ∈ I) :
    HasLinearResolution (Ideal.map (Resolution.deleteVariable (k:=k) j).toRingHom I) := by
  obtain ⟨d,⟨P⟩⟩ := h
  exact ⟨d,⟨P.deleteVariable j hI⟩⟩

end Characterizations
