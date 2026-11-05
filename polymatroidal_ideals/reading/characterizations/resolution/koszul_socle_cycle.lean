import Characterizations.Resolution.KoszulRows

/-! The actual top Koszul socle cycle and its non-boundary property. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
namespace Characterizations.Resolution
open Classical MvPolynomial CommAlg.Koszul
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

lemma mapRows_injective {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (hf : Function.Injective f) (i : ℕ) :
    Function.Injective (mapRows f i) := by
  intro z w he
  apply Finsupp.ext
  intro s
  exact hf (congrArg (fun z => z s) he)

lemma polynomialRows_homogeneous_differential {i t : ℕ}
    (z : KoszulRows (V := V) (MvPolynomial V k) (i + 1))
    (hz : ∀ s, (z s).IsHomogeneous t) :
    ∀ s, (rowDifferential (V := V) (k := k) (MvPolynomial V k) i z s).IsHomogeneous (t + 1) := by
  let f : MvPolynomial V k →ₗ[MvPolynomial V k] (Unit → MvPolynomial V k) :=
    LinearMap.pi (fun _ => LinearMap.id)
  have hh : HomogeneousRows (i + 1) t (mapRows f (i + 1) z) := fun s _ => hz s
  have h := homogeneousRows_differential hh
  rw [rowDifferential_natural] at h
  exact fun s => h s ()

lemma polynomialRows_exact (i : ℕ)
    (z : KoszulRows (V := V) (MvPolynomial V k) (i + 1))
    (hz : rowDifferential (V := V) (k := k) (MvPolynomial V k) i z = 0) :
    ∃ w, rowDifferential (V := V) (k := k) (MvPolynomial V k) (i + 1) w = z := by
  let f : MvPolynomial V k →ₗ[MvPolynomial V k] (Unit → MvPolynomial V k) :=
    LinearMap.pi (fun _ => LinearMap.id)
  let g : (Unit → MvPolynomial V k) →ₗ[MvPolynomial V k] MvPolynomial V k :=
    LinearMap.proj ()
  have hcycle : rowDifferential (V := V) (k := k) (Unit → MvPolynomial V k) i
      (mapRows f (i + 1) z) = 0 := by rw [rowDifferential_natural, hz, map_zero]
  obtain ⟨w, hw⟩ := freeRows_exact i _ hcycle
  refine ⟨mapRows g (i + 2) w, ?_⟩
  rw [rowDifferential_natural, hw]
  apply Finsupp.ext
  intro s
  rfl

lemma polynomialRows_top_injective (m : ℕ) (hcard : Fintype.card V = m + 1)
    (z : KoszulRows (V := V) (MvPolynomial V k) (m + 1))
    (hz : rowDifferential (V := V) (k := k) (MvPolynomial V k) m z = 0) : z = 0 := by
  obtain ⟨w, hw⟩ := polynomialRows_exact m z hz
  haveI : IsEmpty (Set.powersetCard V (m + 2)) := ⟨fun s => by
    have hs := Finset.card_le_univ s.val
    rw [s.property, hcard] at hs
    omega⟩
  have hw0 : w = 0 := Subsingleton.elim _ _
  simpa only [hw0, map_zero] using hw.symm

variable (I : Ideal (MvPolynomial V k))

def socleBoundary {i : ℕ} (s : Set.powersetCard V (i + 1)) (y : MvPolynomial V k)
    (hy : ∀ j : s.val, X j.val * y ∈ I) : KoszulRows (V := V) I i :=
  ∑ j : s.val, Finsupp.single (eraseIndex s j)
    (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • ⟨X j.val * y, hy j⟩)

lemma socleBoundary_inclusion {i : ℕ} (s : Set.powersetCard V (i + 1)) (y : MvPolynomial V k)
    (hy : ∀ j : s.val, X j.val * y ∈ I) :
    mapRows I.subtype i (socleBoundary I s y hy) =
      rowDifferential (V := V) (k := k) (MvPolynomial V k) i (Finsupp.single s y) := by
  rw [socleBoundary, map_sum, coordinateDifferential_single]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mapRows_single]
  congr 1
  change TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • ((X j.val : MvPolynomial V k) • y) =
    (X j.val : MvPolynomial V k) • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • y)
  exact smul_comm _ _ _

lemma socleBoundary_homogeneous {i e : ℕ} (s : Set.powersetCard V (i + 1))
    (y : MvPolynomial V k) (hy : ∀ j : s.val, X j.val * y ∈ I)
    (hdegree : y.IsHomogeneous e) : ∀ a, ((socleBoundary I s y hy) a).val.IsHomogeneous (e + 1) := by
  have hz : ∀ a, (Finsupp.single s y a).IsHomogeneous e := by
    intro a
    by_cases he : s = a
    · simpa only [Finsupp.single_apply, he, ↓reduceIte] using hdegree
    · simp only [Finsupp.single_apply, he, ↓reduceIte]
      exact (homogeneousSubmodule V k e).zero_mem
  have hh := polynomialRows_homogeneous_differential (Finsupp.single s y) hz
  rw [← socleBoundary_inclusion I s y hy] at hh
  exact hh

lemma socleBoundary_cycle {i : ℕ} (s : Set.powersetCard V (i + 1))
    (y : MvPolynomial V k) (hy : ∀ j : s.val, X j.val * y ∈ I) :
    ∀ j (he : i = j + 1), rowDifferential (V := V) (k := k) I j
      (he ▸ socleBoundary I s y hy) = 0 := by
  intro j he
  subst i
  apply mapRows_injective I.subtype Subtype.val_injective j
  rw [map_zero, ← rowDifferential_natural, socleBoundary_inclusion, rowDifferential_square]

/-- The top socle boundary cannot be a boundary inside the ideal: an incoming
chain would have to have the missing socle element as its top coefficient. -/
lemma socleBoundary_not_boundary (m : ℕ) (hcard : Fintype.card V = m + 1)
    (y : MvPolynomial V k) (hy : ∀ j : V, X j * y ∈ I) (hout : y ∉ I) :
    ¬ ∃ w : KoszulRows (V := V) I (m + 1),
      rowDifferential (V := V) (k := k) I m w =
        socleBoundary I (⟨Finset.univ, hcard⟩ : Set.powersetCard V (m + 1)) y
          (fun j => hy j.val) := by
  rintro ⟨w, hw⟩
  let s : Set.powersetCard V (m + 1) := ⟨Finset.univ, hcard⟩
  have hz : rowDifferential (V := V) (k := k) (MvPolynomial V k) m
      (mapRows I.subtype (m + 1) w - Finsupp.single s y) = 0 := by
    rw [map_sub, rowDifferential_natural, hw, socleBoundary_inclusion, sub_self]
  have he := polynomialRows_top_injective m hcard _ hz
  have hrow : mapRows I.subtype (m + 1) w = Finsupp.single s y := sub_eq_zero.mp he
  have hs := congrArg (fun z => z s) hrow
  simp only [mapRows_apply, Submodule.subtype_apply, Finsupp.single_eq_same] at hs
  exact hout (hs ▸ (w s).property)

end Characterizations.Resolution
