import Characterizations.Resolution.KoszulRows
import Characterizations.Resolution.Lift

/-! A graded double-complex staircase, proved by actual element lifting. -/
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Resolution MvPolynomial
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

namespace Resolution

lemma mapRows_comp {M N Q : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    [AddCommGroup Q] [Module (MvPolynomial V k) Q]
    (f : M →ₗ[MvPolynomial V k] N) (g : N →ₗ[MvPolynomial V k] Q)
    (i : ℕ) (z : KoszulRows (V := V) M i) :
    mapRows g i (mapRows f i z) = mapRows (g ∘ₗ f) i z := by
  apply Finsupp.ext
  intro s
  rfl

lemma homogeneousRows_lift {J L : Type} [Fintype J] [Fintype L]
    (f : (J → MvPolynomial V k) →ₗ[MvPolynomial V k] (L → MvPolynomial V k))
    (hf : IsHomogeneousMap f 1) {i t : ℕ}
    (z : KoszulRows (V := V) (L → MvPolynomial V k) i)
    (hz : HomogeneousRows i (t + 1) z)
    (hmem : ∀ s, z s ∈ LinearMap.range f) :
    ∃ w : KoszulRows (V := V) (J → MvPolynomial V k) i,
      HomogeneousRows i t w ∧ mapRows f i w = z := by
  have hh : ∀ s, ∃ x, IsHomogeneousVector x t ∧ f x = z s := by
    intro s
    apply exists_homogeneous_lift f hf ?_ (hmem s)
    intro j
    simpa only [Nat.add_comm] using hz s j
  choose w hw he using hh
  refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_⟩
  · intro s j
    exact hw s j
  · apply Finsupp.ext
    intro s
    exact he s

end Resolution

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)
include P

lemma row_differential_comp (n i : ℕ)
    (z : KoszulRows (V := V) (P.Index (n + 2) → MvPolynomial V k) i) :
    mapRows (P.differential n) i (mapRows (P.differential (n + 1)) i z) = 0 := by
  rw [mapRows_comp, P.differential_comp]
  ext s
  rfl

/-- The diagonal chase uses homogeneous lifts of the exact vertical complex and
actual positive-degree Koszul exactness in the horizontal direction. -/
lemma koszul_staircase (t : ℕ) (ht : 0 < t) : ∀ (i n : ℕ)
    (z : KoszulRows (V := V) (P.Index n → MvPolynomial V k) (i + 1)),
    HomogeneousRows (i + 1) t z →
    (∃ y : KoszulRows (V := V) (P.Index (n + 1) → MvPolynomial V k) i,
      HomogeneousRows i t y ∧ mapRows (P.differential n) i y =
        rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) i z) →
    ∃ (u : KoszulRows (V := V) (P.Index n → MvPolynomial V k) (i + 2))
      (v : KoszulRows (V := V) (P.Index (n + 1) → MvPolynomial V k) (i + 1)),
      z = rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1) u +
        mapRows (P.differential n) (i + 1) v := by
  intro i
  induction i with
  | zero =>
      intro n z hz hLift
      obtain ⟨y, hy, he⟩ := hLift
      obtain ⟨v, hv⟩ := freeRows_zero_boundary ht y hy
      have hcycle : rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) 0
          (z - mapRows (P.differential n) 1 v) = 0 := by
        rw [map_sub, rowDifferential_natural, hv, he, sub_self]
      obtain ⟨u, hu⟩ := freeRows_exact 0 _ hcycle
      refine ⟨u, v, ?_⟩
      rw [hu]
      exact (sub_add_cancel _ _).symm
  | succ i ih =>
      intro n z hz hLift
      obtain ⟨y, hy, he⟩ := hLift
      have hcycle : mapRows (P.differential n) i
          (rowDifferential (V := V) (k := k) (P.Index (n + 1) → MvPolynomial V k) i y) = 0 := by
        rw [← rowDifferential_natural, he, rowDifferential_square]
      have hmem : ∀ s, (rowDifferential (V := V) (k := k) (P.Index (n + 1) → MvPolynomial V k) i y) s ∈
          LinearMap.range (P.differential (n + 1)) := by
        intro s
        rw [P.exact_succ n]
        exact congrArg (fun z => z s) hcycle
      obtain ⟨w, hw, hwe⟩ := homogeneousRows_lift (P.differential (n + 1))
        (P.linear (n + 1)) _ (homogeneousRows_differential hy) hmem
      obtain ⟨u, v, huv⟩ := ih (n + 1) y hy ⟨w, hw, hwe⟩
      have hd : rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1) z =
          rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1)
            (mapRows (P.differential n) (i + 2) u) := by
        rw [← he, huv, map_add, P.row_differential_comp, add_zero, rowDifferential_natural]
      have hcycle' : rowDifferential (V := V) (k := k) (P.Index n → MvPolynomial V k) (i + 1)
          (z - mapRows (P.differential n) (i + 2) u) = 0 := by rw [map_sub, hd, sub_self]
      obtain ⟨w', hw'⟩ := freeRows_exact (i + 1) _ hcycle'
      refine ⟨w', u, ?_⟩
      rw [hw']
      exact (sub_add_cancel _ _).symm

lemma augmentation_rows_lift (i t : ℕ)
    (z : KoszulRows (V := V) (MvPolynomial V k) i)
    (hz : ∀ s, (z s).IsHomogeneous (d + t)) (hmem : ∀ s, z s ∈ I) :
    ∃ w : KoszulRows (V := V) (P.Index 0 → MvPolynomial V k) i,
      HomogeneousRows i t w ∧ mapRows P.augmentation i w = z := by
  have hh : ∀ s, ∃ x, IsHomogeneousVector x t ∧ P.augmentation x = z s := by
    intro s
    have hs : z s ∈ LinearMap.range P.augmentation := by rw [P.augmentation_range]; exact hmem s
    obtain ⟨x, hx⟩ := hs
    refine ⟨component t x, component_homogeneous _ _, ?_⟩
    rw [← P.augmentation_component, hx, homogeneousComponent_eq_self (hz s)]
  choose w hw he using hh
  refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_⟩
  · intro s j
    exact hw s j
  · apply Finsupp.ext
    intro s
    exact he s

lemma augmentationToIdeal_rows_comp (i : ℕ)
    (z : KoszulRows (V := V) (P.Index 1 → MvPolynomial V k) i) :
    mapRows P.augmentationToIdeal i (mapRows (P.differential 0) i z) = 0 := by
  apply Finsupp.ext
  intro s
  apply Subtype.ext
  exact LinearMap.congr_fun P.augmentation_comp (z s)

/-- Genuine coefficient Koszul cycles with coefficient degree strictly above the
linear generator degree are actual boundaries. -/
lemma idealRows_boundary_above (t : ℕ) (ht : 0 < t) (i : ℕ)
    (z : KoszulRows (V := V) I i) (hz : ∀ s, (z s).val.IsHomogeneous (d + t))
    (hcycle : ∀ j (he : i = j + 1), rowDifferential (V := V) (k := k) I j (he ▸ z) = 0) :
    ∃ w : KoszulRows (V := V) I (i + 1), rowDifferential (V := V) (k := k) I i w = z := by
  let incl : I →ₗ[MvPolynomial V k] MvPolynomial V k := I.subtype
  let zs := mapRows incl i z
  obtain ⟨x, hx, hxe⟩ := P.augmentation_rows_lift i t zs hz (fun s => (z s).property)
  have haug : mapRows P.augmentationToIdeal i x = z := by
    apply Finsupp.ext
    intro s
    apply Subtype.ext
    exact congrArg (fun w => w s) hxe
  cases i with
  | zero =>
      obtain ⟨u, hu⟩ := freeRows_zero_boundary ht x hx
      refine ⟨mapRows P.augmentationToIdeal 1 u, ?_⟩
      rw [rowDifferential_natural, hu, haug]
  | succ i =>
      have hz0 : rowDifferential (V := V) (k := k) I i z = 0 := hcycle i rfl
      have hcyclex : mapRows P.augmentation i
          (rowDifferential (V := V) (k := k) (P.Index 0 → MvPolynomial V k) i x) = 0 := by
        rw [← rowDifferential_natural, hxe]
        change rowDifferential (V := V) (k := k) (MvPolynomial V k) i (mapRows incl (i + 1) z) = 0
        rw [rowDifferential_natural, hz0, map_zero]
      have hmem : ∀ s, (rowDifferential (V := V) (k := k) (P.Index 0 → MvPolynomial V k) i x) s ∈
          LinearMap.range (P.differential 0) := by
        intro s
        rw [P.exact_zero]
        exact congrArg (fun w => w s) hcyclex
      obtain ⟨y, hy, hye⟩ := homogeneousRows_lift (P.differential 0) (P.linear 0) _
        (homogeneousRows_differential hx) hmem
      obtain ⟨u, v, huv⟩ := P.koszul_staircase t ht i 0 x hx ⟨y, hy, hye⟩
      refine ⟨mapRows P.augmentationToIdeal (i + 2) u, ?_⟩
      rw [rowDifferential_natural, ← haug, huv, map_add, P.augmentationToIdeal_rows_comp, add_zero]

end LinearResolution
end Characterizations
