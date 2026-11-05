import CommAlg.Simplicial.Filling
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.SingleHomology

/-! # Actual categorical homology of the augmented exterior chains -/

noncomputable section

namespace CommAlg.Simplicial

open CategoryTheory CategoryTheory.Limits

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The usual signed boundary, restricted to the actual face-chain submodules. -/
def chainDifferential {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    Chains (k := k) K (i + 1) →ₗ[k] Chains (k := k) K i :=
  (boundary.domRestrict (Chains K (i + 1))).codRestrict _
    (fun z => boundary_mem hK z.property)

@[simp] lemma chainDifferential_val {K : Finset V → Prop} (hK : Downward K) (i : ℕ)
    (z : Chains (k := k) K (i + 1)) :
    (chainDifferential hK i z).val = boundary z.val := rfl

lemma chainDifferential_comp {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    chainDifferential (k := k) hK i ∘ₗ chainDifferential hK (i + 1) = 0 := by
  ext z
  exact boundary_boundary z.val

/-- This is the genuine augmented simplicial chain complex, with the empty face in degree zero. -/
def chainComplex {K : Finset V → Prop} (hK : Downward K) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (Chains (k := k) K i))
    (fun i => ModuleCat.ofHom (chainDifferential hK i))
    (fun i => ModuleCat.hom_ext (chainDifferential_comp hK i))

@[simp] lemma chainComplex_d {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).d (i + 1) i = ModuleCat.ofHom (chainDifferential hK i) := by
  simp [chainComplex]

lemma chainComplex_exactAt_succ_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).ExactAt (i + 1) ↔ ExactIn (k := k) K (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [chainComplex_d]
  change (∀ z : Chains (k := k) K (i + 1), chainDifferential hK i z = 0 →
    ∃ y : Chains (k := k) K (i + 2), chainDifferential hK (i + 1) y = z) ↔ _
  constructor
  · intro h z hz hc
    obtain ⟨y, hy⟩ := h ⟨z, hz⟩ (Subtype.ext hc)
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h z hz
    obtain ⟨y, hy, heq⟩ := h z.val z.property (congrArg Subtype.val hz)
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

lemma chainComplex_exactAt_zero_iff {K : Finset V → Prop} (hK : Downward K) :
    (chainComplex (k := k) hK).ExactAt 0 ↔ ExactIn (k := k) K 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  rw [chainComplex_d, (chainComplex (k := k) hK).shape 0 0 (by simp)]
  change (∀ z : Chains (k := k) K 0, (0 : Chains (k := k) K 0) = 0 →
    ∃ y : Chains (k := k) K 1, chainDifferential hK 0 y = z) ↔ _
  constructor
  · intro h z hz hc
    obtain ⟨y, hy⟩ := h ⟨z, hz⟩ rfl
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h z hz
    obtain ⟨y, hy, heq⟩ := h z.val z.property (boundary_zero_degree_zero z.property)
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

lemma chainComplex_exactAt_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).ExactAt i ↔ ExactIn (k := k) K i := by
  cases i with
  | zero => exact chainComplex_exactAt_zero_iff hK
  | succ i => exact chainComplex_exactAt_succ_iff hK i

/-- The explicit cycle/nonboundary condition is equivalent to nonvanishing of actual homology. -/
lemma homology_nonzero_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    ¬ IsZero ((chainComplex (k := k) hK).homology i) ↔ NonzeroHomology (k := k) K i := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, chainComplex_exactAt_iff,
    nonzeroHomology_iff_not_exactIn]

end CommAlg.Simplicial
