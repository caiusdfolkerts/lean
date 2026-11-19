module

public import Papers.GraphicalZonotopes.Minkowski

@[expose] public section

/-! Normalization, translations, and genuine geometric Minkowski indecomposability. -/
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem subsetSum_sub (x y : V → ℝ) (S : Finset V) :
    subsetSum (x - y) S = subsetSum x S - subsetSum y S := by
  simp [subsetSum, sum_sub_distrib]

def normalize (z : SetFunction V) : SetFunction V := z - modular (fun v => z {v})

theorem normalize_translationNormalized {z : SetFunction V} (hz : Normalized z) :
    TranslationNormalized (normalize z) := by
  constructor
  · simpa [Normalized, normalize, modular] using hz
  · intro v
    simp [normalize, modular, subsetSum]

theorem delta_normalize (z : SetFunction V) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (normalize z) u v S = delta z u v S := by
  rw [normalize, delta_sub, delta_modular _ huv hu hv, sub_zero]

theorem Supermodular.normalize {z : SetFunction V} (hz : Supermodular z) :
    Supermodular (normalize z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_normalize z huv hu hv]
  exact hz.elemental u v huv S hu hv

theorem normalize_add (z w : SetFunction V) : normalize (z + w) = normalize z + normalize w := by
  funext S
  simp only [normalize, Pi.sub_apply, Pi.add_apply, modular, subsetSum, sum_add_distrib]
  ring

theorem normalize_eq_self {z : SetFunction V} (hz : TranslationNormalized z) :
    normalize z = z := by
  funext S
  simp [normalize, modular, subsetSum, hz.2]

theorem recover_normalize (z : SetFunction V) :
    z = normalize z + modular (fun v => z {v}) := by
  rw [normalize, sub_add_cancel]

theorem basePolytope_translate (z : SetFunction V) (t : V → ℝ) :
    basePolytope (z + modular t) = ({t} : Set (V → ℝ)) + basePolytope z := by
  ext x
  constructor
  · intro hx
    refine ⟨t, rfl, x - t, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [subsetSum_sub]
        have h := hx.1
        change subsetSum x univ = z univ + subsetSum t univ at h
        linarith
      · intro S
        rw [subsetSum_sub]
        have h := hx.2 S
        change z S + subsetSum t S ≤ subsetSum x S at h
        linarith
    · abel
  · rintro ⟨t', ht, y, hy, rfl⟩
    have ht' : t' = t := Set.mem_singleton_iff.mp ht
    subst t'
    refine ⟨?_, ?_⟩
    · rw [subsetSum_add, hy.1]
      change _ = z univ + subsetSum t univ
      ring
    · intro S
      rw [subsetSum_add]
      change z S + subsetSum t S ≤ _
      linarith [hy.2 S]

/-- Extremality in the normalized supermodular cone, expressed by its actual
additive decomposition property. -/
def ExtremeSupermodular (z : SetFunction V) : Prop :=
  TranslationNormalized z ∧ Supermodular z ∧ z ≠ 0 ∧
    ∀ f g : SetFunction V,
      TranslationNormalized f → TranslationNormalized g →
      Supermodular f → Supermodular g → f + g = z →
      ∃ a : ℝ, 0 ≤ a ∧ f = a • z

/-- Every compact convex Minkowski summand is a nonnegative homothetic copy.
This quantifies over actual subsets of real coordinate space. -/
def MinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),
    IsCompact P → IsCompact R → Convex ℝ P → Convex ℝ R →
    P + R = Q → ∃ (a : ℝ) (t : V → ℝ), 0 ≤ a ∧ P = ({t} : Set (V → ℝ)) + a • Q

/-- Cone extremality implies geometric indecomposability with no assumption
that the summands are already generalized permutahedra. -/
theorem ExtremeSupermodular.minkowskiIndecomposable {z : SetFunction V}
    (hz : ExtremeSupermodular z) : MinkowskiIndecomposable (basePolytope z) := by
  have hne := basePolytope_nonempty hz.1.1 hz.2.1
  refine ⟨hne, ?_⟩
  intro P R hP hR hPc hRc heq
  obtain ⟨x, hx⟩ := hne
  rw [← heq] at hx
  obtain ⟨p, hp, r, hr, hpr⟩ := hx
  have hnP : P.Nonempty := ⟨p, hp⟩
  have hnR : R.Nonempty := ⟨r, hr⟩
  have hnP' := lowerSupport_normalized hP hnP
  have hnR' := lowerSupport_normalized hR hnR
  have hsP := summand_lowerSupport_supermodular hz.1.1 hz.2.1 hP hR hnP hnR heq
  have heq' : R + P = basePolytope z := by rw [add_comm]; exact heq
  have hsR := summand_lowerSupport_supermodular hz.1.1 hz.2.1 hR hP hnR hnP heq'
  have hsum : lowerSupport P + lowerSupport R = z := by
    rw [← lowerSupport_add hP hR hnP hnR, heq, lowerSupport_basePolytope hz.1.1 hz.2.1]
  have hnormsum : normalize (lowerSupport P) + normalize (lowerSupport R) = z := by
    rw [← normalize_add, hsum, normalize_eq_self hz.1]
  obtain ⟨a, ha, hscale⟩ := hz.2.2.2 _ _ (normalize_translationNormalized hnP')
    (normalize_translationNormalized hnR') hsP.normalize hsR.normalize hnormsum
  refine ⟨a, (fun v => lowerSupport P {v}), ha, ?_⟩
  conv_lhs => rw [summand_eq_basePolytope hz.1.1 hz.2.1 hP hR hPc hnP hnR heq]
  conv_lhs => rw [recover_normalize (lowerSupport P)]
  rw [basePolytope_translate, hscale, basePolytope_smul hz.1.1 hz.2.1 ha]

end GraphicalZonotopes
