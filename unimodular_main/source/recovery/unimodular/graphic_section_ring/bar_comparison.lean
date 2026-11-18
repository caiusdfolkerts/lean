module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.AlternatingFormsFilteredComparison
public import Recovery.Unimodular.KoszulSupport.PaperVerification.WeightedBarDegrees

/-!
# Leading maps for the genuine reduced bar differential

A coefficient-level leading multiplication formula is lifted through the
literal recursively defined bar differential. No condition on normal words,
permutations of factors, or transitivity of monomial compatibility is used.
The auxiliary height is independent of the ordinary internal degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicSectionRing.BarComparison

open PaperVerification.Fermion.BasisFiltered
open PaperVerification.AlternatingForms.FilteredComparison
open PaperVerification.FilteredComplex
open PaperVerification.ReducedBarBasis
open PaperVerification.AugmentedAlgebraBasis

section LinearShift

variable {K M N I J : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (b : Module.Basis I K M) (w : I → ℕ)
  (c : Module.Basis J K N) (v : J → ℕ)

/-- Homogeneous basis formulas shift the genuine finite-support filtration. -/
theorem hasTop_linearMap_shift (f : M →ₗ[K] N) (s : ℕ)
    (hf : ∀ i, Homogeneous c v (w i + s) (f (b i)))
    {d : ℕ} {x x₀ : M} (hx : HasTop b w d x x₀) :
    HasTop c v (d + s) (f x) (f x₀) := by
  classical
  have hterm (i : I) (hi : i ∈ (b.repr x).support) :
      HasTop c v (d + s) (f (b i)) (f (component b w d (b i))) := by
    have hle := hx.1 i (Finsupp.mem_support_iff.mp hi)
    by_cases he : w i = d
    · refine ⟨?_, ?_⟩
      · simpa only [he] using homogeneous_bound c v (hf i)
      · rw [component_of_homogeneous c v (hf i), if_pos (congrArg (· + s) he.symm),
          component_of_homogeneous b w (homogeneous_basis b w i), if_pos he.symm]
    · have hlt : w i + s < d + s := Nat.add_lt_add_right (lt_of_le_of_ne hle he) s
      refine ⟨bound_mono c v (Nat.add_le_add_right hle s)
        (homogeneous_bound c v (hf i)), ?_⟩
      rw [component_eq_zero_of_bound_lt c v hlt (homogeneous_bound c v (hf i)),
        component_of_homogeneous b w (homogeneous_basis b w i), if_neg (Ne.symm he), map_zero]
  have hs := HasTop.sum c v (b.repr x).support
    (fun i => b.repr x i • f (b i))
    (fun i => b.repr x i • f (component b w d (b i))) (d + s)
    (fun i hi => HasTop.smul c v (hterm i hi) (b.repr x i))
  have hexp : (∑ i ∈ (b.repr x).support, b.repr x i • b i) = x := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr x
  have hleft : (∑ i ∈ (b.repr x).support, b.repr x i • f (b i)) = f x := by
    simpa only [map_sum, map_smul] using congrArg f hexp
  have hright : (∑ i ∈ (b.repr x).support,
      b.repr x i • f (component b w d (b i))) = f x₀ := by
    simpa only [map_sum, map_smul, hx.2] using congrArg (fun y => f (component b w d y)) hexp
  simpa only [hleft, hright] using hs

theorem hasTop_sub {d : ℕ} {x x₀ y y₀ : M}
    (hx : HasTop b w d x x₀) (hy : HasTop b w d y y₀) :
    HasTop b w d (x - y) (x₀ - y₀) :=
  ⟨bound_sub b w hx.1 hy.1, by rw [map_sub, hx.2, hy.2]⟩

end LinearShift

section Bar

variable {K A A₀ I : Type*} [CommRing K] [Ring A] [Algebra K A]
  [Ring A₀] [Algebra K A₀]
  (B : Module.Basis (Option I) K A) (B₀ : Module.Basis (Option I) K A₀)
  (w : I → ℕ)

abbrev wordWeight (L : List I) : ℕ := PaperVerification.WeightedBar.totalDegree w L

abbrev wordBasis : Module.Basis (List I) K (List I →₀ K) := Finsupp.basisSingleOne
abbrev coefficientBasis : Module.Basis I K (I →₀ K) := Finsupp.basisSingleOne

/-- Prefixing a positive basis element shifts the actual height by its height. -/
theorem hasTop_prepend (i : I) {d : ℕ} {x x₀ : List I →₀ K}
    (hx : HasTop (wordBasis (K := K)) (wordWeight w) d x x₀) :
    HasTop (wordBasis (K := K)) (wordWeight w) (w i + d)
      (prepend i x) (prepend i x₀) := by
  have hf (L : List I) : Homogeneous (wordBasis (K := K)) (wordWeight w)
      (wordWeight w L + w i) (prepend i (wordBasis (K := K) L)) := by
    simpa only [wordBasis, Finsupp.coe_basisSingleOne, prefix_single,
      wordWeight, PaperVerification.WeightedBar.totalDegree_cons, Nat.add_comm] using
      (homogeneous_basis (wordBasis (K := K)) (wordWeight w) (i :: L))
  simpa only [Nat.add_comm] using
    hasTop_linearMap_shift (wordBasis (K := K)) (wordWeight w)
      (wordBasis (K := K)) (wordWeight w) (prepend i) (w i) hf hx

/-- Appending a fixed tensor tail also shifts the genuine height exactly. -/
theorem hasTop_appendTail (L : List I) {d : ℕ} {x x₀ : I →₀ K}
    (hx : HasTop (coefficientBasis (K := K)) w d x x₀) :
    HasTop (wordBasis (K := K)) (wordWeight w) (d + wordWeight w L)
      (appendTail L x) (appendTail L x₀) := by
  apply hasTop_linearMap_shift (coefficientBasis (K := K)) w
    (wordBasis (K := K)) (wordWeight w) (appendTail L) (wordWeight w L) ?_ hx
  intro i
  simpa only [coefficientBasis, wordBasis, Finsupp.coe_basisSingleOne, appendTail_single,
    wordWeight, PaperVerification.WeightedBar.totalDegree_cons] using
    (homogeneous_basis (wordBasis (K := K)) (wordWeight w) (i :: L))

/-- The literal bar differential has the asserted leading differential on
every actual basis word, provided the product coefficients do. -/
theorem differentialBasis_hasTop
    (hproduct : ∀ i j, HasTop (coefficientBasis (K := K)) w (w i + w j)
      (productCoefficients B i j) (productCoefficients B₀ i j))
    (L : List I) :
    HasTop (wordBasis (K := K)) (wordWeight w) (wordWeight w L)
      (differentialBasis B L) (differentialBasis B₀ L) := by
  induction L with
  | nil => exact HasTop.zero _ _ _
  | cons i L ih =>
    cases L with
    | nil =>
      simpa only [differentialBasis, merge_single, mergeBasis, smul_zero,
        map_zero, sub_zero] using
        (HasTop.zero (wordBasis (K := K)) (wordWeight w) (wordWeight w [i]))
    | cons j L =>
      change HasTop (wordBasis (K := K)) (wordWeight w) (wordWeight w (i :: j :: L))
        (merge B i (Finsupp.single (j :: L) 1) - prepend i (differentialBasis B (j :: L)))
        (merge B₀ i (Finsupp.single (j :: L) 1) - prepend i (differentialBasis B₀ (j :: L)))
      simp only [merge_single, one_smul, mergeBasis]
      apply hasTop_sub
      · simpa only [wordWeight, PaperVerification.WeightedBar.totalDegree_cons,
          Nat.add_assoc] using hasTop_appendTail w L (hproduct i j)
      · exact hasTop_prepend w i ih

/-- Full finite-support leading-map identity for the actual bar operators. -/
theorem differential_hasLeadingMap
    (hproduct : ∀ i j, HasTop (coefficientBasis (K := K)) w (w i + w j)
      (productCoefficients B i j) (productCoefficients B₀ i j)) :
    HasLeadingMap (wordBasis (K := K)) (wordWeight w)
      (wordBasis (K := K)) (wordWeight w) (differential B) (differential B₀) := by
  apply leadingMap_of_basis
  intro L
  simpa only [wordBasis, Finsupp.coe_basisSingleOne, differential_single, one_smul] using
    differentialBasis_hasTop B B₀ w hproduct L

/-- The resulting leading differential is homogeneous for the actual height. -/
theorem leading_differential_preservesComponents
    (hproduct : ∀ i j, HasTop (coefficientBasis (K := K)) w (w i + w j)
      (productCoefficients B i j) (productCoefficients B₀ i j)) :
    PreservesComponents (wordBasis (K := K)) (wordWeight w)
      (wordBasis (K := K)) (wordWeight w) (differential B₀) := by
  apply preservesComponents_of_basis
  intro L
  have ht := differentialBasis_hasTop B B₀ w hproduct L
  simp only [wordBasis, Finsupp.coe_basisSingleOne, differential_single, one_smul]
  rw [← ht.2]
  exact homogeneous_component (wordBasis (K := K)) (wordWeight w) (wordWeight w L)
      (differentialBasis B L)

#print axioms hasTop_linearMap_shift
#print axioms differentialBasis_hasTop
#print axioms differential_hasLeadingMap
#print axioms leading_differential_preservesComponents

end Bar
end Unimodular.GraphicSectionRing.BarComparison
