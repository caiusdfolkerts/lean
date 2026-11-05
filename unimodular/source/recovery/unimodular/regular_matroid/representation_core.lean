module

public import Mathlib.Data.Real.Basic

public import Recovery.Unimodular.ProductVectorMatroid
public import Continuation.Runtime.MinorRepresentation
public import Recovery.Unimodular.PriorExtensions.SignedSumsRegular
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section

/-! Recovered ordinary representation machinery. All original mathematical
sections below are byte-preserved; the imported geometry is unnecessary.
Fresh native checking and the private dependency audit remain required. -/

set_option maxHeartbeats 0

/-! The ordinary-minor primitives have their unique owner in
`Continuation.Runtime.MinorRepresentation`; the unchanged observation is retained. -/
namespace Unimodular.RepresentationBridge
#print axioms exists_quotient_representation_of_minor
end Unimodular.RepresentationBridge

/-! ## Exact source section: Continuation/Runtime/VectorBases.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-! # Bases of the ordinary vector matroid and square minors -/

open Set Function Submodule

namespace Unimodular.RepresentationBridge

theorem ofFamily_isBase_iff (K : Type*) {E W : Type*}
    [Field K] [AddCommGroup W] [Module K W] (v : E → W) (I : Set E) :
    (VectorMatroid.ofFamily (K := K) v).IsBase I ↔
      LinearIndepOn K v I ∧ ∀ e, v e ∈ span K (v '' I) := by
  constructor
  · intro hB
    have hli := (VectorMatroid.ofFamily_indep v I).mp hB.indep
    refine ⟨hli, fun e ↦ ?_⟩
    by_contra hn
    have heI : e ∉ I := fun he ↦ hn (subset_span (mem_image_of_mem v he))
    have hins : LinearIndepOn K v (insert e I) :=
      (linearIndepOn_insert heI).mpr ⟨hli, hn⟩
    exact heI (hB.mem_of_insert_indep ((VectorMatroid.ofFamily_indep v _).mpr hins))
  · rintro ⟨hli, hspan⟩
    apply ((VectorMatroid.ofFamily_indep v I).mpr hli).isBase_of_maximal
    intro J hJ hIJ
    apply subset_antisymm hIJ
    intro e heJ
    by_contra heI
    have hins := ((VectorMatroid.ofFamily_indep v J).mp hJ).mono (insert_subset heJ hIJ)
    exact ((linearIndepOn_insert heI).mp hins).2 (hspan e)

theorem ofFamily_isBase_iff_card (K : Type*) {E : Type*}
    [Field K] [DecidableEq E] {n : ℕ} (v : E → Fin n → K)
    (hfull : span K (range v) = ⊤) (I : Finset E) :
    (VectorMatroid.ofFamily (K := K) v).IsBase (I : Set E) ↔
      LinearIndepOn K v (I : Set E) ∧ I.card = n := by
  classical
  rw [ofFamily_isBase_iff]
  constructor
  · rintro ⟨hli, hspan⟩
    have hs : span K (v '' (I : Set E)) = ⊤ := by
      apply le_antisymm le_top
      rw [← hfull]
      exact span_le.mpr (by rintro x ⟨e, rfl⟩; exact hspan e)
    let b : Module.Basis I K (Fin n → K) :=
      Module.Basis.mk hli (by rw [Set.image_eq_range] at hs; exact hs.ge)
    refine ⟨hli, ?_⟩
    simpa using (Module.finrank_eq_card_basis b).symm
  · rintro ⟨hli, hcard⟩
    have hs : span K (v '' (I : Set E)) = ⊤ := by
      rw [Set.image_eq_range]
      exact hli.span_eq_top_of_card_eq_finrank' (by simpa using hcard)
    refine ⟨hli, fun e ↦ ?_⟩
    rw [hs]
    trivial

theorem ofFamily_isBase_range_iff_det (K : Type*) {E : Type*}
    [Field K] {n : ℕ} (v : E → Fin n → K) (f : Fin n → E)
    (hf : Function.Injective f) :
    (VectorMatroid.ofFamily (K := K) v).IsBase (Set.range f) ↔
      Matrix.det (fun i j ↦ v (f j) i) ≠ 0 := by
  have hdet : LinearIndependent K (v ∘ f) ↔
      Matrix.det (fun i j ↦ v (f j) i) ≠ 0 := by
    let A : Matrix (Fin n) (Fin n) K := fun i j ↦ v (f j) i
    change LinearIndependent K A.col ↔ A.det ≠ 0
    exact (Matrix.linearIndependent_col_iff_isUnit (A := A)).trans
      ((Matrix.isUnit_iff_isUnit_det A).trans isUnit_iff_ne_zero)
  constructor
  · intro hB
    exact hdet.mp ((linearIndepOn_range_iff hf v).mp
      ((VectorMatroid.ofFamily_indep v _).mp hB.indep))
  · intro hd
    have hli := hdet.mpr hd
    rw [ofFamily_isBase_iff]
    refine ⟨(linearIndepOn_range_iff hf v).mpr hli, fun e ↦ ?_⟩
    have hs : span K (range (v ∘ f)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp)
    rw [← Set.range_comp, hs]
    trivial

def enumList {m : ℕ} (s : Finset (Fin m)) : List (Fin m) :=
  (List.finRange m).filter (· ∈ s)

lemma enumList_length {m : ℕ} (s : Finset (Fin m)) :
    (enumList s).length = s.card := by
  have := ((List.finRange m).filter (· ∈ s)).toFinset_card_of_nodup
    ((List.nodup_finRange m).filter _)
  simpa [enumList] using this.symm

def enumerate {m n : ℕ} (s : Finset (Fin m)) (h : s.card = n) : Fin n → Fin m :=
  fun i ↦ (enumList s)[i.val]'(by rw [enumList_length, h]; exact i.isLt)

lemma enumerate_injective {m n : ℕ} (s : Finset (Fin m)) (h : s.card = n) :
    Function.Injective (enumerate s h) := by
  intro i j hij
  apply Fin.ext
  exact ((List.nodup_finRange m).filter _).getElem_inj_iff.mp hij

lemma range_enumerate {m n : ℕ} (s : Finset (Fin m)) (h : s.card = n) :
    Set.range (enumerate s h) = (s : Set (Fin m)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    have hm : enumerate s h i ∈ enumList s := List.getElem_mem ..
    simpa [enumList] using hm
  · intro hx
    have hm : x ∈ enumList s := by simpa [enumList] using hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hm
    refine ⟨⟨i, by simpa [enumList_length, h] using hi⟩, ?_⟩
    exact hxi

end Unimodular.RepresentationBridge
end

/-! ## Exact source section: Continuation/Runtime/DualRepresentation.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# The dual of a finite vector matroid is represented over the same field

The representation consists of coordinate evaluations on the actual relation
space of the original family. No regularity or matrix normal form is assumed.
Independence of a set of evaluations is equivalent to surjectivity of the
coordinate projection of the relation space, hence to spanning by the
complementary original columns. This is exactly ordinary matroid duality.
-/

noncomputable section
open Set Submodule Function
open scoped Matroid Classical

namespace Unimodular.RepresentationBridge

variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

/-- The labelled coordinate evaluations on the relation space. -/
def dualFamily (v : E → V) : E → (LinearMap.ker (Fintype.linearCombination K v) → K) :=
  fun e x ↦ x.val e

def relationProjection (v : E → V) (I : Set E) :
    LinearMap.ker (Fintype.linearCombination K v) →ₗ[K] (I → K) where
  toFun x i := x.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def extendCoefficients (I : Set E) (c : I → K) : E → K := by
  classical
  exact fun e ↦ if h : e ∈ I then c ⟨e, h⟩ else 0

private theorem linearCombination_extend (v : E → V) (I : Set E) (c : I → K) :
    Fintype.linearCombination K v (extendCoefficients I c) =
      ∑ i : I, c i • v i := by
  classical
  rw [Fintype.linearCombination_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun e ↦ e ∈ I)]
  simp [extendCoefficients]
  apply Finset.sum_eq_zero
  intro i _
  simp [i.property]

private theorem linearCombination_mem_complement (v : E → V) (I : Set E)
    (c : E → K) (hc : ∀ e ∈ I, c e = 0) :
    Fintype.linearCombination K v c ∈ span K (v '' Iᶜ) := by
  classical
  apply Submodule.sum_mem
  intro e _
  by_cases he : e ∈ I
  · simp [hc e he]
  · exact smul_mem _ _ (subset_span ⟨e, he, rfl⟩)

theorem relationProjection_surjective_iff (v : E → V) (I : Set E) :
    Surjective (relationProjection (K := K) v I) ↔ ∀ e, v e ∈ span K (v '' Iᶜ) := by
  classical
  constructor
  · intro h e
    obtain ⟨z, hz⟩ := h (fun i ↦ (Pi.single e (1 : K) : E → K) i.val)
    let c : E → K := Pi.single e 1 - z.val
    have hc : ∀ i ∈ I, c i = 0 := by
      intro i hi
      have hi' := congrFun hz ⟨i, hi⟩
      change z.val i = (Pi.single e (1 : K) : E → K) i at hi'
      simp [c, hi']
    have hm := linearCombination_mem_complement v I c hc
    have heq : Fintype.linearCombination K v c = v e := by
      change Fintype.linearCombination K v (Pi.single e 1 - z.val) = v e
      rw [map_sub, Fintype.linearCombination_apply_single]
      simp only [LinearMap.mem_ker.mp z.property, sub_zero, one_smul]
    rwa [heq] at hm
  · intro h c
    let x : E → K := extendCoefficients I c
    have hx : Fintype.linearCombination K v x ∈ span K (v '' Iᶜ) := by
      apply Submodule.sum_mem
      intro e _
      exact smul_mem _ _ (h e)
    rw [Set.image_eq_range] at hx
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    let y : E → K := extendCoefficients Iᶜ d
    have hy : Fintype.linearCombination K v y = Fintype.linearCombination K v x := by
      rw [linearCombination_extend]
      refine Eq.trans ?_ hd
      exact congrArg (fun F : Fintype ↥(Iᶜ : Set E) ↦
        @Finset.sum ↥(Iᶜ : Set E) V _ (@Finset.univ ↥(Iᶜ : Set E) F)
          (fun i ↦ d i • v i))
        (Subsingleton.elim _ _)
    refine ⟨⟨x - y, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hy, sub_self]
    · ext i
      simp [relationProjection, x, y, extendCoefficients, i.property]

theorem dualFamily_indep_iff (v : E → V) (I : Set E) :
    LinearIndepOn K (dualFamily (K := K) v) I ↔ ∀ e, v e ∈ span K (v '' Iᶜ) := by
  classical
  change LinearIndependent K (fun i : I ↦ dualFamily (K := K) v i.val) ↔ _
  rw [← span_flip_eq_top_iff_linearIndependent]
  change span K (Set.range (relationProjection (K := K) v I)) = ⊤ ↔ _
  rw [← LinearMap.coe_range, Submodule.span_eq, LinearMap.range_eq_top]
  exact relationProjection_surjective_iff (K := K) v I

theorem complementary_span_iff_base (v : E → V) (I : Set E) :
    (∀ e, v e ∈ span K (v '' Iᶜ)) ↔
      ∃ B, (VectorMatroid.ofFamily (K := K) v).IsBase B ∧ Disjoint I B := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := (VectorMatroid.ofFamily (K := K) v).exists_isBasis Iᶜ
    have heq : span K (v '' B) = span K (v '' Iᶜ) := VectorMatroid.isBasis_span_eq v hB
    refine ⟨B, (ofFamily_isBase_iff K v B).mpr ⟨?_, ?_⟩, ?_⟩
    · exact (VectorMatroid.ofFamily_indep v B).mp hB.indep
    · intro e
      rw [heq]
      exact h e
    · exact Set.disjoint_left.mpr (fun e heI heB ↦ hB.subset heB heI)
  · rintro ⟨B, hB, hIB⟩ e
    have hspan := ((ofFamily_isBase_iff K v B).mp hB).2 e
    apply (span_mono (Set.image_mono (show B ⊆ Iᶜ from ?_))) hspan
    intro b hb hi
    exact Set.disjoint_left.mp hIB hi hb

/-- Exact equality with Mathlib's ordinary dual matroid, over every field. -/
theorem ofFamily_dual (v : E → V) :
    (VectorMatroid.ofFamily (K := K) v)✶ =
      VectorMatroid.ofFamily (K := K) (dualFamily (K := K) v) := by
  apply Matroid.ext_indep (by simp)
  intro I _
  rw [Matroid.dual_indep_iff_exists (by simp), VectorMatroid.ofFamily_indep,
    dualFamily_indep_iff, complementary_span_iff_base]

end Unimodular.RepresentationBridge
end
end

/-! ## Exact source section: Continuation/Runtime/RepresentationMap.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-! # Ordinary vector matroids under bijective relabelling -/

open scoped Matroid

namespace Unimodular.RepresentationBridge

theorem ofFamily_mapEquiv (K : Type*) {E F W : Type*}
    [Field K] [AddCommGroup W] [Module K W] (v : E → W) (e : E ≃ F) :
    (VectorMatroid.ofFamily (K := K) v).mapEquiv e =
      VectorMatroid.ofFamily (K := K) (v ∘ e.symm) := by
  apply Matroid.ext_indep (by simp)
  intro I hI
  rw [Matroid.mapEquiv_indep_iff, VectorMatroid.ofFamily_indep,
    VectorMatroid.ofFamily_indep]
  constructor
  · intro h
    exact h.comp_of_image e.symm.injective.injOn
  · intro h
    exact h.image_of_comp e.symm v

theorem mapEquiv_symm_cancel {E F : Type*} (M : Matroid E) (e : E ≃ F) :
    (M.mapEquiv e).mapEquiv e.symm = M := by
  apply Matroid.ext_indep (by simp)
  intro I hI
  simp

end Unimodular.RepresentationBridge

end

/-! ## Exact source section: Continuation/Runtime/FiniteRepresentationBasic.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Finite matrix representations of ordinary matroids

Any finite labelled vector family can be represented in finite coordinates.
Ordinary duals, bijective relabellings, and actual contraction/deletion minors
retain a representation over the same field. These statements have no R₁₀ or
unimodularity dependency.
-/

noncomputable section
open Set Submodule
open scoped Matroid

namespace Unimodular.RepresentationBridge

/-- A finite matrix representation with every label in the ordinary ground set. -/
def HasFiniteRepresentation (K : Type*) [Field K] {E : Type*} (M : Matroid E) : Prop :=
  ∃ n : ℕ, ∃ v : E → Fin n → K, M = VectorMatroid.ofFamily (K := K) v

theorem hasFiniteRepresentation_ofFamily {K E V : Type*} [Field K] [Fintype E]
    [AddCommGroup V] [Module K V] (v : E → V) :
    HasFiniteRepresentation K (VectorMatroid.ofFamily (K := K) v) := by
  let S := span K (Set.range v)
  letI : Module.Finite K S := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let v' : E → S := fun e ↦ ⟨v e, subset_span ⟨e, rfl⟩⟩
  let b := Module.finBasis K S
  let e := b.equivFun
  refine ⟨Module.finrank K S, e ∘ v', ?_⟩
  apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
  intro I
  have h₁ := S.subtype.linearIndepOn_iff_of_injOn S.injective_subtype.injOn
    (v := v') (s := I)
  have h₂ := e.toLinearMap.linearIndepOn_iff_of_injOn e.injective.injOn
    (v := v') (s := I)
  exact h₁.trans h₂.symm

theorem HasFiniteRepresentation.dual {K E : Type*} [Field K] [Fintype E]
    {M : Matroid E} (hM : HasFiniteRepresentation K M) :
    HasFiniteRepresentation K M✶ := by
  obtain ⟨n, v, rfl⟩ := hM
  rw [ofFamily_dual]
  exact hasFiniteRepresentation_ofFamily _

theorem HasFiniteRepresentation.mapEquiv {K E F : Type*} [Field K]
    {M : Matroid E} (hM : HasFiniteRepresentation K M) (e : E ≃ F) :
    HasFiniteRepresentation K (M.mapEquiv e) := by
  obtain ⟨n, v, rfl⟩ := hM
  exact ⟨n, v ∘ e.symm, ofFamily_mapEquiv K v e⟩

theorem HasFiniteRepresentation.of_mapEmbedding_minor {K E F : Type*} [Field K]
    [Fintype F] {M : Matroid E} {N : Matroid F}
    (hM : HasFiniteRepresentation K M) (hN : N.E = Set.univ)
    (f : F ↪ E) (hminor : N.mapEmbedding f ≤m M) :
    HasFiniteRepresentation K N := by
  obtain ⟨n, v, rfl⟩ := hM
  obtain ⟨C, _, heq⟩ := exists_quotient_representation_of_minor N hN v f hminor
  rw [heq]
  exact hasFiniteRepresentation_ofFamily _

end Unimodular.RepresentationBridge
end
end

/-! ## Exact source section: Continuation/Runtime/RationalIntegerRepresentation.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Integral columns for every finite rational representation

A single nonzero common denominator clears every matrix entry. Multiplication
by this scalar is a linear equivalence, so loops, repeated labels and all
independent subsets are preserved. Extension from the rational field to the
real field is proved by nonzero square minors, without any unimodularity
assumption.
-/

noncomputable section
open scoped Matroid

namespace Unimodular.RepresentationBridge

theorem ofFamily_smul_ne_zero {K E V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : E → V) (c : K) (hc : c ≠ 0) :
    VectorMatroid.ofFamily (K := K) (fun e ↦ c • v e) =
      VectorMatroid.ofFamily (K := K) v := by
  let e := LinearEquiv.smulOfNeZero K V c hc
  apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
  intro I
  exact e.toLinearMap.linearIndepOn_iff_of_injOn e.injective.injOn

theorem rational_integer_columns {E : Type*} [Fintype E] {n : ℕ}
    (v : E → Fin n → ℚ) :
    ∃ u : E → Fin n → ℤ,
      VectorMatroid.ofFamily (K := ℚ) v =
        VectorMatroid.ofFamily (K := ℚ) (fun e i ↦ (u e i : ℚ)) := by
  let A : Matrix (Fin n) E ℚ := fun i e ↦ v e i
  let c : ℚ := (A.den : ℚ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr A.den_ne_zero)
  let u : E → Fin n → ℤ := fun e i ↦ A.num i e
  have hv : v = fun e ↦ c • (fun i ↦ (u e i : ℚ)) := by
    funext e i
    exact (congrFun (congrFun A.inv_denom_smul_num i) e).symm
  refine ⟨u, ?_⟩
  rw [hv]
  exact ofFamily_smul_ne_zero _ c hc

theorem rational_real_matroid_eq {E : Type*} [Fintype E] {n : ℕ}
    (v : E → Fin n → ℚ) :
    VectorMatroid.ofFamily (K := ℚ) v =
      VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (v e i : ℝ)) := by
  classical
  apply Matroid.ext_indep (by simp)
  intro I _
  rw [VectorMatroid.ofFamily_indep, VectorMatroid.ofFamily_indep]
  let A : Matrix (Fin n) I ℚ := fun i e ↦ v e.val i
  change LinearIndependent ℚ A.col ↔
    LinearIndependent ℝ (A.map (fun z ↦ (z : ℝ))).col
  rw [SignedSums.independent_cols_iff_minor, SignedSums.independent_cols_iff_minor]
  apply exists_congr
  intro f
  have heq : ((A.map (fun z : ℚ ↦ (z : ℝ))).submatrix f id).det =
      ((A.submatrix f id).det : ℝ) := (Rat.cast_det _).symm
  rw [heq]
  exact Rat.cast_ne_zero.symm

/-- Every ordinary finite rationally represented matroid is the ordinary real
matroid of an integer column family, with exactly the original labels. -/
theorem HasFiniteRepresentation.integer_real {E : Type*} [Fintype E]
    {M : Matroid E} (hM : HasFiniteRepresentation ℚ M) :
    ∃ n : ℕ, ∃ u : E → Fin n → ℤ,
      M = VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (u e i : ℝ)) := by
  obtain ⟨n, v, rfl⟩ := hM
  obtain ⟨u, hu⟩ := rational_integer_columns v
  refine ⟨n, u, hu.trans ?_⟩
  simpa only [Rat.cast_intCast] using
    rational_real_matroid_eq (fun e i ↦ (u e i : ℚ))

theorem ofFamily_finCons_zero {K E : Type*} [Field K] {n : ℕ}
    (v : E → Fin n → K) :
    VectorMatroid.ofFamily (K := K) (fun e ↦ (Fin.cons 0 (v e) : Fin (n + 1) → K)) =
      VectorMatroid.ofFamily (K := K) v := by
  let inclusion : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) :=
    { toFun := fun x : Fin n → K ↦ (Fin.cons 0 x : Fin (n + 1) → K)
      map_add' := by
        intro x y
        funext i
        exact Fin.cases (by simp) (fun j ↦ rfl) i
      map_smul' := by
        intro c x
        funext i
        exact Fin.cases (by simp) (fun j ↦ rfl) i }
  have hinj : Function.Injective inclusion := by
    intro x y h
    funext i
    exact congrFun h i.succ
  apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
  intro I
  exact inclusion.linearIndepOn_iff_of_injOn hinj.injOn

/-- A harmless zero coordinate makes the ambient rank parameter positive,
including for an empty matroid or a family consisting entirely of loops. -/
theorem HasFiniteRepresentation.integer_real_positive {E : Type*} [Fintype E]
    {M : Matroid E} (hM : HasFiniteRepresentation ℚ M) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : E → Fin n → ℤ,
      M = VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (u e i : ℝ)) := by
  obtain ⟨n, u, hu⟩ := hM.integer_real
  refine ⟨n + 1, Nat.succ_pos n, (fun e ↦ Fin.cons 0 (u e)), hu.trans ?_⟩
  have he : (fun e i ↦ ((Fin.cons 0 (u e) : Fin (n + 1) → ℤ) i : ℝ)) =
      (fun e ↦ (Fin.cons 0 (fun i ↦ (u e i : ℝ)) : Fin (n + 1) → ℝ)) := by
    funext e i
    exact Fin.cases (by simp) (fun j ↦ rfl) i
  rw [he]
  exact (ofFamily_finCons_zero (fun e i ↦ (u e i : ℝ))).symm

/-- Representability is stated on the actual ordinary ground set. Mathlib's
`map_val_restrictSubtype_ground_eq` identifies this normalization with the
original matroid, even when its ambient label type has unused elements. -/
def RepresentableOnGround (K : Type*) [Field K] {E : Type*} (M : Matroid E) : Prop :=
  HasFiniteRepresentation K (M.restrictSubtype M.E)

theorem RepresentableOnGround.integer_real_positive {E : Type*}
    (M : Matroid E) [M.Finite] (hM : RepresentableOnGround ℚ M) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : M.E → Fin n → ℤ,
      M.restrictSubtype M.E =
        VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (u e i : ℝ)) := by
  letI : Fintype M.E := M.ground_finite.fintype
  exact HasFiniteRepresentation.integer_real_positive hM

/-- Every actual ordinary minor of an integer ray configuration is rationally
representable. The target uses its actual ground, with no assumption that its
ambient label type equals that ground. -/
theorem integer_ray_minor_ground_representable {E F : Type*} [Fintype E]
    {n : ℕ} (u : E → Fin n → ℤ) (M : Matroid F) [M.Finite]
    (f : M.E ↪ E)
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m
      VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (u e i : ℝ))) :
    RepresentableOnGround ℚ M := by
  letI : Fintype M.E := M.ground_finite.fintype
  have hsource : HasFiniteRepresentation ℚ
      (VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (u e i : ℝ))) := by
    refine ⟨n, (fun e i ↦ (u e i : ℚ)), ?_⟩
    simpa only [Rat.cast_intCast] using
      (rational_real_matroid_eq (fun e i ↦ (u e i : ℚ))).symm
  exact hsource.of_mapEmbedding_minor (by simp) f hminor

end Unimodular.RepresentationBridge
end
end


#print axioms Unimodular.RepresentationBridge.ofFamily_dual
#print axioms Unimodular.RepresentationBridge.HasFiniteRepresentation.of_mapEmbedding_minor
#print axioms Unimodular.RepresentationBridge.RepresentableOnGround.integer_real_positive
#check Unimodular.RepresentationBridge.RepresentableOnGround.integer_real_positive
