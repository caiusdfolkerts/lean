module

public import Continuation.Runtime.MinorRepresentation
public import Continuation.Runtime.FiniteRows
public import Continuation.Runtime.RationalClosure
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.Tactic.Ring
public import Recovery.Unimodular.PriorExtensions.SignedSumsNormalization
public import Recovery.Unimodular.PriorExtensions.SignedSumsPivot
public import Recovery.Unimodular.ProductVectorMatroid

@[expose] public section

set_option debug.skipKernelTC false
set_option maxHeartbeats 0

/-! The exact finite-row lemmas are imported from their unique minimal owner. -/

/-! ## Exact source section: Continuation/Runtime/RationalTU.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Rational and integral totally unimodular representations

Every entry of a rational TU matrix is already 0, 1, or -1. Taking its integer
floor therefore changes no entry after scalar extension, and preserves every
square determinant bound. No finite row or column hypothesis is needed.
-/

namespace Unimodular.RepresentationBridge

noncomputable section

def integerPart {I E : Type*} (A : Matrix I E ℚ) : Matrix I E ℤ :=
  fun i e ↦ ⌊A i e⌋

theorem integerPart_cast {I E : Type*} (A : Matrix I E ℚ)
    (hA : A.IsTotallyUnimodular) (i : I) (e : E) :
    (integerPart A i e : ℚ) = A i e := by
  obtain ⟨s, hs⟩ := hA.apply i e
  unfold integerPart
  rw [← hs]
  cases s <;> norm_num

theorem integerPart_totallyUnimodular {I E : Type*} (A : Matrix I E ℚ)
    (hA : A.IsTotallyUnimodular) : (integerPart A).IsTotallyUnimodular := by
  intro n f g hf hg
  obtain ⟨s, hs⟩ := hA n f g hf hg
  refine ⟨s, ?_⟩
  have hd : (((integerPart A).submatrix f g).det : ℚ) =
      (A.submatrix f g).det := by
    rw [Int.cast_det]
    congr 1
    ext i j
    exact integerPart_cast A hA (f i) (g j)
  have he : ((s.cast : ℤ) : ℚ) = (((integerPart A).submatrix f g).det : ℚ) := by
    calc
      ((s.cast : ℤ) : ℚ) = s.cast := by cases s <;> norm_num
      _ = (A.submatrix f g).det := hs
      _ = (((integerPart A).submatrix f g).det : ℚ) := hd.symm
  exact_mod_cast he

/-- Scalar extension of an integer TU matrix retains every determinant bound. -/
theorem integer_totallyUnimodular_ratCast {I E : Type*} (A : Matrix I E ℤ)
    (hA : A.IsTotallyUnimodular) :
    Matrix.IsTotallyUnimodular (fun i e ↦ (A i e : ℚ)) := by
  intro n f g hf hg
  obtain ⟨s, hs⟩ := hA n f g hf hg
  refine ⟨s, ?_⟩
  have hd : ((A.submatrix f g).det : ℚ) =
      Matrix.det (Matrix.submatrix (fun i e ↦ (A i e : ℚ)) f g) := by
    rw [Int.cast_det]
    rfl
  rw [← hd, ← hs]
  cases s <;> norm_num

/-- Exact passage from the rational TU definition to integer TU columns. -/
theorem rationalTU_integer_model {I E : Type*} (A : Matrix I E ℚ)
    (hA : A.IsTotallyUnimodular) :
    ∃ B : Matrix I E ℤ, B.IsTotallyUnimodular ∧
      VectorMatroid.ofFamily (K := ℚ) (fun e i ↦ A i e) =
        VectorMatroid.ofFamily (K := ℚ) (fun e i ↦ (B i e : ℚ)) := by
  refine ⟨integerPart A, integerPart_totallyUnimodular A hA, ?_⟩
  congr 1
  funext e i
  exact (integerPart_cast A hA i e).symm

/-- Finite ground sets admit finite integer TU coordinates even if the original
rational TU representation uses an infinite row set. -/
theorem rationalTU_finite_integer_model {I E : Type*} [Fintype E]
    (A : Matrix I E ℚ) (hA : A.IsTotallyUnimodular) :
    ∃ n : ℕ, ∃ B : Matrix (Fin n) E ℤ, B.IsTotallyUnimodular ∧
      VectorMatroid.ofFamily (K := ℚ) A.col =
        VectorMatroid.ofFamily (K := ℚ) (fun e i ↦ (B i e : ℚ)) := by
  obtain ⟨n, f, hf⟩ := exists_finite_row_restriction A
  obtain ⟨B, hB, hAB⟩ := rationalTU_integer_model (A.submatrix f id) (hA.submatrix f id)
  exact ⟨n, B, hB, hf.trans hAB⟩

/-- A zero coordinate preserves TU as well as the represented ordinary matroid. -/
theorem finCons_zero_totallyUnimodular {E : Type*} {n : ℕ}
    (A : Matrix (Fin n) E ℤ) (hA : A.IsTotallyUnimodular) :
    Matrix.IsTotallyUnimodular
      (fun i e ↦ (Fin.cons 0 (fun j ↦ A j e) : Fin (n + 1) → ℤ) i) := by
  let f : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (Sum.inr 0) Sum.inl
  have h := (Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff
    (m' := Fin 1) A).mpr hA
  convert h.submatrix f id using 1
  ext i e
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl


end
end Unimodular.RepresentationBridge
end

/-! ## Exact source section: Continuation/Runtime/TUContraction.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Ordinary minors of totally unimodular integer families

A unit pivot eliminates a contracted column. Zeroing its pivot row represents
the quotient by that column and preserves total unimodularity. Keeping this
zero row allows every subsequent contraction to use the same row type.
Loops and elements outside the current ground are handled explicitly.
-/

noncomputable section
open Set Submodule
open scoped Matroid

namespace Unimodular.RepresentationBridge

open Unimodular.SignedSums

def integerColumns {I E : Type*} (A : Matrix I E ℤ) : E → I → ℚ :=
  fun e i ↦ (A i e : ℚ)

def contractMatrix {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (r : I) (c : E) : Matrix I E ℤ :=
  fun i e ↦ if i = r then 0 else A i e - A r c * A i c * A r e

def contractLinear {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (r : I) (c : E) : (I → ℚ) →ₗ[ℚ] (I → ℚ) where
  toFun x i := if i = r then 0 else x i - (A r c : ℚ) * (A i c : ℚ) * x r
  map_add' x y := by
    ext i
    by_cases hi : i = r <;> simp [hi] <;> ring
  map_smul' a x := by
    ext i
    by_cases hi : i = r <;> simp [hi, smul_eq_mul] <;> ring

theorem contractMatrix_totallyUnimodular {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (hA : A.IsTotallyUnimodular) (r : I) (c : E)
    (hp : Pivot.Sign (A r c)) : (contractMatrix A r c).IsTotallyUnimodular := by
  have he : contractMatrix A r c =
      fun i e ↦ (if i = r then 0 else 1) * Pivot.eliminate A r c i e := by
    ext i e
    by_cases hi : i = r <;> simp [contractMatrix, Pivot.eliminate, hi]
  rw [he]
  apply Pivot.tu_scale_rows (Pivot.tu_eliminate hA r c hp)
  intro i
  by_cases hi : i = r <;> simp [hi, Pivot.Small]

theorem contractLinear_ker {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (r : I) (c : E) (hp : Pivot.Sign (A r c)) :
    LinearMap.ker (contractLinear A r c) =
      span ℚ (integerColumns A '' ({c} : Set E)) := by
  have hp2 : (A r c : ℚ) * (A r c : ℚ) = 1 := by
    exact_mod_cast Pivot.sign_square hp
  rw [Set.image_singleton]
  apply le_antisymm
  · intro x hx
    have hx' : contractLinear A r c x = 0 := hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(A r c : ℚ) * x r, ?_⟩
    ext i
    by_cases hi : i = r
    · subst i
      change (A r c : ℚ) * x r * (A r c : ℚ) = x r
      calc
        _ = ((A r c : ℚ) * (A r c : ℚ)) * x r := by ring
        _ = x r := by rw [hp2, one_mul]
    · have hh := congrFun hx' i
      change (if i = r then 0 else x i - (A r c : ℚ) * (A i c : ℚ) * x r) = 0 at hh
      rw [if_neg hi] at hh
      change (A r c : ℚ) * x r * (A i c : ℚ) = x i
      linear_combination -hh
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change contractLinear A r c (integerColumns A c) = 0
    ext i
    by_cases hi : i = r
    · simp [contractLinear, hi]
    · change (if i = r then 0 else
        (A i c : ℚ) - (A r c : ℚ) * (A i c : ℚ) * (A r c : ℚ)) = 0
      rw [if_neg hi]
      calc
        _ = (A i c : ℚ) - ((A r c : ℚ) * (A r c : ℚ)) * (A i c : ℚ) := by ring
        _ = 0 := by rw [hp2]; ring

theorem contractLinear_columns {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (r : I) (c : E) :
    contractLinear A r c ∘ integerColumns A = integerColumns (contractMatrix A r c) := by
  funext e i
  by_cases hi : i = r <;>
    simp [contractLinear, contractMatrix, integerColumns, hi]

theorem exists_tu_contract_singleton {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (hA : A.IsTotallyUnimodular) (S : Set E) (c : E) :
    ∃ B : Matrix I E ℤ, B.IsTotallyUnimodular ∧
      (VectorMatroid.onSet (K := ℚ) (integerColumns A) S) ／ {c} =
        VectorMatroid.onSet (K := ℚ) (integerColumns B) (S \ {c}) := by
  classical
  by_cases hc : c ∈ S
  · by_cases hz : ∀ i, A i c = 0
    · have hv : integerColumns A c = 0 := by ext i; simp [integerColumns, hz i]
      have hker : LinearMap.ker (LinearMap.id : (I → ℚ) →ₗ[ℚ] (I → ℚ)) =
          span ℚ (integerColumns A '' ({c} : Set E)) := by simp [hv]
      refine ⟨A, hA, ?_⟩
      simpa using VectorMatroid.contract_onSet (integerColumns A)
        (Set.singleton_subset_iff.mpr hc) LinearMap.id hker
    · obtain ⟨r, hr⟩ := not_forall.mp hz
      have hp := Pivot.sign_of_small_ne_zero (Pivot.small_entry hA r c) hr
      refine ⟨contractMatrix A r c, contractMatrix_totallyUnimodular A hA r c hp, ?_⟩
      rw [VectorMatroid.contract_onSet (integerColumns A)
        (Set.singleton_subset_iff.mpr hc) (contractLinear A r c)
        (contractLinear_ker A r c hp), contractLinear_columns]
  · have hdiff : S \ {c} = S := by
      ext x
      constructor
      · exact fun h ↦ h.1
      · intro hx
        refine ⟨hx, ?_⟩
        intro he
        have hxc : x = c := Set.mem_singleton_iff.mp he
        exact hc (hxc ▸ hx)
    refine ⟨A, hA, ?_⟩
    rw [hdiff]
    exact Matroid.contract_eq_self_iff.mpr (Set.disjoint_singleton_left.mpr hc)

theorem exists_tu_contract_finset {I E : Type*} [DecidableEq I]
    (A : Matrix I E ℤ) (hA : A.IsTotallyUnimodular) (S : Set E) (C : Finset E) :
    ∃ B : Matrix I E ℤ, B.IsTotallyUnimodular ∧
      (VectorMatroid.onSet (K := ℚ) (integerColumns A) S) ／ (C : Set E) =
        VectorMatroid.onSet (K := ℚ) (integerColumns B) (S \ C) := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨A, hA, by simp⟩
  | @insert c C hc ih =>
      obtain ⟨B, hB, he⟩ := ih
      obtain ⟨B', hB', he'⟩ := exists_tu_contract_singleton B hB (S \ C) c
      refine ⟨B', hB', ?_⟩
      calc
        _ = ((VectorMatroid.onSet (K := ℚ) (integerColumns A) S) ／ (C : Set E)) ／ {c} := by
          rw [Matroid.contract_contract]
          congr 1
          ext e
          simp [or_comm]
        _ = VectorMatroid.onSet (K := ℚ) (integerColumns B') ((S \ C) \ {c}) := by
          rw [he, he']
        _ = _ := by
          congr 1
          ext e
          simp [and_assoc, and_left_comm, and_comm]

/-- Every embedded ordinary minor has a TU integer representation, on exactly
the target labels and in the original coordinate type. -/
theorem tu_integer_model_of_minor {I E F : Type*} [DecidableEq I] [Fintype E]
    (A : Matrix I E ℤ) (hA : A.IsTotallyUnimodular)
    (M : Matroid F) (hME : M.E = Set.univ) (f : F ↪ E)
    (hminor : M.mapEmbedding f ≤m VectorMatroid.ofFamily (K := ℚ) (integerColumns A)) :
    ∃ B : Matrix I F ℤ, B.IsTotallyUnimodular ∧
      M = VectorMatroid.ofFamily (K := ℚ) (integerColumns B) := by
  classical
  obtain ⟨C, D, h⟩ := hminor
  have hground : Set.range f = (Set.univ \ C) \ D := by
    simpa [hME] using congrArg Matroid.E h
  obtain ⟨B, hB, he⟩ := exists_tu_contract_finset A hA Set.univ C.toFinset
  simp only [Set.coe_toFinset] at he
  have hm : M.mapEmbedding f =
      VectorMatroid.onSet (K := ℚ) (integerColumns B) (Set.range f) := by
    rw [h, VectorMatroid.ofFamily, he, VectorMatroid.delete_onSet, ← hground]
  refine ⟨B.submatrix id f, hB.submatrix id f, ?_⟩
  have hmap := VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (K := ℚ) (integerColumns B ∘ f) (integerColumns B) f (fun _ ↦ rfl)
  exact mapEmbedding_injective f (hm.trans hmap.symm)


end Unimodular.RepresentationBridge
end
end

/-! ## Exact source section: Continuation/Runtime/RegularOnGround.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Regularity on the actual finite ground set

We use the standard rational totally unimodular representation definition of
regularity. This is the convention used in `Seymour/Matroid/Regularity.lean` at
commit `2769b10cb73fda17bafc0f13890dc057a2f4ff2a`; the source and its hash are
recorded in `provenance/seymour_sources.json`. We do not replace Mathlib's
matroid type, and do not assert an unproved equivalence with representability
over every field.

The representation is indexed by `M.E`, so unused elements of an ambient type
are immaterial. For a finite ground set, the finite row convention loses no
generality: original rows spanning the row space are selected, preserving both
the column matroid and all square minor bounds. Integer and rational TU models
are proved equivalent, and actual contraction/deletion minors remain regular.
-/

noncomputable section
open scoped Matroid

namespace Unimodular.RepresentationBridge

/-- Regularity in the rational TU convention, on the actual ordinary ground. -/
def RegularOnGround {E : Type*} (M : Matroid E) : Prop :=
  ∃ n : ℕ, ∃ A : Matrix (Fin n) M.E ℚ, A.IsTotallyUnimodular ∧
    M.restrictSubtype M.E = VectorMatroid.ofFamily (K := ℚ) A.col

/-- An arbitrary row index is reduced by selecting finitely many original rows. -/
theorem RegularOnGround.of_rationalTU {E I : Type*} (M : Matroid E) [M.Finite]
    (A : Matrix I M.E ℚ) (hA : A.IsTotallyUnimodular)
    (hM : M.restrictSubtype M.E = VectorMatroid.ofFamily (K := ℚ) A.col) :
    RegularOnGround M := by
  letI : Fintype M.E := M.ground_finite.fintype
  obtain ⟨n, f, hf⟩ := exists_finite_row_restriction A
  exact ⟨n, A.submatrix f id, hA.submatrix f id, hM.trans hf⟩

theorem regularOnGround_iff_integer {E : Type*} (M : Matroid E) :
    RegularOnGround M ↔
      ∃ n : ℕ, ∃ A : Matrix (Fin n) M.E ℤ, A.IsTotallyUnimodular ∧
        M.restrictSubtype M.E =
          VectorMatroid.ofFamily (K := ℚ) (integerColumns A) := by
  constructor
  · rintro ⟨n, A, hA, hM⟩
    obtain ⟨B, hB, he⟩ := rationalTU_integer_model A hA
    exact ⟨n, B, hB, hM.trans he⟩
  · rintro ⟨n, A, hA, hM⟩
    exact ⟨n, (fun i e ↦ (A i e : ℚ)),
      integer_totallyUnimodular_ratCast A hA, hM⟩

theorem RegularOnGround.rationally_representable {E : Type*}
    {M : Matroid E} (hM : RegularOnGround M) : RepresentableOnGround ℚ M := by
  obtain ⟨n, A, _, hA⟩ := hM
  exact ⟨n, A.col, hA⟩

/-- Positive ambient dimension, integral TU coordinates, and the actual real
column matroid are available simultaneously, including for the empty matroid. -/
theorem RegularOnGround.integer_real_positive {E : Type*}
    (M : Matroid E) [M.Finite] (hM : RegularOnGround M) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : M.E → Fin n → ℤ,
      Matrix.IsTotallyUnimodular (fun i e ↦ u e i) ∧
      M.restrictSubtype M.E =
        VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (u e i : ℝ)) := by
  letI : Fintype M.E := M.ground_finite.fintype
  obtain ⟨n, A, hA, hM⟩ := (regularOnGround_iff_integer M).mp hM
  let B : Matrix (Fin (n + 1)) M.E ℤ :=
    fun i e ↦ (Fin.cons 0 (A.col e) : Fin (n + 1) → ℤ) i
  have hB : B.IsTotallyUnimodular := finCons_zero_totallyUnimodular A hA
  have hp : VectorMatroid.ofFamily (K := ℚ) (integerColumns B) =
      VectorMatroid.ofFamily (K := ℚ) (integerColumns A) := by
    have he : integerColumns B =
        fun e ↦ (Fin.cons 0 (integerColumns A e) : Fin (n + 1) → ℚ) := by
      funext e i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [integerColumns, B]
    rw [he]
    exact ofFamily_finCons_zero (integerColumns A)
  refine ⟨n + 1, Nat.succ_pos n, B.col, hB, hM.trans (hp.symm.trans ?_)⟩
  simpa only [integerColumns, Matrix.col_apply, Rat.cast_intCast] using
    rational_real_matroid_eq (integerColumns B)

/-- Regularity descends along an actual ordinary minor between actual grounds.
The embedding preserves labels; no simplified or loopless restriction occurs. -/
theorem RegularOnGround.of_mapEmbedding_minor {E F : Type*}
    (M : Matroid E) (N : Matroid F) [M.Finite] [N.Finite]
    (hN : RegularOnGround N) (f : M.E ↪ N.E)
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m N.restrictSubtype N.E) :
    RegularOnGround M := by
  classical
  letI : Fintype N.E := N.ground_finite.fintype
  obtain ⟨n, A, hA, hN⟩ := (regularOnGround_iff_integer N).mp hN
  rw [hN] at hminor
  obtain ⟨B, hB, hM⟩ := tu_integer_model_of_minor A hA
    (M.restrictSubtype M.E) (by simp) f hminor
  exact (regularOnGround_iff_integer M).mpr ⟨n, B, hB, hM⟩


end Unimodular.RepresentationBridge
end
end

/-! ## Exact source section: Continuation/Fano/RegularRealization.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Regular matroids and uniformly unimodular smooth reflexive polytopes

This is the regular counterpart of `RationalRealization`. Both directions use
actual ordinary ground sets and actual primitive facet normals. In the
necessity direction, uniformity bounds full lattice determinants; it is not
silently replaced by total unimodularity in the original coordinates. We
choose the integral facet basis at an actual vertex, then prove that its
coordinate matrix is TU and represents the same ordinary matroid.
-/

noncomputable section
open Set
open scoped Matroid BigOperators

namespace Unimodular.RegularRealization

/-- The full polytope and ordinary-matroid sufficiency in Proposition 5.2,
with arbitrary divisibility and the additional absence of unimodular triangles. -/
theorem exists_uniform_smooth_reflexive_realization
    {E : Type*} (M : Matroid E) [M.Finite]
    (hM : RepresentationBridge.RegularOnGround M) (d : ℤ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
        (fun v : {v // v ∈ P.normals} ↦ v.val) ∧
      ∃ f : M.E ↪ {v // v ∈ P.normals},
        (M.restrictSubtype M.E).mapEmbedding f ≤m
          VectorMatroid.ofFamily (K := ℝ)
            (fun v : {v // v ∈ P.normals} ↦ embed v.val) ∧
        (∀ F : Set (Ambient n), IsExtreme ℝ P.carrier F →
          ¬ SegmentSimplex.IsUnimodularTriangle F) ∧
        (∃ D : Lattice n → ℤ, ∃ m : Lattice n,
          ∀ u ∈ P.normals, 1 = d * D u + integerPairing m u) ∧
        (∀ a ∈ P.vertices, ∀ b ∈ P.vertices,
          ∃ z : Lattice n, b - a = d • z) := by
  classical
  letI : Fintype M.E := M.ground_finite.fintype
  obtain ⟨r, hr, u, huTU, hu⟩ :=
    RepresentationBridge.RegularOnGround.integer_real_positive M hM
  let n := MultiwedgeSmooth.dimension (n := r) (CubeInput.Block u d)
  let P := CubeInput.presentation u d hd
  refine ⟨n, ?_, P, CubeInput.presentation_uniform u d hd huTU,
    CubeInput.inputFacetEmbedding u d hd, ?_, ?_, ?_, ?_⟩
  · exact hr.trans_le (Nat.le_add_right _ _)
  · rw [hu]
    exact CubeInput.input_matroid_minor u d hd
  · exact CubeInput.presentation_UT_free u d hd
  · obtain ⟨D, hD⟩ := MultiwedgeSmooth.boundary_coefficient_relation
      (CubeInput.Block u d) (CubeInput.normal u) (CubeInput.height u d)
      (CubeInput.block_card u d hd) d (CubeInput.height_dvd u d)
    exact ⟨D, MultiwedgeSmooth.indexCharacter (CubeInput.Block u d), hD⟩
  · intro a ha b hb
    exact MultiwedgeSmooth.packed_vertices_difference
      (CubeInput.Block u d) (CubeInput.normal u) (CubeInput.height u d) d
      (CubeInput.vertices d) (CubeInput.vertex_dvd d) (CubeInput.height_dvd u d)
      a b ha hb

/-- Uniformity plus an actual vertex basis supplies a genuine TU model of the
facet-normal matroid; ordinary TU minor closure then proves necessity. -/
theorem regular_of_uniform_facet_minor
    {E : Type*} {n : ℕ} (P : SmoothReflexivePresentation n)
    (hP : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : {v // v ∈ P.normals} ↦ v.val))
    (M : Matroid E) [M.Finite] (f : M.E ↪ {v // v ∈ P.normals})
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m
      VectorMatroid.ofFamily (K := ℝ)
        (fun v : {v // v ∈ P.normals} ↦ embed v.val)) :
    RepresentationBridge.RegularOnGround M := by
  classical
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let b := P.basis ⟨v, hv⟩
  let A : Matrix (Fin n) {u // u ∈ P.normals} ℤ :=
    fun i u ↦ b.repr u.val i
  have hA : A.IsTotallyUnimodular := by
    apply SignedSums.coordinates_tu_of_uniform (Pi.basisFun ℤ (Fin n)) b
      (fun u : {u // u ∈ P.normals} ↦ u.val) hP
    intro i
    exact ⟨⟨b i, P.basis_mem ⟨v, hv⟩ i⟩, rfl⟩
  have hinj : Function.Injective (realCoordinates b) := by
    intro x y h
    calc
      x = ∑ i, realCoordinates b x i • embed (b i) :=
        (sum_basis_realCoordinates b x).symm
      _ = ∑ i, realCoordinates b y i • embed (b i) := by rw [h]
      _ = y := sum_basis_realCoordinates b y
  have hreal : VectorMatroid.ofFamily (K := ℝ)
        (fun u : {u // u ∈ P.normals} ↦ embed u.val) =
      VectorMatroid.ofFamily (K := ℝ) (fun u i ↦ (A i u : ℝ)) := by
    apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
    intro S
    have he : realCoordinates b ∘ (fun u : {u // u ∈ P.normals} ↦ embed u.val) =
        (fun u i ↦ (A i u : ℝ)) := by
      funext u i
      exact realCoordinates_embed b u.val i
    have h := (realCoordinates b).linearIndepOn_iff_of_injOn hinj.injOn
      (v := fun u : {u // u ∈ P.normals} ↦ embed u.val) (s := S)
    rw [he] at h
    exact h.symm
  have hrat : VectorMatroid.ofFamily (K := ℚ)
        (RepresentationBridge.integerColumns A) =
      VectorMatroid.ofFamily (K := ℝ) (fun u i ↦ (A i u : ℝ)) := by
    simpa only [RepresentationBridge.integerColumns, Rat.cast_intCast] using
      RepresentationBridge.rational_real_matroid_eq
        (RepresentationBridge.integerColumns A)
  rw [hreal, ← hrat] at hminor
  obtain ⟨B, hB, hM⟩ := RepresentationBridge.tu_integer_model_of_minor A hA
    (M.restrictSubtype M.E) (by simp) f hminor
  exact (RepresentationBridge.regularOnGround_iff_integer M).mpr ⟨n, B, hB, hM⟩

/-- A compact exact characterization, with no restriction on the original
ambient label type and no extra representability hypothesis. -/
theorem regular_iff_uniform_smooth_reflexive_minor
    {E : Type*} (M : Matroid E) [M.Finite] :
    RepresentationBridge.RegularOnGround M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
        IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
          (fun v : {v // v ∈ P.normals} ↦ v.val) ∧
        ∃ f : M.E ↪ {v // v ∈ P.normals},
          (M.restrictSubtype M.E).mapEmbedding f ≤m
            VectorMatroid.ofFamily (K := ℝ)
              (fun v : {v // v ∈ P.normals} ↦ embed v.val) := by
  constructor
  · intro hM
    obtain ⟨n, hn, P, hP, f, hf, _⟩ :=
      exists_uniform_smooth_reflexive_realization M hM 2 le_rfl
    exact ⟨n, hn, P, hP, f, hf⟩
  · rintro ⟨n, _, P, hP, f, hf⟩
    exact regular_of_uniform_facet_minor P hP M f hf


end Unimodular.RegularRealization
end
end

#print axioms Unimodular.RepresentationBridge.exists_finite_row_restriction
#print axioms Unimodular.RepresentationBridge.RegularOnGround.of_rationalTU
#print axioms Unimodular.RepresentationBridge.regularOnGround_iff_integer
#print axioms Unimodular.RepresentationBridge.tu_integer_model_of_minor
#print axioms Unimodular.RepresentationBridge.RegularOnGround.integer_real_positive
#print axioms Unimodular.RegularRealization.exists_uniform_smooth_reflexive_realization
#print axioms Unimodular.RegularRealization.regular_of_uniform_facet_minor
#print axioms Unimodular.RegularRealization.regular_iff_uniform_smooth_reflexive_minor
