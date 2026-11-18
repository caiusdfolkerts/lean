module

public import Continuation.Runtime.RegularClosure
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Necessity for arbitrary integral boundary valuations

A finite integral family with zero integral annihilator spans over the
rationals. The proof clears a separating rational functional's denominators.
For a uniformly unimodular family, a selected rational column basis is then
an integral basis. Consequently every ordinary minor is regular.

These statements do not assume that the family was obtained from a fan,
or that an independently supplied toric variety has already been classified.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Unimodular.RepresentationBridge

open Set Submodule
open scoped BigOperators Matroid

variable {E G : Type*} [Fintype E] {n : ℕ}

/-- Clearing the coefficients of a separating rational functional proves
full rational span from the literal integral annihilator condition. -/
theorem rational_span_eq_top_of_integral_annihilator
    (U : E → Lattice n)
    (hann : ∀ m : Lattice n, (∀ e, ∑ i, U e i * m i = 0) → m = 0) :
    Submodule.span ℚ (Set.range (fun e i ↦ (U e i : ℚ))) = ⊤ := by
  classical
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro φ hφ
  change φ = 0
  let A : Matrix (Fin n) Unit ℚ := fun i _ ↦ φ (Pi.single i 1)
  let m : Lattice n := fun i ↦ A.num i ()
  let c : ℚ := (A.den : ℚ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr A.den_ne_zero)
  have hcoord (i : Fin n) : φ (Pi.single i 1) = c * (m i : ℚ) := by
    exact (congrFun (congrFun A.inv_denom_smul_num i) ()).symm
  have hsum (x : Fin n → ℚ) :
      φ x = ∑ i, x i * φ (Pi.single i 1) := by
    have hx : (∑ i : Fin n, x i • Pi.single i (1 : ℚ)) = x := by
      ext j
      simp [Pi.single_apply]
    calc
      φ x = φ (∑ i : Fin n, x i • Pi.single i (1 : ℚ)) := congrArg φ hx.symm
      _ = ∑ i, x i * φ (Pi.single i 1) := by
        simp only [map_sum, map_smul, smul_eq_mul]
  have hvan (e : E) : φ (fun i ↦ (U e i : ℚ)) = 0 :=
    (Submodule.mem_dualAnnihilator φ).mp hφ _ (subset_span ⟨e, rfl⟩)
  have hm : m = 0 := by
    apply hann
    intro e
    have heq : φ (fun i ↦ (U e i : ℚ)) =
        c * (∑ i, (U e i : ℚ) * (m i : ℚ)) := by
      rw [hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoord]
      ring
    have hz := hvan e
    rw [heq] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left hc
    exact_mod_cast hz'
  apply (Pi.basisFun ℚ (Fin n)).ext
  intro i
  simp only [Pi.basisFun_apply, LinearMap.zero_apply]
  rw [hcoord, hm]
  simp

/-- The determinant of a square integral family detects rational and
integral independence equally, including dimension zero. -/
theorem rational_independent_iff_integer_independent
    (v : Fin n → Lattice n) :
    LinearIndependent ℚ (fun i j ↦ (v i j : ℚ)) ↔
      LinearIndependent ℤ v := by
  change LinearIndependent ℚ (Matrix.of (fun i j ↦ (v i j : ℚ))).row ↔
    LinearIndependent ℤ (Matrix.of v).row
  rw [Matrix.linearIndependent_row_iff, Matrix.linearIndependent_row_iff,
    Matrix.nonsingular_iff_det_ne_zero, Matrix.nonsingular_iff_det_ne_zero]
  change ((Matrix.of v).map (fun z : ℤ ↦ (z : ℚ))).det ≠ 0 ↔
    (Matrix.of v).det ≠ 0
  rw [← Int.cast_det]
  exact Int.cast_ne_zero

/-- A uniformly unimodular family with zero integral annihilator contains
an actual integral lattice basis consisting of its original vectors. -/
theorem selected_integral_basis_of_annihilator
    (U : E → Lattice n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) U)
    (hann : ∀ m : Lattice n, (∀ e, ∑ i, U e i * m i = 0) → m = 0) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∃ labels : Fin n → E,
      ∀ i, b i = U (labels i) := by
  classical
  let v : E → Fin n → ℚ := fun e i ↦ (U e i : ℚ)
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ :=
    rational_span_eq_top_of_integral_annihilator U hann
  obtain ⟨I, selected, _, hselected, hind⟩ := exists_linearIndependent' ℚ v
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range (v ∘ selected)) := by
    rw [hselected, hspan]
  let B : Module.Basis I ℚ (Fin n → ℚ) := Module.Basis.mk hind htop
  let e : I ≃ Fin n := B.indexEquiv (Pi.basisFun ℚ (Fin n))
  let labels : Fin n → E := selected ∘ e.symm
  have hq : LinearIndependent ℚ (fun i j ↦ (U (labels i) j : ℚ)) :=
    hind.comp e.symm e.symm.injective
  have hi : LinearIndependent ℤ (U ∘ labels) :=
    (rational_independent_iff_integer_independent (U ∘ labels)).mp hq
  have hs := (IntegralRigidity.uniform_iff_independent_spans
    (Pi.basisFun ℤ (Fin n)) U).mp hU labels hi
  exact ⟨Module.Basis.mk hi hs.ge, labels, fun i ↦ Module.Basis.mk_apply hi hs.ge i⟩

/-- Uniformity plus the actual integral annihilator condition is enough
for regularity of every ordinary minor, without any fan realization input. -/
theorem regular_of_uniform_integer_ray_minor
    (U : E → Lattice n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) U)
    (hann : ∀ m : Lattice n, (∀ e, ∑ i, U e i * m i = 0) → m = 0)
    (M : Matroid G) [M.Finite] (f : M.E ↪ E)
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m
      VectorMatroid.ofFamily (K := ℝ) (fun e ↦ Unimodular.embed (U e))) :
    RegularOnGround M := by
  classical
  obtain ⟨b, labels, hb⟩ := selected_integral_basis_of_annihilator U hU hann
  let A : Matrix (Fin n) E ℤ := fun i e ↦ b.repr (U e) i
  have hA : A.IsTotallyUnimodular :=
    SignedSums.coordinates_tu_of_uniform (Pi.basisFun ℤ (Fin n)) b U hU
      (fun i ↦ ⟨labels i, (hb i).symm⟩)
  have hinj : Function.Injective (realCoordinates b) := by
    intro x y hxy
    calc
      x = ∑ i, realCoordinates b x i • Unimodular.embed (b i) :=
        (sum_basis_realCoordinates b x).symm
      _ = ∑ i, realCoordinates b y i • Unimodular.embed (b i) := by rw [hxy]
      _ = y := sum_basis_realCoordinates b y
  have hreal : VectorMatroid.ofFamily (K := ℝ) (fun e ↦ Unimodular.embed (U e)) =
      VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (A i e : ℝ)) := by
    apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
    intro S
    have he : realCoordinates b ∘ (fun e ↦ Unimodular.embed (U e)) =
        (fun e i ↦ (A i e : ℝ)) := by
      funext e i
      exact realCoordinates_embed b (U e) i
    have hli := (realCoordinates b).linearIndepOn_iff_of_injOn hinj.injOn
      (v := fun e ↦ Unimodular.embed (U e)) (s := S)
    rw [he] at hli
    exact hli.symm
  have hrat : VectorMatroid.ofFamily (K := ℚ) (integerColumns A) =
      VectorMatroid.ofFamily (K := ℝ) (fun e i ↦ (A i e : ℝ)) := by
    simpa only [integerColumns, Rat.cast_intCast] using
      rational_real_matroid_eq (integerColumns A)
  rw [hreal, ← hrat] at hminor
  obtain ⟨B, hB, hM⟩ := tu_integer_model_of_minor A hA
    (M.restrictSubtype M.E) (by simp) f hminor
  exact (regularOnGround_iff_integer M).mpr ⟨n, B, hB, hM⟩

#print axioms rational_span_eq_top_of_integral_annihilator
#print axioms selected_integral_basis_of_annihilator
#print axioms regular_of_uniform_integer_ray_minor

end Unimodular.RepresentationBridge
