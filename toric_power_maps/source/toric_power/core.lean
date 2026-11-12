module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Int.DivMod
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

set_option maxHeartbeats 2000000

/-! ## Source section: LatticeSaturation -/

/-!
# Uniform saturation by a lattice polytope

This file proves the lattice-point assertion of Lemma 7.1 of
*Frobenius generators for smooth toric varieties*.  The proof gives the stronger
uniform bound `dim V`.  It works for every convex set which contains zero and
whose lattice points span `V`; finite generation by vertices is unnecessary.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise
open Set Module

namespace ToricPower

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma convex_sum_mem_of_sum_le_one {ι : Type*} [Fintype ι]
    {K : Set E} (hK : Convex ℝ K) (hzero : (0 : E) ∈ K)
    (v : ι → E) (hv : ∀ i, v i ∈ K) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    ∑ i, w i • v i ∈ K := by
  classical
  let W : Option ι → ℝ := fun i => Option.casesOn i (1 - ∑ j, w j) w
  let Z : Option ι → E := fun i => Option.casesOn i 0 v
  have hW : ∀ i, 0 ≤ W i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact hw i
  have hWs : ∑ i, W i = 1 := by
    simp [W, Fintype.sum_option]
  have hZ : ∀ i, Z i ∈ K := by
    intro i
    cases i with
    | none => exact hzero
    | some i => exact hv i
  simpa [W, Z, Fintype.sum_option] using
    hK.sum_mem (t := Finset.univ) (fun i _ => hW i) hWs (fun i _ => hZ i)

/-- A convex set containing zero and an integral real basis meets every lattice
translate after dilation by at least the number of basis vectors.  The basis
need not be a basis of the lattice itself. -/
theorem lattice_point_translate_dilate_of_basis {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) (L : AddSubgroup E) (K : Set E)
    (hK : Convex ℝ K) (hzero : (0 : E) ∈ K)
    (hbK : ∀ i, b i ∈ K) (hbL : ∀ i, b i ∈ L)
    (t : ℝ) (ht : (Fintype.card ι : ℝ) ≤ t) (p : E) :
    ∃ z ∈ L, ∃ k ∈ K, z = p + t • k := by
  classical
  have ht0 : 0 ≤ t := (Nat.cast_nonneg _).trans ht
  by_cases htzero : t = 0
  · have hcard : Fintype.card ι = 0 := by
      have : (Fintype.card ι : ℝ) ≤ 0 := htzero ▸ ht
      exact_mod_cast (le_antisymm this (Nat.cast_nonneg _))
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    have hp : p = 0 := by
      apply b.repr.injective
      ext i
      exact isEmptyElim i
    exact ⟨0, L.zero_mem, 0, hzero, by simp [hp]⟩
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  let r : ι → ℝ := fun i => b.repr p i
  let z : E := ∑ i, (⌈r i⌉ : ℤ) • b i
  let w : ι → ℝ := fun i => ((⌈r i⌉ : ℝ) - r i) / t
  have hzL : z ∈ L := by
    exact L.sum_mem fun i _ => L.zsmul_mem (hbL i) _
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact div_nonneg (sub_nonneg.mpr (Int.le_ceil _)) ht0
  have hwbound : ∀ i, w i ≤ 1 / t := by
    intro i
    apply (div_le_div_iff_of_pos_right htpos).mpr
    have hceil := Int.ceil_lt_add_one (r i)
    linarith
  have hsum : ∑ i, w i ≤ 1 := by
    calc
      ∑ i, w i ≤ ∑ _i : ι, 1 / t := Finset.sum_le_sum (fun i _ => hwbound i)
      _ = (Fintype.card ι : ℝ) / t := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one htpos).mpr ht
  refine ⟨z, hzL, ∑ i, w i • b i,
    convex_sum_mem_of_sum_le_one hK hzero b hbK w hw hsum, ?_⟩
  have hrepr : ∑ i, r i • b i = p := b.sum_repr p
  rw [← hrepr, Finset.smul_sum, ← Finset.sum_add_distrib]
  unfold z
  apply Finset.sum_congr rfl
  intro i _
  rw [← Int.cast_smul_eq_zsmul ℝ, ← mul_smul, ← add_smul]
  congr 1
  dsimp [w]
  field_simp [htzero]
  <;> ring

/-- Saturation within a real subspace.  The lattice points of `K` need only span
`V` over the reals; neither a unimodular basis nor a full-rank ambient lattice is
required. -/
theorem lattice_point_translate_dilate [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (V : Submodule ℝ E) (K : Set E)
    (hK : Convex ℝ K) (hzero : (0 : E) ∈ K) (hKV : K ⊆ V)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = V)
    (t : ℝ) (ht : (finrank ℝ V : ℝ) ≤ t)
    (p m : E) (hm : m ∈ L) (hpm : p - m ∈ V) :
    ∃ z ∈ L, ∃ k ∈ K, z = p + t • k := by
  classical
  let S : Set V := {v | (v : E) ∈ K ∧ (v : E) ∈ L}
  have himage : Subtype.val '' S = K ∩ (L : Set E) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hKV hx.1⟩, hx, rfl⟩
  have hS : Submodule.span ℝ S = ⊤ := by
    apply (Submodule.span_val_image_eq_iff V S).mp
    rw [himage, hspan]
  let J : Set V := (linearIndepOn_empty ℝ (id : V → V)).extend (empty_subset S)
  let b : Basis J ℝ V := Basis.ofSpan (show ⊤ ≤ Submodule.span ℝ S by rw [hS])
  letI := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ V)
  let L' : AddSubgroup V := L.comap V.subtype.toAddMonoidHom
  let K' : Set V := Subtype.val ⁻¹' K
  have hb : ∀ i, b i ∈ S := fun i => Basis.ofSpan_subset _ ⟨i, rfl⟩
  have hbK : ∀ i, b i ∈ K' := fun i => (hb i).1
  have hbL : ∀ i, b i ∈ L' := fun i => (hb i).2
  have ht' : (Fintype.card J : ℝ) ≤ t := by
    rw [← finrank_eq_card_basis b]
    exact ht
  have hK' : Convex ℝ K' := hK.linear_preimage V.subtype
  have hz' : (0 : V) ∈ K' := hzero
  obtain ⟨z, hz, k, hk, heq⟩ :=
    lattice_point_translate_dilate_of_basis b L' K' hK' hz' hbK hbL t ht'
      (⟨p - m, hpm⟩ : V)
  refine ⟨m + (z : E), L.add_mem hm hz, (k : E), hk, ?_⟩
  have hh := congrArg (fun v : V => (v : E)) heq
  change (z : E) = p - m + t • (k : E) at hh
  rw [hh]
  abel

/-- Lemma 7.1, in a stronger form with the explicit threshold `dim V`.
The right-hand side says exactly that the images of `P` and the lattice meet
in the quotient by `V`.  It is written without choosing quotient coordinates. -/
theorem lattice_saturation_iff [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (V : Submodule ℝ E) (K : Set E)
    (hK : Convex ℝ K) (hzero : (0 : E) ∈ K) (hKV : K ⊆ V)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = V)
    (P : Set E) (t : ℝ) (ht : (finrank ℝ V : ℝ) ≤ t) :
    (∃ z ∈ L, ∃ p ∈ P, ∃ k ∈ K, z = p + t • k) ↔
      ∃ p ∈ P, ∃ m ∈ L, p - m ∈ V := by
  constructor
  · rintro ⟨z, hz, p, hp, k, hk, rfl⟩
    refine ⟨p, hp, p + t • k, hz, ?_⟩
    simpa using V.neg_mem (V.smul_mem t (hKV hk))
  · rintro ⟨p, hp, m, hm, hpm⟩
    obtain ⟨z, hz, k, hk, h⟩ :=
      lattice_point_translate_dilate L V K hK hzero hKV hspan t ht p m hm hpm
    exact ⟨z, hz, p, hp, k, hk, h⟩

end ToricPower


/-! ## Source section: LatticePolytope -/

/-!
# Lattice saturation in the exact polytope and quotient notation

This specializes the stronger convex-set theorem to the polytope hypothesis
of Lemma 7.1, and identifies the right-hand side with intersection of the
images under the quotient map.  In particular the projection formulation is
proved equivalent, not merely described as equivalent.
-/

@[expose] public section
noncomputable section

open scoped Pointwise BigOperators
open Set Module

namespace ToricPower

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

lemma span_convexHull_eq (S : Set E) :
    Submodule.span ℝ (convexHull ℝ S) = Submodule.span ℝ S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    exact convexHull_min (Submodule.subset_span) (Submodule.convex _)
  · exact Submodule.span_mono (subset_convexHull ℝ S)

lemma span_lattice_points_convexHull (L : AddSubgroup E) (S : Set E)
    (hS : S ⊆ L) :
    Submodule.span ℝ (convexHull ℝ S ∩ (L : Set E)) = Submodule.span ℝ S := by
  apply le_antisymm
  · exact (Submodule.span_mono Set.inter_subset_left).trans (span_convexHull_eq S).le
  · apply Submodule.span_mono
    intro x hx
    exact ⟨subset_convexHull ℝ S hx, hS hx⟩

lemma projection_intersection_iff (L : AddSubgroup E) (V : Submodule ℝ E)
    (P : Set E) :
    ((V.mkQ '' P) ∩ (V.mkQ '' (L : Set E))).Nonempty ↔
      ∃ p ∈ P, ∃ m ∈ L, p - m ∈ V := by
  constructor
  · rintro ⟨z, ⟨p, hp, hpz⟩, ⟨m, hm, hmz⟩⟩
    refine ⟨p, hp, m, hm, ?_⟩
    exact (Submodule.Quotient.eq V).mp (hpz.trans hmz.symm)
  · rintro ⟨p, hp, m, hm, hpm⟩
    refine ⟨V.mkQ p, ⟨p, hp, rfl⟩, m, hm, ?_⟩
    exact ((Submodule.Quotient.eq V).mpr hpm).symm

lemma minkowski_intersection_iff (L : AddSubgroup E) (P K : Set E) (t : ℝ) :
    ((P + t • K) ∩ (L : Set E)).Nonempty ↔
      ∃ z ∈ L, ∃ p ∈ P, ∃ k ∈ K, z = p + t • k := by
  constructor
  · rintro ⟨z, hz, hzL⟩
    obtain ⟨p, hp, y, hy, hpy⟩ := hz
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨z, hzL, p, hp, k, hk, hpy.symm⟩
  · rintro ⟨z, hz, p, hp, k, hk, rfl⟩
    exact ⟨p + t • k, ⟨p, hp, t • k, ⟨k, hk, rfl⟩, rfl⟩, hz⟩

/-- The complete assertion of Lemma 7.1 for a lattice polytope, with the
stronger explicit threshold `dim V`.  The finite vertex family may be
redundant, and the ambient lattice may have arbitrary rank. -/
theorem paper_lemma_7_1 (L : AddSubgroup E) (vertices : Finset E)
    (hintegral : (vertices : Set E) ⊆ L)
    (hzero : (0 : E) ∈ convexHull ℝ (vertices : Set E))
    (P : Set E) (t : ℕ)
    (ht : finrank ℝ (Submodule.span ℝ (vertices : Set E)) ≤ t) :
    let K := convexHull ℝ (vertices : Set E)
    let V := Submodule.span ℝ (vertices : Set E)
    ((P + (t : ℝ) • K) ∩ (L : Set E)).Nonempty ↔
      ((V.mkQ '' P) ∩ (V.mkQ '' (L : Set E))).Nonempty := by
  dsimp
  rw [minkowski_intersection_iff, projection_intersection_iff]
  apply lattice_saturation_iff L (Submodule.span ℝ (vertices : Set E))
    (convexHull ℝ (vertices : Set E)) (convex_convexHull ℝ _) hzero
  · exact convexHull_min Submodule.subset_span (Submodule.convex _)
  · exact span_lattice_points_convexHull L (vertices : Set E) hintegral
  · exact_mod_cast ht

/-- The saturation threshold can be chosen using only ambient dimension.
This gives the effective uniform choice `T_A ≤ n` in the final saturation
step of the proof of Theorem 7.2. -/
theorem paper_lemma_7_1_ambient_bound (L : AddSubgroup E) (vertices : Finset E)
    (hintegral : (vertices : Set E) ⊆ L)
    (hzero : (0 : E) ∈ convexHull ℝ (vertices : Set E))
    (P : Set E) (t : ℕ) (ht : finrank ℝ E ≤ t) :
    let K := convexHull ℝ (vertices : Set E)
    let V := Submodule.span ℝ (vertices : Set E)
    ((P + (t : ℝ) • K) ∩ (L : Set E)).Nonempty ↔
      ((V.mkQ '' P) ∩ (V.mkQ '' (L : Set E))).Nonempty := by
  apply paper_lemma_7_1 L vertices hintegral hzero P t
  exact (Submodule.finrank_le _).trans ht

end ToricPower


/-! ## Source section: FloorArithmetic -/

/-!
# Integral arithmetic of toric power-map summands

The coefficient map is literally coordinatewise integral flooring of
`(b + Au)/ell`.  All statements hold in every finite matrix size, and the
quotient by the integral image of `A` retains its torsion.
-/

@[expose] public section
noncomputable section

open scoped BigOperators
open Set

namespace ToricPower

variable {ι κ : Type*} [Fintype κ]

/-- The integral ray-pairing map, in arbitrary lattice bases. -/
def rayMap (A : ι → κ → ℤ) : (κ → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun u i := ∑ j, A i j * u j
  map_add' u v := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r u := by
    ext i
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- A coefficient vector of the actual floor splitting, before taking classes. -/
def powerCoefficient (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ)
    (u : κ → ℤ) : ι → ℤ :=
  fun i => (b i + rayMap A u i) / ell

/-- The integral cokernel, including all torsion. -/
abbrev DivisorClass (A : ι → κ → ℤ) :=
  (ι → ℤ) ⧸ LinearMap.range (rayMap A)

def divisorClass (A : ι → κ → ℤ) (b : ι → ℤ) : DivisorClass A :=
  Submodule.Quotient.mk b

/-- The distinct divisor classes appearing in the floor formula. -/
def frobeniusClasses (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ) :
    Set (DivisorClass A) :=
  Set.range (fun u => divisorClass A (powerCoefficient A b ell u))

/-- The precise raw coefficients of Theorem 7.2. -/
def rawCoefficients (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ) :
    Set (ι → ℤ) :=
  {c | ∃ u : κ → ℤ, (∀ j, 0 ≤ u j ∧ u j < ell) ∧
    powerCoefficient A b ell u = c}

theorem powerCoefficient_eq_floor (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (hell : 0 < ell) (u : κ → ℤ) (i : ι) :
    powerCoefficient A b ell u i =
      ⌊((b i + rayMap A u i : ℤ) : ℝ) / (ell : ℝ)⌋ := by
  symm
  apply Int.floor_eq_iff.mpr
  have hreal : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hb := (Int.ediv_eq_iff_of_pos hell).mp
    (show (b i + rayMap A u i) / ell = powerCoefficient A b ell u i from rfl)
  constructor
  · apply (le_div_iff₀ hreal).mpr
    exact_mod_cast hb.1
  · apply (div_lt_iff₀ hreal).mpr
    have hh : b i + rayMap A u i < (powerCoefficient A b ell u i + 1) * ell := by
      nlinarith [hb.2]
    exact_mod_cast hh

/-- Exact, closed integral inequalities for a floor coefficient.  No strict
real inequality or boundary case is dropped. -/
theorem powerCoefficient_eq_iff (A : ι → κ → ℤ) (b c : ι → ℤ)
    (ell : ℤ) (hell : 0 < ell) (u : κ → ℤ) :
    powerCoefficient A b ell u = c ↔
      ∀ i, ell * c i ≤ b i + rayMap A u i ∧
        b i + rayMap A u i ≤ ell * (c i + 1) - 1 := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [powerCoefficient, Int.ediv_eq_iff_of_pos hell]
  constructor <;> intro h
  · constructor
    · simpa [mul_comm] using h.1
    · have hh := h.2
      nlinarith
  · constructor
    · simpa [mul_comm] using h.1
    · have hh := h.2
      nlinarith

/-- Membership in the coefficient set is precisely the lattice feasibility
problem in Theorem 7.2, in every dimension and for every integer matrix. -/
theorem rawCoefficients_iff_feasible (A : ι → κ → ℤ) (b c : ι → ℤ)
    (ell : ℤ) (hell : 0 < ell) :
    c ∈ rawCoefficients A b ell ↔
      ∃ u : κ → ℤ, (∀ j, 0 ≤ u j ∧ u j ≤ ell - 1) ∧
        ∀ i, ell * c i ≤ b i + rayMap A u i ∧
          b i + rayMap A u i ≤ ell * (c i + 1) - 1 := by
  simp only [rawCoefficients, Set.mem_setOf_eq, powerCoefficient_eq_iff A b c ell hell]
  apply exists_congr
  intro u
  apply and_congr_left
  intro _
  apply forall_congr'
  intro j
  omega

theorem powerCoefficient_translate (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (hell : ell ≠ 0) (u m : κ → ℤ) :
    powerCoefficient A b ell (u + ell • m) =
      powerCoefficient A b ell u + rayMap A m := by
  ext i
  simp only [powerCoefficient, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← add_assoc, Int.add_mul_ediv_left _ _ hell]

theorem divisorClass_rayMap (A : ι → κ → ℤ) (m : κ → ℤ) :
    divisorClass A (rayMap A m) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩

/-- Changing a character representative modulo `ell M` does not change the
divisor class. -/
theorem powerClass_translate (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (hell : ell ≠ 0) (u m : κ → ℤ) :
    divisorClass A (powerCoefficient A b ell (u + ell • m)) =
      divisorClass A (powerCoefficient A b ell u) := by
  rw [powerCoefficient_translate A b ell hell u m]
  change Submodule.Quotient.mk _ = _
  rw [Submodule.Quotient.mk_add]
  change _ + divisorClass A (rayMap A m) = _
  rw [divisorClass_rayMap, add_zero]
  rfl

/-- Principal translation of the input divisor preserves the entire summand
class set. -/
theorem frobeniusClasses_principal_translate (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (m : κ → ℤ) :
    frobeniusClasses A (b + rayMap A m) ell = frobeniusClasses A b ell := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨m + u, ?_⟩
    change divisorClass A (powerCoefficient A b ell (m + u)) =
      divisorClass A (powerCoefficient A (b + rayMap A m) ell u)
    congr 1
    ext i
    simp [powerCoefficient, map_add, add_assoc]
  · rintro ⟨u, rfl⟩
    refine ⟨u - m, ?_⟩
    change divisorClass A (powerCoefficient A (b + rayMap A m) ell (u - m)) =
      divisorClass A (powerCoefficient A b ell u)
    congr 1
    ext i
    simp [powerCoefficient, map_sub]

/-- Integer division composes exactly under positive successive power maps. -/
theorem powerCoefficient_compose (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell k : ℤ) (hk : 0 < k) (u v : κ → ℤ) :
    powerCoefficient A (powerCoefficient A b k u) ell v =
      powerCoefficient A b (k * ell) (u + k • v) := by
  ext i
  simp only [powerCoefficient, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← add_assoc, ← Int.ediv_ediv_of_nonneg hk.le,
    Int.add_mul_ediv_left _ _ hk.ne']

/-- The class set may be computed using precisely the residues in the
half-open cube, even when the cokernel has torsion. -/
theorem frobeniusClasses_iff_bounded (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (hell : 0 < ell) (a : DivisorClass A) :
    a ∈ frobeniusClasses A b ell ↔
      ∃ u : κ → ℤ, (∀ j, 0 ≤ u j ∧ u j < ell) ∧
        divisorClass A (powerCoefficient A b ell u) = a := by
  constructor
  · rintro ⟨u, rfl⟩
    let r : κ → ℤ := fun j => u j % ell
    let q : κ → ℤ := fun j => u j / ell
    have hdecomp : u = r + ell • q := by
      ext j
      exact (Int.emod_add_mul_ediv (u j) ell).symm
    refine ⟨r, fun j => ⟨Int.emod_nonneg _ hell.ne', Int.emod_lt_of_pos _ hell⟩, ?_⟩
    change divisorClass A (powerCoefficient A b ell r) =
      divisorClass A (powerCoefficient A b ell u)
    rw [hdecomp, powerClass_translate A b ell hell.ne' r q]
  · rintro ⟨u, _, hu⟩
    exact ⟨u, hu⟩

/-- Arithmetic form of composition of finite toric power-map pushforwards. -/
theorem frobeniusClasses_compose (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell k : ℤ) (hk : 0 < k) :
    frobeniusClasses A b (k * ell) =
      ⋃ u : κ → ℤ, frobeniusClasses A (powerCoefficient A b k u) ell := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨u, 0, ?_⟩
    change divisorClass A (powerCoefficient A (powerCoefficient A b k u) ell 0) =
      divisorClass A (powerCoefficient A b (k * ell) u)
    rw [powerCoefficient_compose A b ell k hk u 0]
    simp
  · intro ha
    obtain ⟨u, v, hv⟩ := Set.mem_iUnion.mp ha
    refine ⟨u + k • v, ?_⟩
    change divisorClass A (powerCoefficient A b (k * ell) (u + k • v)) = a
    rw [← powerCoefficient_compose A b ell k hk u v]
    exact hv

/-- Eventual floor rounding at a fixed integer, including the negative
boundary correctly. -/
theorem large_scale_floor (a k : ℤ) (hk : |a| < k) :
    a / k = if 0 ≤ a then 0 else -1 := by
  have hkpos : 0 < k := (abs_nonneg a).trans_lt hk
  split_ifs with ha
  · apply (Int.ediv_eq_iff_of_pos hkpos).mpr
    have h := le_abs_self a
    constructor <;> omega
  · apply (Int.ediv_eq_iff_of_pos hkpos).mpr
    have h := neg_abs_le a
    constructor <;> omega

/-- Every accessible sign pattern is the actual raw coefficient vector of
every sufficiently large power map; no divisor-class simplification occurs. -/
theorem accessible_pattern_occurs (A : ι → κ → ℤ) (b : ι → ℤ)
    (w : κ → ℤ) (k : ℤ) (hk : ∀ i, |b i + rayMap A w i| < k) :
    powerCoefficient A b k w =
      fun i => if 0 ≤ b i + rayMap A w i then 0 else -1 := by
  ext i
  exact large_scale_floor _ _ (hk i)

/-- The height-independent finite box used in Theorem 7.2. -/
theorem raw_coefficient_bound (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℤ) (hell : 0 < ell) (u : κ → ℤ)
    (hu : ∀ j, 0 ≤ u j ∧ u j < ell) (i : ι) (hb : |b i| < ell) :
    -(∑ j, |A i j|) - 1 ≤ powerCoefficient A b ell u i ∧
      powerCoefficient A b ell u i ≤ (∑ j, |A i j|) + 1 := by
  have hterm : ∀ j, |A i j * u j| ≤ |A i j| * ell := by
    intro j
    rw [abs_mul, abs_of_nonneg (hu j).1]
    exact mul_le_mul_of_nonneg_left (hu j).2.le (abs_nonneg _)
  have hrow : |rayMap A u i| ≤ (∑ j, |A i j|) * ell := by
    change |∑ j, A i j * u j| ≤ _
    calc
      |∑ j, A i j * u j| ≤ ∑ j, |A i j * u j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A i j| * ell := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by rw [Finset.sum_mul]
  have hn : |b i + rayMap A u i| < ((∑ j, |A i j|) + 1) * ell := by
    have hh := abs_add_le (b i) (rayMap A u i)
    nlinarith
  have hnlow := neg_abs_le (b i + rayMap A u i)
  have hnup := le_abs_self (b i + rayMap A u i)
  have hq := (Int.ediv_eq_iff_of_pos hell).mp
    (show (b i + rayMap A u i) / ell = powerCoefficient A b ell u i from rfl)
  constructor
  · by_contra h
    have hh : powerCoefficient A b ell u i ≤ -(∑ j, |A i j|) - 2 := by omega
    nlinarith [hq.2]
  · by_contra h
    have hh : (∑ j, |A i j|) + 2 ≤ powerCoefficient A b ell u i := by omega
    nlinarith [hq.1]

end ToricPower


/-! ## Source section: IntegralVertices -/

/-!
# Integral affine vertices

These are the determinant-denominator and sign-stabilization arguments used
for the vertex families in Theorem 7.2.  All dimensions and all integral
coefficient matrices are arbitrary.
-/

@[expose] public section
noncomputable section

open scoped BigOperators Matrix
open Matrix

namespace ToricPower

variable {n : Type*} [Fintype n] [DecidableEq n]

def realMatrix (A : Matrix n n ℤ) : Matrix n n ℝ :=
  A.map (Int.castRingHom ℝ)

@[simp] theorem realMatrix_apply (A : Matrix n n ℤ) (i j : n) :
    realMatrix A i j = (A i j : ℝ) := rfl

theorem realMatrix_det (A : Matrix n n ℤ) :
    (realMatrix A).det = (A.det : ℝ) := by
  exact ((Int.castRingHom ℝ).map_det A).symm

theorem realMatrix_adjugate (A : Matrix n n ℤ) :
    realMatrix A.adjugate = (realMatrix A).adjugate := by
  exact (Int.castRingHom ℝ).map_adjugate A

theorem realMatrix_mulVec (A : Matrix n n ℤ) (b : n → ℤ) :
    realMatrix A *ᵥ (fun i => (b i : ℝ)) = fun i => ((A *ᵥ b) i : ℝ) := by
  ext i
  simp [Matrix.mulVec, dotProduct, realMatrix, Matrix.map_apply]

/-- Cramer's denominator statement, including singular matrices whenever the
asserted divisibility still makes sense. -/
theorem integral_multiple_of_solution (A : Matrix n n ℤ) (b : n → ℤ)
    (x : n → ℝ) (h : realMatrix A *ᵥ x = fun i => (b i : ℝ))
    (D : ℤ) (hD : A.det ∣ D) :
    ∃ z : n → ℤ, ∀ i, (z i : ℝ) = (D : ℝ) * x i := by
  obtain ⟨q, hq⟩ := hD
  have hh := congrArg (fun v => (realMatrix A).adjugate *ᵥ v) h
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, realMatrix_det, ← realMatrix_adjugate,
    realMatrix_mulVec] at hh
  refine ⟨fun i => q * (A.adjugate *ᵥ b) i, ?_⟩
  intro i
  have hi := congrFun hh i
  change (A.det : ℝ) * x i = ((A.adjugate *ᵥ b) i : ℝ) at hi
  simp only [Int.cast_mul, hq]
  rw [← hi]
  ring

/-- A nonsingular integral system has at most one real solution. -/
theorem realMatrix_solution_unique (A : Matrix n n ℤ) (hA : A.det ≠ 0)
    (x y : n → ℝ) (h : realMatrix A *ᵥ x = realMatrix A *ᵥ y) : x = y := by
  have hh := congrArg (fun v => (realMatrix A).adjugate *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, realMatrix_det] at hh
  have hd : (A.det : ℝ) ≠ 0 := by exact_mod_cast hA
  ext i
  exact (mul_left_cancel₀ hd (congrFun hh i))

/-- Solving a fixed nonsingular system commutes with affine variation of the
right-hand side.  This is the precise `u_I(ell) = ell*x_I + y_I` identity. -/
theorem affine_solution (A : Matrix n n ℤ) (hA : A.det ≠ 0)
    (d e x y u : n → ℝ) (hd : realMatrix A *ᵥ x = d)
    (he : realMatrix A *ᵥ y = e) (ell : ℝ)
    (hu : realMatrix A *ᵥ u = ell • d + e) : u = ell • x + y := by
  apply realMatrix_solution_unique A hA
  rw [hu, Matrix.mulVec_add, Matrix.mulVec_smul, hd, he]

/-- Beyond the absolute constant term, an affine function with integral slope
has a fixed weak sign, including the zero-slope boundary case. -/
theorem integer_affine_nonpos_iff (a b : ℤ) (x : ℝ)
    (hx : (|b| : ℝ) < x) :
    (a : ℝ) * x + b ≤ 0 ↔ a < 0 ∨ a = 0 ∧ b ≤ 0 := by
  have hx0 : 0 < x := (abs_nonneg (b : ℝ)).trans_lt hx
  have hb1 : -( |b| : ℝ) ≤ (b : ℝ) := neg_abs_le _
  have hb2 : (b : ℝ) ≤ (|b| : ℝ) := le_abs_self _
  constructor
  · intro h
    by_cases ha : a < 0
    · exact Or.inl ha
    have ha0 : 0 ≤ a := le_of_not_gt ha
    have hae : a = 0 := by
      by_contra hne
      have hapos : (1 : ℤ) ≤ a := by omega
      have hap : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hapos
      nlinarith
    right
    refine ⟨hae, ?_⟩
    simpa [hae] using h
  · rintro (ha | ⟨rfl, hb⟩)
    · have ham : a ≤ -1 := by omega
      have har : (a : ℝ) ≤ -1 := by exact_mod_cast ham
      nlinarith
    · simpa using (show (b : ℝ) ≤ 0 by exact_mod_cast hb)

theorem integer_affine_sign_stable (a b : ℤ) (x y : ℝ)
    (hx : (|b| : ℝ) < x) (hy : (|b| : ℝ) < y) :
    ((a : ℝ) * x + b ≤ 0) ↔ ((a : ℝ) * y + b ≤ 0) := by
  rw [integer_affine_nonpos_iff a b x hx, integer_affine_nonpos_iff a b y hy]

end ToricPower


/-! ## Source section: DeterminantPeriod -/

/-!
# The exact determinant period

The period is the least common multiple of nonzero maximal minors of the ray
matrix with the coordinate rows adjoined.  Enumerating ordered row selections
also lists repeated rows, whose zero determinants are replaced by one; it does
not change the least common multiple.
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace ToricPower

variable {n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def minorMagnitude (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) : ℕ :=
  if (C.submatrix I id).det = 0 then 1 else (C.submatrix I id).det.natAbs

def minorPeriod (C : Matrix ι (Fin n) ℤ) : ℕ :=
  Finset.univ.lcm (minorMagnitude C)

theorem nonzero_minor_injective (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι)
    (hI : (C.submatrix I id).det ≠ 0) : Function.Injective I := by
  intro i j hij
  by_contra hne
  apply hI
  apply Matrix.det_zero_of_row_eq hne
  ext k
  exact congrArg (fun r => C r k) hij

/-- Repeated row selections contribute only the neutral lcm factor `1`.
Thus the executable enumeration agrees with the lcm over genuine minors. -/
theorem minorPeriod_eq_genuine_minors (C : Matrix ι (Fin n) ℤ) :
    minorPeriod C = Finset.univ.lcm (fun I : Fin n ↪ ι => minorMagnitude C I) := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro I _
    by_cases hI : (C.submatrix I id).det = 0
    · simp [minorMagnitude, hI]
    · let e : Fin n ↪ ι := ⟨I, nonzero_minor_injective C I hI⟩
      exact Finset.dvd_lcm (s := Finset.univ)
        (f := fun J : Fin n ↪ ι => minorMagnitude C J) (Finset.mem_univ e)
  · apply Finset.lcm_dvd
    intro I _
    exact Finset.dvd_lcm (s := Finset.univ) (f := minorMagnitude C) (Finset.mem_univ (I : Fin n → ι))

theorem minorMagnitude_pos (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) :
    0 < minorMagnitude C I := by
  unfold minorMagnitude
  split_ifs with h
  · omega
  · exact Int.natAbs_pos.mpr h

theorem minorPeriod_pos (C : Matrix ι (Fin n) ℤ) : 0 < minorPeriod C := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro I _
  exact ne_of_gt (minorMagnitude_pos C I)

theorem minor_dvd_period (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι)
    (hI : (C.submatrix I id).det ≠ 0) :
    (C.submatrix I id).det ∣ (minorPeriod C : ℤ) := by
  apply Int.dvd_natCast.mpr
  have h := Finset.dvd_lcm (s := Finset.univ) (f := minorMagnitude C) (Finset.mem_univ I)
  simpa [minorMagnitude, hI, minorPeriod] using h

def augmentedRayMatrix (A : Matrix (Fin s) (Fin n) ℤ) :
    Matrix (Fin n ⊕ Fin s) (Fin n) ℤ :=
  fun i j => Sum.casesOn i (fun k => if k = j then 1 else 0) (fun k => A k j)

/-- The `Δ` of Sections 6 and 7, as a finite executable lcm expression. -/
def rayPeriod (A : Matrix (Fin s) (Fin n) ℤ) : ℕ := minorPeriod (augmentedRayMatrix A)

def constraintSign : Bool → ℤ
  | false => -1
  | true => 1

@[simp] theorem abs_constraintSign (b : Bool) : |constraintSign b| = 1 := by
  cases b <;> norm_num [constraintSign]

@[simp] theorem natAbs_constraintSign (b : Bool) : (constraintSign b).natAbs = 1 := by
  cases b <;> norm_num [constraintSign]

def signedRows (C : Matrix ι (Fin n) ℤ) : Matrix (Bool × ι) (Fin n) ℤ :=
  fun i j => constraintSign i.1 * C i.2 j

theorem signedRows_minor_det (C : Matrix ι (Fin n) ℤ) (I : Fin n → Bool × ι) :
    ((signedRows C).submatrix I id).det =
      (∏ k, constraintSign (I k).1) * (C.submatrix (fun k => (I k).2) id).det := by
  exact Matrix.det_mul_column (fun k => constraintSign (I k).1)
    (C.submatrix (fun k => (I k).2) id)

theorem signedRows_minor_natAbs (C : Matrix ι (Fin n) ℤ) (I : Fin n → Bool × ι) :
    ((signedRows C).submatrix I id).det.natAbs =
      (C.submatrix (fun k => (I k).2) id).det.natAbs := by
  rw [signedRows_minor_det, Int.natAbs_mul]
  have hp : (∏ k, constraintSign (I k).1).natAbs = 1 := by
    change Int.natAbsHom (∏ k, constraintSign (I k).1) = 1
    rw [map_prod]
    simp
  rw [hp, one_mul]

theorem signedRows_minor_dvd_period (C : Matrix ι (Fin n) ℤ)
    (I : Fin n → Bool × ι) (hI : ((signedRows C).submatrix I id).det ≠ 0) :
    ((signedRows C).submatrix I id).det ∣ (minorPeriod C : ℤ) := by
  have hbase : (C.submatrix (fun k => (I k).2) id).det ≠ 0 := by
    intro h
    apply hI
    rw [signedRows_minor_det, h, mul_zero]
  apply Int.dvd_natCast.mpr
  rw [signedRows_minor_natAbs]
  exact Int.dvd_natCast.mp (minor_dvd_period C _ hbase)

theorem rayPeriod_pos (A : Matrix (Fin s) (Fin n) ℤ) : 0 < rayPeriod A :=
  minorPeriod_pos _

theorem rayPeriod_zero_dimension (A : Matrix (Fin s) (Fin 0) ℤ) : rayPeriod A = 1 := by
  unfold rayPeriod minorPeriod
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro I _
    simp [minorMagnitude]
  · exact one_dvd _

end ToricPower


/-! ## Source section: LatticePeriod -/

/-!
# Periodicity from rational Minkowski expansion

This is the last geometric step of Theorem 7.2.  It proves the period from the
literal Minkowski identity and a finite integral vertex family after clearing
denominators.  The bound is the ambient dimension, uniformly for all polytopes.
-/

@[expose] public section
noncomputable section

open Set Module
open scoped BigOperators Pointwise

namespace ToricPower

def integerLattice (n : ℕ) : AddSubgroup (Fin n → ℝ) where
  carrier := {x | ∃ z : Fin n → ℤ, ∀ i, (z i : ℝ) = x i}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by intro i; simp [hz, hw]⟩
  neg_mem' := by
    rintro x ⟨z, hz⟩
    exact ⟨-z, by intro i; simp [hz]⟩

@[simp] theorem mem_integerLattice {n : ℕ} (x : Fin n → ℝ) :
    x ∈ integerLattice n ↔ ∃ z : Fin n → ℤ, ∀ i, (z i : ℝ) = x i := Iff.rfl

theorem integer_cast_mem {n : ℕ} (z : Fin n → ℤ) :
    (fun i => (z i : ℝ)) ∈ integerLattice n := ⟨z, fun _ => rfl⟩

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma lattice_intersection_translate (L : AddSubgroup E) (P : Set E)
    (a : E) (ha : a ∈ L) :
    ((({a} : Set E) + P) ∩ (L : Set E)).Nonempty ↔ (P ∩ (L : Set E)).Nonempty := by
  constructor
  · rintro ⟨z, ⟨a', ha', p, hp, rfl⟩, hz⟩
    have h : a' = a := ha'
    subst a'
    refine ⟨p, hp, ?_⟩
    simpa using L.sub_mem hz ha
  · rintro ⟨p, hp, hpL⟩
    exact ⟨a + p, ⟨a, rfl, p, hp, rfl⟩, L.add_mem ha hpL⟩

lemma centered_set_eq (Q : Set E) (q : E) :
    ({q} : Set E) + (Q + {-q}) = Q := by
  calc
    ({q} : Set E) + (Q + {-q}) = Q + ({q} + {-q}) := by ac_rfl
    _ = Q := by simp

lemma centered_convexHull [DecidableEq E] (vertices : Finset E) (q : E) (D : ℝ) :
    convexHull ℝ ((vertices.image (fun v => D • (v - q)) : Finset E) : Set E) =
      D • (convexHull ℝ (vertices : Set E) + {-q}) := by
  classical
  have hset : (((vertices.image (fun v => D • (v - q)) : Finset E) : Set E)) =
      D • ((vertices : Set E) + {-q}) := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨v - q, ⟨v, hv, -q, rfl, by simp [sub_eq_add_neg]⟩, rfl⟩
    · rintro ⟨v, ⟨w, hw, r, hr, rfl⟩, rfl⟩
      have : r = -q := hr
      subst r
      exact Finset.mem_image.mpr ⟨w, hw, by simp [sub_eq_add_neg]⟩
  rw [hset, convexHull_smul, convexHull_add]
  simp

lemma scaled_centered_decomposition (Q : Set E) (hQ : Convex ℝ Q)
    (q : E) (D r t : ℝ) (hr : 0 ≤ r) (htD : 0 ≤ t * D) :
    (r + t * D) • Q =
      r • Q + ({t • (D • q)} : Set E) + t • (D • (Q + {-q})) := by
  rw [hQ.add_smul hr htD, add_assoc]
  congr 1
  calc
    (t * D) • Q = (t * D) • (({q} : Set E) + (Q + {-q})) := by
      rw [centered_set_eq]
    _ = (t * D) • ({q} : Set E) + (t * D) • (Q + {-q}) := smul_add _ _ _
    _ = ({t • (D • q)} : Set E) + t • (D • (Q + {-q})) := by
      simp [smul_smul]

theorem rational_expansion_residue_stable [FiniteDimensional ℝ E]
    (Lattice : AddSubgroup E) (vertices : Finset E) (q : E)
    (hq : q ∈ convexHull ℝ (vertices : Set E))
    (D : ℕ) (hintegral : ∀ v ∈ vertices, (D : ℝ) • v ∈ Lattice)
    (hqintegral : (D : ℝ) • q ∈ Lattice)
    (P : Set E) (r : ℝ) (hr : 0 ≤ r)
    (t u : ℕ) (ht : finrank ℝ E ≤ t) (hu : finrank ℝ E ≤ u) :
    ((P + (r + (t : ℝ) * D) • convexHull ℝ (vertices : Set E)) ∩
      (Lattice : Set E)).Nonempty ↔
    ((P + (r + (u : ℝ) * D) • convexHull ℝ (vertices : Set E)) ∩
      (Lattice : Set E)).Nonempty := by
  classical
  let centered := vertices.image (fun v => (D : ℝ) • (v - q))
  have hcint : (centered : Set E) ⊆ Lattice := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    change (D : ℝ) • (v - q) ∈ Lattice
    rw [smul_sub]
    exact Lattice.sub_mem (hintegral v hv) hqintegral
  have hcenter : convexHull ℝ (centered : Set E) =
      (D : ℝ) • (convexHull ℝ (vertices : Set E) + {-q}) :=
    centered_convexHull vertices q D
  have hc0 : (0 : E) ∈ convexHull ℝ (centered : Set E) := by
    rw [hcenter]
    refine ⟨0, ⟨q, hq, -q, rfl, by simp⟩, by simp⟩
  have htranslate (v : ℕ) : (v : ℝ) • ((D : ℝ) • q) ∈ Lattice := by
    simpa only [Nat.cast_smul_eq_nsmul] using Lattice.nsmul_mem hqintegral v
  have hreduce (v : ℕ) :
      ((P + (r + (v : ℝ) * D) • convexHull ℝ (vertices : Set E)) ∩
        (Lattice : Set E)).Nonempty ↔
      (((P + r • convexHull ℝ (vertices : Set E)) +
        (v : ℝ) • convexHull ℝ (centered : Set E)) ∩ (Lattice : Set E)).Nonempty := by
    rw [scaled_centered_decomposition _ (convex_convexHull ℝ _) q (D : ℝ) r
      (v : ℝ) hr (by positivity), ← hcenter]
    have heq : P + (r • convexHull ℝ (vertices : Set E) +
        {(v : ℝ) • ((D : ℝ) • q)} + (v : ℝ) • convexHull ℝ (centered : Set E)) =
      ({(v : ℝ) • ((D : ℝ) • q)} : Set E) +
        ((P + r • convexHull ℝ (vertices : Set E)) +
          (v : ℝ) • convexHull ℝ (centered : Set E)) := by ac_rfl
    rw [heq]
    exact lattice_intersection_translate _ _ _ (htranslate v)
  rw [hreduce t, hreduce u]
  exact (paper_lemma_7_1_ambient_bound Lattice centered hcint hc0 _ t ht).trans
    (paper_lemma_7_1_ambient_bound Lattice centered hcint hc0 _ u hu).symm

/-- Once a family is an exact Minkowski expansion by a rational polytope,
integer feasibility is periodic with its common vertex denominator.  The
threshold is explicit and permits empty family members and zero-dimensional
polytopes. -/
theorem rational_expansion_eventually_periodic [FiniteDimensional ℝ E]
    (Lattice : AddSubgroup E) (vertices : Finset E) (q : E)
    (hq : q ∈ convexHull ℝ (vertices : Set E))
    (D : ℕ) (hD : 0 < D)
    (hintegral : ∀ v ∈ vertices, (D : ℝ) • v ∈ Lattice)
    (hqintegral : (D : ℝ) • q ∈ Lattice)
    (P : Set E) (family : ℕ → Set E) (base : ℕ)
    (hexpand : ∀ ell : ℕ, base ≤ ell →
      family ell = P + ((ell - base : ℕ) : ℝ) • convexHull ℝ (vertices : Set E))
    (ell : ℕ) (hell : base + D * finrank ℝ E ≤ ell) :
    (family (ell + D) ∩ (Lattice : Set E)).Nonempty ↔
      (family ell ∩ (Lattice : Set E)).Nonempty := by
  let t := (ell - base) / D
  let r := (ell - base) % D
  have hb : base ≤ ell := by omega
  have hdec : ell - base = r + t * D := by
    simpa [t, r, Nat.mul_comm] using (Nat.mod_add_div (ell - base) D).symm
  have hr : r < D := Nat.mod_lt _ hD
  have ht : finrank ℝ E ≤ t := by
    by_contra h
    have hsmall : t + 1 ≤ finrank ℝ E := by omega
    have hmul := Nat.mul_le_mul_right D hsmall
    have hlarge : D * finrank ℝ E ≤ ell - base := by omega
    nlinarith
  have hdec' : ell + D - base = r + (t + 1) * D := by
    have hshift : ell + D - base = (ell - base) + D := by omega
    rw [hshift, hdec]
    ring
  rw [hexpand (ell + D) (by omega), hexpand ell hb, hdec, hdec']
  push_cast
  simpa only [Nat.cast_add, Nat.cast_one] using
    rational_expansion_residue_stable Lattice vertices q hq D hintegral hqintegral
    P (r : ℝ) (Nat.cast_nonneg _) (t + 1) t (by omega) ht

end ToricPower
