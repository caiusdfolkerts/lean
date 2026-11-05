module

public import paper_verification.literal016
import all paper_verification.literal016
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsTorusAction -/


/-!
# The diagonal torus of the regular Borel action

In chain coordinates the integer weights are `2k-2i`. This gives precisely
`H aᵢ=(2i-2k-2)aᵢ` and `H bⱼ=(2k-2j)bⱼ`. The pullback weights of the two
forms are `-2` and `0`, and the torus rescales the nilpotent generator by the
square character. All identities are for actual linear maps and forms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

open RegularNilpotentFlag

variable {K : Type*} [Field K] [CharZero K]

/-- Integer torus weights along the chain. -/
def chainWeight (k : ℕ) (i : Fin (2*k+1)) : ℤ := 2*(k : ℤ)-2*(i.val : ℤ)

/-- The diagonal torus acts through actual integer powers of a nonzero scalar. -/
def torusMap (k : ℕ) (t : Kˣ) : Module.End K (ChainSpace K k) where
  toFun v i := ((t^chainWeight k i : Kˣ) : K)*v i
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]

@[simp] theorem torusMap_apply (k : ℕ) (t : Kˣ) (v : ChainSpace K k) (i) :
    torusMap k t v i=((t^chainWeight k i : Kˣ) : K)*v i := rfl

@[simp] theorem torusMap_one (k : ℕ) : torusMap (K := K) k 1=1 := by
  ext v i
  simp [torusMap]

theorem torusMap_mul (k : ℕ) (t u : Kˣ) :
    torusMap k (t*u)=torusMap k t*torusMap k u := by
  ext v i
  simp [torusMap,mul_zpow,mul_assoc]

@[simp] theorem torusMap_single (k : ℕ) (t : Kˣ) (i : Fin (2*k+1)) :
    torusMap k t (Pi.single i 1)=((t^chainWeight k i : Kˣ) : K) • Pi.single i 1 := by
  ext j
  by_cases h : i=j
  · subst j
    simp [torusMap,Pi.single_apply]
  · simp [torusMap,Pi.single_apply,h]

/-- A common anti-diagonal gives a single torus weight. -/
theorem torus_antiDiagonal_coeff (k r : ℕ) (t : Kˣ) (i j : Fin (2*k+1)) :
    ((t^chainWeight k i : Kˣ) : K)*((t^chainWeight k j : Kˣ) : K)*
        skewAntiDiagonal k r i j =
      ((t^(4*(k : ℤ)-2*(r : ℤ)) : Kˣ) : K)*skewAntiDiagonal k r i j := by
  by_cases h : i.val+j.val=r
  · have hcast : (i.val : ℤ)+(j.val : ℤ)=(r : ℤ) := by exact_mod_cast h
    have hw : chainWeight k i+chainWeight k j=4*(k : ℤ)-2*(r : ℤ) := by
      unfold chainWeight
      linear_combination -2*hcast
    rw [← Units.val_mul,← zpow_add,hw]
  · simp [skewAntiDiagonal,h]

/-- Exact pullback as an equality of actual bilinear forms. -/
theorem torus_antiDiagonal_pullback (k r : ℕ) (t : Kˣ) :
    ((skewAntiDiagonal (K := K) k r).toBilin').comp (torusMap k t) (torusMap k t) =
      ((t^(4*(k : ℤ)-2*(r : ℤ)) : Kˣ) : K) • (skewAntiDiagonal k r).toBilin' := by
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro i
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro j
  simp only [Pi.basisFun_apply,LinearMap.BilinForm.comp_apply,torusMap_single,
    map_smul,LinearMap.smul_apply,smul_eq_mul,Matrix.toBilin'_single]
  rw [← mul_assoc]
  simpa only [mul_comm] using torus_antiDiagonal_coeff k r t i j

/-- The first form has weight `-2`. -/
theorem firstForm_torus_pullback (k : ℕ) (t : Kˣ) :
    (firstForm k).comp (torusMap k t) (torusMap k t)=
      ((t^(-2 : ℤ) : Kˣ) : K) • firstForm k := by
  have h : 4*(k : ℤ)-2*((2*k+1 : ℕ) : ℤ)=(-2 : ℤ) := by push_cast; ring
  simpa only [firstForm,h] using torus_antiDiagonal_pullback k (2*k+1) t

/-- The second form has weight zero. -/
theorem secondForm_torus_pullback (k : ℕ) (t : Kˣ) :
    (secondForm k).comp (torusMap k t) (torusMap k t)=secondForm k := by
  have h : 4*(k : ℤ)-2*((2*k : ℕ) : ℤ)=0 := by push_cast; ring
  simpa only [secondForm,h,zpow_zero,Units.val_one,one_smul] using
    torus_antiDiagonal_pullback k (2*k) t

/-- The square character intertwines the generator and the torus. -/
theorem torusMap_generator (k : ℕ) (t : Kˣ) :
    torusMap k t*generator k=(t.val^2) • (generator k*torusMap k t) := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [Module.End.mul_apply,torusMap_apply,generator,weightedShift_apply,
    LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs with h
  · have hw : chainWeight k i=2+chainWeight k ⟨i.val+1,h⟩ := by
      simp only [chainWeight,Nat.cast_add,Nat.cast_one]
      ring
    rw [hw,zpow_add]
    simp only [Units.val_mul,zpow_ofNat,Units.val_pow_eq_pow_val]
    ring
  · simp

/-- The actual unipotent and torus maps satisfy the Borel semidirect-product
relation, so the action has the required square character. -/
theorem torusMap_gaMap (k : ℕ) (t : Kˣ) (u : K) :
    torusMap k t*gaMap k u=gaMap k (t.val^2*u)*torusMap k t := by
  unfold gaMap
  have hcompat : ((t.val^2*u) • generator (K := K) k) ∘ₗ torusMap k t =
      torusMap k t ∘ₗ (u • generator k) := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun T : Module.End K (ChainSpace K k) => T v)
      (torusMap_generator k t)
    simp only [Module.End.mul_apply,LinearMap.smul_apply] at h
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul,h,smul_smul]
    rw [mul_comm u]
  exact (Module.End.commute_exp_left_of_commute
    ((generator_nilpotent k).smul u)
    ((generator_nilpotent k).smul (t.val^2*u)) hcompat).symm

end PaperVerification.AlternatingForms.CanonicalUnipotent
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsTorusAction"

section ComponentSource_1
/- Original module: PaperVerification.DiagonalInvariantSubspaces -/


/-!
# Invariant subspaces for a diagonal operator with distinct eigenvalues

The proof constructs the finite spectral projectors as products of linear
factors. It identifies an invariant subspace with the actual coordinate
subspace spanned by the coordinate vectors it contains. This applies to the
torus-fixed subspaces once one torus element has distinct eigenvalues.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DiagonalInvariantSubspaces

open scoped BigOperators Classical

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The actual diagonal endomorphism in the coordinate basis. -/
def diagonal (d : ι → K) : Module.End K (ι → K) where
  toFun v i := d i * v i
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]

@[simp] theorem diagonal_apply (d : ι → K) (v : ι → K) (i : ι) :
    diagonal d v i = d i * v i := rfl

/-- Applying any finite product of factors `D-dⱼ` preserves an invariant
subspace. The displayed expression gives every coordinate of the result. -/
theorem spectralProduct_mem (d : ι → K) (U : Submodule K (ι → K))
    (hU : ∀ v ∈ U, diagonal d v ∈ U) (s : Finset ι)
    (v : ι → K) (hv : v ∈ U) :
    (fun i => (∏ j ∈ s, (d i-d j))*v i) ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert j s hj ih =>
    have h := U.sub_mem (hU _ ih) (U.smul_mem (d j) ih)
    convert h using 1
    ext i
    simp only [Finset.prod_insert hj, Pi.sub_apply, Pi.smul_apply,
      diagonal_apply, smul_eq_mul]
    ring

/-- A coordinate component of a vector in an invariant subspace belongs
to that subspace when all diagonal entries are distinct. -/
theorem coordinateComponent_mem (d : ι → K) (hd : Function.Injective d)
    (U : Submodule K (ι → K)) (hU : ∀ v ∈ U, diagonal d v ∈ U)
    (v : ι → K) (hv : v ∈ U) (i : ι) : Pi.single i (v i) ∈ U := by
  classical
  let c := ∏ j ∈ Finset.univ.erase i, (d i-d j)
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hd h).symm)
  have h := U.smul_mem c⁻¹ (spectralProduct_mem d U hU (Finset.univ.erase i) v hv)
  convert h using 1
  ext j
  by_cases hji : j = i
  · subst j
    simp [c, hc]
  · have hprod : (∏ q ∈ Finset.univ.erase i, (d j-d q)) = 0 :=
      Finset.prod_eq_zero (show j ∈ Finset.univ.erase i by simp [hji]) (by simp)
    simp [Pi.single_apply, hji, hprod]

/-- The coordinate support of a subspace, defined intrinsically by which
coordinate vectors belong to it. -/
def coordinateSupport (U : Submodule K (ι → K)) : Set ι :=
  {i | Pi.single i 1 ∈ U}

/-- Every invariant subspace is a coordinate subspace; there are no further
invariant subspaces when the eigenvalues are pairwise distinct. -/
theorem invariant_eq_coordinateSubspace (d : ι → K) (hd : Function.Injective d)
    (U : Submodule K (ι → K)) (hU : ∀ v ∈ U, diagonal d v ∈ U) :
    U = Pi.spanSubset K (coordinateSupport U) := by
  classical
  apply le_antisymm
  · intro v hv
    rw [Pi.mem_spanSubset_iff]
    intro i hi
    by_contra hvi
    apply hi
    change Pi.single i 1 ∈ U
    have h := U.smul_mem (v i)⁻¹ (coordinateComponent_mem d hd U hU v hv i)
    convert h using 1
    ext j
    by_cases hij : i = j
    · subst j
      simp [hvi]
    · simp [Pi.single_apply, hij]
  · change Submodule.span K (Pi.basisFun K ι '' coordinateSupport U) ≤ U
    rw [Submodule.span_le]
    rintro _ ⟨i,hi,rfl⟩
    change Pi.basisFun K ι i ∈ U
    rw [Pi.basisFun_apply]
    exact hi

/-- Every coordinate subspace is invariant under every diagonal map. -/
theorem coordinateSubspace_invariant (d : ι → K) (s : Set ι)
    (v : ι → K) (hv : v ∈ Pi.spanSubset K s) : diagonal d v ∈ Pi.spanSubset K s := by
  rw [Pi.mem_spanSubset_iff] at hv ⊢
  intro i hi
  simp [hv i hi]

theorem invariant_iff_coordinateSubspace (d : ι → K) (hd : Function.Injective d)
    (U : Submodule K (ι → K)) :
    (∀ v ∈ U, diagonal d v ∈ U) ↔ ∃ s : Set ι, U = Pi.spanSubset K s := by
  constructor
  · intro h
    exact ⟨coordinateSupport U,invariant_eq_coordinateSubspace d hd U h⟩
  · rintro ⟨s,rfl⟩
    exact coordinateSubspace_invariant d s

end PaperVerification.DiagonalInvariantSubspaces
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.DiagonalInvariantSubspaces"

section ComponentSource_2
/- Original module: PaperVerification.AlternatingFormsTorusFixedPlanes -/


/-!
# The actual torus-fixed planes are coordinate planes

The torus element with scalar `2` has pairwise distinct eigenvalues over every
characteristic-zero field. The proof transports the strict monotonicity of
rational powers of `2` through the injective rational embedding. The spectral
projector theorem then classifies all fixed subspaces, in every dimension.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

variable {K : Type*} [Field K] [CharZero K]

/-- A fixed non-torsion scalar for separating all integer torus weights. -/
def twoUnit : Kˣ := Units.mk0 2 (by norm_num)

theorem chainWeight_injective (k : ℕ) : Function.Injective (chainWeight k) := by
  intro i j hij
  apply Fin.ext
  unfold chainWeight at hij
  omega

/-- The eigenvalues of one actual torus element are pairwise distinct. -/
theorem twoUnit_eigenvalues_injective (k : ℕ) :
    Function.Injective (fun i : Fin (2*k+1) =>
      ((twoUnit (K:=K)^chainWeight k i : Kˣ) : K)) := by
  intro i j hij
  have hK : (2 : K)^chainWeight k i = (2 : K)^chainWeight k j := by
    simpa only [Units.val_zpow_eq_zpow_val,twoUnit,Units.val_mk0] using hij
  have hQ : (2 : ℚ)^chainWeight k i = (2 : ℚ)^chainWeight k j := by
    apply Rat.cast_injective (α:=K)
    simpa only [Rat.cast_zpow,Rat.cast_ofNat] using hK
  exact chainWeight_injective k ((zpow_right_strictMono₀ (by norm_num : (1 : ℚ)<2)).injective hQ)

/-- Every coordinate subspace is preserved, as a subspace and not merely by
inclusion, by each invertible diagonal torus element. -/
theorem coordinateSubspace_map_torus (k : ℕ) (s : Set (Fin (2*k+1))) (t : Kˣ) :
    (Pi.spanSubset K s).map (torusMap k t) = Pi.spanSubset K s := by
  have hs (t : Kˣ) (v : ChainSpace K k) (hv : v ∈ Pi.spanSubset K s) :
      torusMap k t v ∈ Pi.spanSubset K s :=
    DiagonalInvariantSubspaces.coordinateSubspace_invariant
      (fun i => ((t^chainWeight k i : Kˣ) : K)) s v hv
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact hs t v hv
  · intro v hv
    apply Submodule.mem_map.mpr
    refine ⟨torusMap k t⁻¹ v,hs t⁻¹ v hv,?_⟩
    change (torusMap k t * torusMap k t⁻¹) v = v
    rw [← torusMap_mul,mul_inv_cancel,torusMap_one,Module.End.one_apply]

/-- Exact classification of all fixed subspaces of the actual torus action. -/
theorem torus_fixed_iff_coordinateSubspace (k : ℕ) (U : Submodule K (ChainSpace K k)) :
    (∀ t : Kˣ, U.map (torusMap k t)=U) ↔
      ∃ s : Set (Fin (2*k+1)), U=Pi.spanSubset K s := by
  constructor
  · intro h
    apply (DiagonalInvariantSubspaces.invariant_iff_coordinateSubspace
      (fun i => ((twoUnit (K:=K)^chainWeight k i : Kˣ) : K))
      (twoUnit_eigenvalues_injective k) U).mp
    intro v hv
    have hm : torusMap k twoUnit v ∈ U.map (torusMap k twoUnit) :=
      Submodule.mem_map.mpr ⟨v,hv,rfl⟩
    rwa [h twoUnit] at hm
  · rintro ⟨s,rfl⟩
    exact coordinateSubspace_map_torus k s

/-- In particular the torus has only finitely many fixed subspaces; imposing
dimension and isotropy can only select a finite subset of these. -/
theorem finite_torus_fixed_subspaces (k : ℕ) :
    Finite {U : Submodule K (ChainSpace K k) // ∀ t : Kˣ, U.map (torusMap k t)=U} := by
  let f : Set (Fin (2*k+1)) →
      {U : Submodule K (ChainSpace K k) // ∀ t : Kˣ, U.map (torusMap k t)=U} :=
    fun s => ⟨Pi.spanSubset K s,coordinateSubspace_map_torus k s⟩
  apply Finite.of_surjective f
  intro U
  obtain ⟨s,hs⟩ := (torus_fixed_iff_coordinateSubspace k U.val).mp U.property
  exact ⟨s,Subtype.ext hs.symm⟩

/-- In the chain coordinates the two forms join exactly the pairs with
index sums `2k` or `2k+1`; diagonal pairs are alternating and contribute zero. -/
def IsIndependentCoordinateSet (k : ℕ) (S : Set (Fin (2*k+1))) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i=j ∨ (i.val+j.val ≠ 2*k ∧ i.val+j.val ≠ 2*k+1)

/-- This combinatorial condition is equivalent to the original two
bilinear isotropy equations on the entire coordinate subspace. -/
theorem coordinateSubspace_isotropic_iff (k : ℕ) (S : Set (Fin (2*k+1))) :
    IsCommonIsotropic k (Pi.spanSubset K S) ↔ IsIndependentCoordinateSet k S := by
  classical
  have hsingle (i : Fin (2*k+1)) (hi : i ∈ S) :
      Pi.single i (1 : K) ∈ Pi.spanSubset K S := by
    rw [Pi.mem_spanSubset_iff]
    intro j hj
    have hne : i ≠ j := fun he => hj (he ▸ hi)
    simp [Pi.single_apply,hne]
  constructor
  · intro h i hi j hj
    by_cases hij : i=j
    · exact Or.inl hij
    · right
      have hvals : i.val ≠ j.val := fun he => hij (Fin.ext he)
      have hforms := h _ (hsingle i hi) _ (hsingle j hj)
      simp only [firstForm,secondForm,Matrix.toBilin'_single] at hforms
      constructor
      · intro he
        have hz := hforms.2
        unfold skewAntiDiagonal at hz
        rcases lt_or_gt_of_ne hvals with hlt|hgt
        · simp [he,hlt,not_lt_of_gt hlt] at hz
        · simp [he,hgt,not_lt_of_gt hgt] at hz
      · intro he
        have hz := hforms.1
        unfold skewAntiDiagonal at hz
        rcases lt_or_gt_of_ne hvals with hlt|hgt
        · simp [he,hlt,not_lt_of_gt hlt] at hz
        · simp [he,hgt,not_lt_of_gt hgt] at hz
  · intro h u hu v hv
    rw [Pi.mem_spanSubset_iff] at hu hv
    have hform (r : ℕ) (hr : r=2*k ∨ r=2*k+1) :
        (skewAntiDiagonal (K:=K) k r).toBilin' u v=0 := by
      rw [Matrix.toBilin'_apply]
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ S
        · have hz : skewAntiDiagonal (K:=K) k r i j=0 := by
            rcases h i hi j hj with rfl|hij
            · simp [skewAntiDiagonal]
            · rcases hr with rfl|rfl <;> simp [skewAntiDiagonal,hij.1,hij.2]
          rw [hz]
          simp
        · rw [hv j hj,mul_zero]
      · rw [hu i hi,zero_mul,zero_mul]
    exact ⟨hform _ (Or.inr rfl),hform _ (Or.inl rfl)⟩

end PaperVerification.AlternatingForms.CanonicalUnipotent
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsTorusFixedPlanes"

section ComponentSource_3
/- Original module: PaperVerification.SeparatedSubsets -/


/-!
# Subsets with a gap between successive entries

Deleting one unused position before each selected entry gives an explicit
bijection between the `s`-element independent subsets of an `n`-vertex path
and the `s`-element subsets of `Fin (n + 1 - s)`.

This is the finite combinatorial input for the attracting-cell argument.
Neither a cohomology dimension nor a geometric assertion enters its definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SeparatedSubsets

/-- The actual independent subsets of the path on the ordered vertices `Fin n`. -/
abbrev Independent (n s : ℕ) :=
  {S : Finset (Fin n) // S.card = s ∧
    ∀ i ∈ S, ∀ j ∈ S, i < j → i.val + 2 ≤ j.val}

/-- Increasing parametrizations of independent subsets. -/
abbrev SpacedEmbedding (n s : ℕ) :=
  {e : Fin s ↪o Fin n // ∀ i j, i < j → (e i).val + 2 ≤ (e j).val}

/-- An order embedding is uniquely determined by its finite image. -/
def orderEmbeddingEquivSubsets (n s : ℕ) :
    (Fin s ↪o Fin n) ≃ {S : Finset (Fin n) // S.card = s} where
  toFun e := ⟨Finset.univ.map e.toEmbedding, by simp⟩
  invFun S := S.val.orderEmbOfFin S.property
  left_inv e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  right_inv S := by
    apply Subtype.ext
    exact Finset.map_orderEmbOfFin_univ S.val S.property

/-- Enumerating a finite set identifies its intrinsic separation condition
with the corresponding condition on its increasing parametrization. -/
def independentEquivSpaced (n s : ℕ) : Independent n s ≃ SpacedEmbedding n s where
  toFun S := ⟨S.val.orderEmbOfFin S.property.1, by
    intro i j hij
    apply S.property.2
    · exact Finset.orderEmbOfFin_mem _ _ i
    · exact Finset.orderEmbOfFin_mem _ _ j
    · exact (S.val.orderEmbOfFin S.property.1).strictMono hij⟩
  invFun e := ⟨Finset.univ.map e.val.toEmbedding, by
    constructor
    · simp
    · intro i hi j hj hij
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hj
      exact e.property a b (e.val.lt_iff_lt.mp hij)⟩
  left_inv S := by
    apply Subtype.ext
    exact Finset.map_orderEmbOfFin_univ S.val S.property.1
  right_inv e := by
    apply Subtype.ext
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Successive gaps of size at least two accumulate across an arbitrary interval. -/
theorem spaced_distance {n s : ℕ} (e : SpacedEmbedding n s)
    (i j : Fin s) (hij : i ≤ j) :
    (e.val i).val + 2 * (j.val - i.val) ≤ (e.val j).val := by
  have H : ∀ b, ∀ hb : b < s, i.val ≤ b →
      (e.val i).val + 2 * (b - i.val) ≤ (e.val ⟨b, hb⟩).val := by
    intro b
    induction b with
    | zero =>
        intro hb hi
        have hval : i.val = 0 := by omega
        have h : i = ⟨0, hb⟩ := Fin.ext hval
        subst i
        simp
    | succ b ih =>
        intro hb hi
        by_cases he : i.val = b + 1
        · have h : i = ⟨b + 1, hb⟩ := Fin.ext he
          subst i
          simp
        · have hb' : b < s := by omega
          have hprev := ih hb' (by omega)
          have hstep := e.property ⟨b, hb'⟩ ⟨b + 1, hb⟩ (by
            change b < b + 1
            omega)
          omega
  exact H j.val j.isLt hij

theorem spaced_lower_bound {n s : ℕ} (e : SpacedEmbedding n s) (i : Fin s) :
    2 * i.val ≤ (e.val i).val := by
  have hs : 0 < s := by have := i.isLt; omega
  have h := spaced_distance e ⟨0, hs⟩ i (by change 0 ≤ i.val; omega)
  dsimp only at h
  omega

theorem compressed_bound {n s : ℕ} (e : SpacedEmbedding n s) (i : Fin s) :
    (e.val i).val - i.val < n + 1 - s := by
  have hs : 0 < s := by have := i.isLt; omega
  let j : Fin s := ⟨s - 1, by omega⟩
  have h := spaced_distance e i j (by change i.val ≤ s - 1; have := i.isLt; omega)
  have hn := (e.val j).isLt
  have hi := i.isLt
  have hl := spaced_lower_bound e i
  dsimp only [j] at h hn
  omega

theorem compressed_strictMono {n s : ℕ} (e : SpacedEmbedding n s) :
    StrictMono (fun i : Fin s => (e.val i).val - i.val) := by
  intro i j hij
  have h := spaced_distance e i j (le_of_lt hij)
  have hi := spaced_lower_bound e i
  have hj := spaced_lower_bound e j
  change i.val < j.val at hij
  change (e.val i).val - i.val < (e.val j).val - j.val
  omega

/-- Remove the `i` unused positions forced before the `i`-th selected vertex. -/
def compress {n s : ℕ} (e : SpacedEmbedding n s) : Fin s ↪o Fin (n + 1 - s) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(e.val i).val - i.val, compressed_bound e i⟩)
    (compressed_strictMono e)

/-- Reinsert those positions. This map is valid also for the empty subset. -/
def expand {n s : ℕ} (hs : s ≤ n + 1)
    (e : Fin s ↪o Fin (n + 1 - s)) : SpacedEmbedding n s := by
  let f : Fin s → Fin n := fun i => ⟨(e i).val + i.val, by
    have hi := i.isLt
    have he := (e i).isLt
    omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have he := e.strictMono hij
    change (e i).val < (e j).val at he
    change i.val < j.val at hij
    change (e i).val + i.val < (e j).val + j.val
    omega
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro i j hij
  have he := e.strictMono hij
  change (e i).val < (e j).val at he
  change i.val < j.val at hij
  change (e i).val + i.val + 2 ≤ (e j).val + j.val
  omega

/-- The gap-deletion bijection, retaining every size in the stated range. -/
def gapEquiv (n s : ℕ) (hs : s ≤ n + 1) :
    SpacedEmbedding n s ≃ (Fin s ↪o Fin (n + 1 - s)) where
  toFun := compress
  invFun := expand hs
  left_inv e := by
    apply Subtype.ext
    apply RelEmbedding.ext
    intro i
    apply Fin.ext
    change (e.val i).val - i.val + i.val = (e.val i).val
    have h := spaced_lower_bound e i
    omega
  right_inv e := by
    apply RelEmbedding.ext
    intro i
    apply Fin.ext
    change (e i).val + i.val - i.val = (e i).val
    omega

/-- An explicit bijection with ordinary subsets of the shortened interval. -/
def independentEquivSubsets (n s : ℕ) (hs : s ≤ n + 1) :
    Independent n s ≃ {S : Finset (Fin (n + 1 - s)) // S.card = s} :=
  (independentEquivSpaced n s).trans
    ((gapEquiv n s hs).trans (orderEmbeddingEquivSubsets (n + 1 - s) s))

/-- The number of actual independent `s`-subsets of a finite path. -/
theorem card_independent (n s : ℕ) (hs : s ≤ n + 1) :
    Nat.card (Independent n s) = (n + 1 - s).choose s := by
  rw [Nat.card_congr (independentEquivSubsets n s hs), Nat.card_eq_fintype_card]
  simp

end PaperVerification.SeparatedSubsets
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SeparatedSubsets"

section ComponentSource_4
/- Original module: PaperVerification.OddPathIndependent -/


/-!
# Counting the odd pencil's coordinate fixed planes

The Jordan-chain order is `b₀, …, bₖ, aₖ, …, a₁`. The two alternating
forms pair distinct coordinates whose indices sum to `2k` or `2k + 1`.
Interleaving the two halves turns those edges into the ordinary path
`b₀, a₁, b₁, …, aₖ, bₖ`. This file proves the reindexing and the complete
binomial count, including the empty subset and the maximal independent subset.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.OddPathIndependent

open SeparatedSubsets

/-- The index in Jordan-chain order of a vertex in alternating path order. -/
def pathToChain (k : ℕ) (i : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  if i.val % 2 = 0 then ⟨i.val / 2, by have := i.isLt; omega⟩
  else ⟨2 * k - i.val / 2, by omega⟩

/-- The path index of a vector in Jordan-chain order. -/
def chainToPath (k : ℕ) (i : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  if h : i.val ≤ k then ⟨2 * i.val, by omega⟩
  else ⟨2 * (2 * k - i.val) + 1, by have := i.isLt; omega⟩

theorem chainToPath_pathToChain (k : ℕ) (i : Fin (2 * k + 1)) :
    chainToPath k (pathToChain k i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases hp : i.val % 2 = 0
  · have hq : i.val / 2 ≤ k := by omega
    simp [pathToChain, hp, chainToPath, hq] <;> omega
  · have hq : ¬ (2 * k - i.val / 2 ≤ k) := by omega
    simp [pathToChain, hp, chainToPath, hq] <;> omega

theorem pathToChain_chainToPath (k : ℕ) (i : Fin (2 * k + 1)) :
    pathToChain k (chainToPath k i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [chainToPath, pathToChain]
  split_ifs <;> dsimp only at * <;> omega

/-- The actual reordering of the two bases. -/
def pathChainEquiv (k : ℕ) : Fin (2 * k + 1) ≃ Fin (2 * k + 1) where
  toFun := pathToChain k
  invFun := chainToPath k
  left_inv := chainToPath_pathToChain k
  right_inv := pathToChain_chainToPath k

/-- The two anti-diagonals become exactly the consecutive edges of the path.
The distinctness clause removes the diagonal middle entry, as alternation does. -/
theorem chain_edge_iff_path_adjacent (k : ℕ) (i j : Fin (2 * k + 1)) :
    (i ≠ j ∧ ((pathToChain k i).val + (pathToChain k j).val = 2 * k ∨
      (pathToChain k i).val + (pathToChain k j).val = 2 * k + 1)) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [ne_eq, Fin.ext_iff, pathToChain]
  split_ifs <;> simp only [Fin.val_mk] <;> omega

/-- The original coordinate condition, expressed on a finite subset. -/
def ChainIndependent (k : ℕ) (S : Finset (Fin (2 * k + 1))) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i = j ∨
    (i.val + j.val ≠ 2 * k ∧ i.val + j.val ≠ 2 * k + 1)

/-- A coordinate subset of a fixed dimension, with the actual two isotropy
conditions on each pair of distinct basis vectors. -/
abbrev CoordinateSubsets (k s : ℕ) :=
  {S : Finset (Fin (2 * k + 1)) // S.card = s ∧ ChainIndependent k S}

theorem chainIndependent_map_iff (k : ℕ) (S : Finset (Fin (2 * k + 1))) :
    ChainIndependent k (S.map (pathChainEquiv k).toEmbedding) ↔
      ∀ i ∈ S, ∀ j ∈ S, i < j → i.val + 2 ≤ j.val := by
  constructor
  · intro h i hi j hj hij
    have hne : i ≠ j := ne_of_lt hij
    have hpi : pathToChain k i ∈ S.map (pathChainEquiv k).toEmbedding :=
      Finset.mem_map.mpr ⟨i, hi, rfl⟩
    have hpj : pathToChain k j ∈ S.map (pathChainEquiv k).toEmbedding :=
      Finset.mem_map.mpr ⟨j, hj, rfl⟩
    have he := h _ hpi _ hpj
    have hpne : pathToChain k i ≠ pathToChain k j :=
      fun hp => hne ((pathChainEquiv k).injective hp)
    have hz : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      intro hbad
      have hedge := (chain_edge_iff_path_adjacent k i j).mpr hbad
      rcases he with he | he
      · exact hpne he
      · exact hedge.2.elim he.1 he.2
    change i.val < j.val at hij
    omega
  · intro h i hi j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hj
    by_cases hab : a = b
    · exact Or.inl (congrArg (pathToChain k) hab)
    · right
      have hn : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · have hg := h a ha b hb hlt
          change a.val < b.val at hlt
          omega
        · have hg := h b hb a ha hgt
          change b.val < a.val at hgt
          omega
      have he := (chain_edge_iff_path_adjacent k a b).not.mpr hn
      constructor
      · intro hz
        exact he ⟨hab, Or.inl hz⟩
      · intro hz
        exact he ⟨hab, Or.inr hz⟩

/-- Reordering the actual coordinate subsets gives precisely path-independent
subsets of the same cardinality. -/
def coordinateEquivIndependent (k s : ℕ) :
    CoordinateSubsets k s ≃ Independent (2 * k + 1) s where
  toFun S := ⟨S.val.map (pathChainEquiv k).symm.toEmbedding, by
    constructor
    · simpa only [Finset.card_map] using S.property.1
    · apply (chainIndependent_map_iff k _).mp
      simpa only [Finset.map_map, Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
        Finset.map_refl] using S.property.2⟩
  invFun S := ⟨S.val.map (pathChainEquiv k).toEmbedding, by
    constructor
    · simpa only [Finset.card_map] using S.property.1
    · exact (chainIndependent_map_iff k S.val).mpr S.property.2⟩
  left_inv S := by
    apply Subtype.ext
    simp only [Finset.map_map, Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
      Finset.map_refl]
  right_inv S := by
    apply Subtype.ext
    simp only [Finset.map_map, Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding,
      Finset.map_refl]

/-- The exact number of isotropic coordinate `s`-planes in an odd pencil. -/
theorem card_coordinateSubsets (k s : ℕ) (hs : s ≤ k + 1) :
    Nat.card (CoordinateSubsets k s) = (2 * k + 2 - s).choose s := by
  rw [Nat.card_congr (coordinateEquivIndependent k s), card_independent]
  omega

end PaperVerification.OddPathIndependent
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.OddPathIndependent"

section ComponentSource_5
/- Original module: PaperVerification.AlternatingFormsTorusFixedCount -/


/-!+# Counting the actual fixed isotropic subspaces

The objects counted here are submodules of the original vector space. Their
defining properties are their actual finite dimension, vanishing of both
alternating forms on every pair of vectors, and equality under every torus
map. The coordinate classification and an explicit finite-set equivalence
identify these objects with the independent subsets of a path.

No geometric cell decomposition or cohomological dimension is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

open OddPathIndependent

variable (K : Type*) [Field K] [CharZero K]

/-- The fixed points described by their intrinsic subspace properties. -/
abbrev TorusFixedIsotropicPlanes (k s : ℕ) :=
  {U : Submodule K (ChainSpace K k) //
    Module.finrank K U = s ∧ IsCommonIsotropic k U ∧
      ∀ t : Kˣ, U.map (torusMap k t) = U}

/-- A coordinate vector belongs to a coordinate span exactly when its
index belongs to the indexing set. -/
theorem single_mem_coordinateSubspace_iff (k : ℕ)
    (S : Set (Fin (2 * k + 1))) (i : Fin (2 * k + 1)) :
    Pi.single i (1 : K) ∈ Pi.spanSubset K S ↔ i ∈ S := by
  classical
  constructor
  · intro h
    by_contra hi
    have hz := Pi.mem_spanSubset_iff.mp h i hi
    simpa using hz
  · intro hi
    rw [Pi.mem_spanSubset_iff]
    intro j hj
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [Pi.single_apply, hne]

/-- Distinct coordinate subsets give distinct actual subspaces. -/
theorem coordinateSubspace_injective (k : ℕ) :
    Function.Injective (fun S : Set (Fin (2 * k + 1)) => Pi.spanSubset K S) := by
  intro S T h
  change Pi.spanSubset K S = Pi.spanSubset K T at h
  ext i
  rw [← single_mem_coordinateSubspace_iff K k S i,
    ← single_mem_coordinateSubspace_iff K k T i, h]

/-- An independent coordinate subset gives a fixed common isotropic plane
of precisely its original cardinality. -/
def coordinateFixedPlane (k s : ℕ) (I : CoordinateSubsets k s) :
    TorusFixedIsotropicPlanes K k s :=
  ⟨Pi.spanSubset K (I.val : Set (Fin (2 * k + 1))), by
    refine ⟨?_, ?_, coordinateSubspace_map_torus k _⟩
    · simpa only [Pi.dim_spanSubset, Set.ncard_coe_finset] using I.property.1
    · exact (coordinateSubspace_isotropic_iff k _).mpr I.property.2⟩

theorem coordinateFixedPlane_injective (k s : ℕ) :
    Function.Injective (coordinateFixedPlane K k s) := by
  intro I J h
  apply Subtype.ext
  apply Finset.coe_injective
  apply coordinateSubspace_injective K k
  exact congrArg Subtype.val h

theorem coordinateFixedPlane_surjective (k s : ℕ) :
    Function.Surjective (coordinateFixedPlane K k s) := by
  classical
  intro U
  obtain ⟨S, hS⟩ := (torus_fixed_iff_coordinateSubspace k U.val).mp U.property.2.2
  have hdim : S.toFinset.card = s := by
    have h := U.property.1
    rw [hS, Pi.dim_spanSubset] at h
    simpa only [Set.ncard_eq_toFinset_card'] using h
  have hiso : ChainIndependent k S.toFinset := by
    have h := U.property.2.1
    rw [hS, coordinateSubspace_isotropic_iff] at h
    simpa only [ChainIndependent, IsIndependentCoordinateSet, Set.mem_toFinset] using h
  refine ⟨⟨S.toFinset, hdim, hiso⟩, ?_⟩
  apply Subtype.ext
  change Pi.spanSubset K (↑S.toFinset : Set (Fin (2 * k + 1))) = U.val
  rw [Set.coe_toFinset, ← hS]

/-- The classification is a genuine bijection, not merely an upper bound
on the number of fixed points. -/
def coordinateFixedPlaneEquiv (k s : ℕ) :
    CoordinateSubsets k s ≃ TorusFixedIsotropicPlanes K k s :=
  Equiv.ofBijective (coordinateFixedPlane K k s)
    ⟨coordinateFixedPlane_injective K k s, coordinateFixedPlane_surjective K k s⟩

instance finiteTorusFixedIsotropicPlanes (k s : ℕ) :
    Finite (TorusFixedIsotropicPlanes K k s) :=
  Finite.of_equiv (CoordinateSubsets k s) (coordinateFixedPlaneEquiv K k s)

/-- The exact cardinality of all actual torus-fixed common isotropic
`s`-planes, over every characteristic-zero field and throughout the full range. -/
theorem card_torusFixedIsotropicPlanes (k s : ℕ) (hs : s ≤ k + 1) :
    Nat.card (TorusFixedIsotropicPlanes K k s) = (2 * k + 2 - s).choose s := by
  rw [← Nat.card_congr (coordinateFixedPlaneEquiv K k s)]
  exact card_coordinateSubsets k s hs

end PaperVerification.AlternatingForms.CanonicalUnipotent
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsTorusFixedCount"

section ComponentSource_6
/- Original module: PaperVerification.FiniteAlgebraFromPairing -/


/-!+# Identifying a finite algebra from an integration pairing

Suppose a known quotient `P / I` has the same dimension as an upper bound for
an independently defined algebra `B`. If an algebra map `P → B` has kernel
contained in `I`, the dimension bound forces both surjectivity and equality
of the two ideals. An integration functional with exact annihilator `I`
provides precisely that kernel containment.

In a geometric application, both the dimension bound and the integration
identity must be proved for the actual geometric algebra. This lemma does
not define that algebra or supply either of those inputs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.FiniteAlgebraFromPairing

variable {K P B : Type*} [Field K] [CommRing P] [CommRing B]
  [Algebra K P] [Algebra K B]

/-- A quotient of the indicated dimension cannot have a strictly smaller
defining ideal while mapping into an algebra of at most that dimension. -/
theorem kernel_eq_and_surjective (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (hker : RingHom.ker f ≤ I)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) :
    RingHom.ker f = I ∧ Function.Surjective f := by
  let e := Ideal.quotientKerEquivRange f
  letI : FiniteDimensional K (P ⧸ RingHom.ker f) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let q : (P ⧸ RingHom.ker f) →ₐ[K] P ⧸ I := Ideal.Quotient.factorₐ K hker
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hQA : Module.finrank K (P ⧸ I) ≤ Module.finrank K (P ⧸ RingHom.ker f) :=
    LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
  have hQB : Module.finrank K (P ⧸ RingHom.ker f) ≤ Module.finrank K B := by
    rw [e.toLinearEquiv.finrank_eq]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := f.range.val.toLinearMap) Subtype.val_injective
  have hQAeq : Module.finrank K (P ⧸ RingHom.ker f) = Module.finrank K (P ⧸ I) :=
    le_antisymm (hQB.trans hdim) hQA
  have hqi : Function.Injective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := q.toLinearMap) hQAeq).mpr hq
  have hI : I ≤ RingHom.ker f := by
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hqi
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hRange : Module.finrank K f.range = Module.finrank K B := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact le_antisymm hQB (hdim.trans hQA)
  have hSurjRange : Function.Surjective f.range.val :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.range.val.toLinearMap) hRange).mp Subtype.val_injective
  refine ⟨le_antisymm hker hI, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hSurjRange b
  obtain ⟨p, hp⟩ := a.property
  exact ⟨p, hp.trans ha⟩

/-- The actual quotient isomorphism produced by the dimension argument. -/
def quotientEquiv (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (hker : RingHom.ker f ≤ I)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) :
    (P ⧸ I) ≃ₐ[K] B :=
  (Ideal.quotientEquivAlgOfEq K (kernel_eq_and_surjective I f hker hdim).1.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (kernel_eq_and_surjective I f hker hdim).2)

@[simp] theorem quotientEquiv_mk (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (hker : RingHom.ker f ≤ I)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) (p : P) :
    quotientEquiv I f hker hdim (Ideal.Quotient.mk I p) = f p := by
  simp only [quotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- Factoring an exact annihilator pairing through an algebra map forces
its kernel to be contained in the known relation ideal. -/
theorem kernel_le_of_pairing (I : Ideal P) (f : P →ₐ[K] B)
    (L : P →ₗ[K] K) (trace : B →ₗ[K] K)
    (hI : ∀ p, p ∈ I ↔ ∀ q, L (p * q) = 0)
    (htrace : ∀ p, trace (f p) = L p) :
    RingHom.ker f ≤ I := by
  intro p hp
  apply (hI p).mpr
  intro q
  rw [← htrace, map_mul, RingHom.mem_ker.mp hp, zero_mul, map_zero]

/-- An integration formula and the sharp total-dimension bound identify
the complete algebra. No duality property of `B` is an extra assumption. -/
def quotientEquivOfPairing (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (L : P →ₗ[K] K) (trace : B →ₗ[K] K)
    (hI : ∀ p, p ∈ I ↔ ∀ q, L (p * q) = 0)
    (htrace : ∀ p, trace (f p) = L p)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) :
    (P ⧸ I) ≃ₐ[K] B :=
  quotientEquiv I f (kernel_le_of_pairing I f L trace hI htrace) hdim

@[simp] theorem quotientEquivOfPairing_mk (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (L : P →ₗ[K] K) (trace : B →ₗ[K] K)
    (hI : ∀ p, p ∈ I ↔ ∀ q, L (p * q) = 0)
    (htrace : ∀ p, trace (f p) = L p)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) (p : P) :
    quotientEquivOfPairing I f L trace hI htrace hdim (Ideal.Quotient.mk I p) = f p := by
  exact quotientEquiv_mk I f _ hdim p

end PaperVerification.FiniteAlgebraFromPairing
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.FiniteAlgebraFromPairing"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.SeparatedSubsets.independentEquivSubsets, "definition"),
    (`PaperVerification.SeparatedSubsets.card_independent, "theorem"),
    (`PaperVerification.OddPathIndependent.pathChainEquiv, "definition"),
    (`PaperVerification.OddPathIndependent.chain_edge_iff_path_adjacent, "theorem"),
    (`PaperVerification.OddPathIndependent.coordinateEquivIndependent, "definition"),
    (`PaperVerification.OddPathIndependent.card_coordinateSubsets, "theorem"),
    (`PaperVerification.DiagonalInvariantSubspaces.invariant_iff_coordinateSubspace, "theorem"),
    (`PaperVerification.AlternatingForms.CanonicalUnipotent.torus_fixed_iff_coordinateSubspace, "theorem"),
    (`PaperVerification.AlternatingForms.CanonicalUnipotent.coordinateSubspace_isotropic_iff, "theorem"),
    (`PaperVerification.AlternatingForms.CanonicalUnipotent.coordinateFixedPlaneEquiv, "definition"),
    (`PaperVerification.AlternatingForms.CanonicalUnipotent.card_torusFixedIsotropicPlanes, "theorem"),
    (`PaperVerification.FiniteAlgebraFromPairing.kernel_eq_and_surjective, "theorem"),
    (`PaperVerification.FiniteAlgebraFromPairing.quotientEquiv, "definition"),
    (`PaperVerification.FiniteAlgebraFromPairing.quotientEquiv_mk, "theorem"),
    (`PaperVerification.FiniteAlgebraFromPairing.kernel_le_of_pairing, "theorem"),
    (`PaperVerification.FiniteAlgebraFromPairing.quotientEquivOfPairing, "definition"),
    (`PaperVerification.FiniteAlgebraFromPairing.quotientEquivOfPairing_mk, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "1588420817fe49f2bb6ef9d63d2f3dab"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:1588420817fe49f2bb6ef9d63d2f3dab"
