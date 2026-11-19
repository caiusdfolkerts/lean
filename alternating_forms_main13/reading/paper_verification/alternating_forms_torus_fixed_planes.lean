module

public import PaperVerification.AlternatingFormsTorusAction
public import PaperVerification.DiagonalInvariantSubspaces
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.Order.GroupWithZero.Basic

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
