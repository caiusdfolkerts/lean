module
public import PaperVerification.GaussianProduct
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
@[expose] public section
/-!
# Exact Gaussian factorization for D_n and D_n^+

The theta functions below start as series over actual even-sum integer tuples.
The factorization into one-dimensional series is proved, not used as a definition.
The final equivalence identifies the tagged two-coset sum with the set of distinct
points in `dPlusSet`, so no lattice point is counted twice.
-/

noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

abbrev EvenTuple (n : ℕ) := {z : Fin n → ℤ // Even (∑ i, z i)}

def dGaussian {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : EvenTuple n, Real.exp (-α * sqDist (intVec z.val) x)

def dPlusGaussian {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  dGaussian α x + dGaussian α (fun i ↦ x i - 1 / 2)

def setGaussian {n : ℕ} (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : L, Real.exp (-α * sqDist z.val x)

def IsColdSpot {n : ℕ} (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ y, setGaussian L α x ≤ setGaussian L α y

lemma paritySign_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    paritySign (∑ i ∈ s, f i) = ∏ i ∈ s, paritySign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [paritySign_zero]
  | @insert i s hi ih => simp [hi, paritySign_add, ih]

lemma signed_gaussian_term_product {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (z : Fin n → ℤ) :
    paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x) =
      ∏ i, (paritySign (z i) * Real.exp (-α * ((z i : ℝ) - x i) ^ 2)) := by
  rw [paritySign_sum]
  rw [exp_neg_sqDist, Finset.prod_mul_distrib]

lemma summable_signed_integerGaussian {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ ↦
      paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x)) := by
  simp only [signed_gaussian_term_product]
  exact summable_fin_product n
    (fun i z ↦ paritySign z * Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_alternatingGaussian hα (x i))

lemma signed_integerGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
      paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x)) =
      ∏ i, alternatingGaussian α (x i) := by
  simp only [signed_gaussian_term_product, alternatingGaussian]
  exact tsum_fin_product n
    (fun i z ↦ paritySign z * Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_alternatingGaussian hα (x i))

lemma summable_dGaussian {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : EvenTuple n ↦ Real.exp (-α * sqDist (intVec z.val) x)) :=
  (summable_integerGaussian hα x).subtype _

/-- The parity projector gives the D_n theta function exactly. -/
theorem dGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dGaussian α x = (1 / 2) *
      ((∏ i, gaussian α (x i)) + (∏ i, alternatingGaussian α (x i))) := by
  unfold dGaussian
  change (∑' z : {z : Fin n → ℤ | Even (∑ i, z i)},
    Real.exp (-α * sqDist (intVec z.val) x)) = _
  rw [tsum_subtype {z : Fin n → ℤ | Even (∑ i, z i)}
    (fun z ↦ Real.exp (-α * sqDist (intVec z) x))]
  have hpoint (z : Fin n → ℤ) :
      Set.indicator {z : Fin n → ℤ | Even (∑ i, z i)}
        (fun z ↦ Real.exp (-α * sqDist (intVec z) x)) z =
      (1 / 2) * (Real.exp (-α * sqDist (intVec z) x) +
        paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x)) := by
    by_cases hz : Even (∑ i, z i) <;> simp [Set.indicator, paritySign, hz] <;> ring
  simp_rw [hpoint]
  rw [tsum_mul_left, (summable_integerGaussian hα x).tsum_add
    (summable_signed_integerGaussian hα x)]
  rw [signed_integerGaussian_eq_product hα x]
  change (1 / 2) * (integerGaussian α x + _) = _
  rw [integerGaussian_eq_product hα x]

/-- Equation (8) of the manuscript, for every positive parameter and every dimension. -/
theorem dPlusGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dPlusGaussian α x = (1 / 2) *
      ((∏ i, gaussian α (x i)) + (∏ i, alternatingGaussian α (x i)) +
       (∏ i, gaussian α (x i - 1 / 2)) +
       (∏ i, alternatingGaussian α (x i - 1 / 2))) := by
  rw [dPlusGaussian, dGaussian_eq_product hα, dGaussian_eq_product hα]
  ring

lemma intVec_injective (n : ℕ) : Function.Injective (@intVec n) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrFun h i)

lemma integer_ne_half_shift (a b : ℤ) : (a : ℝ) ≠ (b : ℝ) + 1 / 2 := by
  intro h
  have h' : (2 : ℤ) * a = 2 * b + 1 := by
    exact_mod_cast (show (2 : ℝ) * a = 2 * b + 1 by linarith)
  omega

def dPlusTagMap {n : ℕ} : EvenTuple n ⊕ EvenTuple n → dPlusSet n
  | .inl z => ⟨intVec z.val, z.val, z.property, Or.inl rfl⟩
  | .inr z => ⟨(fun i ↦ (z.val i : ℝ) + 1 / 2), z.val, z.property, Or.inr rfl⟩

lemma dPlusTagMap_bijective {n : ℕ} (hn : 0 < n) :
    Function.Bijective (@dPlusTagMap n) := by
  constructor
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        congr 1
        apply Subtype.ext
        exact intVec_injective n (congrArg Subtype.val h)
      | inr b =>
        have hi := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
        exact (integer_ne_half_shift (a.val ⟨0, hn⟩) (b.val ⟨0, hn⟩) hi).elim
    | inr a =>
      cases b with
      | inl b =>
        have hi := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
        exact (integer_ne_half_shift (b.val ⟨0, hn⟩) (a.val ⟨0, hn⟩) hi.symm).elim
      | inr b =>
        congr 1
        apply Subtype.ext
        funext i
        have hi := congrFun (congrArg Subtype.val h) i
        apply Int.cast_injective (α := ℝ)
        dsimp [dPlusTagMap] at hi
        linarith
  · rintro ⟨x, z, hz, h | h⟩
    · exact ⟨Sum.inl ⟨z, hz⟩, Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨z, hz⟩, Subtype.ext h.symm⟩

def dPlusTagEquiv {n : ℕ} (hn : 0 < n) :
    EvenTuple n ⊕ EvenTuple n ≃ dPlusSet n :=
  Equiv.ofBijective dPlusTagMap (dPlusTagMap_bijective hn)

lemma sqDist_half_shift {n : ℕ} (z : Fin n → ℤ) (x : Fin n → ℝ) :
    sqDist (fun i ↦ (z i : ℝ) + 1 / 2) x =
      sqDist (intVec z) (fun i ↦ x i - 1 / 2) := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp [intVec]
  ring

/-- The two-coset formula counts exactly the points of the stated real lattice. -/
theorem setGaussian_dPlus_eq {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) : setGaussian (dPlusSet n) α x = dPlusGaussian α x := by
  let f : dPlusSet n → ℝ := fun z ↦ Real.exp (-α * sqDist z.val x)
  have hl : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inl z)))
      (dGaussian α x) := by
    change HasSum (fun z : EvenTuple n ↦ Real.exp (-α * sqDist (intVec z.val) x))
      (dGaussian α x)
    unfold dGaussian
    exact (summable_dGaussian hα x).hasSum
  have hr : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inr z)))
      (dGaussian α (fun i ↦ x i - 1 / 2)) := by
    change HasSum (fun z : EvenTuple n ↦
      Real.exp (-α * sqDist (fun i ↦ (z.val i : ℝ) + 1 / 2) x)) _
    simp only [sqDist_half_shift]
    unfold dGaussian
    exact (summable_dGaussian hα (fun i ↦ x i - 1 / 2)).hasSum
  have hsum : HasSum (fun z : EvenTuple n ⊕ EvenTuple n ↦ f (dPlusTagEquiv hn z))
      (dPlusGaussian α x) := hl.sum hr
  exact ((dPlusTagEquiv hn).hasSum_iff (f := f)).mp hsum |>.tsum_eq

end PaperVerification.ColdSpots
