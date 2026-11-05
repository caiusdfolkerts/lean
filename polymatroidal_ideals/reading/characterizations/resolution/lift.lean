import Characterizations.Resolution.Basic

/-! # Homogeneous comparison maps for free resolutions -/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqLift (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]
variable {I J : Ideal (MvPolynomial V k)} {d : ℕ}

namespace LinearResolution

lemma augmentation_component (P : LinearResolution I d)
    (x : P.Index 0 → MvPolynomial V k) (t : ℕ) :
    homogeneousComponent (d + t) (P.augmentation x) = P.augmentation (component t x) := by
  let f : (P.Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k]
      (Unit → MvPolynomial V k) := LinearMap.pi (fun _ => P.augmentation)
  have hf : IsHomogeneousMap f d := fun _ b => P.augmentation_homogeneous b
  exact congrFun (homogeneousMap_component f hf x t) ()

lemma homogeneous_augmentation_lift (P : LinearResolution I d)
    {y : MvPolynomial V k} (hy : y.IsHomogeneous (d + 1)) (hI : y ∈ I) :
    ∃ x, IsHomogeneousVector x 1 ∧ P.augmentation x = y := by
  have hmem : y ∈ LinearMap.range P.augmentation := by simpa only [P.augmentation_range] using hI
  obtain ⟨x, rfl⟩ := hmem
  refine ⟨component 1 x, component_homogeneous _ _, ?_⟩
  rw [← P.augmentation_component, homogeneousComponent_eq_self hy]

variable (Q : LinearResolution J 1) (P : LinearResolution I d)
    (g : MvPolynomial V k) (hg : g.IsHomogeneous d)
    (hmul : ∀ z ∈ J, g * z ∈ I)

def liftZeroImage (b : Q.Index 0) : P.Index 0 → MvPolynomial V k :=
  Classical.choose (P.homogeneous_augmentation_lift
    (hg.mul (Q.augmentation_homogeneous b))
    (hmul _ (by simpa only [← Q.augmentation_range] using
      LinearMap.mem_range_self Q.augmentation (Pi.single b 1))))

lemma liftZeroImage_spec (b : Q.Index 0) :
    IsHomogeneousVector (liftZeroImage Q P g hg hmul b) 1 ∧
      P.augmentation (liftZeroImage Q P g hg hmul b) = g * Q.augmentation (Pi.single b 1) :=
  by
    exact Classical.choose_spec (P.homogeneous_augmentation_lift
    (hg.mul (Q.augmentation_homogeneous b))
    (hmul _ (by simpa only [← Q.augmentation_range] using
      LinearMap.mem_range_self Q.augmentation (Pi.single b 1))))

def liftZero : (Q.Index 0 → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (P.Index 0 → MvPolynomial V k) :=
  (Pi.basisFun (MvPolynomial V k) (Q.Index 0)).constr (MvPolynomial V k)
    (liftZeroImage Q P g hg hmul)

lemma liftZero_apply_single (b : Q.Index 0) :
    liftZero Q P g hg hmul (Pi.single b 1) = liftZeroImage Q P g hg hmul b := by
  exact Module.Basis.constr_basis _ _ _ b

lemma liftZero_homogeneous : IsHomogeneousMap (liftZero Q P g hg hmul) 1 := by
  intro a b
  rw [liftZero_apply_single]
  exact (liftZeroImage_spec Q P g hg hmul b).1 a

lemma liftZero_aug (x : Q.Index 0 → MvPolynomial V k) :
    P.augmentation (liftZero Q P g hg hmul x) = g * Q.augmentation x := by
  have h : P.augmentation ∘ₗ liftZero Q P g hg hmul =
      (LinearMap.mulLeft (MvPolynomial V k) g) ∘ₗ Q.augmentation := by
    apply (Pi.basisFun (MvPolynomial V k) (Q.Index 0)).ext
    intro b
    change P.augmentation (liftZero Q P g hg hmul (Pi.single b 1)) =
      g * Q.augmentation (Pi.single b 1)
    rw [liftZero_apply_single]
    exact (liftZeroImage_spec Q P g hg hmul b).2
  exact LinearMap.congr_fun h x

/-- One adjacent pair of genuine homogeneous comparison maps. -/
structure LiftPair (n : ℕ) where
  low : (Q.Index n → MvPolynomial V k) →ₗ[MvPolynomial V k] (P.Index n → MvPolynomial V k)
  high : (Q.Index (n + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (P.Index (n + 1) → MvPolynomial V k)
  low_homogeneous : IsHomogeneousMap low 1
  high_homogeneous : IsHomogeneousMap high 1
  comm : P.differential n ∘ₗ high = low ∘ₗ Q.differential n

def liftOneImage (b : Q.Index 1) : P.Index 1 → MvPolynomial V k :=
  Classical.choose (exists_homogeneous_lift (P.differential 0) (P.linear 0)
    (homogeneousMap_apply (liftZero Q P g hg hmul) (liftZero_homogeneous Q P g hg hmul)
      (Q.linear 0 · b)) (by
        rw [P.exact_zero]
        apply LinearMap.mem_ker.mpr
        rw [liftZero_aug]
        have hz := LinearMap.congr_fun Q.augmentation_comp (Pi.single b 1)
        change Q.augmentation (Q.differential 0 (Pi.single b 1)) = 0 at hz
        rw [hz, mul_zero]))

lemma liftOneImage_spec (b : Q.Index 1) :
    IsHomogeneousVector (liftOneImage Q P g hg hmul b) 1 ∧
      P.differential 0 (liftOneImage Q P g hg hmul b) =
        liftZero Q P g hg hmul (Q.differential 0 (Pi.single b 1)) := by
  exact Classical.choose_spec (exists_homogeneous_lift (P.differential 0) (P.linear 0)
    (homogeneousMap_apply (liftZero Q P g hg hmul) (liftZero_homogeneous Q P g hg hmul)
      (Q.linear 0 · b)) (by
        rw [P.exact_zero]
        apply LinearMap.mem_ker.mpr
        rw [liftZero_aug]
        have hz := LinearMap.congr_fun Q.augmentation_comp (Pi.single b 1)
        change Q.augmentation (Q.differential 0 (Pi.single b 1)) = 0 at hz
        rw [hz, mul_zero]))

def initialLiftPair : LiftPair Q P 0 where
  low := liftZero Q P g hg hmul
  high := (Pi.basisFun (MvPolynomial V k) (Q.Index 1)).constr (MvPolynomial V k)
    (liftOneImage Q P g hg hmul)
  low_homogeneous := liftZero_homogeneous Q P g hg hmul
  high_homogeneous := by
    intro a b
    change (((Pi.basisFun (MvPolynomial V k) (Q.Index 1)).constr (MvPolynomial V k)
      (liftOneImage Q P g hg hmul)) ((Pi.basisFun _ _) b) a).IsHomogeneous 1
    rw [Module.Basis.constr_basis]
    exact (liftOneImage_spec Q P g hg hmul b).1 a
  comm := by
    apply (Pi.basisFun (MvPolynomial V k) (Q.Index 1)).ext
    intro b
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact (liftOneImage_spec Q P g hg hmul b).2

def nextLiftImage {n : ℕ} (A : LiftPair Q P n) (b : Q.Index (n + 2)) :
    P.Index (n + 2) → MvPolynomial V k :=
  Classical.choose (exists_homogeneous_lift (P.differential (n + 1)) (P.linear (n + 1))
    (homogeneousMap_apply A.high A.high_homogeneous (Q.linear (n + 1) · b)) (by
      rw [P.exact_succ n]
      apply LinearMap.mem_ker.mpr
      change (P.differential n ∘ₗ A.high) (Q.differential (n + 1) (Pi.single b 1)) = 0
      rw [A.comm]
      change A.low ((Q.differential n ∘ₗ Q.differential (n + 1)) (Pi.single b 1)) = 0
      rw [Q.differential_comp]
      simp))

lemma nextLiftImage_spec {n : ℕ} (A : LiftPair Q P n) (b : Q.Index (n + 2)) :
    IsHomogeneousVector (nextLiftImage Q P A b) 1 ∧
      P.differential (n + 1) (nextLiftImage Q P A b) =
        A.high (Q.differential (n + 1) (Pi.single b 1)) := by
  exact Classical.choose_spec (exists_homogeneous_lift (P.differential (n + 1)) (P.linear (n + 1))
    (homogeneousMap_apply A.high A.high_homogeneous (Q.linear (n + 1) · b)) (by
      rw [P.exact_succ n]
      apply LinearMap.mem_ker.mpr
      change (P.differential n ∘ₗ A.high) (Q.differential (n + 1) (Pi.single b 1)) = 0
      rw [A.comm]
      change A.low ((Q.differential n ∘ₗ Q.differential (n + 1)) (Pi.single b 1)) = 0
      rw [Q.differential_comp]
      simp))

def nextLiftPair {n : ℕ} (A : LiftPair Q P n) : LiftPair Q P (n + 1) where
  low := A.high
  high := (Pi.basisFun (MvPolynomial V k) (Q.Index (n + 2))).constr (MvPolynomial V k)
    (nextLiftImage Q P A)
  low_homogeneous := A.high_homogeneous
  high_homogeneous := by
    intro a b
    change (((Pi.basisFun (MvPolynomial V k) (Q.Index (n + 2))).constr (MvPolynomial V k)
      (nextLiftImage Q P A)) ((Pi.basisFun _ _) b) a).IsHomogeneous 1
    rw [Module.Basis.constr_basis]
    exact (nextLiftImage_spec Q P A b).1 a
  comm := by
    apply (Pi.basisFun (MvPolynomial V k) (Q.Index (n + 2))).ext
    intro b
    simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact (nextLiftImage_spec Q P A b).2

def liftPairs : ∀ n, LiftPair Q P n
  | 0 => initialLiftPair Q P g hg hmul
  | n + 1 => nextLiftPair Q P (liftPairs n)

/-- A homogeneous lift of multiplication by `g`, obtained from actual exactness. -/
def multiplicationLift (n : ℕ) :
    (Q.Index n → MvPolynomial V k) →ₗ[MvPolynomial V k] (P.Index n → MvPolynomial V k) :=
  (liftPairs Q P g hg hmul n).low

lemma multiplicationLift_homogeneous (n : ℕ) :
    IsHomogeneousMap (multiplicationLift Q P g hg hmul n) 1 :=
  (liftPairs Q P g hg hmul n).low_homogeneous

lemma multiplicationLift_comm (n : ℕ) :
    P.differential n ∘ₗ multiplicationLift Q P g hg hmul (n + 1) =
      multiplicationLift Q P g hg hmul n ∘ₗ Q.differential n :=
  (liftPairs Q P g hg hmul n).comm

lemma multiplicationLift_aug (x : Q.Index 0 → MvPolynomial V k) :
    P.augmentation (multiplicationLift Q P g hg hmul 0 x) = g * Q.augmentation x :=
  liftZero_aug Q P g hg hmul x

end LinearResolution
end Characterizations
