import Characterizations.Resolution.Lift
import Mathlib.RingTheory.Ideal.Colon

/-! # The actual graded mapping cone for adjoining one generator -/

noncomputable section
@[reducible] local instance (priority := 2000) classicalBasisDecidableEqCone (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace Characterizations
open Classical Resolution MvPolynomial
universe u
variable {V k : Type u} [CommRing k]
variable {I C : Ideal (MvPolynomial V k)} {d : ℕ}
namespace LinearResolution

abbrev leftProjection (A B : Type*) : (A ⊕ B → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (A → MvPolynomial V k) := LinearMap.pi (fun a => LinearMap.proj (Sum.inl a))
abbrev rightProjection (A B : Type*) : (A ⊕ B → MvPolynomial V k) →ₗ[MvPolynomial V k]
    (B → MvPolynomial V k) := LinearMap.pi (fun b => LinearMap.proj (Sum.inr b))

@[simp] lemma leftProjection_apply (A B : Type*) (x : A ⊕ B → MvPolynomial V k) :
    leftProjection A B x = (fun a => x (Sum.inl a)) := rfl
@[simp] lemma rightProjection_apply (A B : Type*) (x : A ⊕ B → MvPolynomial V k) :
    rightProjection A B x = (fun b => x (Sum.inr b)) := rfl

abbrev joinMaps {A B L : Type*}
    (f : (L → MvPolynomial V k) →ₗ[MvPolynomial V k] (A → MvPolynomial V k))
    (g : (L → MvPolynomial V k) →ₗ[MvPolynomial V k] (B → MvPolynomial V k)) :
    (L → MvPolynomial V k) →ₗ[MvPolynomial V k] (A ⊕ B → MvPolynomial V k) :=
  LinearMap.pi (Sum.elim (fun a => (LinearMap.proj a).comp f) (fun b => (LinearMap.proj b).comp g))

@[simp] lemma left_single_inl {A B : Type*} [Fintype A] [Fintype B] (a : A) :
    (fun i : A => (Pi.single (Sum.inl a) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inl i)) = Pi.single a 1 := by
  funext i
  simp [Pi.single_apply]
@[simp] lemma left_single_inr {A B : Type*} [Fintype A] [Fintype B] (b : B) :
    (fun i : A => (Pi.single (Sum.inr b) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inl i)) = 0 := by
  funext i
  simp [Pi.single_apply]
@[simp] lemma right_single_inl {A B : Type*} [Fintype A] [Fintype B] (a : A) :
    (fun i : B => (Pi.single (Sum.inl a) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inr i)) = 0 := by
  funext i
  simp [Pi.single_apply]
@[simp] lemma right_single_inr {A B : Type*} [Fintype A] [Fintype B] (b : B) :
    (fun i : B => (Pi.single (Sum.inr b) (1 : MvPolynomial V k) : A ⊕ B → _) (Sum.inr i)) = Pi.single b 1 := by
  funext i
  simp [Pi.single_apply]

variable (P : LinearResolution I d) (Q : LinearResolution C 1)
    (g : MvPolynomial V k) (hg : g.IsHomogeneous d)
    (hcolon : C = I.colon {g})

include hcolon in
lemma mul_mem (z : MvPolynomial V k) (hz : z ∈ C) : g * z ∈ I := by
  rw [hcolon, Submodule.mem_colon_singleton] at hz
  simpa [smul_eq_mul, mul_comm] using hz

def theta (n : ℕ) := Q.multiplicationLift P g hg (mul_mem g hcolon) n

lemma theta_comm (n : ℕ) (x : Q.Index (n + 1) → MvPolynomial V k) :
    P.differential n (theta P Q g hg hcolon (n + 1) x) =
      theta P Q g hg hcolon n (Q.differential n x) :=
  LinearMap.congr_fun (Q.multiplicationLift_comm P g hg (mul_mem g hcolon) n) x

lemma theta_aug (x : Q.Index 0 → MvPolynomial V k) :
    P.augmentation (theta P Q g hg hcolon 0 x) = g * Q.augmentation x :=
  Q.multiplicationLift_aug P g hg (mul_mem g hcolon) x

abbrev coneRight : ℕ → Type
  | 0 => PUnit
  | n + 1 => Q.Index n

abbrev coneIndex (n : ℕ) : Type := P.Index n ⊕ coneRight Q n

instance coneIndex_fintype (n : ℕ) : Fintype (coneIndex P Q n) := by
  cases n <;> dsimp [coneIndex, coneRight] <;> infer_instance

def coneAugmentation : (coneIndex P Q 0 → MvPolynomial V k) →ₗ[MvPolynomial V k]
    MvPolynomial V k :=
  P.augmentation.comp (leftProjection _ _) +
    (LinearMap.mulLeft (MvPolynomial V k) g).comp (LinearMap.proj (Sum.inr PUnit.unit))

def coneDifferential : ∀ n,
    (coneIndex P Q (n + 1) → MvPolynomial V k) →ₗ[MvPolynomial V k]
      (coneIndex P Q n → MvPolynomial V k)
  | 0 => joinMaps
      ((P.differential 0).comp (leftProjection _ _) +
        (theta P Q g hg hcolon 0).comp (rightProjection _ _))
      (LinearMap.pi (fun _ : PUnit => -(Q.augmentation.comp (rightProjection _ _))))
  | n + 1 => joinMaps
      ((P.differential (n + 1)).comp (leftProjection _ _) +
        (theta P Q g hg hcolon (n + 1)).comp (rightProjection _ _))
      (-((Q.differential n).comp (rightProjection _ _)))

lemma coneDifferential_left (n : ℕ)
    (x : coneIndex P Q (n + 1) → MvPolynomial V k) (a : P.Index n) :
    coneDifferential P Q g hg hcolon n x (Sum.inl a) =
      P.differential n (fun a => x (Sum.inl a)) a +
        theta P Q g hg hcolon n (fun b => x (Sum.inr b)) a := by
  cases n <;> rfl

lemma coneDifferential_right_zero
    (x : coneIndex P Q 1 → MvPolynomial V k) :
    coneDifferential P Q g hg hcolon 0 x (Sum.inr PUnit.unit) =
      -Q.augmentation (fun b => x (Sum.inr b)) := rfl

lemma coneDifferential_right_succ (n : ℕ)
    (x : coneIndex P Q (n + 2) → MvPolynomial V k) (b : Q.Index n) :
    coneDifferential P Q g hg hcolon (n + 1) x (Sum.inr b) =
      -Q.differential n (fun b => x (Sum.inr b)) b := rfl

lemma coneAugmentation_apply (x : coneIndex P Q 0 → MvPolynomial V k) :
    coneAugmentation P Q g x = P.augmentation (fun a => x (Sum.inl a)) + g * x (Sum.inr PUnit.unit) := rfl

lemma coneAugmentation_range : LinearMap.range (coneAugmentation P Q g) = I ⊔ Ideal.span {g} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [coneAugmentation_apply]
    apply add_mem
    · exact (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) (show P.augmentation _ ∈ I by
        simpa only [P.augmentation_range] using LinearMap.mem_range_self P.augmentation (fun a => x (Sum.inl a)))
    · exact (show Ideal.span {g} ≤ I ⊔ Ideal.span {g} from le_sup_right) (Ideal.mem_span_singleton'.mpr ⟨x (Sum.inr PUnit.unit), mul_comm _ _⟩)
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha' : a ∈ LinearMap.range P.augmentation := by simpa only [P.augmentation_range] using ha
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨Sum.elim x (fun _ => c), ?_⟩
    change P.augmentation x + g * c = P.augmentation x + c * g
    ring

lemma coneExact_zero : LinearMap.range (coneDifferential P Q g hg hcolon 0) =
    LinearMap.ker (coneAugmentation P Q g) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [coneAugmentation_apply]
    change P.augmentation (P.differential 0 _ + theta P Q g hg hcolon 0 _) + _ = 0
    rw [map_add, theta_aug]
    have hz := LinearMap.congr_fun P.augmentation_comp (fun a => y (Sum.inl a))
    change P.augmentation (P.differential 0 _) = 0 at hz
    simp only [leftProjection_apply, rightProjection_apply]
    rw [hz, coneDifferential_right_zero]
    ring
  · intro hx
    have he := LinearMap.mem_ker.mp hx
    rw [coneAugmentation_apply] at he
    let a : P.Index 0 → MvPolynomial V k := fun i => x (Sum.inl i)
    let c := x (Sum.inr PUnit.unit)
    have hgc : g * c ∈ I := by
      have hp : P.augmentation a ∈ I := by
        simpa only [P.augmentation_range] using LinearMap.mem_range_self P.augmentation a
      have hneg : g * c = -P.augmentation a := by change P.augmentation a + g * c = 0 at he; linear_combination he
      rw [hneg]
      exact I.neg_mem hp
    have hc : c ∈ C := by
      rw [hcolon, Submodule.mem_colon_singleton]
      simpa [smul_eq_mul, mul_comm] using hgc
    have hc' : c ∈ LinearMap.range Q.augmentation := by simpa only [Q.augmentation_range] using hc
    obtain ⟨q, hq⟩ := hc'
    have hp : a + theta P Q g hg hcolon 0 q ∈ LinearMap.ker P.augmentation := by
      apply LinearMap.mem_ker.mpr
      rw [map_add, theta_aug, hq]
      exact he
    rw [← P.exact_zero] at hp
    obtain ⟨p, hp⟩ := hp
    refine ⟨Sum.elim p (-q), ?_⟩
    funext i
    cases i with
    | inl i =>
      rw [coneDifferential_left]
      change (P.differential 0 p + theta P Q g hg hcolon 0 (-q)) i = a i
      rw [hp, map_neg]
      simp
    | inr i =>
      cases i
      rw [coneDifferential_right_zero]
      change -Q.augmentation (-q) = c
      rw [map_neg, neg_neg, hq]

lemma coneDifferential_comp (n : ℕ) :
    coneDifferential P Q g hg hcolon n ∘ₗ coneDifferential P Q g hg hcolon (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  cases n with
  | zero =>
    cases i with
    | inl i =>
      simp only [LinearMap.comp_apply, coneDifferential_left, coneDifferential_right_succ]
      change (P.differential 0 (P.differential 1 _ + theta P Q g hg hcolon 1 _) +
        theta P Q g hg hcolon 0 (-Q.differential 0 _)) i = 0
      rw [map_add, theta_comm, map_neg]
      have hz := LinearMap.congr_fun (P.differential_comp 0) (fun a => x (Sum.inl a))
      change P.differential 0 (P.differential 1 _) = 0 at hz
      simp only [leftProjection_apply, rightProjection_apply]
      rw [hz]
      simp
    | inr i =>
      cases i
      rw [LinearMap.comp_apply, coneDifferential_right_zero]
      change -Q.augmentation (-Q.differential 0 _) = 0
      rw [map_neg, neg_neg]
      exact LinearMap.congr_fun Q.augmentation_comp _
  | succ n =>
    cases i with
    | inl i =>
      simp only [LinearMap.comp_apply, coneDifferential_left, coneDifferential_right_succ]
      change (P.differential (n + 1) (P.differential (n + 2) _ + theta P Q g hg hcolon (n + 2) _) +
        theta P Q g hg hcolon (n + 1) (-Q.differential (n + 1) _)) i = 0
      rw [map_add, theta_comm, map_neg]
      have hz := LinearMap.congr_fun (P.differential_comp (n + 1)) (fun a => x (Sum.inl a))
      change P.differential (n + 1) (P.differential (n + 2) _) = 0 at hz
      simp only [leftProjection_apply, rightProjection_apply]
      rw [hz]
      simp
    | inr i =>
      rw [LinearMap.comp_apply, coneDifferential_right_succ]
      change -Q.differential n (-Q.differential (n + 1) _) i = 0
      rw [map_neg]
      have hz := LinearMap.congr_fun (Q.differential_comp n) (fun b => x (Sum.inr b))
      change Q.differential n (Q.differential (n + 1) _) = 0 at hz
      simp only [leftProjection_apply, rightProjection_apply]
      rw [hz]
      simp

lemma coneExact_succ (n : ℕ) :
    LinearMap.range (coneDifferential P Q g hg hcolon (n + 1)) =
      LinearMap.ker (coneDifferential P Q g hg hcolon n) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (coneDifferential_comp P Q g hg hcolon n)
  · intro x hx
    let a : P.Index (n + 1) → MvPolynomial V k := fun i => x (Sum.inl i)
    let b : Q.Index n → MvPolynomial V k := fun j => x (Sum.inr j)
    have hx0 := LinearMap.mem_ker.mp hx
    have hleft : P.differential n a + theta P Q g hg hcolon n b = 0 := by
      funext i
      have h := congrFun hx0 (Sum.inl i)
      rw [coneDifferential_left P Q g hg hcolon n] at h
      change P.differential n a i + theta P Q g hg hcolon n b i = 0 at h
      exact h
    have hb : b ∈ LinearMap.range (Q.differential n) := by
      cases n with
      | zero =>
        rw [Q.exact_zero]
        apply LinearMap.mem_ker.mpr
        have h := congrFun hx0 (Sum.inr PUnit.unit)
        change -Q.augmentation b = 0 at h
        exact neg_eq_zero.mp h
      | succ n =>
        rw [Q.exact_succ n]
        apply LinearMap.mem_ker.mpr
        funext j
        have h := congrFun hx0 (Sum.inr j)
        change -Q.differential n b j = 0 at h
        exact neg_eq_zero.mp h
    obtain ⟨q, hq⟩ := hb
    have hp : a + theta P Q g hg hcolon (n + 1) q ∈ LinearMap.range (P.differential (n + 1)) := by
      rw [P.exact_succ n]
      apply LinearMap.mem_ker.mpr
      rw [map_add, theta_comm, hq]
      exact hleft
    obtain ⟨p, hp⟩ := hp
    refine ⟨Sum.elim p (-q), ?_⟩
    funext i
    cases i with
    | inl i =>
      rw [coneDifferential_left]
      change (P.differential (n + 1) p + theta P Q g hg hcolon (n + 1) (-q)) i = a i
      rw [hp, map_neg]
      simp
    | inr i =>
      rw [coneDifferential_right_succ]
      change -Q.differential n (-q) i = b i
      rw [map_neg, hq]
      simp

/-- Adjoining one degree-`d` generator with a linearly resolved colon ideal
produces a genuine `d`-linear free resolution of the enlarged ideal. -/
def adjoin : LinearResolution (I ⊔ Ideal.span {g}) d where
  Index := coneIndex P Q
  finite := coneIndex_fintype P Q
  differential := coneDifferential P Q g hg hcolon
  augmentation := coneAugmentation P Q g
  augmentation_range := coneAugmentation_range P Q g
  exact_zero := coneExact_zero P Q g hg hcolon
  exact_succ := coneExact_succ P Q g hg hcolon
  linear := by
    intro n
    intro a b
    cases n with
    | zero =>
      cases a with
      | inl a =>
        rw [coneDifferential_left]
        cases b with
        | inl b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using P.linear 0 a b
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using Q.multiplicationLift_homogeneous P g hg (mul_mem g hcolon) 0 a b
      | inr a =>
        cases a
        rw [coneDifferential_right_zero]
        cases b with
        | inl b => simp only [left_single_inr, right_single_inl, map_zero, Pi.zero_apply, neg_zero]; exact isHomogeneous_zero _ _ _
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using (Q.augmentation_homogeneous b).neg
    | succ n =>
      cases a with
      | inl a =>
        rw [coneDifferential_left]
        cases b with
        | inl b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using P.linear (n + 1) a b
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using Q.multiplicationLift_homogeneous P g hg (mul_mem g hcolon) (n + 1) a b
      | inr a =>
        rw [coneDifferential_right_succ]
        cases b with
        | inl b => simp only [left_single_inr, right_single_inl, map_zero, Pi.zero_apply, neg_zero]; exact isHomogeneous_zero _ _ _
        | inr b => simpa only [left_single_inl, right_single_inl, left_single_inr, right_single_inr, map_zero, Pi.zero_apply, zero_add, add_zero, mul_zero, mul_one, theta] using (Q.linear n a b).neg
  augmentation_homogeneous := by
    intro b
    rw [coneAugmentation_apply]
    cases b with
    | inl b =>
      rw [left_single_inl]
      simpa only [Pi.single_apply, Sum.inr_ne_inl, ite_false, mul_zero, add_zero] using
        P.augmentation_homogeneous b
    | inr b =>
      rw [left_single_inr, map_zero, zero_add]
      cases b
      simpa only [Pi.single_eq_same, mul_one] using hg

end LinearResolution
end Characterizations
