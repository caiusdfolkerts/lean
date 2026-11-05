module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Equivariant polynomial towers from an actual lifted basis

The source is the direct sum of copies of the quotient, indexed by every
nonnegative power. The map sends its `j`th summand to `T^j` of a chosen
section. A tower basis proves this map is an isomorphism; commutation with the
parameter and equivariance of the section prove equivariance of the map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.EquivariantTowers

variable {K V W I : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def extension (T : Module.End K V) (s : W →ₗ[K] V) : (ℕ →₀ W) →ₗ[K] V :=
  Finsupp.lsum K fun j => (T ^ j).comp s

@[simp] theorem extension_single (T : Module.End K V) (s : W →ₗ[K] V)
    (j : ℕ) (x : W) : extension T s (Finsupp.single j x) = (T ^ j) (s x) := by
  rw [extension, Finsupp.lsum_single, LinearMap.comp_apply]

def sigmaProd : (Σ _ : ℕ, I) ≃ ℕ × I where
  toFun a := (a.1, a.2)
  invFun a := ⟨a.1, a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

theorem extension_bijective (T : Module.End K V) (s : W →ₗ[K] V)
    (B : Module.Basis I K W) (C : Module.Basis (ℕ × I) K V)
    (hC : ∀ a, C a = (T ^ a.1) (s (B a.2))) :
    Function.Bijective (extension T s) := by
  let Bsum := Finsupp.basis fun _ : ℕ => B
  let e := Bsum.equiv C sigmaProd
  have he : extension T s = e.toLinearMap := by
    apply Bsum.ext
    intro a
    change extension T s (Bsum a) = e (Bsum a)
    dsimp only [e]
    rw [Module.Basis.equiv_apply]
    rw [show Bsum a = Finsupp.single a.1 (B a.2) from
      congrFun (Finsupp.coe_basis (fun _ : ℕ => B)) a]
    change extension T s (Finsupp.single a.1 (B a.2)) = C (a.1, a.2)
    rw [extension_single, hC]
  rw [he]
  exact e.bijective

def extensionEquiv (T : Module.End K V) (s : W →ₗ[K] V)
    (B : Module.Basis I K W) (C : Module.Basis (ℕ × I) K V)
    (hC : ∀ a, C a = (T ^ a.1) (s (B a.2))) : (ℕ →₀ W) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (extension T s) (extension_bijective T s B C hC)

variable {G : Type*} [Monoid G]

def sourceAction (σ : G →* Module.End K W) : G →* Module.End K (ℕ →₀ W) where
  toFun g := Finsupp.mapRange.linearMap (σ g)
  map_one' := by simp only [map_one, Module.End.one_eq_id, Finsupp.mapRange.linearMap_id]
  map_mul' g h := by
    simp only [map_mul, Module.End.mul_eq_comp, Finsupp.mapRange.linearMap_comp]

@[simp] theorem sourceAction_single (σ : G →* Module.End K W) (g : G) (j : ℕ) (x : W) :
    sourceAction σ g (Finsupp.single j x) = Finsupp.single j (σ g x) := by
  change Finsupp.mapRange.linearMap (σ g) (Finsupp.single j x) = _
  simp only [Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single]

theorem powers_intertwine (ρ : G →* Module.End K V) (T : Module.End K V)
    (hT : ∀ g x, ρ g (T x) = T (ρ g x)) (g : G) (j : ℕ) (x : V) :
    (T ^ j) (ρ g x) = ρ g ((T ^ j) x) := by
  induction j with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, ← hT, Module.End.mul_apply]

theorem extension_intertwines
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (T : Module.End K V) (s : W →ₗ[K] V)
    (hT : ∀ g x, ρ g (T x) = T (ρ g x))
    (hs : ∀ g x, s (σ g x) = ρ g (s x)) (g : G) (x : ℕ →₀ W) :
    extension T s (sourceAction σ g x) = ρ g (extension T s x) := by
  have he : (extension T s).comp (sourceAction σ g) =
      (ρ g).comp (extension T s) := by
    apply Finsupp.lhom_ext
    intro j y
    simp only [LinearMap.comp_apply, sourceAction_single, extension_single, hs]
    exact powers_intertwine ρ T hT g j (s y)
  exact DFunLike.congr_fun he x

theorem extensionEquiv_intertwines
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (T : Module.End K V) (s : W →ₗ[K] V)
    (B : Module.Basis I K W) (C : Module.Basis (ℕ × I) K V)
    (hC : ∀ a, C a = (T ^ a.1) (s (B a.2)))
    (hT : ∀ g x, ρ g (T x) = T (ρ g x))
    (hs : ∀ g x, s (σ g x) = ρ g (s x)) (g : G) (x : ℕ →₀ W) :
    extensionEquiv T s B C hC (sourceAction σ g x) =
      ρ g (extensionEquiv T s B C hC x) :=
  extension_intertwines ρ σ T s hT hs g x

end PaperVerification.EquivariantTowers
