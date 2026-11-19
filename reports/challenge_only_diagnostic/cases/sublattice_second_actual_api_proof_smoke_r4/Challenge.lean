module
public import Mathlib
/- Canonical API proof smoke for measured errors in full run44385218736.
All propositions below have actual proofs. This is an API diagnostic, not a
paper theorem submission. No source imports, axioms or proof placeholders. -/
@[expose] public noncomputable section
open Classical MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace PalomarReesAPISecond
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
abbrev S := MvPolynomial V k
abbrev C (M : Type u) [Zero M] (p : ℕ) := Set.powersetCard V p →₀ M
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  [Module (S (V := V) (k := k)) M] [Module (S (V := V) (k := k)) N]
  [Module k M] [Module k N]
  [IsScalarTower k (S (V := V) (k := k)) M]
  [IsScalarTower k (S (V := V) (k := k)) N]
def erase {p : ℕ} (s : Set.powersetCard V (p+1)) (j : {j // j ∈ s.val}) :
    Set.powersetCard V p :=
  ⟨s.val.erase j.val,by simp [Finset.card_erase_of_mem j.property,Set.powersetCard.card_eq]⟩
def sign (j : V) (s : Finset V) : ℤˣ := (-1 : ℤˣ) ^ (s.filter (· < j)).card
/-- Exact signed variable-multiplication sum in actual coefficient modules. -/
def sourceD (M : Type u) [AddCommGroup M] [Module (S (V := V) (k := k)) M] (p : ℕ) :
    C (V := V) M (p+1) →ₗ[S (V := V) (k := k)] C (V := V) M p :=
  Finsupp.lsum (S (V := V) (k := k)) (fun s : Set.powersetCard V (p+1) =>
    ∑ j : {j // j ∈ s.val}, (Finsupp.lsingle (erase s j)).comp
      (LinearMap.lsmul (S (V := V) (k := k)) M
        (X j.val * (((sign j.val s.val : ℤˣ) : ℤ) : S (V := V) (k := k)))))
theorem sourceD_single (p : ℕ) (s : Set.powersetCard V (p+1)) (m : M) :
    sourceD (k := k) M p (Finsupp.single s m) =
      ∑ j : {j // j ∈ s.val}, Finsupp.single (erase s j)
        ((X j.val * (((sign j.val s.val : ℤˣ) : ℤ) : S (V := V) (k := k))) • m) := by
  simp only [sourceD,Finsupp.lsum_single,LinearMap.sum_apply,
    LinearMap.comp_apply,Finsupp.lsingle_apply,LinearMap.lsmul_apply]
/-- Restriction of scalars must be evaluated before rewriting an S-linear
single-coordinate formula. This is the measured root at286/1039. -/
theorem restricted_single (p : ℕ) (s : Set.powersetCard V (p+1)) (m : M) :
    (sourceD (k := k) M p).restrictScalars k (Finsupp.single s m) =
      ∑ j : {j // j ∈ s.val}, Finsupp.single (erase s j)
        ((X j.val * (((sign j.val s.val : ℤˣ) : ℤ) : S (V := V) (k := k))) • m) := by
  rw [LinearMap.restrictScalars_apply,sourceD_single]
def previous (M : Type u) [AddCommGroup M] [Module (S (V := V) (k := k)) M]
    [Module k M] [IsScalarTower k (S (V := V) (k := k)) M] :
    ∀ p : ℕ, C (V := V) M p →ₗ[k] C (V := V) M p.pred
  | 0 => 0
  | p+1 => (sourceD (k := k) M p).restrictScalars k
/-- The indexed previous map keeps its varying exterior type. -/
theorem previous_succ (p : ℕ) (x : C (V := V) M (p+1)) :
    previous (k := k) M (p+1) x = sourceD (k := k) M p x := rfl
/-- Every exterior coordinate contributes exactly the declared homological
cardinality, rather than the unreduced membership proposition. -/
theorem integer_degree_card (p q a : ℕ) (s : Set.powersetCard V p)
    (h : (a : ℤ)+(p : ℤ)=(q : ℤ)) : a+s.val.card=q := by
  rw [Set.powersetCard.card_eq]
  exact_mod_cast h
section Maps
variable (L : M →ₗ[S (V := V) (k := k)] N)
def chainMap (p : ℕ) : C (V := V) M p →ₗ[k] C (V := V) N p :=
  (Finsupp.mapRange.linearMap L).restrictScalars k
theorem chainMap_single (p : ℕ) (s : Set.powersetCard V p) (m : M) :
    chainMap L p (Finsupp.single s m) = Finsupp.single s (L m) := by
  change Finsupp.mapRange L (map_zero L) (Finsupp.single s m) = _
  exact Finsupp.mapRange_single
theorem differential_comm (p : ℕ) (x : C (V := V) M (p+1)) :
    chainMap L p (sourceD (k := k) M p x) =
      sourceD (k := k) N p (chainMap L (p+1) x) := by
  have h : (chainMap L p).comp ((sourceD (k := k) M p).restrictScalars k) =
      ((sourceD (k := k) N p).restrictScalars k).comp (chainMap L (p+1)) := by
    apply Finsupp.lhom_ext
    intro s m
    simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply,
      sourceD_single,chainMap_single,map_sum,map_smul]
  exact LinearMap.congr_fun h x
/-- No standalone nondependent match is used for the varying target. -/
theorem previous_comm (p : ℕ) (x : C (V := V) M p) :
    chainMap L p.pred (previous (k := k) M p x) =
      previous (k := k) N p (chainMap L p x) := by
  cases p with
  | zero => simp only [previous,LinearMap.zero_apply,map_zero]
  | succ p => exact differential_comm L p x
end Maps
end PalomarReesAPISecond
namespace PalomarReesAPISecond.Projection
universe u v w x
variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} {Z : Type x}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module R X] [Module R Y] [Module R Z]
def boundaryMap (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : g.comp f = 0) :
    X →ₗ[R] LinearMap.ker g :=
  f.codRestrict _ (fun x => LinearMap.congr_fun h x)
theorem boundaryMap_val (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : g.comp f = 0) (x : X) :
    (boundaryMap f g h x).val = f x := rfl
theorem cycle_zero_projection (P : Submodule R Y) : ((0 : P) : Y)=0 :=
  ZeroMemClass.coe_zero P
end PalomarReesAPISecond.Projection
namespace PalomarReesAPISecond.Quotient
universe u v w
variable {k : Type u} [CommRing k] {A : Type v} {B : Type w}
  [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (I : Ideal A) [I.IsTwoSided] (J : Ideal B) [J.IsTwoSided]
/-- The exact pinned API takes target ideal = map of source ideal. -/
def induced (e : A ≃ₐ[k] B) (h : Ideal.map e.toRingEquiv.toRingHom I = J) :
    (A ⧸ I) ≃ₐ[k] (B ⧸ J) := Ideal.quotientEquivAlg I J e h.symm
end PalomarReesAPISecond.Quotient

namespace PalomarReesAPISecond.MixedActions
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- The actual source coefficient object is the bundled polynomial module. -/
def sourceSigned (I : Ideal (MvPolynomial V k)) (e : ℤˣ) (v : V)
    (m : ModuleCat.of (MvPolynomial V k) I) : ModuleCat.of (MvPolynomial V k) I :=
  X v • (e • m)
/-- Exact mixed integral-unit/polynomial-scalar action in actual ideal coefficients. -/
theorem signed_ideal_action (I : Ideal (MvPolynomial V k)) (e : ℤˣ) (v : V) (m : I) :
    ((X v * (((e : ℤˣ) : ℤ) : MvPolynomial V k)) • m : I) =
      sourceSigned I e v m := by
  change ((X v * (((e : ℤˣ) : ℤ) : MvPolynomial V k)) • m : I) = X v • (e • m)
  apply Subtype.ext
  simp only [Submodule.coe_smul,mul_smul,Units.smul_def,Int.cast_smul_eq_zsmul]
section Equivalences
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  (e : M ≃ₗ[k] N)
def chainEquiv (p : ℕ) : (Set.powersetCard V p →₀ M) ≃ₗ[k] (Set.powersetCard V p →₀ N) :=
  Finsupp.mapRange.linearEquiv e
/-- The protected field avoids generic ZeroHomClass inference. -/
theorem chainEquiv_zero (p : ℕ) : chainEquiv (V := V) e p 0 = 0 :=
  LinearEquiv.map_zero (chainEquiv (V := V) e p)
/-- The same actual equivalence's linear-map view gives an unambiguous additive map. -/
theorem chainEquiv_sum {α : Type*} (p : ℕ) (t : Finset α)
    (f : α → Set.powersetCard V p →₀ M) :
    chainEquiv (V := V) e p (∑ a ∈ t, f a) = ∑ a ∈ t, chainEquiv (V := V) e p (f a) :=
  map_sum (chainEquiv (V := V) e p).toLinearMap f t
end Equivalences
end PalomarReesAPISecond.MixedActions
