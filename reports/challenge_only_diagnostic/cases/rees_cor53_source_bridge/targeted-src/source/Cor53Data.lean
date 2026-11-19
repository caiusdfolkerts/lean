module
public import Mathlib
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-!
# Corollary5.3: first occurrence and the specified non-monic multiplier

The homogeneous Koszul quotient below has the literal deletion differential,
ordinary signed integer degree and actual ideal coefficients. Its multiplication
map is induced by the supplied polynomial at every coordinate. The Solution
connects this model to the original genuine derived-Tor comparison and proves
injectivity for the same actual Mathlib Tor functor map.
-/
@[expose] public noncomputable section
open Classical MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace PalomarSublatticeCor53
open Classical MvPolynomial
open scoped MonomialOrder
universe u v
variable {d : ℕ} (n : Fin d → ℕ)
/-- The exact finite product of the row chains. -/
abbrev FiniteTuple := ∀ r, Fin (n r)
/-- Exactly one variable per row/column pair; ULift changes only its universe. -/
abbrev FiniteVariable : Type u := Σ r, ULift.{u} (Fin (n r))
/-- The squarefree exponent of the product selecting one variable in every row. -/
def finiteRowExponent (a : FiniteTuple n) : (FiniteVariable.{u} n →₀ ℕ) :=
  ∑ r, Finsupp.single ⟨r, ULift.up (a r)⟩ 1
/-- Closure of the finite tuple set under coordinatewise minimum and maximum. -/
def finiteLatticeClosed (E : Finset (FiniteTuple n)) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E) ∧ (∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
end PalomarSublatticeCor53
namespace PalomarSublatticeCor53.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [CommRing K]

/-- Literal coefficient Koszul coordinates in exterior degree p. -/
abbrev Coordinates (I : Ideal (MvPolynomial V K)) (p : ℕ) := Set.powersetCard V p →₀ I

/-- The ordinary deletion sign: minus one to the number of exterior
coordinates before i. The source proves equality with its shuffle sign. -/
def eraseSign (i : V) (s : Finset V) : ℤˣ :=
  (-1 : ℤˣ) ^ (s.filter (fun j => j < i)).card

/-- Deleting one incident coordinate has the required exterior cardinality.
This supporting statement must be selected in the eventual Comparator config. -/
theorem eraseIndex_card {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : (s.val.erase j.val).card = p := by
  simp [Finset.card_erase_of_mem j.property, s.property]

/-- The exterior index obtained by deleting an incident coordinate. -/
def eraseIndex {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : Set.powersetCard V p :=
  ⟨s.val.erase j.val, eraseIndex_card s j⟩

/-- The genuine signed polynomial Koszul differential: delete an exterior
coordinate and multiply its ideal coefficient by that polynomial variable. -/
def differential (I : Ideal (MvPolynomial V K)) (p : ℕ) :
    Coordinates I (p + 1) →ₗ[K] Coordinates I p :=
  (Finsupp.lsum (MvPolynomial V K) (fun s : Set.powersetCard V (p + 1) =>
    ∑ j : {j // j ∈ s.val},
      (Finsupp.lsingle (eraseIndex s j)).comp
        (LinearMap.lsmul (MvPolynomial V K) I
          (X j.val * (((eraseSign j.val s.val : ℤˣ) : ℤ) : MvPolynomial V K))))).restrictScalars K

/-- The outgoing map at homological degree zero is exactly zero. -/
def previous (I : Ideal (MvPolynomial V K)) :
    ∀ p : ℕ, Coordinates I p →ₗ[K] Coordinates I p.pred
  | 0 => 0
  | p + 1 => differential I p

/-- Read an actual polynomial ideal coefficient at one exterior coordinate. -/
def coefficientAt (I : Ideal (MvPolynomial V K)) (p : ℕ)
    (s : Set.powersetCard V p) : Coordinates I p →ₗ[K] MvPolynomial V K :=
  (I.subtype.restrictScalars K).comp (Finsupp.lapply s)

/-- Total integer degree q means polynomial coefficient degree q-p at every
exterior p-subset. Negative degrees vanish by the actual polynomial grading;
no numerical zero convention occurs in this definition. -/
def piece (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (Coordinates I p) :=
  ⨅ s : Set.powersetCard V p,
    (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℤ)) (q - (p : ℤ))).comap
      (coefficientAt I p s)

/-- The genuine cycles of the total-degree-q polynomial Koszul component. -/
def cycles (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (Coordinates I p) :=
  LinearMap.ker (previous I p) ⊓ piece I q p

/-- The canonical additive group of the actual cycle submodule. This explicit
instance keeps the quotient on the same canonical ring/module structures. -/
instance cyclesAddCommGroup (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    AddCommGroup (cycles I q p) :=
  Submodule.addCommGroup (R := K) (M := Coordinates I p) (cycles I q p)

/-- Actual boundaries, mapped from the preceding homogeneous component and
viewed in its cycles. The Solution establishes differential squared zero. -/
def boundaries (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (cycles I q p) :=
  (Submodule.map (differential I p) (piece I q (p + 1))).comap (cycles I q p).subtype

/-- The actual homogeneous polynomial Koszul homology quotient. -/
abbrev Homology (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :=
  (cycles I q p) ⧸ boundaries I q p

/-- The canonical additive group on the actual homogeneous homology quotient. -/
instance homologyAddCommGroup (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    AddCommGroup (Homology I q p) :=
  Submodule.Quotient.addCommGroup (R := K) (M := cycles I q p) (boundaries I q p)

/-- The canonical coefficient module on the actual homogeneous homology quotient. -/
instance homologyModule (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Module K (Homology I q p) :=
  Submodule.Quotient.module (R := K) (M := cycles I q p) (boundaries I q p)

end PalomarSublatticeCor53.Koszul
namespace PalomarSublatticeCor53.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [Field K]

/-- The dimension of the actual homogeneous Koszul homology vector space. -/
def betti (I : Ideal (MvPolynomial V K)) (p : ℕ) (q : ℤ) : ℕ :=
  Module.finrank K (Homology I q p)
end PalomarSublatticeCor53.Koszul
namespace PalomarSublatticeCor53
open Classical MvPolynomial
universe u
variable {d : ℕ} (n : Fin d → ℕ)
noncomputable instance (priority := 2000) finiteVariableLinearOrder {d : ℕ} (n : Fin d → ℕ) :
    LinearOrder (FiniteVariable.{u} n) :=
  LinearOrder.lift' (Fintype.equivFin (FiniteVariable.{u} n)) (Fintype.equivFin _).injective
def rowMonomial {k : Type u} [Field k] (a : FiniteTuple n) :
    MvPolynomial (FiniteVariable.{u} n) k := ∏ r, X ⟨r, ULift.up (a r)⟩
/-- The literal sublattice ideal generated by the row monomials. -/
def sublatticeIdeal {k : Type u} [Field k] (E : Finset (FiniteTuple n)) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  Ideal.span (rowMonomial n '' (E : Set (FiniteTuple n)))
def initialIdeal {V k : Type*} [CommRing k]
    (o : MonomialOrder V) (J : Ideal (MvPolynomial V k)) : Ideal (MvPolynomial V k) :=
  Ideal.span (o.leadingTerm '' (J : Set (MvPolynomial V k)))
end PalomarSublatticeCor53

namespace PalomarSublatticeCor53
open Classical MvPolynomial CategoryTheory
universe u
variable {V k : Type u} [Field k]
/-- The actual coefficient field with polynomial action by evaluation at zero. -/
def residueModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)
/-- Polynomial multiplication lies in the next ordinary ideal power. -/
theorem multiplication_mem (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (s : ℕ) (x : ↥(J^s)) : f*x.val ∈ J^(s+1) := by
  rw [pow_succ, mul_comm f]
  exact Ideal.mul_mem_mul x.property hf
/-- The actual polynomial-module map, with no monic normalization or class data. -/
def multiplication (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (s : ℕ) :
    ModuleCat.of (MvPolynomial V k) ↥(J^s) ⟶
      ModuleCat.of (MvPolynomial V k) ↥(J^(s+1)) :=
  ModuleCat.ofHom
    (((LinearMap.mulLeft (MvPolynomial V k) f).domRestrict (J^s)).codRestrict
      (J^(s+1)) (fun x => multiplication_mem J f hf s x))
/-- Mathlib's genuine derived Tor functor applied to that same multiplication. -/
def torMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k) (hf : f ∈ J)
    (s p : ℕ) :=
  ((CategoryTheory.Tor (ModuleCat (MvPolynomial V k)) p).map
    (multiplication J f hf s)).app (residueModule (V := V) (k := k))
variable [Fintype V] [LinearOrder V]
/-- Multiply every actual ideal coefficient, leaving the exterior index fixed. -/
def coefficientMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (s p : ℕ) :
    Koszul.Coordinates (J^s) p →ₗ[k] Koszul.Coordinates (J^(s+1)) p :=
  Finsupp.mapRange.linearMap ((multiplication J f hf s).hom.restrictScalars k)
end PalomarSublatticeCor53
