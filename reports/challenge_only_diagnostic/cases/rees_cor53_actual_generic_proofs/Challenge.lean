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
/-- The coefficient-first derived-Tor map, matching the displayed k-first
convention. The source proves its natural braiding to the other Tor map. -/
def coefficientFirstTorMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (s p : ℕ) :=
  ((CategoryTheory.Tor' (ModuleCat (MvPolynomial V k)) p).obj
    (residueModule (V := V) (k := k))).map (multiplication J f hf s)
variable [Fintype V] [LinearOrder V]
/-- Multiply every actual ideal coefficient, leaving the exterior index fixed. -/
def coefficientMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (s p : ℕ) :
    Koszul.Coordinates (J^s) p →ₗ[k] Koszul.Coordinates (J^(s+1)) p :=
  Finsupp.mapRange.linearMap ((multiplication J f hf s).hom.restrictScalars k)
end PalomarSublatticeCor53

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Classical MvPolynomial CategoryTheory
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace PalomarSublatticeCor53
universe u
variable {V k : Type u} [Field k] [Fintype V] [LinearOrder V]

private theorem coefficientMap_single (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (a : Set.powersetCard V p) (x : ↥(J^s)) :
    coefficientMap J f hf s p (Finsupp.single a x) =
      Finsupp.single a (multiplication J f hf s x) := by
  simp [coefficientMap]

private theorem coefficientMap_apply_val (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) (a : Set.powersetCard V p) :
    (coefficientMap J f hf s p z a).val = f*(z a).val := by
  simp [coefficientMap,multiplication]

private theorem differential_single (I : Ideal (MvPolynomial V k)) (p : ℕ)
    (a : Set.powersetCard V (p+1)) (x : I) :
    Koszul.differential I p (Finsupp.single a x) =
      ∑ j : {j // j ∈ a.val}, Finsupp.single (Koszul.eraseIndex a j)
        ((X j.val * (((Koszul.eraseSign j.val a.val : ℤˣ) : ℤ) : MvPolynomial V k)) • x) := by
  simp only [Koszul.differential,LinearMap.restrictScalars_apply,Finsupp.lsum_single,
    LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,LinearMap.lsmul_apply]

/-- The actual coefficient multiplier commutes with the deletion differential. -/
private theorem coefficientMap_differential (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) (p+1)) :
    coefficientMap J f hf s p (Koszul.differential (J^s) p z) =
      Koszul.differential (J^(s+1)) p (coefficientMap J f hf s (p+1) z) := by
  have h : (coefficientMap J f hf s p).comp (Koszul.differential (J^s) p) =
      (Koszul.differential (J^(s+1)) p).comp (coefficientMap J f hf s (p+1)) := by
    apply Finsupp.lhom_ext
    intro a x
    simp only [LinearMap.comp_apply,coefficientMap_single,differential_single,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coefficientMap_single]
    congr 1
    exact (multiplication J f hf s).hom.map_smul _ x
  exact LinearMap.congr_fun h z

private theorem coefficientMap_previous (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) :
    coefficientMap J f hf s p.pred (Koszul.previous (J^s) p z) =
      Koszul.previous (J^(s+1)) p (coefficientMap J f hf s p z) := by
  cases p with
  | zero => simp only [Koszul.previous,LinearMap.zero_apply,map_zero]
  | succ p => exact coefficientMap_differential J f hf s p z

private theorem homogeneous_nat_to_int (f : MvPolynomial V k) (d : ℕ)
    (hf : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d) :
    f.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (d : ℤ) := by
  intro a ha
  have he : Finsupp.weight (fun _ : V => (1 : ℤ)) a =
      (Finsupp.weight (fun _ : V => (1 : ℕ)) a : ℤ) := by
    simp only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,mul_one,Nat.cast_sum,Nat.cast_id]
  rw [he,hf ha]

private theorem coefficientMap_piece (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) (z : Koszul.Coordinates (J^s) p)
    (hz : z ∈ Koszul.piece (J^s) q p) :
    coefficientMap J f hf s p z ∈ Koszul.piece (J^(s+1)) (q+(d : ℤ)) p := by
  simp only [Koszul.piece,Submodule.mem_iInf,Submodule.mem_comap] at hz ⊢
  intro a
  have ha := hz a
  change (z a).val.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (q-(p : ℤ)) at ha
  change (coefficientMap J f hf s p z a).val.IsWeightedHomogeneous
    (fun _ : V => (1 : ℤ)) ((q+(d : ℤ))-(p : ℤ))
  rw [coefficientMap_apply_val]
  convert (homogeneous_nat_to_int f d hhom).mul ha using 1 <;> omega

theorem multiplication_cycles (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) (z : Koszul.cycles (J^s) q p) :
    coefficientMap J f hf s p z.val ∈ Koszul.cycles (J^(s+1)) (q+(d : ℤ)) p := by
  refine ⟨?_,coefficientMap_piece J f hf d hhom s p q z.val z.property.2⟩
  change Koszul.previous (J^(s+1)) p (coefficientMap J f hf s p z.val)=0
  rw [← coefficientMap_previous,show Koszul.previous (J^s) p z.val=0 from z.property.1,map_zero]

/-- The induced linear map on the actual homogeneous cycles. -/
def cyclesMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.cycles (J^s) q p →ₗ[k] Koszul.cycles (J^(s+1)) (q+(d : ℤ)) p :=
  ((coefficientMap J f hf s p).domRestrict _).codRestrict _
    (fun z => multiplication_cycles J f hf d hhom s p q z)

theorem multiplication_boundaries (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.boundaries (J^s) q p ≤
      (Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p).comap
        (cyclesMap J f hf d hhom s p q) := by
  intro z hz
  change z.val ∈ Submodule.map (Koszul.differential (J^s) p)
    (Koszul.piece (J^s) q (p+1)) at hz
  obtain ⟨w,hw,hwz⟩ := hz
  change coefficientMap J f hf s p z.val ∈
    Submodule.map (Koszul.differential (J^(s+1)) p)
      (Koszul.piece (J^(s+1)) (q+(d : ℤ)) (p+1))
  refine ⟨coefficientMap J f hf s (p+1) w,
    coefficientMap_piece J f hf d hhom s (p+1) q w hw,?_⟩
  rw [← coefficientMap_differential,hwz]

/-- The literal induced map on the genuine degree-q Koszul homology quotient.
Its target degree is q+d for every signed integer q. -/
def homologyMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.Homology (J^s) q p →ₗ[k] Koszul.Homology (J^(s+1)) (q+(d : ℤ)) p :=
  (Koszul.boundaries (J^s) q p).mapQ
    (Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p)
    (cyclesMap J f hf d hhom s p q) (multiplication_boundaries J f hf d hhom s p q)

/-- Actual boundary reflection is the exact quotient-injectivity criterion. -/
theorem homologyMap_injective_of_boundary_reflection
    (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ)
    (h : ∀ z : Koszul.cycles (J^s) q p,
      cyclesMap J f hf d hhom s p q z ∈ Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p →
        z ∈ Koszul.boundaries (J^s) q p) :
    Function.Injective (homologyMap J f hf d hhom s p q) := by
  apply LinearMap.ker_eq_bot.mp
  rw [homologyMap,Submodule.ker_mapQ]
  apply le_antisymm
  · rintro z ⟨x,hx,rfl⟩
    change (Koszul.boundaries (J^s) q p).mkQ x=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact h x hx
  · exact bot_le

end PalomarSublatticeCor53

#print axioms PalomarSublatticeCor53.multiplication_mem
#print axioms PalomarSublatticeCor53.multiplication_cycles
#print axioms PalomarSublatticeCor53.multiplication_boundaries
#print axioms PalomarSublatticeCor53.homologyMap_injective_of_boundary_reflection
