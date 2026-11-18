module

public import sunlet.latin_orbits
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.Group
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Fintype.Quotient
public import sunlet.ordinary_edge_rigidity
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Group.MinimalAxioms
public import sunlet.normalized_variations
public import sunlet.matrix_specialization
public import sunlet.rational_partials
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Algebra.Rat
public import sunlet.contact_equations
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases
public import sunlet.jacobian_finite
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.BigOperators.Finprod
public import sunlet.sparse_contact
public import Mathlib.LinearAlgebra.Basis.Basic
public import sunlet.etale_derivations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import sunlet.permutation_families
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
noncomputable section


section Source_LoopAbelianization


/-! The universal abelian group of a finite loop.
It is constructed as a proved quotient of the free abelian group. Every
quotient element has a loop representative, and translation identifies all
fibers. In particular its order divides the loop order. -/


namespace Sunlet

/-- A loop written as normalized left translations, with both Latin
conditions retained explicitly. -/
structure LoopData (Ω : Type*) where
  identity : Ω
  left : Ω → Equiv.Perm Ω
  left_identity : left identity = Equiv.refl Ω
  right_identity : ∀ x, left x identity = x
  column_bijective : ∀ y, Function.Bijective (fun x => left x y)

namespace LoopData

variable {Ω : Type*} (L : LoopData Ω)

def mul (x y : Ω) : Ω := L.left x y

@[simp] theorem identity_mul (x : Ω) : L.mul L.identity x = x := by
  simp [mul, L.left_identity]

@[simp] theorem mul_identity (x : Ω) : L.mul x L.identity = x := L.right_identity x

/-- Associativity has its ordinary quantified meaning, not a new typeclass
assumption on the loop. -/
def IsAssociative : Prop := ∀ x y z, L.mul (L.mul x y) z = L.mul x (L.mul y z)

def relations : AddSubgroup (FreeAbelianGroup Ω) :=
  AddSubgroup.closure ({FreeAbelianGroup.of L.identity} ∪
    Set.range (fun xy : Ω × Ω => FreeAbelianGroup.of (L.mul xy.1 xy.2) -
      FreeAbelianGroup.of xy.1 - FreeAbelianGroup.of xy.2))

abbrev AbelianGroup := FreeAbelianGroup Ω ⧸ L.relations

def toAbelianGroup (x : Ω) : L.AbelianGroup :=
  QuotientAddGroup.mk' L.relations (FreeAbelianGroup.of x)

@[simp] theorem toAbelianGroup_identity : L.toAbelianGroup L.identity = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure (Or.inl rfl)

@[simp] theorem toAbelianGroup_mul (x y : Ω) :
    L.toAbelianGroup (L.mul x y) = L.toAbelianGroup x + L.toAbelianGroup y := by
  have h : (QuotientAddGroup.mk' L.relations)
      (FreeAbelianGroup.of (L.mul x y) - FreeAbelianGroup.of x - FreeAbelianGroup.of y) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact AddSubgroup.subset_closure (Or.inr ⟨(x, y), rfl⟩)
  change (L.toAbelianGroup (L.mul x y) - L.toAbelianGroup x) - L.toAbelianGroup y = 0 at h
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp h)).trans (add_comm _ _)

theorem toAbelianGroup_left_inverse (x : Ω) :
    L.toAbelianGroup ((L.left x).symm L.identity) = -L.toAbelianGroup x := by
  have h := L.toAbelianGroup_mul x ((L.left x).symm L.identity)
  have he : L.mul x ((L.left x).symm L.identity) = L.identity :=
    (L.left x).apply_symm_apply L.identity
  rw [he, L.toAbelianGroup_identity] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Every element of the universal abelian group is represented by a single
loop element. This also proves finiteness without assuming it. -/
theorem toAbelianGroup_surjective : Function.Surjective L.toAbelianGroup := by
  intro q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.relations q
  induction z using FreeAbelianGroup.induction_on with
  | zero => exact ⟨L.identity, L.toAbelianGroup_identity⟩
  | of x => exact ⟨x, rfl⟩
  | neg x _ =>
    refine ⟨(L.left x).symm L.identity, ?_⟩
    simpa only [map_neg, toAbelianGroup] using L.toAbelianGroup_left_inverse x
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨L.mul a b, by rw [L.toAbelianGroup_mul, ha, hb, map_add]⟩

instance abelianGroup_finite [Finite Ω] : Finite L.AbelianGroup :=
  Finite.of_surjective L.toAbelianGroup L.toAbelianGroup_surjective

instance abelianGroup_fintype [Finite Ω] : Fintype L.AbelianGroup := Fintype.ofFinite _

section UniversalProperty

variable {A : Type*} [AddCommGroup A]

def lift (f : Ω → A) (hidentity : f L.identity = 0)
    (hmul : ∀ x y, f (L.mul x y) = f x + f y) : L.AbelianGroup →+ A :=
  QuotientAddGroup.lift L.relations (FreeAbelianGroup.lift f) (by
    apply (AddSubgroup.closure_le _).mpr
    intro z hz
    rcases hz with hz | ⟨⟨x, y⟩, rfl⟩
    · have he : z = FreeAbelianGroup.of L.identity := hz
      subst z
      change (FreeAbelianGroup.lift f) (FreeAbelianGroup.of L.identity) = 0
      simpa using hidentity
    · change (FreeAbelianGroup.lift f)
        (FreeAbelianGroup.of (L.mul x y) - FreeAbelianGroup.of x - FreeAbelianGroup.of y) = 0
      simp [hmul])

@[simp] theorem lift_toAbelianGroup (f : Ω → A) (hidentity : f L.identity = 0)
    (hmul : ∀ x y, f (L.mul x y) = f x + f y) (x : Ω) :
    L.lift f hidentity hmul (L.toAbelianGroup x) = f x := by
  simp [lift, toAbelianGroup]

theorem lift_unique (f : Ω → A) (hidentity : f L.identity = 0)
    (hmul : ∀ x y, f (L.mul x y) = f x + f y) (g : L.AbelianGroup →+ A)
    (hg : ∀ x, g (L.toAbelianGroup x) = f x) : g = L.lift f hidentity hmul := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := L.toAbelianGroup_surjective q
  exact (hg x).trans (L.lift_toAbelianGroup f hidentity hmul x).symm

end UniversalProperty

section Cardinality

variable [Fintype Ω] [DecidableEq Ω]

abbrev IdentityFiber := {x : Ω // L.toAbelianGroup x = 0}

noncomputable def representative (q : L.AbelianGroup) : Ω :=
  Classical.choose (L.toAbelianGroup_surjective q)

@[simp] theorem representative_image (q : L.AbelianGroup) :
    L.toAbelianGroup (L.representative q) = q :=
  Classical.choose_spec (L.toAbelianGroup_surjective q)

/-- Left translation identifies every fiber with the identity fiber. -/
theorem translation_bijective : Function.Bijective
    (fun qx : L.AbelianGroup × L.IdentityFiber => L.left (L.representative qx.1) qx.2) := by
  constructor
  · rintro ⟨q, x⟩ ⟨r, y⟩ h
    have he := congrArg L.toAbelianGroup h
    change L.toAbelianGroup (L.mul (L.representative q) x) =
      L.toAbelianGroup (L.mul (L.representative r) y) at he
    simp only [L.toAbelianGroup_mul, L.representative_image, x.property, y.property, add_zero] at he
    subst r
    exact Prod.ext rfl (Subtype.ext ((L.left (L.representative q)).injective h))
  · intro x
    let q := L.toAbelianGroup x
    let y := (L.left (L.representative q)).symm x
    have hy : L.toAbelianGroup y = 0 := by
      have hh := L.toAbelianGroup_mul (L.representative q) y
      have he : L.mul (L.representative q) y = x :=
        (L.left (L.representative q)).apply_symm_apply x
      rw [he, L.representative_image] at hh
      exact add_left_cancel (hh.symm.trans (add_zero q).symm)
    exact ⟨(q, ⟨y, hy⟩), (L.left (L.representative q)).apply_symm_apply x⟩

theorem abelianGroup_card_dvd : Fintype.card L.AbelianGroup ∣ Fintype.card Ω := by
  classical
  let e := Equiv.ofBijective _ L.translation_bijective
  have h := Fintype.card_congr e
  simp only [Fintype.card_prod] at h
  exact ⟨Fintype.card L.IdentityFiber, h.symm⟩

theorem associative_of_abelianGroup_card_eq
    (hcard : Fintype.card L.AbelianGroup = Fintype.card Ω) : L.IsAssociative := by
  have hinj : Function.Injective L.toAbelianGroup :=
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨L.toAbelianGroup_surjective, hcard.symm⟩).injective
  intro x y z
  apply hinj
  simp only [L.toAbelianGroup_mul, add_assoc]

/-- The group-theoretic input of Theorem 5.1: a nonassociative loop of prime
order has trivial universal abelian group. -/
theorem abelianGroup_card_eq_one_of_prime_nonassociative
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative) :
    Fintype.card L.AbelianGroup = 1 := by
  rcases hprime.eq_one_or_self_of_dvd _ L.abelianGroup_card_dvd with h | h
  · exact h
  · exact False.elim (hnonassoc (L.associative_of_abelianGroup_card_eq h))

end Cardinality
end LoopData

namespace NormalizedLatinSystem

variable {ι Ω : Type*} (L : NormalizedLatinSystem ι Ω)

/-- Relabeling a normalized Latin system by its column at the chosen point
produces the literal loop used in the degree statement. -/
def loopAt (o : Ω) : LoopData Ω := by
  let e : ι ≃ Ω := Equiv.ofBijective (fun a => L.perm a o) (L.column_bijective o)
  have he : e.symm o = L.identity := by
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    change o = L.perm L.identity o
    simp [L.normalized]
  exact
    { identity := o
      left := fun x => L.perm (e.symm x)
      left_identity := by rw [he, L.normalized]
      right_identity := fun x => e.apply_symm_apply x
      column_bijective := fun y => (L.column_bijective y).comp e.symm.bijective }

end NormalizedLatinSystem
end Sunlet

end Source_LoopAbelianization

section Source_LoopCharacters


/-! Characters of the loop are exactly characters of its constructed
universal abelian group. The character count uses Mathlib's proved finite
abelian duality theorem with all roots-of-unity hypotheses supplied. -/


namespace Sunlet.LoopData

variable {Ω M : Type*} (L : LoopData Ω) [CommGroup M]

def characterSubgroup : Subgroup (Ω → M) where
  carrier := {χ | χ L.identity = 1 ∧ ∀ x y, χ (L.mul x y) = χ x * χ y}
  one_mem' := by simp
  mul_mem' := by
    intro χ ψ hχ hψ
    refine ⟨by simp [hχ.1, hψ.1], ?_⟩
    intro x y
    simp only [Pi.mul_apply, hχ.2, hψ.2]
    ac_rfl
  inv_mem' := by
    intro χ hχ
    refine ⟨by simp [hχ.1], ?_⟩
    intro x y
    simp only [Pi.inv_apply, hχ.2, mul_inv_rev]
    exact mul_comm _ _

def restrictCharacter (χ : Multiplicative L.AbelianGroup →* M) : L.characterSubgroup (M := M) :=
  ⟨fun x => χ (.ofAdd (L.toAbelianGroup x)), by
    constructor
    · simpa using χ.map_one
    · intro x y
      change χ (.ofAdd (L.toAbelianGroup (L.mul x y))) =
        χ (.ofAdd (L.toAbelianGroup x)) * χ (.ofAdd (L.toAbelianGroup y))
      rw [L.toAbelianGroup_mul]
      exact χ.map_mul _ _⟩

def liftCharacter (χ : L.characterSubgroup (M := M)) : Multiplicative L.AbelianGroup →* M where
  toFun q := Additive.toMul (L.lift (fun x => Additive.ofMul (χ.1 x)) χ.2.1 χ.2.2 q.toAdd)
  map_one' := by change Additive.toMul ((L.lift _ _ _) 0) = 1; rw [map_zero]; rfl
  map_mul' q r := by
    change Additive.toMul ((L.lift _ _ _) (q.toAdd + r.toAdd)) = _
    rw [map_add]
    rfl

@[simp] theorem liftCharacter_generator (χ : L.characterSubgroup (M := M)) (x : Ω) :
    L.liftCharacter χ (.ofAdd (L.toAbelianGroup x)) = χ.1 x := by
  exact congrArg Additive.toMul
    (L.lift_toAbelianGroup (A := Additive M) (fun y => Additive.ofMul (χ.1 y)) χ.2.1 χ.2.2 x)

/-- Exact multiplicative character equivalence, with the universal property
of the quotient proved in `LoopAbelianization`. -/
def characterEquiv : (Multiplicative L.AbelianGroup →* M) ≃* L.characterSubgroup (M := M) where
  toFun := L.restrictCharacter
  invFun := L.liftCharacter
  left_inv χ := by
    apply MonoidHom.ext
    intro q
    obtain ⟨x, hx⟩ := L.toAbelianGroup_surjective q.toAdd
    have he : Multiplicative.ofAdd (L.toAbelianGroup x) = q := congrArg Multiplicative.ofAdd hx
    rw [← he, L.liftCharacter_generator]
    rfl
  right_inv χ := by
    apply Subtype.ext
    funext x
    exact L.liftCharacter_generator χ x
  map_mul' χ ψ := by
    apply Subtype.ext
    rfl

section AlgebraicallyClosed

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Finite Ω]

private theorem enoughRoots :
    HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative L.AbelianGroup)) := by
  letI : NeZero (Monoid.exponent (Multiplicative L.AbelianGroup) : K) :=
    ⟨by exact_mod_cast (NeZero.ne (Monoid.exponent (Multiplicative L.AbelianGroup)))⟩
  infer_instance

/-- Over an algebraically closed field of characteristic zero, the number
of loop characters is precisely the order of its universal abelian group. -/
theorem character_card : Nat.card (L.characterSubgroup (M := Kˣ)) = Nat.card L.AbelianGroup := by
  letI := L.enoughRoots (K := K)
  calc
    Nat.card (L.characterSubgroup (M := Kˣ)) =
        Nat.card (Multiplicative L.AbelianGroup →* Kˣ) :=
      Nat.card_congr (L.characterEquiv (M := Kˣ)).symm.toEquiv
    _ = Nat.card (Multiplicative L.AbelianGroup) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
    _ = Nat.card L.AbelianGroup := Nat.card_congr Multiplicative.toAdd

instance character_finite : Finite (L.characterSubgroup (M := Kˣ)) := by
  letI := L.enoughRoots (K := K)
  let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
    (Multiplicative L.AbelianGroup) K).some
  letI : Finite (Multiplicative L.AbelianGroup →* Kˣ) :=
    Finite.of_equiv (Multiplicative L.AbelianGroup) e.symm.toEquiv
  exact Finite.of_equiv _ (L.characterEquiv (M := Kˣ)).toEquiv

end AlgebraicallyClosed
end Sunlet.LoopData

end Source_LoopCharacters

section Source_LoopToricFibers


/-! Exact fibers of the single ratio-monomial map on its parameter torus.
The equivalence with the character group is explicit. This is the toric
factor in the later secant-degree calculation, not a replacement for it. -/


namespace Sunlet.LoopData

variable {Ω M : Type*} (L : LoopData Ω) [CommGroup M]

@[ext] structure ToricParameters where
  coefficient : Ω → M
  torus : Ω → M
  coefficient_identity : coefficient L.identity = 1
  torus_identity : torus L.identity = 1

namespace ToricParameters

variable {L}

def coordinate (p : L.ToricParameters (M := M)) (a b : Ω) : M :=
  p.coefficient a * p.torus b / p.torus (L.mul a b)

def characterAction (p : L.ToricParameters (M := M)) (χ : L.characterSubgroup (M := M)) :
    L.ToricParameters (M := M) where
  coefficient a := p.coefficient a * χ.1 a
  torus b := p.torus b * χ.1 b
  coefficient_identity := by simp [p.coefficient_identity, χ.2.1]
  torus_identity := by simp [p.torus_identity, χ.2.1]

@[simp] theorem characterAction_coordinate (p : L.ToricParameters (M := M))
    (χ : L.characterSubgroup (M := M)) (a b : Ω) :
    (p.characterAction χ).coordinate a b = p.coordinate a b := by
  change (p.coefficient a * χ.1 a) * (p.torus b * χ.1 b) /
    (p.torus (L.mul a b) * χ.1 (L.mul a b)) =
      (p.coefficient a * p.torus b) / p.torus (L.mul a b)
  rw [mul_mul_mul_comm, χ.2.2, mul_div_mul_right_eq_div]

lemma coefficient_of_same_coordinates (p q : L.ToricParameters (M := M))
    (h : ∀ a b, p.coordinate a b = q.coordinate a b) (a : Ω) :
    q.coefficient a = p.coefficient a * (q.torus a / p.torus a) := by
  have hh := (h a L.identity).symm
  simp only [coordinate, p.torus_identity, q.torus_identity, L.mul_identity, mul_one] at hh
  calc
    q.coefficient a = (q.coefficient a / q.torus a) * q.torus a := by simp
    _ = (p.coefficient a / p.torus a) * q.torus a := congrArg (fun z : M => z * q.torus a) hh
    _ = p.coefficient a * (q.torus a / p.torus a) := by
      simp only [div_eq_mul_inv]
      ac_rfl

def quotientCharacter (p q : L.ToricParameters (M := M))
    (h : ∀ a b, p.coordinate a b = q.coordinate a b) : L.characterSubgroup (M := M) := by
  let χ : Ω → M := fun b => q.torus b / p.torus b
  have htorus : ∀ b, q.torus b = p.torus b * χ b := by intro b; simp [χ, mul_comm]
  have hcoefficient : ∀ a, q.coefficient a = p.coefficient a * χ a :=
    coefficient_of_same_coordinates p q h
  refine ⟨χ, by simp [χ, p.torus_identity, q.torus_identity], ?_⟩
  intro a b
  have he : q.coordinate a b = p.coordinate a b * (χ a * χ b / χ (L.mul a b)) := by
    simp only [coordinate, hcoefficient, htorus]
    rw [mul_mul_mul_comm, mul_div_mul_comm]
  have hh : p.coordinate a b * (χ a * χ b / χ (L.mul a b)) = p.coordinate a b * 1 := by
    rw [← he, ← h a b, mul_one]
  exact (div_eq_one.mp (mul_left_cancel hh)).symm

@[simp] theorem quotientCharacter_apply (p q : L.ToricParameters (M := M))
    (h : ∀ a b, p.coordinate a b = q.coordinate a b) (b : Ω) :
    (p.quotientCharacter q h).1 b = q.torus b / p.torus b := rfl

theorem characterAction_quotientCharacter (p q : L.ToricParameters (M := M))
    (h : ∀ a b, p.coordinate a b = q.coordinate a b) :
    p.characterAction (p.quotientCharacter q h) = q := by
  apply ToricParameters.ext
  · funext a
    exact (coefficient_of_same_coordinates p q h a).symm
  · funext b
    simp [characterAction, quotientCharacter_apply, mul_comm]

theorem characterAction_injective (p : L.ToricParameters (M := M)) :
    Function.Injective p.characterAction := by
  intro χ ψ h
  apply Subtype.ext
  funext b
  have hh := congrArg (fun q : L.ToricParameters (M := M) => q.torus b) h
  exact mul_left_cancel hh

/-- The full fiber on the normalized parameter torus, with an explicit
inverse obtained by dividing the two torus parameter families. -/
def fiberEquivCharacters (p : L.ToricParameters (M := M)) :
    {q : L.ToricParameters (M := M) // ∀ a b, p.coordinate a b = q.coordinate a b} ≃
      L.characterSubgroup (M := M) where
  toFun q := p.quotientCharacter q.1 q.2
  invFun χ := ⟨p.characterAction χ, fun a b => (characterAction_coordinate p χ a b).symm⟩
  left_inv q := Subtype.ext (characterAction_quotientCharacter p q.1 q.2)
  right_inv χ := by
    apply p.characterAction_injective
    exact characterAction_quotientCharacter p (p.characterAction χ) _

end ToricParameters

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Finite Ω]

/-- The single toric fiber has exactly the claimed finite character count.
The two-summand secant degree additionally requires the separate unordered
identifiability theorem. -/
theorem toric_fiber_card (p : L.ToricParameters (M := Kˣ)) :
    Nat.card {q : L.ToricParameters (M := Kˣ) // ∀ a b, p.coordinate a b = q.coordinate a b} =
      Nat.card L.AbelianGroup := by
  rw [Nat.card_congr p.fiberEquivCharacters]
  exact L.character_card

end Sunlet.LoopData

end Source_LoopToricFibers

section Source_LatinNoPreservedBlock


/-! The incidence-count argument underlying orbit halving. A normalized
Latin family contains a color preserving none of the blocks of any
nontrivial finite partition. -/

open scoped BigOperators

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω Q : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Fintype Q] [DecidableEq Q] (L : NormalizedLatinSystem ι Ω)

def PreservesBlock (f : Ω → Q) (a : ι) (q : Q) : Prop :=
  ∀ x, f x = q → f (L.perm a x) = q

instance preservesBlockDecidable (f : Ω → Q) (a : ι) (q : Q) :
    Decidable (L.PreservesBlock f a q) :=
  inferInstanceAs (Decidable (∀ x, f x = q → f (L.perm a x) = q))

/-- The number of nonidentity colors preserving a block is at most one less
than its size, because their images of a chosen point are all distinct. -/
theorem preserving_card_bound (f : Ω → Q) (hf : Function.Surjective f) (q : Q) :
    Fintype.card {a : ι // a ≠ L.identity ∧ L.PreservesBlock f a q} + 1 ≤
      Fintype.card {x : Ω // f x = q} := by
  classical
  obtain ⟨x, hx⟩ := hf q
  let base : {x : Ω // f x = q} := ⟨x, hx⟩
  let g : {a : ι // a ≠ L.identity ∧ L.PreservesBlock f a q} →
      {y : {x : Ω // f x = q} // y ≠ base} := fun a =>
    ⟨⟨L.perm a.1 x, a.2.2 x hx⟩, fun h => L.derangement a.1 a.2.1 x (congrArg (fun y => y.1) h)⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact (L.column_bijective x).injective (congrArg (fun y => y.1.1) h)
  have hc := Fintype.card_le_of_injective g hg
  have hsub : Fintype.card {y : {x : Ω // f x = q} // y ≠ base} =
      Fintype.card {x : Ω // f x = q} - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun y : {x : Ω // f x = q} => y = base)
  have hpos : 0 < Fintype.card {x : Ω // f x = q} := Fintype.card_pos_iff.mpr ⟨base⟩
  omega

/-- A color preserving none of the blocks exists for every nontrivial
partition. The proof counts actual block--color incidences. -/
theorem exists_color_preserving_no_block (o : Ω) (f : Ω → Q)
    (hf : Function.Surjective f) (hQ : 2 ≤ Fintype.card Q) :
    ∃ a : ι, a ≠ L.identity ∧ ∀ q, ¬L.PreservesBlock f a q := by
  classical
  by_contra hn
  push_neg at hn
  have chooseBlock : ∀ a : {a : ι // a ≠ L.identity}, ∃ q, L.PreservesBlock f a.1 q :=
    fun a => hn a.1 a.2
  choose block hblock using chooseBlock
  let g : {a : ι // a ≠ L.identity} →
      (Σ q : Q, {a : ι // a ≠ L.identity ∧ L.PreservesBlock f a q}) :=
    fun a => ⟨block a, ⟨a.1, a.2, hblock a⟩⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : Σ q : Q, {a : ι // a ≠ L.identity ∧ L.PreservesBlock f a q} => z.2.1) h
  have hc := Fintype.card_le_of_injective g hg
  rw [Fintype.card_sigma] at hc
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset Q)) =>
    L.preserving_card_bound f hf q)
  have hfibers : (∑ q : Q, Fintype.card {x : Ω // f x = q}) = Fintype.card Ω := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hsum : (∑ q : Q, Fintype.card {a : ι // a ≠ L.identity ∧ L.PreservesBlock f a q}) +
      Fintype.card Q ≤ Fintype.card Ω := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one, hfibers] using hs
  have hnonid : Fintype.card {a : ι // a ≠ L.identity} = Fintype.card Ω - 1 := by
    rw [← L.card_eq o]
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun a : ι => a = L.identity)
  omega

end Sunlet.NormalizedLatinSystem

end Source_LatinNoPreservedBlock

section Source_LatinOrbitHalving


/-! Adding a color that preserves no old orbit halves the number of orbits.
All orbit quotients and their maps are constructed explicitly. -/

open scoped BigOperators

namespace Sunlet

lemma twice_card_le_of_other_in_fiber {Q R : Type*} [Fintype Q] [Fintype R]
    (f : Q → R) (hf : Function.Surjective f)
    (hother : ∀ q, ∃ q', q' ≠ q ∧ f q' = f q) :
    2 * Fintype.card R ≤ Fintype.card Q := by
  classical
  have hsize : ∀ r, 2 ≤ Fintype.card {q : Q // f q = r} := by
    intro r
    obtain ⟨q, hq⟩ := hf r
    obtain ⟨q', hne, he⟩ := hother q
    apply (show 1 < Fintype.card {q : Q // f q = r} → 2 ≤ _ by omega)
    apply Fintype.one_lt_card_iff.mpr
    exact ⟨⟨q', he.trans hq⟩, ⟨q, hq⟩, fun h => hne (congrArg Subtype.val h)⟩
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset R)) => hsize r)
  have hcard : (∑ r : R, Fintype.card {q : Q // f q = r}) = Fintype.card Q := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, Nat.mul_comm] using hsum

namespace NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

def familyOrbitSetoid (P : Finset ι) : Setoid Ω := Relation.EqvGen.setoid (ColorEdge L.perm (P : Set ι))

abbrev OrbitClasses (P : Finset ι) := Quotient (L.familyOrbitSetoid P)

instance orbitClassesFintype (P : Finset ι) : Fintype (L.OrbitClasses P) := Fintype.ofFinite _

instance orbitClassesDecidableEq (P : Finset ι) : DecidableEq (L.OrbitClasses P) := Classical.decEq _

def orbitClass (P : Finset ι) (x : Ω) : L.OrbitClasses P := Quotient.mk _ x

theorem orbitClass_surjective (P : Finset ι) : Function.Surjective (L.orbitClass P) :=
  Quotient.mk_surjective

theorem orbitClass_step {P : Finset ι} {a : ι} (ha : a ∈ P) (x : Ω) :
    L.orbitClass P (L.perm a x) = L.orbitClass P x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (colorConnected_step L.perm (P : Set ι) ha x)

def coarsenOrbits {P Q : Finset ι} (hPQ : P ⊆ Q) : L.OrbitClasses P → L.OrbitClasses Q :=
  Quotient.map _root_.id (fun _ _ h => colorConnected_mono (fun a ha => hPQ ha) h)

@[simp] theorem coarsenOrbits_class {P Q : Finset ι} (hPQ : P ⊆ Q) (x : Ω) :
    L.coarsenOrbits hPQ (L.orbitClass P x) = L.orbitClass Q x := rfl

theorem coarsenOrbits_surjective {P Q : Finset ι} (hPQ : P ⊆ Q) :
    Function.Surjective (L.coarsenOrbits hPQ) := by
  intro q
  obtain ⟨x, rfl⟩ := L.orbitClass_surjective Q q
  exact ⟨L.orbitClass P x, rfl⟩

theorem transitive_iff_orbit_card_one (o : Ω) (P : Finset ι) :
    TransitiveFamily L.perm (P : Set ι) ↔ Fintype.card (L.OrbitClasses P) = 1 := by
  constructor
  · intro h
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨L.orbitClass P o, ?_⟩
    intro q
    obtain ⟨x, rfl⟩ := L.orbitClass_surjective P q
    exact Quotient.sound (h x o)
  · intro h x y
    obtain ⟨q, hq⟩ := Fintype.card_eq_one_iff.mp h
    exact Quotient.exact ((hq (L.orbitClass P x)).trans (hq (L.orbitClass P y)).symm)

theorem orbit_card_empty : Fintype.card (L.OrbitClasses ∅) = Fintype.card Ω := by
  have hinj : Function.Injective (L.orbitClass ∅) := by
    intro x y h
    have he := Quotient.exact h
    change ColorConnected L.perm ((∅ : Finset ι) : Set ι) x y at he
    clear h
    induction he with
    | rel x y h => obtain ⟨a, ha, _⟩ := h; exact False.elim (Finset.notMem_empty a ha)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (Fintype.card_congr (Equiv.ofBijective _ ⟨hinj, L.orbitClass_surjective ∅⟩)).symm

/-- Every nontransitive color family can be enlarged by one nonidentity
color, halving its number of orbits. -/
theorem exists_halving_color (o : Ω) (P : Finset ι)
    (hP : ¬TransitiveFamily L.perm (P : Set ι)) :
    ∃ a : ι, a ≠ L.identity ∧ a ∉ P ∧
      2 * Fintype.card (L.OrbitClasses (insert a P)) ≤ Fintype.card (L.OrbitClasses P) := by
  classical
  have hpos : 0 < Fintype.card (L.OrbitClasses P) := Fintype.card_pos_iff.mpr ⟨L.orbitClass P o⟩
  have hone : Fintype.card (L.OrbitClasses P) ≠ 1 :=
    fun h => hP ((L.transitive_iff_orbit_card_one o P).mpr h)
  obtain ⟨a, hae, ha⟩ := L.exists_color_preserving_no_block o (L.orbitClass P)
    (L.orbitClass_surjective P) (by omega)
  have haP : a ∉ P := by
    intro hm
    apply ha (L.orbitClass P o)
    intro x hx
    rw [L.orbitClass_step hm, hx]
  refine ⟨a, hae, haP, ?_⟩
  let ρ := L.coarsenOrbits (Finset.subset_insert a P)
  apply twice_card_le_of_other_in_fiber ρ (L.coarsenOrbits_surjective _)
  intro q
  have hh := ha q
  change ¬∀ x, L.orbitClass P x = q → L.orbitClass P (L.perm a x) = q at hh
  obtain ⟨x, hx⟩ := not_forall.mp hh
  obtain ⟨hx, hxa⟩ := not_imp.mp hx
  refine ⟨L.orbitClass P (L.perm a x), hxa, ?_⟩
  rw [← hx]
  change L.orbitClass (insert a P) (L.perm a x) = L.orbitClass (insert a P) x
  exact L.orbitClass_step (Finset.mem_insert_self a P) x

/-- Iterated orbit halving, stated without logarithms so the final support
size can be chosen directly from the desired cardinal bound. -/
theorem exists_small_orbit_bound (o : Ω) (n : ℕ) :
    ∃ P : Finset ι, L.identity ∉ P ∧ P.card ≤ n ∧
      (TransitiveFamily L.perm (P : Set ι) ∨
        2 ^ n * Fintype.card (L.OrbitClasses P) ≤ Fintype.card Ω) := by
  induction n with
  | zero =>
    refine ⟨∅, Finset.notMem_empty _, by simp, Or.inr ?_⟩
    simp [L.orbit_card_empty]
  | succ n ih =>
    obtain ⟨P, he, hcard, hbound⟩ := ih
    by_cases ht : TransitiveFamily L.perm (P : Set ι)
    · exact ⟨P, he, by omega, Or.inl ht⟩
    · have hb := hbound.resolve_left ht
      obtain ⟨a, hae, haP, hhalf⟩ := L.exists_halving_color o P ht
      refine ⟨insert a P, by simp [Ne.symm hae, he], ?_, Or.inr ?_⟩
      · rw [Finset.card_insert_of_notMem haP]
        omega
      · calc
          2 ^ (n + 1) * Fintype.card (L.OrbitClasses (insert a P)) =
              2 ^ n * (2 * Fintype.card (L.OrbitClasses (insert a P))) := by rw [pow_succ, Nat.mul_assoc]
          _ ≤ 2 ^ n * Fintype.card (L.OrbitClasses P) := Nat.mul_le_mul_left _ hhalf
          _ ≤ Fintype.card Ω := hb

theorem exists_small_transitive_family (o : Ω) (n : ℕ)
    (hbound : Fintype.card Ω < 2 ^ (n + 1)) :
    ∃ P : Finset ι, L.identity ∉ P ∧ P.card ≤ n ∧ TransitiveFamily L.perm (P : Set ι) := by
  obtain ⟨P, he, hcard, ht | hb⟩ := L.exists_small_orbit_bound o n
  · exact ⟨P, he, hcard, ht⟩
  · refine ⟨P, he, hcard, ?_⟩
    by_contra ht
    have hpos : 0 < Fintype.card (L.OrbitClasses P) := Fintype.card_pos_iff.mpr ⟨L.orbitClass P o⟩
    have hone : Fintype.card (L.OrbitClasses P) ≠ 1 :=
      fun h => ht ((L.transitive_iff_orbit_card_one o P).mpr h)
    have htwo : 2 ≤ Fintype.card (L.OrbitClasses P) := by omega
    have hh := Nat.mul_le_mul_left (2 ^ n) htwo
    rw [pow_succ] at hbound
    omega

end NormalizedLatinSystem
end Sunlet

end Source_LatinOrbitHalving

section Source_LatinOrdinaryConnectivity


/-! A finite degree bound proves connectivity after deleting the distinguished
vertex. This uses the actual ordinary-edge graph, not full-orbit connectivity. -/

open Finset

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

theorem inverse_column_injective (o : Ω) :
    Function.Injective (fun a => (L.perm a).symm o) := by
  intro a b h
  change (L.perm a).symm o = (L.perm b).symm o at h
  apply (L.column_bijective ((L.perm a).symm o)).injective
  change L.perm a ((L.perm a).symm o) = L.perm b ((L.perm a).symm o)
  rw [(L.perm a).apply_symm_apply, h, (L.perm b).apply_symm_apply]

theorem ordinary_connected_of_neighbor (o : Ω) (P : Finset ι)
    (x y : {z : Ω // z ≠ o}) (hy : y.1 ∈ L.neighbors P x.1) :
    Relation.EqvGen (PuncturedBothEndpoints.OrdinaryEdge o L.perm (P : Set ι)) x y := by
  rcases mem_insert.mp hy with he | he
  · have hxy : x = y := Subtype.ext he.symm
    subst y
    exact Relation.EqvGen.refl _
  · obtain ⟨a, ha, he⟩ := mem_image.mp he
    exact Relation.EqvGen.rel _ _ ⟨a, ha, he⟩

/-- Each ordinary-edge component has at least as many vertices as colors:
deleting one vertex removes at most one member of the Latin neighbor set. -/
theorem punctured_neighbors_card (o : Ω) (P : Finset ι)
    (he : L.identity ∉ P) (x : Ω) :
    P.card ≤ ((L.neighbors P x).erase o).card := by
  have hc := L.card_neighbors P he x
  by_cases ho : o ∈ L.neighbors P x
  · rw [card_erase_of_mem ho]
    omega
  · rw [erase_eq_of_notMem ho, hc]
    omega

/-- Strictly more than half the nondeleted vertices in each component
forces the actual ordinary-edge graph to be connected. -/
theorem ordinary_connected_of_card (o : Ω) (P : Finset ι)
    (he : L.identity ∉ P) (hcard : Fintype.card Ω - 1 < 2 * P.card) :
    ∀ x y, Relation.EqvGen
      (PuncturedBothEndpoints.OrdinaryEdge o L.perm (P : Set ι)) x y := by
  intro x y
  by_contra hxy
  have hdis : Disjoint ((L.neighbors P x.1).erase o) ((L.neighbors P y.1).erase o) := by
    apply disjoint_left.mpr
    intro z hzx hzy
    have hzo : z ≠ o := (mem_erase.mp hzx).1
    let z' : {z : Ω // z ≠ o} := ⟨z, hzo⟩
    apply hxy
    exact Relation.EqvGen.trans _ _ _
      (L.ordinary_connected_of_neighbor o P x z' (mem_erase.mp hzx).2)
      (Relation.EqvGen.symm _ _
        (L.ordinary_connected_of_neighbor o P y z' (mem_erase.mp hzy).2))
  have hsub : (L.neighbors P x.1).erase o ∪ (L.neighbors P y.1).erase o ⊆
      (univ.erase o : Finset Ω) := by
    intro z hz
    rcases mem_union.mp hz with hz | hz <;>
      exact mem_erase.mpr ⟨(mem_erase.mp hz).1, mem_univ _⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_erase_of_mem (mem_univ _), card_univ] at hc
  have hx := L.punctured_neighbors_card o P he x
  have hy := L.punctured_neighbors_card o P he y
  omega

end Sunlet.NormalizedLatinSystem

end Source_LatinOrdinaryConnectivity

section Source_LatinLargeSupports


/-! Contact supports in every Latin order seven or at least nine. The small
transitive family is proved by orbit halving; every deletion of its large
complement is transitive by the Latin cardinality bound. -/

open Finset

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

structure ContactSupports (o : Ω) (A B : Finset ι) : Prop where
  identity_first : L.identity ∉ A
  identity_second : L.identity ∉ B
  disjoint : Disjoint A B
  first_two : 2 ≤ A.card
  second_three : 3 ≤ B.card
  first_transitive : TransitiveFamily L.perm (A : Set ι)
  second_transitive : TransitiveFamily L.perm (B : Set ι)
  deletion_transitive : ∀ b ∈ B, TransitiveFamily L.perm ((B.erase b : Finset ι) : Set ι)
  ordinary_connected : ∀ x y, Relation.EqvGen
    (PuncturedBothEndpoints.OrdinaryEdge o L.perm (B : Set ι)) x y

theorem supports_of_small_transitive (o : Ω) (A : Finset ι)
    (he : L.identity ∉ A) (htwo : 2 ≤ A.card)
    (hsmall : 2 * A.card + 2 < Fintype.card Ω)
    (htr : TransitiveFamily L.perm (A : Set ι)) :
    L.ContactSupports o A ((univ.erase L.identity) \ A) := by
  classical
  let B := (univ.erase L.identity) \ A
  change L.ContactSupports o A B
  have hsub : A ⊆ univ.erase L.identity := by
    intro a ha
    exact mem_erase.mpr ⟨fun h => he (h ▸ ha), mem_univ _⟩
  have hBcard : B.card = Fintype.card Ω - 1 - A.card := by
    dsimp [B]
    rw [card_sdiff_of_subset hsub, card_erase_of_mem (mem_univ _), card_univ, L.card_eq o]
  have hBe : L.identity ∉ B := fun h => (mem_erase.mp (mem_sdiff.mp h).1).1 rfl
  have hBlarge : Fintype.card Ω < 2 * B.card := by omega
  refine ⟨he, hBe, ?_, htwo, by omega, htr, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr (fun a ha hb => (mem_sdiff.mp hb).2 ha)
  · exact L.transitive_of_card B hBe (by omega)
  · intro b hb
    apply L.transitive_of_card (B.erase b) (fun h => hBe (mem_erase.mp h).2)
    rw [card_erase_of_mem hb]
    omega
  · exact L.ordinary_connected_of_card o B hBe (by omega)

theorem exists_contact_supports_of_bound (o : Ω) (n : ℕ)
    (hn : 2 ≤ n) (hsize : 2 * n + 2 < Fintype.card Ω)
    (hpower : Fintype.card Ω < 2 ^ (n + 1)) :
    ∃ A B : Finset ι, L.ContactSupports o A B := by
  obtain ⟨P, he, hcard, htr⟩ := L.exists_small_transitive_family o n hpower
  have hsub : P ⊆ (univ.erase L.identity : Finset ι) := by
    intro a ha
    exact mem_erase.mpr ⟨fun h => he (h ▸ ha), mem_univ _⟩
  have htotal : (univ.erase L.identity : Finset ι).card = Fintype.card Ω - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, L.card_eq o]
  obtain ⟨A, hPA, hA, hAn⟩ := exists_subsuperset_card_eq hsub hcard
    (show n ≤ (univ.erase L.identity : Finset ι).card by omega)
  have heA : L.identity ∉ A := fun h => (mem_erase.mp (hA h)).1 rfl
  refine ⟨A, (univ.erase L.identity) \ A, L.supports_of_small_transitive o A heA ?_ ?_ ?_⟩
  · omega
  · omega
  · exact fun x y => colorConnected_mono (fun a ha => hPA ha) (htr x y)

private theorem linear_bound_lt_power (n : ℕ) (hn : 3 ≤ n) :
    2 * n + 4 < 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
    omega

/-- The entire nonexceptional range in the paper's support argument. -/
theorem exists_contact_supports_large (o : Ω)
    (hm : Fintype.card Ω = 7 ∨ 9 ≤ Fintype.card Ω) :
    ∃ A B : Finset ι, L.ContactSupports o A B := by
  rcases hm with hm | hm
  · exact L.exists_contact_supports_of_bound o 2 (by omega) (by omega) (by norm_num [hm])
  · let n := (Fintype.card Ω - 3) / 2
    have hn : 3 ≤ n := by dsimp [n]; omega
    apply L.exists_contact_supports_of_bound o n (by omega)
    · dsimp [n]
      omega
    · have hh := linear_bound_lt_power n hn
      have hle : Fintype.card Ω ≤ 2 * n + 4 := by dsimp [n]; omega
      omega

end Sunlet.NormalizedLatinSystem

end Source_LatinLargeSupports

section Source_LatinSixPairs


/-! In order six, every nontransitive pair consists of two inverse
three-cycle permutations. Consequently the bad pairs form a matching. -/

open Finset

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

theorem orbit_pair_card_three (hm : Fintype.card Ω = 6)
    (a b : ι) (hae : a ≠ L.identity) (hbe : b ≠ L.identity) (hab : a ≠ b)
    (hnot : ¬TransitiveFamily L.perm ({a, b} : Finset ι)) (x : Ω) :
    (L.orbit {a, b} x).card = 3 := by
  classical
  let P : Finset ι := {a, b}
  have he : L.identity ∉ P := by simp [P, Ne.symm hae, Ne.symm hbe]
  have hP : P.card = 2 := by simp [P, hab]
  have hex : ∃ y, ¬ColorConnected L.perm (P : Set ι) x y := by
    by_contra hn
    push_neg at hn
    apply hnot
    intro y z
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hn y)) (hn z)
  obtain ⟨y, hy⟩ := hex
  let S := L.orbit P x
  let T := univ \ S
  have hyT : y ∈ T := by simpa [T, S] using hy
  have hTstable : ∀ c ∈ P, ∀ z ∈ T, L.perm c z ∈ T := by
    intro c hc z hz
    have hzS : z ∉ S := (mem_sdiff.mp hz).2
    simp only [T, mem_sdiff, mem_univ, true_and]
    exact fun h => hzS ((L.perm_mem_orbit_iff hc x z).mp h)
  have hScard : 3 ≤ S.card := by
    have hh := L.orbit_card_lower P he x
    dsimp [S]
    omega
  have hTcard : 3 ≤ T.card := by
    have hh := card_le_card (L.neighbors_subset hTstable hyT)
    rw [L.card_neighbors P he y, hP] at hh
    exact hh
  have htotal : T.card + S.card = 6 := by
    have hh := card_sdiff_add_card_eq_card (subset_univ S)
    simpa only [card_univ, hm] using hh
  change S.card = 3
  omega

/-- A bad pair has a uniquely determined second permutation. This proof
uses the actual three-element orbits, without a cycle-type axiom. -/
theorem bad_pair_square (hm : Fintype.card Ω = 6)
    (a b : ι) (hae : a ≠ L.identity) (hbe : b ≠ L.identity) (hab : a ≠ b)
    (hnot : ¬TransitiveFamily L.perm ({a, b} : Finset ι)) :
    ∀ x, L.perm b x = L.perm a (L.perm a x) := by
  intro x
  let P : Finset ι := {a, b}
  have he : L.identity ∉ P := by simp [P, Ne.symm hae, Ne.symm hbe]
  have hP : P.card = 2 := by simp [P, hab]
  have hsize := L.orbit_pair_card_three hm a b hae hbe hab hnot x
  have hneigh : L.neighbors P x = L.orbit P x :=
    eq_of_subset_of_card_le (L.neighbors_subset_orbit P x)
      (by rw [L.card_neighbors P he x, hP]; exact hsize.le)
  have hxya : L.perm a x ≠ x := L.derangement a hae x
  have hxyz : L.perm b x ≠ x := L.derangement b hbe x
  have hyz : L.perm a x ≠ L.perm b x := fun h => hab ((L.column_bijective x).injective h)
  have hmem (z : Ω) (hz : z ∈ L.orbit P x) :
      z = x ∨ z = L.perm a x ∨ z = L.perm b x := by
    rw [← hneigh] at hz
    simpa [neighbors, P, eq_comm] using hz
  have hbx : L.perm b x ∈ L.orbit P x :=
    (L.perm_mem_orbit_iff (show b ∈ P by simp [P]) x x).mpr (L.self_mem_orbit P x)
  have hax : L.perm a x ∈ L.orbit P x :=
    (L.perm_mem_orbit_iff (show a ∈ P by simp [P]) x x).mpr (L.self_mem_orbit P x)
  have habx : L.perm a (L.perm b x) = x := by
    have hh := hmem _ ((L.perm_mem_orbit_iff (show a ∈ P by simp [P]) x _).mpr hbx)
    rcases hh with hh | hh | hh
    · exact hh
    · exact False.elim (hxyz ((L.perm a).injective hh))
    · exact False.elim (L.derangement a hae _ hh)
  have haax := hmem _ ((L.perm_mem_orbit_iff (show a ∈ P by simp [P]) x _).mpr hax)
  rcases haax with hh | hh | hh
  · exact False.elim (hyz ((L.perm a).injective (hh.trans habx.symm)))
  · exact False.elim (L.derangement a hae _ hh)
  · exact hh.symm

theorem bad_pair_unique (o : Ω) (hm : Fintype.card Ω = 6)
    (a b c : ι) (hae : a ≠ L.identity) (hbe : b ≠ L.identity) (hce : c ≠ L.identity)
    (hab : a ≠ b) (hac : a ≠ c)
    (hbadb : ¬TransitiveFamily L.perm ({a, b} : Finset ι))
    (hbadc : ¬TransitiveFamily L.perm ({a, c} : Finset ι)) : b = c := by
  apply (L.column_bijective o).injective
  change L.perm b o = L.perm c o
  rw [L.bad_pair_square hm a b hae hbe hab hbadb,
    L.bad_pair_square hm a c hae hce hac hbadc]

end Sunlet.NormalizedLatinSystem

end Source_LatinSixPairs

section Source_MatchingFive


/-! A matching on five vertices can be separated by a two--three partition.
This is the finite combinatorial input for order-six contact supports. -/

open Finset

namespace Sunlet

theorem matching_five_partition {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (hC : C.card = 5) (R : ι → ι → Prop)
    (hirr : ∀ a, ¬R a a) (hsym : ∀ a b, R a b → R b a)
    (hunique : ∀ a b c, R a b → R a c → b = c) :
    ∃ A : Finset ι, A ⊆ C ∧ A.card = 2 ∧
      (∀ a ∈ A, ∀ b ∈ A, ¬R a b) ∧
      (∀ a ∈ C \ A, ∀ b ∈ C \ A, ¬R a b) := by
  classical
  by_cases hex : ∃ a ∈ C, ∃ b ∈ C, R a b
  · obtain ⟨a, haC, b, hbC, habR⟩ := hex
    have hab : a ≠ b := fun h => hirr b (h ▸ habR)
    let D := C \ {a, b}
    have hDC : D ⊆ C := sdiff_subset
    have hDcard : D.card = 3 := by
      dsimp [D]
      rw [card_sdiff_of_subset (show ({a, b} : Finset ι) ⊆ C by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haC
        · exact hbC), card_pair hab, hC]
    have haD : a ∉ D := by simp [D]
    have hbD : b ∉ D := by simp [D]
    have construct (c : ι) (hcD : c ∈ D)
        (hrest : ∀ x ∈ D \ {c}, ∀ y ∈ D \ {c}, ¬R x y) :
        ∃ A : Finset ι, A ⊆ C ∧ A.card = 2 ∧
          (∀ a ∈ A, ∀ b ∈ A, ¬R a b) ∧
          (∀ a ∈ C \ A, ∀ b ∈ C \ A, ¬R a b) := by
      have hca : c ≠ a := fun h => haD (h ▸ hcD)
      have hcb : c ≠ b := fun h => hbD (h ▸ hcD)
      have hacR : ¬R a c := fun h => hcb (hunique a c b h habR)
      refine ⟨{a, c}, ?_, card_pair (Ne.symm hca), ?_, ?_⟩
      · intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haC
        · exact hDC hcD
      · intro x hx y hy hxy
        simp only [mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact hirr _ hxy
        · exact hacR hxy
        · exact hacR (hsym _ _ hxy)
        · exact hirr _ hxy
      · intro x hx y hy hxy
        have hxC := (mem_sdiff.mp hx).1
        have hyC := (mem_sdiff.mp hy).1
        have hxa : x ≠ a := fun h => (mem_sdiff.mp hx).2 (by simp [h])
        have hxc : x ≠ c := fun h => (mem_sdiff.mp hx).2 (by simp [h])
        have hya : y ≠ a := fun h => (mem_sdiff.mp hy).2 (by simp [h])
        have hyc : y ≠ c := fun h => (mem_sdiff.mp hy).2 (by simp [h])
        have hxb : x ≠ b := by
          intro he
          subst x
          exact hya (hunique b y a hxy (hsym a b habR))
        have hyb : y ≠ b := by
          intro he
          subst y
          exact hxa (hunique b x a (hsym x b hxy) (hsym a b habR))
        exact hrest x (by simp [D, hxC, hxa, hxb, hxc])
          y (by simp [D, hyC, hya, hyb, hyc]) hxy
    by_cases hDedge : ∃ c ∈ D, ∃ d ∈ D, R c d
    · obtain ⟨c, hcD, d, hdD, hcdR⟩ := hDedge
      have hcd : c ≠ d := fun h => hirr d (h ▸ hcdR)
      apply construct c hcD
      intro x hx y hy hxy
      have hxD := (mem_sdiff.mp hx).1
      have hyD := (mem_sdiff.mp hy).1
      have hxc : x ≠ c := by simpa using (mem_sdiff.mp hx).2
      have hyc : y ≠ c := by simpa using (mem_sdiff.mp hy).2
      have hxd : x ≠ d := by
        intro he
        subst x
        exact hyc (hunique d y c hxy (hsym c d hcdR))
      have hyd : y ≠ d := by
        intro he
        subst y
        exact hxc (hunique d x c (hsym x d hxy) (hsym c d hcdR))
      have hsize : (D \ {c, d}).card = 1 := by
        rw [card_sdiff_of_subset (show ({c, d} : Finset ι) ⊆ D by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hcD
          · exact hdD), card_pair hcd, hDcard]
      have hxy' : x = y := (card_le_one.mp (show (D \ {c, d}).card ≤ 1 by omega))
        x (by simp [hxD, hxc, hxd]) y (by simp [hyD, hyc, hyd])
      exact hirr y (hxy' ▸ hxy)
    · obtain ⟨c, hcD⟩ := card_pos.mp (show 0 < D.card by omega)
      apply construct c hcD
      intro x hx y hy hxy
      exact hDedge ⟨x, (mem_sdiff.mp hx).1, y, (mem_sdiff.mp hy).1, hxy⟩
  · obtain ⟨A, hAC, hA⟩ := exists_subset_card_eq (show 2 ≤ C.card by omega)
    refine ⟨A, hAC, hA, ?_, ?_⟩
    · intro a ha b hb h
      exact hex ⟨a, hAC ha, b, hAC hb, h⟩
    · intro a ha b hb h
      exact hex ⟨a, (mem_sdiff.mp ha).1, b, (mem_sdiff.mp hb).1, h⟩

end Sunlet

end Source_MatchingFive

section Source_LatinSixSupports


/-! The complete support construction in order six. -/

open Finset

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

theorem exists_contact_supports_six (o : Ω) (hm : Fintype.card Ω = 6) :
    ∃ A B : Finset ι, L.ContactSupports o A B := by
  classical
  let C : Finset ι := univ.erase L.identity
  have hCcard : C.card = 5 := by
    dsimp [C]
    rw [card_erase_of_mem (mem_univ _), card_univ, L.card_eq o, hm]
  let R : ι → ι → Prop := fun a b => a ∈ C ∧ b ∈ C ∧ a ≠ b ∧
    ¬TransitiveFamily L.perm ({a, b} : Finset ι)
  have hirr : ∀ a, ¬R a a := fun a h => h.2.2.1 rfl
  have hsym : ∀ a b, R a b → R b a := by
    intro a b h
    refine ⟨h.2.1, h.1, Ne.symm h.2.2.1, ?_⟩
    simpa only [pair_comm] using h.2.2.2
  have huniq : ∀ a b c, R a b → R a c → b = c := by
    intro a b c hb hc
    exact L.bad_pair_unique o hm a b c (mem_erase.mp hb.1).1
      (mem_erase.mp hb.2.1).1 (mem_erase.mp hc.2.1).1
      hb.2.2.1 hc.2.2.1 hb.2.2.2 hc.2.2.2
  obtain ⟨A, hAC, hAcard, hAgood, hBgood⟩ := matching_five_partition C hCcard R hirr hsym huniq
  let B := C \ A
  have hBC : B ⊆ C := sdiff_subset
  have hBcard : B.card = 3 := by dsimp [B]; rw [card_sdiff_of_subset hAC, hCcard, hAcard]
  have heA : L.identity ∉ A := fun h => (mem_erase.mp (hAC h)).1 rfl
  have heB : L.identity ∉ B := fun h => (mem_erase.mp (hBC h)).1 rfl
  have hpair (P : Finset ι) (hPC : P ⊆ C) (hcard : P.card = 2)
      (hgood : ∀ a ∈ P, ∀ b ∈ P, ¬R a b) : TransitiveFamily L.perm (P : Set ι) := by
    obtain ⟨a, b, hab, hP⟩ := card_eq_two.mp hcard
    subst P
    by_contra ht
    exact hgood a (by simp) b (by simp) ⟨hPC (by simp), hPC (by simp), hab, ht⟩
  refine ⟨A, B, heA, heB, ?_, by omega, by omega,
    hpair A hAC hAcard hAgood, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr (fun a ha hb => (mem_sdiff.mp hb).2 ha)
  · exact L.transitive_of_card B heB (by omega)
  · intro b hb
    apply hpair (B.erase b) (fun a ha => hBC (mem_erase.mp ha).2)
    · rw [card_erase_of_mem hb, hBcard]
    · intro a ha c hc
      exact hBgood a (mem_erase.mp ha).2 c (mem_erase.mp hc).2
  · exact L.ordinary_connected_of_card o B heB (by omega)

end Sunlet.NormalizedLatinSystem

end Source_LatinSixSupports

section Source_LatinEightInvolutions


/-! The exceptional order-eight reduction begins without any enumeration
of cycle types. Orbit halving forces every nonidentity color to be an
involution whenever no two colors are transitive. -/

open Finset
open scoped BigOperators

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

def NoTransitivePair : Prop :=
  ∀ a b, a ≠ L.identity → b ≠ L.identity → a ≠ b →
    ¬TransitiveFamily L.perm ({a, b} : Finset ι)

theorem singleton_not_transitive_of_no_pair (o : Ω)
    (hm : 3 ≤ Fintype.card Ω) (hno : L.NoTransitivePair)
    (a : ι) (ha : a ≠ L.identity) :
    ¬TransitiveFamily L.perm ({a} : Finset ι) := by
  intro ht
  have hcard : 0 < (univ \ {a, L.identity} : Finset ι).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_pair ha, card_univ, L.card_eq o]
    omega
  obtain ⟨b, hb⟩ := card_pos.mp hcard
  have hba : b ≠ a := by
    intro he
    exact (mem_sdiff.mp hb).2 (by simp [he])
  have hbe : b ≠ L.identity := by
    intro he
    exact (mem_sdiff.mp hb).2 (by simp [he])
  apply hno a b ha hbe (Ne.symm hba)
  intro x y
  exact colorConnected_mono (by
    intro c hc
    exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hc))) (ht x y)

theorem singleton_orbit_count_ge_four (o : Ω)
    (hm : Fintype.card Ω = 8) (hno : L.NoTransitivePair)
    (a : ι) (ha : a ≠ L.identity) :
    4 ≤ Fintype.card (L.OrbitClasses {a}) := by
  obtain ⟨b, hbe, hba, hh⟩ := L.exists_halving_color o {a}
    (L.singleton_not_transitive_of_no_pair o (by omega) hno a ha)
  have hne : b ≠ a := by simpa using hba
  have hnot : ¬TransitiveFamily L.perm (insert b {a} : Finset ι) := by
    simpa only [pair_comm] using hno a b ha hbe (Ne.symm hne)
  have hpos : 0 < Fintype.card (L.OrbitClasses (insert b {a})) :=
    Fintype.card_pos_iff.mpr ⟨L.orbitClass _ o⟩
  have hone : Fintype.card (L.OrbitClasses (insert b {a})) ≠ 1 :=
    fun h => hnot ((L.transitive_iff_orbit_card_one o _).mpr h)
  omega

theorem singleton_fiber_card_two (o : Ω)
    (hm : Fintype.card Ω = 8) (hno : L.NoTransitivePair)
    (a : ι) (ha : a ≠ L.identity) (q : L.OrbitClasses {a}) :
    Fintype.card {x : Ω // L.orbitClass {a} x = q} = 2 := by
  classical
  let f := L.orbitClass {a}
  have hsize : ∀ q, 2 ≤ Fintype.card {x : Ω // f x = q} := by
    intro q
    obtain ⟨x, hx⟩ := L.orbitClass_surjective {a} q
    have hy : f (L.perm a x) = q := (L.orbitClass_step (by simp) x).trans hx
    apply (show 1 < Fintype.card {x : Ω // f x = q} → 2 ≤ _ by omega)
    apply Fintype.one_lt_card_iff.mpr
    exact ⟨⟨L.perm a x, hy⟩, ⟨x, hx⟩, fun h => L.derangement a ha x (congrArg Subtype.val h)⟩
  have hsum : (∑ q, Fintype.card {x : Ω // f x = q}) = 8 := by
    have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    simpa only [Fintype.card_sigma, hm] using hh
  have hcount := L.singleton_orbit_count_ge_four o hm hno a ha
  have hbound := Finset.sum_le_sum (fun q (_ : q ∈ (univ : Finset (L.OrbitClasses {a}))) => hsize q)
  have hcountEq : Fintype.card (L.OrbitClasses {a}) = 4 := by
    simp only [sum_const, card_univ, smul_eq_mul, hsum] at hbound
    omega
  have heq : (∑ _q : L.OrbitClasses {a}, 2) =
      ∑ q, Fintype.card {x : Ω // f x = q} := by simp [hcountEq, hsum]
  exact ((Finset.sum_eq_sum_iff_of_le (fun q (_ : q ∈ (univ : Finset (L.OrbitClasses {a}))) =>
    hsize q)).mp heq q (mem_univ _)).symm

/-- With no transitive pair in order eight, every row squares to the
identity. In particular the exceptional case really is an exponent-two
permutation system, rather than merely sharing its cycle counts. -/
theorem involutions_of_no_pair (o : Ω)
    (hm : Fintype.card Ω = 8) (hno : L.NoTransitivePair) :
    ∀ a x, L.perm a (L.perm a x) = x := by
  classical
  intro a x
  by_cases ha : a = L.identity
  · subst a
    simp [L.normalized]
  · by_contra hxx
    let q := L.orbitClass {a} x
    let V := {y : Ω // L.orbitClass {a} y = q}
    let x₀ : V := ⟨x, rfl⟩
    let x₁ : V := ⟨L.perm a x, L.orbitClass_step (by simp) x⟩
    let x₂ : V := ⟨L.perm a (L.perm a x),
      (L.orbitClass_step (by simp) (L.perm a x)).trans (L.orbitClass_step (by simp) x)⟩
    have h01 : x₀ ≠ x₁ := fun h => L.derangement a ha x (congrArg Subtype.val h).symm
    have h02 : x₀ ≠ x₂ := fun h => hxx (congrArg Subtype.val h).symm
    have h12 : x₁ ≠ x₂ := fun h => L.derangement a ha (L.perm a x) (congrArg Subtype.val h).symm
    have hc : ({x₀, x₁, x₂} : Finset V).card = 3 := by simp [h01, h02, h12]
    have hh := card_le_card (subset_univ ({x₀, x₁, x₂} : Finset V))
    rw [hc, card_univ, L.singleton_fiber_card_two o hm hno a ha q] at hh
    omega

end Sunlet.NormalizedLatinSystem

end Source_LatinEightInvolutions

section Source_LatinEightCommuting


/-! The no-transitive-pair order-eight system consists of commuting
involutions. The proof uses explicit four-point orbit neighborhoods. -/

open Finset

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

def fourNeighbors (a b : ι) (x : Ω) : Finset Ω :=
  {x, L.perm a x, L.perm b x, L.perm a (L.perm b x)}

theorem fourNeighbors_card (hInv : ∀ a x, L.perm a (L.perm a x) = x)
    (a b : ι) (ha : a ≠ L.identity) (hb : b ≠ L.identity) (hab : a ≠ b) (x : Ω) :
    (L.fourNeighbors a b x).card = 4 := by
  have hax : L.perm a x ≠ x := L.derangement a ha x
  have hbx : L.perm b x ≠ x := L.derangement b hb x
  have habx : L.perm a x ≠ L.perm b x := fun h => hab ((L.column_bijective x).injective h)
  have hfourx : L.perm a (L.perm b x) ≠ x := by
    intro h
    have hh := congrArg (L.perm a) h
    rw [hInv] at hh
    exact habx hh.symm
  have hfoura : L.perm a (L.perm b x) ≠ L.perm a x :=
    fun h => hbx ((L.perm a).injective h)
  have hfourb : L.perm a (L.perm b x) ≠ L.perm b x := L.derangement a ha _
  simp [fourNeighbors, Ne.symm hax, Ne.symm hbx, Ne.symm hfourx,
    habx, Ne.symm hfoura, Ne.symm hfourb]

theorem fourNeighbors_subset_orbit (a b : ι) (x : Ω) :
    L.fourNeighbors a b x ⊆ L.orbit {a, b} x := by
  have ha : a ∈ ({a, b} : Finset ι) := by simp
  have hb : b ∈ ({a, b} : Finset ι) := by simp
  have hx := L.self_mem_orbit ({a, b} : Finset ι) x
  have hax := (L.perm_mem_orbit_iff ha x x).mpr hx
  have hbx := (L.perm_mem_orbit_iff hb x x).mpr hx
  have habx := (L.perm_mem_orbit_iff ha x _).mpr hbx
  simpa only [fourNeighbors, insert_subset_iff, singleton_subset_iff] using
    And.intro hx (And.intro hax (And.intro hbx habx))

theorem pair_orbit_card_four (o : Ω) (hm : Fintype.card Ω = 8)
    (hno : L.NoTransitivePair) (a b : ι)
    (ha : a ≠ L.identity) (hb : b ≠ L.identity) (hab : a ≠ b) (x : Ω) :
    (L.orbit {a, b} x).card = 4 := by
  classical
  have hInv := L.involutions_of_no_pair o hm hno
  let P : Finset ι := {a, b}
  have hyex : ∃ y, ¬ColorConnected L.perm (P : Set ι) x y := by
    by_contra hn
    push_neg at hn
    apply hno a b ha hb hab
    intro y z
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hn y)) (hn z)
  obtain ⟨y, hy⟩ := hyex
  let S := L.orbit P x
  let T := univ \ S
  have hS : 4 ≤ S.card := by
    have hh := card_le_card (L.fourNeighbors_subset_orbit a b x)
    rw [L.fourNeighbors_card hInv a b ha hb hab x] at hh
    exact hh
  have hsub : L.fourNeighbors a b y ⊆ T := by
    intro z hz
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hzS
    apply hy
    exact Relation.EqvGen.trans _ _ _ ((L.mem_orbit P x z).mp hzS)
      (Relation.EqvGen.symm _ _ ((L.mem_orbit P y z).mp
        (L.fourNeighbors_subset_orbit a b y hz)))
  have hT : 4 ≤ T.card := by
    have hh := card_le_card hsub
    rw [L.fourNeighbors_card hInv a b ha hb hab y] at hh
    exact hh
  have htotal : T.card + S.card = 8 := by
    have hh := card_sdiff_add_card_eq_card (subset_univ S)
    simpa only [card_univ, hm] using hh
  change S.card = 4
  omega

/-- All translations commute in the only remaining order-eight case. -/
theorem commuting_of_no_pair (o : Ω) (hm : Fintype.card Ω = 8)
    (hno : L.NoTransitivePair) :
    ∀ a b x, L.perm a (L.perm b x) = L.perm b (L.perm a x) := by
  intro a b x
  by_cases ha : a = L.identity
  · subst a; simp [L.normalized]
  by_cases hb : b = L.identity
  · subst b; simp [L.normalized]
  by_cases hab : a = b
  · subst b; rfl
  have hInv := L.involutions_of_no_pair o hm hno
  have hsize := L.pair_orbit_card_four o hm hno a b ha hb hab x
  have hEq : L.fourNeighbors a b x = L.orbit {a, b} x :=
    eq_of_subset_of_card_le (L.fourNeighbors_subset_orbit a b x)
      (by rw [L.fourNeighbors_card hInv a b ha hb hab x]; exact hsize.le)
  have haP : a ∈ ({a, b} : Finset ι) := by simp
  have hbP : b ∈ ({a, b} : Finset ι) := by simp
  have hmem : L.perm b (L.perm a x) ∈ L.fourNeighbors a b x := by
    rw [hEq]
    exact (L.perm_mem_orbit_iff hbP x _).mpr
      ((L.perm_mem_orbit_iff haP x _).mpr (L.self_mem_orbit _ x))
  simp only [fourNeighbors, mem_insert, mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hh := congrArg (L.perm b) h
    rw [hInv] at hh
    exact False.elim (hab ((L.column_bijective x).injective hh))
  · exact False.elim (L.derangement b hb _ h)
  · exact False.elim (L.derangement a ha x ((L.perm b).injective h))
  · exact h.symm

end Sunlet.NormalizedLatinSystem

namespace Sunlet.LoopData

variable {Ω : Type*} (L : LoopData Ω)

/-- Commuting left translations force loop commutativity. -/
theorem commutative_of_commuting_translations
    (h : ∀ x y z, L.left x (L.left y z) = L.left y (L.left x z)) :
    ∀ x y, L.mul x y = L.mul y x := by
  intro x y
  simpa only [L.right_identity, mul] using h x y L.identity

/-- Their action is regular, so commuting translations also force
associativity. This reconstructs the group law, rather than assuming it. -/
theorem associative_of_commuting_translations
    (h : ∀ x y z, L.left x (L.left y z) = L.left y (L.left x z)) : L.IsAssociative := by
  have hc := L.commutative_of_commuting_translations h
  intro x y z
  calc
    L.mul (L.mul x y) z = L.mul z (L.mul x y) := hc _ _
    _ = L.mul x (L.mul z y) := h z x y
    _ = L.mul x (L.mul y z) := by rw [hc z y]

end Sunlet.LoopData

end Source_LatinEightCommuting

section Source_LatinEightGroup


/-! The exceptional order-eight loop is explicitly identified with a
three-dimensional vector space over the field with two elements. -/


namespace Sunlet.LoopData

variable {Ω : Type*} (L : LoopData Ω)

def exponentTwoAddCommGroup
    (hcomm : ∀ x y, L.mul x y = L.mul y x) (hassoc : L.IsAssociative)
    (hsquare : ∀ x, L.mul x x = L.identity) : AddCommGroup Ω := by
  letI : Add Ω := ⟨L.mul⟩
  letI : Zero Ω := ⟨L.identity⟩
  letI : Neg Ω := ⟨_root_.id⟩
  exact { AddGroup.ofLeftAxioms hassoc L.identity_mul hsquare with add_comm := hcomm }

/-- A commutative associative exponent-two loop of order eight has an
actual addition-preserving coordinate equivalence with `(ZMod 2)^3`. -/
theorem cube_equiv [Fintype Ω]
    (hcard : Fintype.card Ω = 8)
    (hcomm : ∀ x y, L.mul x y = L.mul y x) (hassoc : L.IsAssociative)
    (hsquare : ∀ x, L.mul x x = L.identity) :
    ∃ e : Ω ≃ (Fin 3 → ZMod 2), e L.identity = 0 ∧
      ∀ x y, e (L.mul x y) = e x + e y := by
  letI := L.exponentTwoAddCommGroup hcomm hassoc hsquare
  letI : Module (ZMod 2) Ω := AddCommGroup.zmodModule (n := 2) (by
    intro x
    rw [two_nsmul]
    exact hsquare x)
  have hdim : Module.finrank (ZMod 2) Ω = 3 := by
    apply Nat.pow_right_injective (show 2 ≤ 2 by decide)
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Ω)
    simpa [hcard, ZMod.card] using h.symm
  let b := Module.finBasisOfFinrankEq (R := ZMod 2) (M := Ω) hdim
  refine ⟨b.equivFun.toEquiv, ?_, ?_⟩
  · exact b.equivFun.map_zero
  · exact b.equivFun.map_add

end Sunlet.LoopData

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

/-- The no-transitive-pair case is a full coordinate identification with
the elementary abelian group, including the loop product. -/
theorem cube_equiv_of_no_pair (o : Ω) (hm : Fintype.card Ω = 8)
    (hno : L.NoTransitivePair) :
    ∃ e : Ω ≃ (Fin 3 → ZMod 2), e o = 0 ∧
      ∀ x y, e ((L.loopAt o).mul x y) = e x + e y := by
  let M := L.loopAt o
  have hc : ∀ x y z, M.left x (M.left y z) = M.left y (M.left x z) := by
    intro x y z
    exact L.commuting_of_no_pair o hm hno _ _ z
  have hs : ∀ x, M.mul x x = M.identity := by
    intro x
    have h := L.involutions_of_no_pair o hm hno
    change M.left x x = o
    calc
      M.left x x = M.left x (M.left x o) := congrArg (M.left x) (M.right_identity x).symm
      _ = o := h _ o
  exact M.cube_equiv hm (M.commutative_of_commuting_translations hc)
    (M.associative_of_commuting_translations hc) hs

end Sunlet.NormalizedLatinSystem

end Source_LatinEightGroup

section Source_ToricPairAlgebra


/-! The actual Laurent parameter algebra of a pair of toric summands.
Coefficient variables remain affine. Only nonbase torus variables are
inverted; the sparse points therefore define honest specialization maps. -/

open scoped BigOperators

namespace Sunlet.ToricPairAlgebra

variable {ι Ω k : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field k] (o : Ω)

abbrev Index := Bool × NormalizedVariations.Index ι Ω o
abbrev PolynomialRing := MvPolynomial (Index (ι := ι) o) k
abbrev FunctionField := FractionRing (PolynomialRing (k := k) (ι := ι) o)

def denominator : PolynomialRing (k := k) (ι := ι) o :=
  ∏ j : Bool × {x : Ω // x ≠ o}, MvPolynomial.X (j.1, Sum.inr j.2)

abbrev LaurentRing := Localization.Away (denominator (k := k) (ι := ι) o)

def parameterVariable (j : Index (ι := ι) o) : LaurentRing (k := k) (ι := ι) o :=
  algebraMap (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o) (MvPolynomial.X j)

private theorem factor_isUnit_in_product_localization
    {R S J : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype J]
    (f : J → R) [IsLocalization.Away (∏ j, f j) S] (j : J) :
    IsUnit (algebraMap R S (f j)) := by
  exact IsLocalization.Away.isUnit_of_dvd (S := S) (∏ j, f j)
    (Finset.dvd_prod_of_mem f (Finset.mem_univ j))

theorem torus_variable_isUnit (b : Bool) (x : {x : Ω // x ≠ o}) :
    IsUnit (parameterVariable (k := k) (ι := ι) o (b, .inr x)) := by
  letI : IsLocalization.Away
      (∏ j : Bool × {x : Ω // x ≠ o},
        (MvPolynomial.X (j.1, Sum.inr j.2) : PolynomialRing (k := k) (ι := ι) o))
      (LaurentRing (k := k) (ι := ι) o) := by
    change IsLocalization.Away (denominator (k := k) (ι := ι) o)
      (LaurentRing (k := k) (ι := ι) o)
    infer_instance
  change IsUnit (algebraMap (PolynomialRing (k := k) (ι := ι) o)
    (LaurentRing (k := k) (ι := ι) o) (MvPolynomial.X (b, Sum.inr x)))
  exact factor_isUnit_in_product_localization
    (S := LaurentRing (k := k) (ι := ι) o)
    (fun j : Bool × {x : Ω // x ≠ o} =>
      (MvPolynomial.X (j.1, Sum.inr j.2) : PolynomialRing (k := k) (ι := ι) o)) (b, x)

def coefficient (b : Bool) (a : ι) : LaurentRing (k := k) (ι := ι) o := parameterVariable o (b, .inl a)

def torus (b : Bool) (x : Ω) : (LaurentRing (k := k) (ι := ι) o)ˣ :=
  if hx : x = o then 1 else (torus_variable_isUnit (k := k) (ι := ι) o b ⟨x, hx⟩).unit

@[simp] theorem torus_base (b : Bool) : torus (k := k) (ι := ι) o b o = 1 := by simp [torus]

@[simp] theorem torus_value (b : Bool) (x : Ω) (hx : x ≠ o) :
    (torus (k := k) (ι := ι) o b x : LaurentRing (k := k) (ι := ι) o) =
      parameterVariable o (b, .inr ⟨x, hx⟩) := by simp [torus, hx]

section Evaluation

variable {F : Type*} [Field F] [Algebra k F]

def variableValues (U : Bool → ι → F) (h : Bool → Ω → Fˣ) : Index (ι := ι) o → F
  | (b, .inl a) => U b a
  | (b, .inr x) => h b x

theorem evaluated_denominator_isUnit (U : Bool → ι → F) (h : Bool → Ω → Fˣ) :
    IsUnit (MvPolynomial.aeval (variableValues o U h) (denominator (k := k) o)) := by
  apply isUnit_iff_ne_zero.mpr
  simp only [denominator, map_prod, MvPolynomial.aeval_X, variableValues]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => Units.ne_zero _)

def evaluate (U : Bool → ι → F) (h : Bool → Ω → Fˣ) : LaurentRing (k := k) (ι := ι) o →ₐ[k] F :=
  IsLocalization.Away.liftAlgHom (denominator (k := k) o) (evaluated_denominator_isUnit o U h)

@[simp] theorem evaluate_variable (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (j : Index (ι := ι) o) :
    evaluate (k := k) o U h (parameterVariable o j) = variableValues o U h j := by
  simp [evaluate, parameterVariable, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem evaluate_coefficient (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (b : Bool) (a : ι) : evaluate (k := k) o U h (coefficient o b a) = U b a := by
  simp [coefficient, variableValues]

@[simp] theorem evaluate_torus (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hbase : ∀ b, h b o = 1) (b : Bool) (x : Ω) :
    evaluate (k := k) o U h (torus (k := k) (ι := ι) o b x).val = (h b x : F) := by
  by_cases hx : x = o
  · subst x
    simp [hbase]
  · simp [torus, hx, variableValues]

end Evaluation

section MapEvaluation

variable {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']

/-- Evaluation commutes with an arbitrary embedding of coefficient fields. -/
theorem evaluate_comp (φ : F →ₐ[k] F') (U : Bool → ι → F) (h : Bool → Ω → Fˣ) :
    evaluate (k := k) o (fun b a => φ (U b a))
      (fun b x => Units.map φ.toMonoidHom (h b x)) = φ.comp (evaluate o U h) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (denominator (k := k) (ι := ι) o))
  ext j
  change evaluate (k := k) o (fun b a => φ (U b a))
      (fun b x => Units.map φ.toMonoidHom (h b x)) (parameterVariable o j) =
    φ (evaluate o U h (parameterVariable o j))
  rw [evaluate_variable, evaluate_variable]
  rcases j with ⟨b, a | x⟩
  all_goals rfl

end MapEvaluation

def genericVariable (j : Index (ι := ι) o) : FunctionField (k := k) (ι := ι) o :=
  algebraMap (PolynomialRing (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o) (MvPolynomial.X j)

theorem genericVariable_ne_zero (j : Index (ι := ι) o) : genericVariable (k := k) o j ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := k) j
  apply IsFractionRing.injective (PolynomialRing (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o)
  simpa [genericVariable] using h

def genericCoefficient (b : Bool) (a : ι) : FunctionField (k := k) (ι := ι) o := genericVariable o (b, .inl a)

def genericTorus (b : Bool) (x : Ω) : (FunctionField (k := k) (ι := ι) o)ˣ :=
  if hx : x = o then 1 else Units.mk0 (genericVariable o (b, .inr ⟨x, hx⟩))
    (genericVariable_ne_zero o _)

@[simp] theorem genericTorus_base (b : Bool) : genericTorus (k := k) (ι := ι) o b o = 1 := by
  simp [genericTorus]

def generic : LaurentRing (k := k) (ι := ι) o →ₐ[k] FunctionField (k := k) (ι := ι) o :=
  evaluate o (genericCoefficient o) (genericTorus o)

@[simp] theorem generic_variable (j : Index (ι := ι) o) :
    generic (k := k) o (parameterVariable o j) = genericVariable o j := by
  rcases j with ⟨b, a | x⟩
  · simp [generic, variableValues, genericCoefficient]
  · simp [generic, variableValues, genericTorus, x.property]

theorem generic_algebraMap (f : PolynomialRing (k := k) (ι := ι) o) :
    generic o (algebraMap (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o) f) =
      algebraMap (PolynomialRing (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o) f := by
  have h : (generic (k := k) (ι := ι) o).comp
      (IsScalarTower.toAlgHom k (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o)) =
      IsScalarTower.toAlgHom k (PolynomialRing (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o) := by
    ext j
    exact generic_variable o j
  exact AlgHom.congr_fun h f

/-- The generic map is faithful, proved directly from the localization
universal property and injectivity of the polynomial fraction map. -/
theorem generic_injective : Function.Injective (generic (k := k) (ι := ι) o) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (denominator (k := k) (ι := ι) o)) (generic (k := k) (ι := ι) o).toRingHom).mpr
  intro f g
  constructor
  · exact congrArg (generic o)
  · intro h
    change generic o (algebraMap (PolynomialRing (k := k) (ι := ι) o)
        (LaurentRing (k := k) (ι := ι) o) f) =
      generic o (algebraMap (PolynomialRing (k := k) (ι := ι) o)
        (LaurentRing (k := k) (ι := ι) o) g) at h
    rw [generic_algebraMap, generic_algebraMap] at h
    exact congrArg (algebraMap (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o))
      (IsFractionRing.injective (PolynomialRing (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o) h)

end Sunlet.ToricPairAlgebra

end Source_ToricPairAlgebra

section Source_ContactCertificate


/-! Small exact matrix certificates for the finite contact exceptions.
The certificate proves equations between the actual tangent and Hessian
matrices. No rank or contact assertion is accepted without these equations. -/

open scoped BigOperators Matrix

namespace Sunlet.ContactCertificate

variable {K J W O T D : Type*} [Field K]
  [Fintype J] [Fintype O] [Fintype T] [Fintype D] [DecidableEq J]

def radialProjection (r : J → K) (p : J) : Matrix J J K :=
  fun i j => (if i = j then 1 else 0) - r i * (if j = p then 1 else 0)

theorem radialProjection_mulVec (r : J → K) (p : J) (v : J → K) (i : J) :
    (radialProjection r p *ᵥ v) i = v i - r i * v p := by
  classical
  simp only [Matrix.mulVec, dotProduct, radialProjection, sub_mul, Finset.sum_sub_distrib]
  simp [mul_assoc, ← Finset.mul_sum]

structure Certificate (tangent : Matrix O T K) (hessian : W → Matrix O J K)
    (radial : J → K) (pivot : J) where
  tests : D → W
  annihilator : Matrix D O K
  combination : Matrix J D K
  annihilator_tangent : annihilator * tangent = 0
  projection_identity : combination *
      (show Matrix D J K from fun d j => ∑ o, annihilator d o * hessian (tests d) o j) =
    radialProjection radial pivot

/-- A checked annihilator and left inverse force every contact direction
to be radial. The hypothesis is membership in the actual tangent range. -/
theorem radial_of_certificate
    {tangent : Matrix O T K} {hessian : W → Matrix O J K}
    {radial : J → K} {pivot : J}
    (c : Certificate (D := D) tangent hessian radial pivot)
    (v : J → K)
    (hcontact : ∀ w, ∃ z : T → K, tangent *ᵥ z = hessian w *ᵥ v) :
    v = v pivot • radial := by
  let C : Matrix D J K := fun d j => ∑ o, c.annihilator d o * hessian (c.tests d) o j
  have hCv : C *ᵥ v = 0 := by
    funext d
    obtain ⟨z, hz⟩ := hcontact (c.tests d)
    have he := congrArg (fun f : O → K => (c.annihilator *ᵥ f) d) hz
    have hleft : (c.annihilator *ᵥ (tangent *ᵥ z)) d = 0 := by
      rw [Matrix.mulVec_mulVec, c.annihilator_tangent]
      simp
    rw [hleft] at he
    have hrow : (C *ᵥ v) d = (c.annihilator *ᵥ (hessian (c.tests d) *ᵥ v)) d := by
      simp only [Matrix.mulVec, dotProduct, C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    exact hrow.trans he.symm
  have hproj : radialProjection radial pivot *ᵥ v = 0 := by
    rw [← c.projection_identity]
    change (c.combination * C) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec, hCv]
    simp
  funext j
  have h := congrFun hproj j
  rw [radialProjection_mulVec] at h
  simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using sub_eq_zero.mp h

section Map

variable {E : Type*} [Field E] (f : K →+* E)

theorem map_radialProjection (r : J → K) (p : J) :
    (radialProjection r p).map f = radialProjection (fun j => f (r j)) p := by
  ext i j
  by_cases hij : i = j <;> by_cases hjp : j = p <;> simp [radialProjection, hij, hjp]

/-- Rational certificate identities remain valid over any characteristic-zero
field through the actual rational algebra map. -/
def Certificate.map
    {tangent : Matrix O T K} {hessian : W → Matrix O J K}
    {radial : J → K} {pivot : J}
    (c : Certificate (D := D) tangent hessian radial pivot) :
    Certificate (D := D) (tangent.map f) (fun w => (hessian w).map f)
      (fun j => f (radial j)) pivot where
  tests := c.tests
  annihilator := c.annihilator.map f
  combination := c.combination.map f
  annihilator_tangent := by
    rw [← Matrix.map_mul, c.annihilator_tangent]
    ext i j
    exact f.map_zero
  projection_identity := by
    have hmid : (show Matrix D J E from
        fun d j => ∑ o, f (c.annihilator d o) * f (hessian (c.tests d) o j)) =
        (show Matrix D J K from fun d j => ∑ o,
          c.annihilator d o * hessian (c.tests d) o j).map f := by
      ext d j
      change (∑ o, f (c.annihilator d o) * f (hessian (c.tests d) o j)) =
        f (∑ o, c.annihilator d o * hessian (c.tests d) o j)
      simp only [map_sum, map_mul]
    change c.combination.map f *
      (show Matrix D J E from
        fun d j => ∑ o, f (c.annihilator d o) * f (hessian (c.tests d) o j)) = _
    rw [hmid, ← Matrix.map_mul, c.projection_identity, map_radialProjection]

end Map
end Sunlet.ContactCertificate

end Source_ContactCertificate

section Source_SparseContactCertificate


/-! Exact finite certificates are connected to the literal sparse tangent
space and second differential. Thus a checked rational matrix certificate
proves the required contact assertion over every characteristic-zero field. -/

open scoped BigOperators Matrix

namespace Sunlet.SparseContactCertificate

open NormalizedVariations ToricDifferential

variable {ι Ω K : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field K] [CharZero K]

def hessianLinear (π : ι → Equiv.Perm Ω) (o : Ω) (A : Set ι)
    [DecidablePred (· ∈ A)] (w : Index ι Ω o → K) :
    (Index ι Ω o → K) →ₗ[K] (ι × Ω → K) where
  toFun v := hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o v) (asVariation o w)
  map_add' := by
    intro v u
    funext ab
    change hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o (v + u)) (asVariation o w) ab =
      hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o v) (asVariation o w) ab +
      hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o u) (asVariation o w) ab
    simp only [map_add, hessian, ratio, div_self one_ne_zero, one_mul]
    dsimp
    ring
  map_smul' := by
    intro r v
    funext ab
    change hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o (r • v)) (asVariation o w) ab =
      r * hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o v) (asVariation o w) ab
    simp only [map_smul, hessian, ratio, div_self one_ne_zero, one_mul]
    dsimp
    ring

def tangentMatrix (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    Matrix (ι × Ω) (Bool × Index ι Ω o) K := LinearMap.toMatrix' (sparsePair π o A B)

def hessianMatrix (π : ι → Equiv.Perm Ω) (o : Ω) (A : Set ι)
    [DecidablePred (· ∈ A)] (w : Index ι Ω o) :
    Matrix (ι × Ω) (Index ι Ω o) K :=
  LinearMap.toMatrix' (hessianLinear π o A (Pi.single w 1))

def radialVector (o : Ω) (A : Set ι) [DecidablePred (· ∈ A)] : Index ι Ω o → K :=
  Sum.elim (sparseCoefficients A) (fun _ => 0)

@[simp] theorem asVariation_radialVector (o : Ω) (A : Set ι) [DecidablePred (· ∈ A)] :
    asVariation o (radialVector (K := K) o A) = (sparseCoefficients A, (0 : Ω → K)) := by
  apply Prod.ext
  · rfl
  · funext x
    by_cases hx : x = o <;> simp [asVariation, radialVector, hx]

theorem tangentMatrix_mulVec (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (z : Bool × Index ι Ω o → K) :
    tangentMatrix π o A B *ᵥ z = sparsePair π o A B z := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem hessianMatrix_mulVec (π : ι → Equiv.Perm Ω) (o : Ω) (A : Set ι)
    [DecidablePred (· ∈ A)] (w : Index ι Ω o) (v : Index ι Ω o → K) :
    hessianMatrix π o A w *ᵥ v =
      hessian π (sparseCoefficients A) (fun _ => 1) (asVariation o v) (asVariation o (Pi.single w 1)) := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem mem_tangentSpan_iff_matrix_range (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (t : ι × Ω → K) :
    t ∈ Contact.tangentSpan π o A B ↔ ∃ z, tangentMatrix π o A B *ᵥ z = t := by
  constructor
  · intro h
    obtain ⟨c, J, d, M, hJ, hM, ht⟩ := (Contact.mem_tangentSpan_iff_field π o A B t).mp h
    let z : Bool × Index ι Ω o → K := fun bj =>
      if bj.1 then coordinates o (d, M) bj.2 else coordinates o (c, J) bj.2
    refine ⟨z, ?_⟩
    rw [tangentMatrix_mulVec, sparsePair_apply]
    have hv : asVariation o (fun j => z (false, j)) = (c, J) := by
      change asVariation o (coordinates o (c, J)) = _
      rw [asVariation_coordinates]
      simp [hJ]
    have hw : asVariation o (fun j => z (true, j)) = (d, M) := by
      change asVariation o (coordinates o (d, M)) = _
      rw [asVariation_coordinates]
      simp [hM]
    rw [hv, hw]
    funext ax
    exact (ht ax.1 ax.2).symm
  · rintro ⟨z, hz⟩
    rw [tangentMatrix_mulVec, sparsePair_apply] at hz
    exact ⟨_, hz⟩

private theorem rat_map_single {J : Type*} [DecidableEq J] (j : J) :
    (fun i : J => algebraMap ℚ K ((Pi.single j (1 : ℚ) : J → ℚ) i)) =
      (Pi.single j (1 : K) : J → K) := by
  funext i
  by_cases h : i = j <;> simp [Pi.single_apply, h, eq_comm]

private theorem rat_map_sparsePair_apply (π : ι → Equiv.Perm Ω) (o : Ω)
    (A B : Set ι) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (z : Bool × Index ι Ω o → ℚ) (a : ι) (x : Ω) :
    algebraMap ℚ K (sparsePair (K := ℚ) π o A B z (a, x)) =
      sparsePair (K := K) π o A B (fun j => algebraMap ℚ K (z j)) (a, x) := by
  by_cases hx : x = o
  · subst x
    by_cases hp : π a o = o <;> by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;>
      simp [sparsePair_apply, Contact.pairDifferential_apply, asVariation,
        hp, hA, hB]
  · by_cases hp : π a x = o <;> by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;>
      simp [sparsePair_apply, Contact.pairDifferential_apply, asVariation,
        hx, hp, hA, hB]

private theorem rat_map_sparseHessian_apply (π : ι → Equiv.Perm Ω) (o : Ω)
    (A : Set ι) [DecidablePred (· ∈ A)]
    (v w : Index ι Ω o → ℚ) (a : ι) (x : Ω) :
    algebraMap ℚ K (hessian π (sparseCoefficients (E := ℚ) A) (fun _ => (1 : ℚ))
      (asVariation o v) (asVariation o w) (a, x)) =
      hessian π (sparseCoefficients (E := K) A) (fun _ => (1 : K))
        (asVariation o (fun j => algebraMap ℚ K (v j)))
        (asVariation o (fun j => algebraMap ℚ K (w j))) (a, x) := by
  by_cases hx : x = o
  · subst x
    by_cases hp : π a o = o <;> by_cases hA : a ∈ A <;>
      simp [hessian, ratio, sparseCoefficients, asVariation, hp, hA]
  · by_cases hp : π a x = o <;> by_cases hA : a ∈ A <;>
      simp [hessian, ratio, sparseCoefficients, asVariation, hx, hp, hA]

theorem map_tangentMatrix (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    (tangentMatrix (K := ℚ) π o A B).map (algebraMap ℚ K) = tangentMatrix (K := K) π o A B := by
  ext ab j
  rcases ab with ⟨a, x⟩
  simp only [Matrix.map_apply, tangentMatrix, LinearMap.toMatrix'_apply]
  rw [rat_map_sparsePair_apply, rat_map_single]

theorem map_hessianMatrix (π : ι → Equiv.Perm Ω) (o : Ω) (A : Set ι)
    [DecidablePred (· ∈ A)] (w : Index ι Ω o) :
    (hessianMatrix (K := ℚ) π o A w).map (algebraMap ℚ K) = hessianMatrix (K := K) π o A w := by
  ext ab j
  rcases ab with ⟨a, x⟩
  simp only [Matrix.map_apply, hessianMatrix, LinearMap.toMatrix'_apply]
  change algebraMap ℚ K
      (hessian π (sparseCoefficients (E := ℚ) A) (fun _ => (1 : ℚ))
        (asVariation o (Pi.single j 1)) (asVariation o (Pi.single w 1)) (a, x)) =
    hessian π (sparseCoefficients (E := K) A) (fun _ => (1 : K))
      (asVariation o (Pi.single j 1)) (asVariation o (Pi.single w 1)) (a, x)
  rw [rat_map_sparseHessian_apply, rat_map_single, rat_map_single]

theorem map_radialVector (o : Ω) (A : Set ι) [DecidablePred (· ∈ A)] :
    (fun j => algebraMap ℚ K (radialVector (K := ℚ) o A j)) = radialVector (K := K) o A := by
  funext j
  cases j <;> simp [radialVector, sparseCoefficients]

/-- A rational certificate implies the actual radial contact statement,
with no omitted torus directions and no assumed smoothness at the sparse point. -/
theorem radial {D : Type*} [Fintype D]
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (pivot : Index ι Ω o)
    (certificate : ContactCertificate.Certificate (D := D)
      (tangentMatrix (K := ℚ) π o A B) (hessianMatrix (K := ℚ) π o A)
      (radialVector (K := ℚ) o A) pivot)
    (v : ToricDifferential.Variation K ι Ω) (hbase : v.2 o = 0)
    (hcontact : ∀ w : ToricDifferential.Variation K ι Ω,
      hessian π (sparseCoefficients A) (fun _ => 1) v w ∈ Contact.tangentSpan π o A B) :
    ∃ lam : K, v = lam • (sparseCoefficients A, (0 : Ω → K)) := by
  let vc := coordinates o v
  have hvc : asVariation o vc = v := by
    rw [asVariation_coordinates]
    simp [hbase]
  have cert := certificate.map (algebraMap ℚ K)
  rw [map_tangentMatrix, map_radialVector] at cert
  have hH : (fun w => (hessianMatrix (K := ℚ) π o A w).map (algebraMap ℚ K)) =
      hessianMatrix (K := K) π o A := funext (map_hessianMatrix π o A)
  rw [hH] at cert
  have hv := ContactCertificate.radial_of_certificate cert vc (by
    intro w
    rw [hessianMatrix_mulVec, hvc]
    exact (mem_tangentSpan_iff_matrix_range π o A B _).mp (hcontact _))
  refine ⟨vc pivot, ?_⟩
  have hh := congrArg (asVariation o) hv
  simpa only [hvc, map_smul, asVariation_radialVector] using hh

end Sunlet.SparseContactCertificate

end Source_SparseContactCertificate

section Source_VectorDerivations


/-! Every coordinate tangent vector defines an actual derivation of the
rational function field. Its value on coordinate functions is the literal
Jacobian product. -/

open scoped BigOperators

namespace Sunlet.RationalPartials

variable {k ι κ : Type*} [Field k] [Fintype ι] [DecidableEq ι]

def vectorDerivative (v : ι → FunctionField k ι) :
    Derivation k (FunctionField k ι) (FunctionField k ι) :=
  ∑ i, v i • partialDerivative i

@[simp] theorem vectorDerivative_variable (v : ι → FunctionField k ι) (j : ι) :
    vectorDerivative v (coordinateVariable j) = v j := by
  simp [vectorDerivative, partial_variable]

theorem vectorDerivative_eq_jacobian (q : κ → FunctionField k ι)
    (v : ι → FunctionField k ι) (j : κ) :
    vectorDerivative v (q j) = JacobianFinite.jacobian q v j := by
  have h := chain_rule (vectorDerivative v) (q j)
  simpa only [vectorDerivative_variable, Algebra.algebraMap_self, RingHom.id_apply,
    JacobianFinite.jacobian_apply, mul_comm] using h

end Sunlet.RationalPartials

end Source_VectorDerivations

section Source_ToricGenericJacobian


/-! The sparse tangent calculation implies generic finiteness of the
actual two-summand rational map. The Jacobian is computed by genuine
derivations of its parameter function field. -/

open scoped BigOperators Matrix

namespace Sunlet.ToricPairAlgebra

open NormalizedVariations ToricDifferential

variable {ι Ω k : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field k] [CharZero k] (o : Ω)

def basisCoefficient {R : Type*} [Zero R] [One R]
    (j : NormalizedVariations.Index ι Ω o) (a : ι) : R :=
  match j with
  | .inl c => if a = c then 1 else 0
  | .inr _ => 0

def basisTorus {R : Type*} [Zero R] [One R]
    (j : NormalizedVariations.Index ι Ω o) (x : Ω) : R :=
  match j with
  | .inl _ => 0
  | .inr b => if x = b.1 then 1 else 0

theorem asVariation_single_coefficient {F : Type*} [Field F]
    (j : NormalizedVariations.Index ι Ω o) (a : ι) :
    (asVariation o (Pi.single j (1 : F))).1 a = basisCoefficient o j a := by
  cases j <;> simp [asVariation, Pi.single_apply, basisCoefficient]

theorem asVariation_single_torus {F : Type*} [Field F]
    (j : NormalizedVariations.Index ι Ω o) (x : Ω) :
    (asVariation o (Pi.single j (1 : F))).2 x = basisTorus o j x := by
  cases j with
  | inl a => simp [asVariation, Pi.single_apply, basisTorus]
  | inr y =>
    by_cases hx : x = o
    · subst x
      simp [asVariation, basisTorus, Ne.symm y.property]
    · simp [asVariation, Pi.single_apply, basisTorus, hx, Subtype.ext_iff]

def tangentEntry (π : ι → Equiv.Perm Ω) :
    Matrix (ι × Ω) (Index (ι := ι) o) (LaurentRing (k := k) (ι := ι) o) :=
  fun ab bj => (torus (k := k) (ι := ι) o bj.1 ab.2).val *
    ((torus (k := k) (ι := ι) o bj.1 (π ab.1 ab.2))⁻¹).val *
    (basisCoefficient o bj.2 ab.1 + coefficient o bj.1 ab.1 *
      (basisTorus o bj.2 ab.2 - basisTorus o bj.2 (π ab.1 ab.2)))

section FieldPair

variable {F : Type*} [Field F] [CharZero F]

def fieldPairDifferential (π : ι → Equiv.Perm Ω) (U : Bool → ι → F) (h : Bool → Ω → Fˣ) :
    (Index (ι := ι) o → F) →ₗ[F] (ι × Ω → F) :=
  (differential π (U false) (fun x => (h false x).val)).comp
    ((asVariation o).comp (component o false)) +
  (differential π (U true) (fun x => (h true x).val)).comp
    ((asVariation o).comp (component o true))

@[simp] theorem fieldPairDifferential_apply (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (v : Index (ι := ι) o → F) :
    fieldPairDifferential o π U h v = fun ab =>
      differential π (U false) (fun x => (h false x).val) (asVariation o (fun j => v (false, j))) ab +
      differential π (U true) (fun x => (h true x).val) (asVariation o (fun j => v (true, j))) ab := rfl

theorem fieldPairDifferential_single (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (b : Bool)
    (j : NormalizedVariations.Index ι Ω o) :
    fieldPairDifferential o π U h (Pi.single (b, j) 1) =
      differential π (U b) (fun x => (h b x).val) (asVariation o (Pi.single j 1)) := by
  funext ax
  rcases ax with ⟨a, x⟩
  cases b <;> simp [fieldPairDifferential_apply, Pi.single_apply,
    asVariation, differential_apply]

variable [Algebra k F]

theorem evaluate_basisCoefficient (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (j : NormalizedVariations.Index ι Ω o) (a : ι) :
    evaluate (k := k) o U h
        (basisCoefficient (R := LaurentRing (k := k) (ι := ι) o) o j a) =
      basisCoefficient (R := F) o j a := by
  cases j with
  | inl c => by_cases hc : a = c <;> simp only [basisCoefficient, hc, ite_true,
      ite_false, map_one, map_zero]
  | inr x => simp only [basisCoefficient, map_zero]

theorem evaluate_basisTorus (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (j : NormalizedVariations.Index ι Ω o) (x : Ω) :
    evaluate (k := k) o U h
        (basisTorus (R := LaurentRing (k := k) (ι := ι) o) o j x) =
      basisTorus (R := F) o j x := by
  cases j with
  | inl a => simp only [basisTorus, map_zero]
  | inr y => by_cases hy : x = y.val <;> simp only [basisTorus, hy, ite_true,
      ite_false, map_one, map_zero]

theorem evaluate_torus_inverse (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hbase : ∀ b, h b o = 1) (b : Bool) (x : Ω) :
    evaluate (k := k) o U h ((torus (k := k) (ι := ι) o b x)⁻¹).val =
      ((h b x).val)⁻¹ := by
  rw [map_units_inv, evaluate_torus o U h hbase]

theorem evaluate_tangentEntry (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1) :
    (tangentEntry (k := k) o π).map (evaluate o U h) =
      LinearMap.toMatrix' (fieldPairDifferential o π U h) := by
  ext ab bj
  rcases ab with ⟨a, x⟩
  rcases bj with ⟨b, j⟩
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply, fieldPairDifferential_single,
    differential_apply, asVariation_single_coefficient, asVariation_single_torus]
  simp only [tangentEntry, map_mul, map_add, map_sub,
    evaluate_torus o U h hbase, evaluate_torus_inverse o U h hbase,
    evaluate_basisCoefficient, evaluate_basisTorus, evaluate_coefficient,
    ratio, div_eq_mul_inv]

end FieldPair

def sparseCoefficient (A B : Set ι) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (b : Bool) : ι → k := if b then sparseCoefficients B else sparseCoefficients A

def sparseTorus (b : Bool) (x : Ω) : kˣ :=
  if b then Units.mk0 (sparseScale o x) (sparseScale_ne_zero o x) else 1

@[simp] theorem sparseTorus_base (b : Bool) : sparseTorus (k := k) o b o = 1 := by
  cases b <;> ext <;> simp [sparseTorus, sparseScale, TwoRatioRigidity.scale]

theorem sparse_fieldPairDifferential (π : ι → Equiv.Perm Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    fieldPairDifferential o π (sparseCoefficient (k := k) A B) (sparseTorus o) =
      NormalizedVariations.sparsePair (K := k) π o A B := by
  apply LinearMap.ext
  intro v
  funext ab
  change differential π (sparseCoefficients (E := k) A) (fun _ => (1 : k))
      (asVariation o (fun j => v (false, j))) ab +
    differential π (sparseCoefficients B) (sparseScale o)
      (asVariation o (fun j => v (true, j))) ab = _
  exact congrFun (sparse_pair_differential (E := k) π o A B _ _) ab

def genericLogDifferential (π : ι → Equiv.Perm Ω) :
    (Index (ι := ι) o → FunctionField (k := k) (ι := ι) o) →ₗ[FunctionField (k := k) (ι := ι) o]
      (ι × Ω → FunctionField (k := k) (ι := ι) o) :=
  fieldPairDifferential o π (genericCoefficient (k := k) (ι := ι) o)
    (genericTorus (k := k) (ι := ι) o)

theorem generic_tangentEntry (π : ι → Equiv.Perm Ω) :
    (tangentEntry (k := k) o π).map (generic o) = LinearMap.toMatrix' (genericLogDifferential o π) :=
  evaluate_tangentEntry (k := k) o π (genericCoefficient (k := k) o)
    (genericTorus (k := k) o) (genericTorus_base (k := k) (ι := ι) o)

/-- The injective sparse tangent map persists in the parameter function
field by an explicitly proved determinant-specialization argument. -/
theorem genericLogDifferential_injective
    (π : ι → Equiv.Perm Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B) :
    Function.Injective (genericLogDifferential (k := k) o π) := by
  have hspecial : Function.Injective
      ((tangentEntry (k := k) o π).map
        (evaluate (k := k) (F := k) o (sparseCoefficient (k := k) A B)
          (sparseTorus (k := k) o))).mulVecLin := by
    rw [evaluate_tangentEntry o π _ _ (sparseTorus_base (k := k) o),
      sparse_fieldPairDifferential]
    intro v w hvw
    apply NormalizedVariations.sparsePair_injective π o A B hdis hmoves hAtwo hBtwo hAtrans hBtrans
    simpa only [Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec] using hvw
  have hg := MatrixSpecialization.injective_of_specialization (tangentEntry (k := k) o π)
    (evaluate (k := k) (F := k) o (sparseCoefficient (k := k) A B)
      (sparseTorus (k := k) o)) (generic o).toRingHom
    (generic_injective o) hspecial
  intro v w hvw
  apply hg
  change ((tangentEntry (k := k) o π).map (generic o)) *ᵥ v =
    ((tangentEntry (k := k) o π).map (generic o)) *ᵥ w
  rw [generic_tangentEntry, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact hvw

def genericCoordinates (π : ι → Equiv.Perm Ω) (ab : ι × Ω) : FunctionField (k := k) (ι := ι) o :=
  coordinate π (genericCoefficient (k := k) o false)
    (fun x => (genericTorus (k := k) (ι := ι) o false x).val) ab.1 ab.2 +
  coordinate π (genericCoefficient (k := k) o true)
    (fun x => (genericTorus (k := k) (ι := ι) o true x).val) ab.1 ab.2

def logarithmicChange (v : Index (ι := ι) o → FunctionField (k := k) (ι := ι) o) :
    Index (ι := ι) o → FunctionField (k := k) (ι := ι) o :=
  fun bj => match bj.2 with
  | .inl _ => v bj
  | .inr _ => v bj / genericVariable o bj

theorem logarithmicChange_injective : Function.Injective (logarithmicChange (k := k) (ι := ι) o) := by
  intro v w h
  funext bj
  rcases bj with ⟨b, a | x⟩
  · exact congrFun h (b, .inl a)
  · have hh := congrFun h (b, .inr x)
    change v (b, .inr x) / genericVariable (k := k) o (b, .inr x) =
      w (b, .inr x) / genericVariable (k := k) o (b, .inr x) at hh
    exact (div_left_inj' (genericVariable_ne_zero (k := k) o (b, .inr x))).mp hh

theorem vector_logVelocity (v : Index (ι := ι) o → FunctionField (k := k) (ι := ι) o) (b : Bool) :
    logarithmicVelocity (RationalPartials.vectorDerivative v)
      (genericCoefficient (k := k) o b)
      (fun x => (genericTorus (k := k) (ι := ι) o b x).val) =
      asVariation o (fun j => logarithmicChange o v (b, j)) := by
  apply Prod.ext
  · funext a
    exact RationalPartials.vectorDerivative_variable v (b, .inl a)
  · funext x
    by_cases hx : x = o
    · subst x
      simp [logarithmicVelocity, genericTorus]
    · simp [logarithmicVelocity, genericTorus, hx, asVariation, logarithmicChange,
        genericVariable, RationalPartials.coordinateVariable]
      exact RationalPartials.vectorDerivative_variable v (b, .inr ⟨x, hx⟩)

theorem actualJacobian_eq_logarithmic (π : ι → Equiv.Perm Ω)
    (v : Index (ι := ι) o → FunctionField (k := k) (ι := ι) o) :
    JacobianFinite.jacobian (genericCoordinates (k := k) o π) v =
      genericLogDifferential o π (logarithmicChange o v) := by
  funext ab
  rw [← RationalPartials.vectorDerivative_eq_jacobian]
  simp only [genericCoordinates, map_add,
    derivation_coordinate (RationalPartials.vectorDerivative v) π
      (genericCoefficient (k := k) o false)
      (fun x => (genericTorus (k := k) (ι := ι) o false x).val)
      (fun x => Units.ne_zero (genericTorus (k := k) (ι := ι) o false x)),
    derivation_coordinate (RationalPartials.vectorDerivative v) π
      (genericCoefficient (k := k) o true)
      (fun x => (genericTorus (k := k) (ι := ι) o true x).val)
      (fun x => Units.ne_zero (genericTorus (k := k) (ι := ι) o true x)),
    vector_logVelocity]
  rfl

/-- The complete finite/separable conclusion for the actual coordinate
field of the normalized two-summand map. -/
theorem generic_finite_separable
    (π : ι → Equiv.Perm Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B) :
    Module.Finite (JacobianFinite.generatedField (genericCoordinates (k := k) o π))
      (FunctionField (k := k) (ι := ι) o) ∧
    Algebra.IsSeparable (JacobianFinite.generatedField (genericCoordinates (k := k) o π))
      (FunctionField (k := k) (ι := ι) o) := by
  apply JacobianFinite.finite_separable_of_jacobian_injective
  intro v w h
  rw [actualJacobian_eq_logarithmic, actualJacobian_eq_logarithmic] at h
  exact logarithmicChange_injective o
    (genericLogDifferential_injective o π A B hdis hmoves hAtwo hBtwo hAtrans hBtrans h)

end Sunlet.ToricPairAlgebra

end Source_ToricGenericJacobian

section Source_ToricPairSwap


/-! Interchange of the two parameter families preserves faithfulness of
the generic Laurent evaluation and the actual combined tangent range. -/


namespace Sunlet.ToricPairAlgebra

variable {ι Ω k : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field k] [CharZero k] (o : Ω)

def switchIndex : Index (ι := ι) o ≃ Index (ι := ι) o where
  toFun j := (!j.1, j.2)
  invFun j := (!j.1, j.2)
  left_inv j := by cases j with | mk b j => cases b <;> rfl
  right_inv j := by cases j with | mk b j => cases b <;> rfl

theorem polynomial_algebraMap_injective : Function.Injective
    (algebraMap (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o)) := by
  intro f g h
  apply IsFractionRing.injective (PolynomialRing (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o)
  have hh := congrArg (generic o) h
  simpa only [generic_algebraMap] using hh

section Field

variable {F : Type*} [Field F] [CharZero F] [Algebra k F]

theorem evaluate_polynomial (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (f : PolynomialRing (k := k) (ι := ι) o) :
    evaluate o U h (algebraMap (PolynomialRing (k := k) (ι := ι) o)
      (LaurentRing (k := k) (ι := ι) o) f) = MvPolynomial.aeval (variableValues o U h) f := by
  simp [evaluate, IsLocalization.Away.liftAlgHom_apply]

/-- Switching the two Boolean-indexed parameter families cannot impose
an algebraic relation that was absent before the switch. -/
theorem evaluate_switch_injective (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hfaithful : Function.Injective (evaluate (k := k) o U h)) :
    Function.Injective (evaluate (k := k) o (fun b => U (!b)) (fun b => h (!b))) := by
  have hp : Function.Injective (MvPolynomial.aeval (R := k) (variableValues o U h)) := by
    intro f g he
    apply polynomial_algebraMap_injective o
    apply hfaithful
    simpa only [evaluate_polynomial] using he
  have hs : MvPolynomial.aeval (R := k) (variableValues o (fun b => U (!b)) (fun b => h (!b))) =
      (MvPolynomial.aeval (R := k) (variableValues o U h)).comp
        (MvPolynomial.rename (switchIndex (ι := ι) o)) := by
    ext j
    rcases j with ⟨b, a | x⟩ <;> simp [variableValues, switchIndex]
  have hps : Function.Injective
      (MvPolynomial.aeval (R := k) (variableValues o (fun b => U (!b)) (fun b => h (!b)))) := by
    rw [hs]
    exact hp.comp (MvPolynomial.rename_injective _ (switchIndex o).injective)
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (denominator (k := k) (ι := ι) o))
    (evaluate o (fun b => U (!b)) (fun b => h (!b))).toRingHom).mpr
  intro f g
  constructor
  · exact congrArg (evaluate o (fun b => U (!b)) (fun b => h (!b)))
  · intro he
    change evaluate (k := k) o (fun b => U (!b)) (fun b => h (!b))
        (algebraMap (PolynomialRing (k := k) (ι := ι) o)
          (LaurentRing (k := k) (ι := ι) o) f) =
      evaluate (k := k) o (fun b => U (!b)) (fun b => h (!b))
        (algebraMap (PolynomialRing (k := k) (ι := ι) o)
          (LaurentRing (k := k) (ι := ι) o) g) at he
    rw [evaluate_polynomial, evaluate_polynomial] at he
    exact congrArg (algebraMap (PolynomialRing (k := k) (ι := ι) o)
      (LaurentRing (k := k) (ι := ι) o)) (hps he)

theorem fieldPairDifferential_switch (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (v : Index (ι := ι) o → F) :
    fieldPairDifferential o π (fun b => U (!b)) (fun b => h (!b)) v =
      fieldPairDifferential o π U h (fun j => v (switchIndex o j)) := by
  funext ax
  simp only [fieldPairDifferential_apply, switchIndex]
  exact add_comm _ _

theorem fieldPairDifferential_switch_range (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) :
    LinearMap.range (fieldPairDifferential o π (fun b => U (!b)) (fun b => h (!b))) =
      LinearMap.range (fieldPairDifferential o π U h) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨fun j => v (switchIndex o j), (fieldPairDifferential_switch o π U h v).symm⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨fun j => v (switchIndex o j), ?_⟩
    rw [fieldPairDifferential_switch]
    congr 1
    funext j
    rcases j with ⟨b, j⟩
    cases b <;> rfl

end Field
end Sunlet.ToricPairAlgebra

end Source_ToricPairSwap

section Source_RadialSpecialization


/-! A radial contact kernel persists from an explicitly checked point to
the generic parameter field. The proof uses one augmented matrix, adding
the equation that the pivot component of the contact velocity is zero. -/

open scoped BigOperators Matrix

namespace Sunlet.RadialSpecialization

variable {R K E J W O T : Type*}
  [CommRing R] [Field K] [Field E] [Algebra K R]
  [Fintype J] [Fintype W] [Fintype O] [Fintype T]
  [DecidableEq J] [DecidableEq W] [DecidableEq O] [DecidableEq T]

def augmented (tangent : Matrix O T R) (hessian : W → Matrix O J R) (pivot : J) :
    Matrix ((W × O) ⊕ Unit) (J ⊕ (W × T)) R := fun row col =>
  match row, col with
  | .inl wo, .inl j => hessian wo.1 wo.2 j
  | .inl wo, .inr wt => if wo.1 = wt.1 then -tangent wo.2 wt.2 else 0
  | .inr _, .inl j => if j = pivot then 1 else 0
  | .inr _, .inr _ => 0

theorem augmented_main (tangent : Matrix O T R) (hessian : W → Matrix O J R) (pivot : J)
    (z : J ⊕ (W × T) → R) (w : W) (o : O) :
    (augmented tangent hessian pivot *ᵥ z) (.inl (w, o)) =
      (hessian w *ᵥ (fun j => z (.inl j))) o -
        (tangent *ᵥ (fun t => z (.inr (w, t)))) o := by
  simp [Matrix.mulVec, dotProduct, augmented, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Finset.sum_neg_distrib, ← sub_eq_add_neg]

theorem augmented_pivot (tangent : Matrix O T R) (hessian : W → Matrix O J R) (pivot : J)
    (z : J ⊕ (W × T) → R) :
    (augmented tangent hessian pivot *ᵥ z) (.inr ()) = z (.inl pivot) := by
  simp [Matrix.mulVec, dotProduct, augmented, Fintype.sum_sum_type]

theorem map_augmented (f : R →+* E) (tangent : Matrix O T R)
    (hessian : W → Matrix O J R) (pivot : J) :
    (augmented tangent hessian pivot).map f =
      augmented (tangent.map f) (fun w => (hessian w).map f) pivot := by
  ext row col
  cases row with
  | inl wo =>
    cases col with
    | inl j => rfl
    | inr wt =>
      by_cases he : wo.1 = wt.1 <;> simp [augmented, he]
  | inr u =>
    cases col with
    | inl j =>
      by_cases he : j = pivot <;> simp [augmented, he]
    | inr wt => simp [augmented]

theorem augmented_injective (tangent : Matrix O T K) (hessian : W → Matrix O J K)
    (radial : J → K) (pivot : J) (hpivot : radial pivot ≠ 0)
    (htangent : Function.Injective tangent.mulVecLin)
    (hcontact : ∀ v : J → K, (∀ w, ∃ z, tangent *ᵥ z = hessian w *ᵥ v) →
      ∃ lam : K, v = lam • radial) :
    Function.Injective (augmented tangent hessian pivot).mulVecLin := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let v : J → K := fun j => z (.inl j)
  have hmain : ∀ w, tangent *ᵥ (fun t => z (.inr (w, t))) = hessian w *ᵥ v := by
    intro w
    funext o
    have hh := congrFun hz (.inl (w, o))
    rw [Matrix.mulVecLin_apply, augmented_main] at hh
    exact (sub_eq_zero.mp hh).symm
  obtain ⟨lam, hv⟩ := hcontact v (fun w => ⟨_, hmain w⟩)
  have hp : v pivot = 0 := by
    have hh := congrFun hz (.inr ())
    rw [Matrix.mulVecLin_apply, augmented_pivot] at hh
    exact hh
  have hlam : lam = 0 := by
    rw [hv] at hp
    exact (mul_eq_zero.mp hp).resolve_right hpivot
  have hvzero : v = 0 := by simp [hv, hlam]
  have hwzero : ∀ w, (fun t => z (.inr (w, t))) = 0 := by
    intro w
    apply htangent
    change tangent *ᵥ _ = tangent *ᵥ 0
    rw [hmain, hvzero]
    simp
  funext j
  rcases j with j | ⟨w, t⟩
  · exact congrFun hvzero j
  · exact congrFun (hwzero w) t

/-- The generic radial assertion follows from the sparse radial assertion,
the injective sparse tangent map, and the universal radial Hessian identity. -/
theorem generic_radial
    (tangent : Matrix O T R) (hessian : W → Matrix O J R) (radial : J → R) (pivot : J)
    (evaluate : R →ₐ[K] K) (generic : R →+* E) (hgeneric : Function.Injective generic)
    (hpivot : evaluate (radial pivot) ≠ 0)
    (htangent : Function.Injective (tangent.map evaluate).mulVecLin)
    (hspecial : ∀ v : J → K,
      (∀ w, ∃ z, tangent.map evaluate *ᵥ z = (hessian w).map evaluate *ᵥ v) →
      ∃ lam : K, v = lam • (fun j => evaluate (radial j)))
    (hradial : ∀ w, ∃ z, tangent.map generic *ᵥ z =
      (hessian w).map generic *ᵥ (fun j => generic (radial j))) :
    ∀ v : J → E,
      (∀ w, ∃ z, tangent.map generic *ᵥ z = (hessian w).map generic *ᵥ v) →
      ∃ lam : E, v = lam • (fun j => generic (radial j)) := by
  have hs : Function.Injective ((augmented tangent hessian pivot).map evaluate).mulVecLin := by
    change Function.Injective ((augmented tangent hessian pivot).map
      evaluate.toRingHom).mulVecLin
    rw [map_augmented evaluate.toRingHom]
    exact augmented_injective _ _ _ pivot hpivot htangent hspecial
  have hg := MatrixSpecialization.injective_of_specialization (augmented tangent hessian pivot)
    evaluate generic hgeneric hs
  rw [map_augmented] at hg
  have hr : generic (radial pivot) ≠ 0 := by
    intro h
    have he : radial pivot = 0 := hgeneric (h.trans generic.map_zero.symm)
    exact hpivot (by rw [he, map_zero])
  intro v hv
  classical
  choose zv hzv using hv
  choose zr hzr using hradial
  let lam := v pivot / generic (radial pivot)
  let v₀ : J → E := v - lam • (fun j => generic (radial j))
  let z : J ⊕ (W × T) → E := Sum.elim v₀ (fun wt => zv wt.1 wt.2 - lam * zr wt.1 wt.2)
  have hz : (augmented (tangent.map generic) (fun w => (hessian w).map generic) pivot).mulVecLin z = 0 := by
    funext row
    rcases row with ⟨w, o⟩ | u
    · rw [Matrix.mulVecLin_apply, augmented_main]
      change ((hessian w).map generic *ᵥ v₀) o -
        (tangent.map generic *ᵥ (zv w - lam • zr w)) o = 0
      have he : (hessian w).map generic *ᵥ v₀ = tangent.map generic *ᵥ (zv w - lam • zr w) := by
        change ((hessian w).map generic).mulVecLin (v - lam • _) =
          (tangent.map generic).mulVecLin (zv w - lam • zr w)
        rw [map_sub, map_smul, map_sub, map_smul]
        simp only [Matrix.mulVecLin_apply]
        change _ - _ = _ - _
        rw [hzv, hzr]
      rw [he]
      exact sub_self _
    · cases u
      rw [Matrix.mulVecLin_apply, augmented_pivot]
      simp [z, v₀, lam, hr]
  have hz0 : z = 0 := (injective_iff_map_eq_zero _).mp hg z hz
  refine ⟨lam, ?_⟩
  funext j
  have hh := congrFun hz0 (.inl j)
  exact sub_eq_zero.mp hh

end Sunlet.RadialSpecialization

end Source_RadialSpecialization

section Source_ToricGenericContact


/-! The sparse contact calculation is promoted to the actual generic
parameter field by a Laurent-ring Hessian matrix and the explicit augmented
matrix specialization theorem. Every test direction is retained. -/

open scoped BigOperators Matrix

namespace Sunlet.ToricPairAlgebra

open NormalizedVariations ToricDifferential

variable {ι Ω k : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field k] [CharZero k] (o : Ω)

/-- The normalized logarithmic Hessian, linear in both actual tangent
coordinate vectors. -/
def normalizedHessian {F : Type*} [Field F]
    (π : ι → Equiv.Perm Ω) (U : ι → F) (h : Ω → F) :
    (NormalizedVariations.Index ι Ω o → F) →ₗ[F]
      (NormalizedVariations.Index ι Ω o → F) →ₗ[F] (ι × Ω → F) where
  toFun v := {
    toFun w := hessian π U h (asVariation o v) (asVariation o w)
    map_add' := by
      intro w t
      funext ab
      change hessian π U h (asVariation o v) (asVariation o (w + t)) ab =
        hessian π U h (asVariation o v) (asVariation o w) ab +
        hessian π U h (asVariation o v) (asVariation o t) ab
      simp only [map_add, hessian]
      dsimp
      ring
    map_smul' := by
      intro r w
      funext ab
      change hessian π U h (asVariation o v) (asVariation o (r • w)) ab =
        r * hessian π U h (asVariation o v) (asVariation o w) ab
      simp only [map_smul, hessian]
      dsimp
      ring }
  map_add' := by
    intro v t
    apply LinearMap.ext
    intro w
    funext ab
    change hessian π U h (asVariation o (v + t)) (asVariation o w) ab =
      hessian π U h (asVariation o v) (asVariation o w) ab +
      hessian π U h (asVariation o t) (asVariation o w) ab
    simp only [map_add, hessian]
    dsimp
    ring
  map_smul' := by
    intro r v
    apply LinearMap.ext
    intro w
    funext ab
    change hessian π U h (asVariation o (r • v)) (asVariation o w) ab =
      r * hessian π U h (asVariation o v) (asVariation o w) ab
    simp only [map_smul, hessian]
    dsimp
    ring

@[simp] theorem normalizedHessian_apply {F : Type*} [Field F]
    (π : ι → Equiv.Perm Ω) (U : ι → F) (h : Ω → F)
    (v w : NormalizedVariations.Index ι Ω o → F) :
    normalizedHessian o π U h v w = hessian π U h (asVariation o v) (asVariation o w) := rfl

/-- Checking basis test directions is equivalent to checking every
normalized logarithmic direction. -/
theorem hessian_mem_of_basis {F : Type*} [Field F]
    (π : ι → Equiv.Perm Ω) (U : ι → F) (h : Ω → F)
    (v : NormalizedVariations.Index ι Ω o → F) (T : Submodule F (ι × Ω → F))
    (hbasis : ∀ w, normalizedHessian o π U h v (Pi.single w 1) ∈ T) :
    ∀ w, normalizedHessian o π U h v w ∈ T := by
  have ht : T.comap (normalizedHessian o π U h v) = ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun F (NormalizedVariations.Index ι Ω o))).mpr
    intro j
    simpa only [Submodule.mem_comap, Pi.basisFun_apply] using hbasis j
  intro w
  have hw : w ∈ T.comap (normalizedHessian o π U h v) := by rw [ht]; trivial
  exact hw

def hessianEntry (π : ι → Equiv.Perm Ω) (b : Bool)
    (w : NormalizedVariations.Index ι Ω o) :
    Matrix (ι × Ω) (NormalizedVariations.Index ι Ω o) (LaurentRing (k := k) (ι := ι) o) :=
  fun ax j => (torus (k := k) (ι := ι) o b ax.2).val *
    ((torus (k := k) (ι := ι) o b (π ax.1 ax.2))⁻¹).val *
    (basisCoefficient o w ax.1 * (basisTorus o j ax.2 - basisTorus o j (π ax.1 ax.2)) +
      basisCoefficient o j ax.1 * (basisTorus o w ax.2 - basisTorus o w (π ax.1 ax.2)) +
      coefficient o b ax.1 * (basisTorus o j ax.2 - basisTorus o j (π ax.1 ax.2)) *
        (basisTorus o w ax.2 - basisTorus o w (π ax.1 ax.2)))

def radialEntry (b : Bool) :
    NormalizedVariations.Index ι Ω o → LaurentRing (k := k) (ι := ι) o :=
  Sum.elim (coefficient o b) (fun _ => 0)

section Evaluation

variable {F : Type*} [Field F] [CharZero F] [Algebra k F]

theorem evaluate_hessianEntry (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (b : Bool) (w : NormalizedVariations.Index ι Ω o) :
    (hessianEntry (k := k) o π b w).map (evaluate o U h) =
      LinearMap.toMatrix' ((normalizedHessian o π (U b) (fun x => (h b x).val)).flip (Pi.single w 1)) := by
  ext ax j
  rcases ax with ⟨a, x⟩
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply, LinearMap.flip_apply,
    normalizedHessian_apply, hessian, asVariation_single_coefficient,
    asVariation_single_torus]
  simp only [hessianEntry, map_mul, map_add, map_sub,
    evaluate_torus o U h hbase, evaluate_torus_inverse o U h hbase,
    evaluate_basisCoefficient, evaluate_basisTorus, evaluate_coefficient,
    ratio, div_eq_mul_inv]

theorem evaluate_radialEntry (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (b : Bool) :
    (fun j => evaluate (k := k) o U h (radialEntry o b j)) =
      Sum.elim (U b) (fun _ => (0 : F)) := by
  funext j
  cases j <;> simp [radialEntry]

theorem evaluate_hessianEntry_mulVec (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (b : Bool) (w : NormalizedVariations.Index ι Ω o)
    (v : NormalizedVariations.Index ι Ω o → F) :
    (hessianEntry (k := k) o π b w).map (evaluate o U h) *ᵥ v =
      normalizedHessian o π (U b) (fun x => (h b x).val) v (Pi.single w 1) := by
  rw [evaluate_hessianEntry o π U h hbase]
  exact LinearMap.toMatrix'_mulVec _ _

theorem evaluated_radial_contact (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (b : Bool) (w : NormalizedVariations.Index ι Ω o) :
    ∃ z : Index (ι := ι) o → F,
      (tangentEntry (k := k) o π).map (evaluate o U h) *ᵥ z =
      (hessianEntry (k := k) o π b w).map (evaluate o U h) *ᵥ
        (fun j => evaluate (k := k) o U h (radialEntry (k := k) (ι := ι) o b j)) := by
  let direction := asVariation o (Pi.single w (1 : F))
  let v : NormalizedVariations.Index ι Ω o → F := coordinates o (0, direction.2)
  let z : Index (ι := ι) o → F := fun bj => if bj.1 = b then v bj.2 else 0
  refine ⟨z, ?_⟩
  rw [evaluate_tangentEntry o π U h hbase, LinearMap.toMatrix'_mulVec,
    evaluate_radialEntry, evaluate_hessianEntry_mulVec o π U h hbase]
  have hr : asVariation o (Sum.elim (U b) (fun _ => (0 : F))) = (U b, (0 : Ω → F)) := by
    apply Prod.ext
    · rfl
    · funext x
      by_cases hx : x = o <;> simp [asVariation, hx]
  have hv : asVariation o v = (0, direction.2) := by
    rw [asVariation_coordinates]
    simp [direction]
  rw [normalizedHessian_apply, hr, radial_hessian]
  cases b
  · change differential π (U false) (fun x => (h false x).val) (asVariation o v) +
        differential π (U true) (fun x => (h true x).val)
          (asVariation o (0 : NormalizedVariations.Index ι Ω o → F)) =
      differential π (U false) (fun x => (h false x).val) (0, direction.2)
    rw [hv, map_zero, map_zero, add_zero]
  · change differential π (U false) (fun x => (h false x).val)
          (asVariation o (0 : NormalizedVariations.Index ι Ω o → F)) +
        differential π (U true) (fun x => (h true x).val) (asVariation o v) =
      differential π (U true) (fun x => (h true x).val) (0, direction.2)
    rw [hv, map_zero, map_zero, zero_add]

end Evaluation

/-- A sparse radial contact calculation implies the generic radial
contact assertion for the literal two-summand ratio map. The sole
specialization hypothesis concerns actual Hessians and actual tangent
spaces, and is discharged by `SparseContact.radial` or an exact finite
certificate in subsequent applications. -/
theorem radial_of_sparse_at_faithful_parameters
    {F : Type*} [Field F] [CharZero F] [Algebra k F]
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (hfaithful : Function.Injective (evaluate (k := k) o U h))
    (π : ι → Equiv.Perm Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (a₀ : ι) (ha₀ : a₀ ∈ A)
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B)
    (hspecial : ∀ v : ToricDifferential.Variation k ι Ω, v.2 o = 0 →
      (∀ w, hessian π (sparseCoefficients A) (fun _ => 1) v w ∈ Contact.tangentSpan π o A B) →
      ∃ lam : k, v = lam • (sparseCoefficients A, (0 : Ω → k))) :
    ∀ v : NormalizedVariations.Index ι Ω o → F,
      (∀ w, normalizedHessian o π (U false) (fun x => (h false x).val)
        v w ∈ LinearMap.range (fieldPairDifferential o π U h)) →
      ∃ lam : F, v = lam • Sum.elim (U false) (fun _ => 0) := by
  let ev : LaurentRing (k := k) (ι := ι) o →ₐ[k] k :=
    evaluate (k := k) o (sparseCoefficient (k := k) A B)
      (sparseTorus (k := k) o)
  have ht : Function.Injective ((tangentEntry (k := k) o π).map ev).mulVecLin := by
    rw [evaluate_tangentEntry o π _ _ (sparseTorus_base (k := k) o),
      sparse_fieldPairDifferential]
    intro v w h
    apply sparsePair_injective π o A B hdis hmoves hAtwo hBtwo hAtrans hBtrans
    simpa only [Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec] using h
  have hp : ev (radialEntry o false (.inl a₀)) ≠ 0 := by
    simp [ev, radialEntry, sparseCoefficient, sparseCoefficients, ha₀]
  have hs : ∀ v : NormalizedVariations.Index ι Ω o → k,
      (∀ w, ∃ z, (tangentEntry o π).map ev *ᵥ z = (hessianEntry o π false w).map ev *ᵥ v) →
      ∃ lam : k, v = lam • (fun j => ev (radialEntry o false j)) := by
    intro v hv
    have hvbasis : ∀ w, normalizedHessian o π (sparseCoefficients A) (fun _ => (1 : k))
        v (Pi.single w 1) ∈ Contact.tangentSpan π o A B := by
      intro w
      obtain ⟨z, hz⟩ := hv w
      rw [evaluate_tangentEntry o π _ _ (sparseTorus_base (k := k) o),
        evaluate_hessianEntry_mulVec o π _ _ (sparseTorus_base (k := k) o),
        sparse_fieldPairDifferential, LinearMap.toMatrix'_mulVec] at hz
      exact ⟨_, hz⟩
    have hfull := hessian_mem_of_basis o π (sparseCoefficients A) (fun _ => (1 : k))
      v (Contact.tangentSpan π o A B) hvbasis
    obtain ⟨lam, hlam⟩ := hspecial (asVariation o v) (asVariation_base o v) (by
      intro w
      rw [← hessian_coordinates o π (sparseCoefficients A) (fun _ => (1 : k)) (asVariation o v) w]
      exact hfull (coordinates o w))
    refine ⟨lam, ?_⟩
    have hh := congrArg (coordinates o) hlam
    rw [coordinates_asVariation, map_smul] at hh
    calc
      v = lam • coordinates o (sparseCoefficients A, (0 : Ω → k)) := hh
      _ = lam • (fun j => ev (radialEntry o false j)) := by
        funext j
        cases j <;> simp [ev, radialEntry, sparseCoefficient, coordinates]
  have hg := RadialSpecialization.generic_radial (tangentEntry (k := k) o π)
    (hessianEntry o π false) (radialEntry o false) (.inl a₀) ev (evaluate o U h).toRingHom
    hfaithful hp ht hs
    (fun w => evaluated_radial_contact o π U h hbase false w)
  intro v hv
  obtain ⟨lam, hlam⟩ := hg v (by
    intro w
    obtain ⟨z, hz⟩ := hv (Pi.single w 1)
    refine ⟨z, ?_⟩
    change (tangentEntry (k := k) o π).map (evaluate (k := k) o U h) *ᵥ z =
      (hessianEntry (k := k) o π false w).map (evaluate (k := k) o U h) *ᵥ v
    rw [evaluate_tangentEntry o π U h hbase, LinearMap.toMatrix'_mulVec,
      evaluate_hessianEntry_mulVec o π U h hbase]
    exact hz)
  refine ⟨lam, ?_⟩
  change v = lam • (fun j => evaluate (k := k) o U h
    (radialEntry (k := k) (ι := ι) o false j)) at hlam
  simpa only [evaluate_radialEntry] using hlam

/-- The same checked sparse calculation controls both generic summands.
Interchange is an actual permutation of the independent parameter variables. -/
theorem radial_at_either_faithful_parameter
    {F : Type*} [Field F] [CharZero F] [Algebra k F]
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (hfaithful : Function.Injective (evaluate (k := k) o U h))
    (π : ι → Equiv.Perm Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (a₀ : ι) (ha₀ : a₀ ∈ A)
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B)
    (hspecial : ∀ v : ToricDifferential.Variation k ι Ω, v.2 o = 0 →
      (∀ w, hessian π (sparseCoefficients A) (fun _ => 1) v w ∈ Contact.tangentSpan π o A B) →
      ∃ lam : k, v = lam • (sparseCoefficients A, (0 : Ω → k)))
    (b : Bool) (v : NormalizedVariations.Index ι Ω o → F)
    (hv : ∀ w, normalizedHessian o π (U b) (fun x => (h b x).val) v w ∈
      LinearMap.range (fieldPairDifferential o π U h)) :
    ∃ lam : F, v = lam • Sum.elim (U b) (fun _ => 0) := by
  cases b
  · exact radial_of_sparse_at_faithful_parameters o U h hbase hfaithful π A B a₀ ha₀
      hdis hmoves hAtwo hBtwo hAtrans hBtrans hspecial v hv
  · apply radial_of_sparse_at_faithful_parameters o (fun b => U (!b)) (fun b => h (!b))
      (fun b => hbase (!b)) (evaluate_switch_injective o U h hfaithful) π A B a₀ ha₀
      hdis hmoves hAtwo hBtwo hAtrans hBtrans hspecial v
    intro w
    rw [fieldPairDifferential_switch_range]
    exact hv w

end Sunlet.ToricPairAlgebra

end Source_ToricGenericContact

section Source_DerivativeChords


/-! The dimension argument excluding a third mixed point on a generic
secant line. It is proved directly using derivations and finite-dimensional
linear algebra; no generalized trisecant theorem is assumed. -/


namespace Sunlet.DerivativeChords

variable {k E J O : Type*} [Field k] [Field E] [Algebra k E]
  [Fintype J] [Fintype O] [DecidableEq J]

def vectorDerivative (D : Derivation k E E) (x : O → E) : O → E := fun o => D (x o)

theorem derivative_chord (D : Derivation k E E) (x y : O → E) (a b : E) :
    vectorDerivative D (a • x + b • y) =
      D a • x + a • vectorDerivative D x + D b • y + b • vectorDerivative D y := by
  funext o
  simp only [vectorDerivative, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, D.leibniz]
  ring

private theorem range_le_of_basis
    (U : (J → E) →ₗ[E] (O → E)) (T : Submodule E (O → E))
    (h : ∀ j, U (Pi.single j 1) ∈ T) : LinearMap.range U ≤ T := by
  have hc : T.comap U = ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun E J)).mpr
    intro j
    change U ((Pi.basisFun E J) j) ∈ T
    simpa only [Pi.basisFun_apply] using h j
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ T.comap U := by rw [hc]; trivial
  exact hv

/-- If a nonzero coefficient of a moving point occurs in a chord, its
tangent space lies in the tangent space of the chord point together with
the two-dimensional chord plane. -/
theorem tangent_le_of_chord
    (x y z : O → E) (a b : E) (ha : a ≠ 0) (hz : z = a • x + b • y)
    (U W : (J → E) →ₗ[E] (O → E)) (D : J → Derivation k E E)
    (hx : ∀ j, vectorDerivative (D j) x = U (Pi.single j 1))
    (hy : ∀ j, vectorDerivative (D j) y = 0)
    (hW : ∀ j, vectorDerivative (D j) z ∈ LinearMap.range W) :
    LinearMap.range U ≤ LinearMap.range W ⊔ Submodule.span E ({x, y} : Set (O → E)) := by
  let T : Submodule E (O → E) := LinearMap.range W ⊔ Submodule.span E ({x, y} : Set (O → E))
  have hxT : x ∈ T := (show Submodule.span E ({x, y} : Set (O → E)) ≤ T from le_sup_right)
    (Submodule.subset_span (by simp))
  have hyT : y ∈ T := (show Submodule.span E ({x, y} : Set (O → E)) ≤ T from le_sup_right)
    (Submodule.subset_span (by simp))
  apply range_le_of_basis U T
  intro j
  apply (T.smul_mem_iff ha).mp
  have hzT : vectorDerivative (D j) z ∈ T :=
    (show LinearMap.range W ≤ T from le_sup_left) (hW j)
  have he : a • U (Pi.single j 1) =
      vectorDerivative (D j) z - (D j) a • x - (D j) b • y := by
    rw [hz, derivative_chord, hx, hy]
    simp only [smul_zero, add_zero]
    abel
  rw [he]
  exact T.sub_mem (T.sub_mem hzT (T.smul_mem _ hxT)) (T.smul_mem _ hyT)

/-- An injective pair of `d`-dimensional tangent maps, with `d > 2`,
cannot both be contained in a `d`-dimensional tangent space plus a chord
plane. -/
theorem paired_dimension_contradiction
    (U V W : (J → E) →ₗ[E] (O → E)) (x y : O → E)
    (hdim : 2 < Fintype.card J) (hpair : Function.Injective (U.coprod V))
    (hU : LinearMap.range U ≤ LinearMap.range W ⊔ Submodule.span E ({x, y} : Set (O → E)))
    (hV : LinearMap.range V ≤ LinearMap.range W ⊔ Submodule.span E ({x, y} : Set (O → E))) : False := by
  classical
  have hle : LinearMap.range (U.coprod V) ≤
      LinearMap.range W ⊔ Submodule.span E ({x, y} : Set (O → E)) := by
    rw [LinearMap.range_coprod]
    exact sup_le hU hV
  have hdimle := Submodule.finrank_mono hle
  have hpairdim := LinearMap.finrank_range_of_inj hpair
  have hWdim := W.finrank_range_le
  have hspan : Module.finrank E (Submodule.span E ({x, y} : Set (O → E))) ≤ 2 := by
    have h := finrank_span_le_card (R := E) ({x, y} : Set (O → E))
    exact h.trans (by by_cases hxy : x = y <;> simp [hxy])
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range W) (Submodule.span E ({x, y} : Set (O → E)))
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at hpairdim hWdim
  omega

/-- A third point on the generic chord cannot have both coefficients
nonzero. This is the only trisecant-type input needed later. -/
theorem no_mixed_chord
    (x y z : O → E) (a b : E) (hz : z = a • x + b • y)
    (U V W : (J → E) →ₗ[E] (O → E))
    (D₁ D₂ : J → Derivation k E E)
    (hdim : 2 < Fintype.card J) (hpair : Function.Injective (U.coprod V))
    (hx₁ : ∀ j, vectorDerivative (D₁ j) x = U (Pi.single j 1))
    (hy₁ : ∀ j, vectorDerivative (D₁ j) y = 0)
    (hx₂ : ∀ j, vectorDerivative (D₂ j) x = 0)
    (hy₂ : ∀ j, vectorDerivative (D₂ j) y = V (Pi.single j 1))
    (hz₁ : ∀ j, vectorDerivative (D₁ j) z ∈ LinearMap.range W)
    (hz₂ : ∀ j, vectorDerivative (D₂ j) z ∈ LinearMap.range W) :
    a = 0 ∨ b = 0 := by
  by_contra h
  push_neg at h
  have hU := tangent_le_of_chord x y z a b h.1 hz U W D₁ hx₁ hy₁ hz₁
  have hV := tangent_le_of_chord y x z b a h.2 (by simpa [add_comm] using hz)
    V W D₂ hy₂ hx₂ hz₂
  rw [Set.pair_comm y x] at hV
  exact paired_dimension_contradiction U V W x y hdim hpair hU hV

end Sunlet.DerivativeChords

end Source_DerivativeChords

section Source_EulerChord


/-! The algebraic chord-plane calculation in the Euler-derivation proof
of generic two-identifiability. No geometric identifiability assertion is
hidden in these elementary linear-algebra statements. -/


namespace Sunlet.DerivativeChords

variable {k E O : Type*} [Field k] [Field E] [Algebra k E]

/-- Two decompositions with radial derivatives span the same chord plane.
The independence hypothesis has its ordinary two-vector meaning. -/
theorem same_chord_of_radial_derivatives
    (D : Derivation k E E) (x y x' y' : O → E) (a b : E)
    (hind : ∀ r s : E, r • x + s • y = 0 → r = 0 ∧ s = 0)
    (hsum : x + y = x' + y')
    (hx : vectorDerivative D x = x) (hy : vectorDerivative D y = 0)
    (hx' : vectorDerivative D x' = a • x') (hy' : vectorDerivative D y' = b • y') :
    a ≠ b ∧
      x' = ((1 - b) / (a - b)) • x + (-b / (a - b)) • y ∧
      y' = ((a - 1) / (a - b)) • x + (a / (a - b)) • y := by
  have hdiff : x = a • x' + b • y' := by
    have h := congrArg (vectorDerivative D) hsum
    have hleft : vectorDerivative D (x + y) = x := by
      funext o
      change D (x o + y o) = x o
      have hxv : D (x o) = x o := congrFun hx o
      have hyv : D (y o) = 0 := congrFun hy o
      rw [map_add, hxv, hyv, add_zero]
    have hright : vectorDerivative D (x' + y') = a • x' + b • y' := by
      funext o
      change D (x' o + y' o) = a * x' o + b * y' o
      have hxv : D (x' o) = a * x' o := congrFun hx' o
      have hyv : D (y' o) = b * y' o := congrFun hy' o
      rw [map_add, hxv, hyv]
    rwa [hleft, hright] at h
  have hab : a ≠ b := by
    intro heq
    have hz : (1 - a) • x + (-a) • y = 0 := by
      funext o
      have hs := congrFun hsum o
      have hd := congrFun hdiff o
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs hd ⊢
      rw [← heq] at hd
      have ha : a * (x o + y o) = x o := by rw [hs]; linear_combination -hd
      linear_combination -ha
    obtain ⟨h₁, h₂⟩ := hind _ _ hz
    have ha : a = 0 := neg_eq_zero.mp h₂
    exact (one_ne_zero : (1 : E) ≠ 0) (by simpa [ha] using h₁)
  have hden : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨hab, ?_, ?_⟩
  · funext o
    have hs := congrFun hsum o
    have hd := congrFun hdiff o
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs hd ⊢
    field_simp [hden]
    linear_combination b * hs - hd
  · funext o
    have hs := congrFun hsum o
    have hd := congrFun hdiff o
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs hd ⊢
    field_simp [hden]
    linear_combination hd - a * hs

/-- If both points on the chord avoid mixed coefficients, their sum
determines the exact unordered pair, including its affine scaling. -/
theorem unordered_eq_of_unmixed_chords
    (x y x' y' : O → E) (a b c d : E)
    (hind : ∀ r s : E, r • x + s • y = 0 → r = 0 ∧ s = 0)
    (hsum : x + y = x' + y')
    (hx' : x' = a • x + b • y) (hy' : y' = c • x + d • y)
    (hab : a = 0 ∨ b = 0) (hcd : c = 0 ∨ d = 0) :
    (x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x) := by
  have hz : (a + c - 1) • x + (b + d - 1) • y = 0 := by
    rw [hx', hy'] at hsum
    funext o
    have hs := congrFun hsum o
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs ⊢
    linear_combination -hs
  obtain ⟨hac, hbd⟩ := hind _ _ hz
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact False.elim ((neg_ne_zero.mpr (one_ne_zero : (1 : E) ≠ 0))
      (by simpa [ha, hc] using hac))
  · have hc1 : c = 1 := by simpa [ha] using sub_eq_zero.mp hac
    have hb1 : b = 1 := by simpa [hd] using sub_eq_zero.mp hbd
    right
    simpa [hx', hy', ha, hd, hc1, hb1]
  · have ha1 : a = 1 := by simpa [hc] using sub_eq_zero.mp hac
    have hd1 : d = 1 := by simpa [hb] using sub_eq_zero.mp hbd
    left
    simpa [hx', hy', hb, hc, ha1, hd1]
  · exact False.elim ((neg_ne_zero.mpr (one_ne_zero : (1 : E) ≠ 0))
      (by simpa [hb, hd] using hbd))

end Sunlet.DerivativeChords

end Source_EulerChord

section Source_RationalEmbeddingDifferentials


/-! Chain rules under arbitrary field embeddings, and equality of the
actual generic tangent ranges when all coordinate functions agree. The
algebra structures used by the chain rule are the structures induced by
the stated embedding, rather than an implicit canonical inclusion. -/

open scoped BigOperators Matrix

namespace Sunlet.RationalPartials

variable {k J O A : Type*} [Field k] [Fintype J] [DecidableEq J]
  [Fintype O] [Field A] [Algebra k A]

/-- The rational chain rule after an arbitrary base-field embedding. -/
theorem chain_rule_algHom (φ : FunctionField k J →ₐ[k] A)
    (D : Derivation k A A) (f : FunctionField k J) :
    D (φ f) = ∑ j, D (φ (coordinateVariable j)) * φ (partialDerivative j f) := by
  letI : Algebra (FunctionField k J) A := φ.toRingHom.toAlgebra
  let ψ : PolynomialRing k J →ₐ[k] A :=
    φ.comp (IsScalarTower.toAlgHom k (PolynomialRing k J) (FunctionField k J))
  letI : Algebra (PolynomialRing k J) A := ψ.toRingHom.toAlgebra
  letI : IsScalarTower k (FunctionField k J) A := IsScalarTower.of_algHom φ
  letI : IsScalarTower k (PolynomialRing k J) A := IsScalarTower.of_algHom ψ
  letI : IsScalarTower (PolynomialRing k J) (FunctionField k J) A :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact chain_rule (D.compAlgebraMap (FunctionField k J)) f

def jacobianAt (φ : FunctionField k J →ₐ[k] A) (q : O → FunctionField k J) :
    Matrix O J A := fun o j => φ (partialDerivative j (q o))

theorem derivative_coordinates_mem_range (φ : FunctionField k J →ₐ[k] A)
    (q : O → FunctionField k J) (D : Derivation k A A) :
    (fun o => D (φ (q o))) ∈ LinearMap.range (jacobianAt φ q).mulVecLin := by
  refine ⟨fun j => D (φ (coordinateVariable j)), ?_⟩
  funext o
  change ∑ j, φ (partialDerivative j (q o)) * D (φ (coordinateVariable j)) = _
  rw [chain_rule_algHom φ D]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem derivative_coordinates_basis (φ : FunctionField k J →ₐ[k] A)
    (q : O → FunctionField k J) (D : J → Derivation k A A)
    (hD : ∀ i j, D i (φ (coordinateVariable j)) = if j = i then 1 else 0) (i : J) :
    (fun o => D i (φ (q o))) = (jacobianAt φ q).mulVecLin (Pi.single i 1) := by
  funext o
  rw [chain_rule_algHom φ (D i)]
  simp [hD, jacobianAt, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Equality of the output coordinates and a full generic Jacobian force
equality of the tangent ranges for the two embeddings. Only the original
embedding needs a dual family of extended coordinate derivations. -/
theorem tangent_range_eq_of_coordinate_eq
    (φ ψ : FunctionField k J →ₐ[k] A) (q : O → FunctionField k J)
    (D : J → Derivation k A A)
    (hD : ∀ i j, D i (φ (coordinateVariable j)) = if j = i then 1 else 0)
    (hcoord : ∀ o, φ (q o) = ψ (q o))
    (hinj : Function.Injective (jacobianAt φ q).mulVecLin) :
    LinearMap.range (jacobianAt φ q).mulVecLin =
      LinearMap.range (jacobianAt ψ q).mulVecLin := by
  have hle : LinearMap.range (jacobianAt φ q).mulVecLin ≤
      LinearMap.range (jacobianAt ψ q).mulVecLin := by
    have hc : (LinearMap.range (jacobianAt ψ q).mulVecLin).comap
        (jacobianAt φ q).mulVecLin = ⊤ := by
      apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun A J)).mpr
      intro j
      change (jacobianAt φ q).mulVecLin ((Pi.basisFun A J) j) ∈
        LinearMap.range (jacobianAt ψ q).mulVecLin
      simp only [Pi.basisFun_apply]
      rw [← derivative_coordinates_basis φ q D hD j]
      simpa only [hcoord] using derivative_coordinates_mem_range ψ q (D j)
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ (LinearMap.range (jacobianAt ψ q).mulVecLin).comap
        (jacobianAt φ q).mulVecLin := by rw [hc]; trivial
    exact hv
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [LinearMap.finrank_range_of_inj hinj]
  exact (jacobianAt ψ q).mulVecLin.finrank_range_le

end Sunlet.RationalPartials

namespace Sunlet.DerivativeChords

variable {k E J O : Type*} [Field k] [Field E] [Algebra k E]
  [Fintype J] [Fintype O]

/-- Stability of matrix columns under a derivation implies stability of
their whole linear span, including coefficients depending on parameters. -/
theorem derivative_mem_range_of_columns
    (D : Derivation k E E) (M : Matrix O J E)
    (hcolumns : ∀ j, vectorDerivative D (fun o => M o j) ∈ LinearMap.range M.mulVecLin)
    (v : O → E) (hv : v ∈ LinearMap.range M.mulVecLin) :
    vectorDerivative D v ∈ LinearMap.range M.mulVecLin := by
  classical
  obtain ⟨c, rfl⟩ := hv
  have he : vectorDerivative D (M.mulVecLin c) =
      ∑ j, (D (c j) • (fun o => M o j) + c j • vectorDerivative D (fun o => M o j)) := by
    funext o
    simp only [vectorDerivative, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      map_sum, D.leibniz, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    refine ⟨Pi.single j 1, ?_⟩
    funext o
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  · exact Submodule.smul_mem _ _ (hcolumns j)

end Sunlet.DerivativeChords

end Source_RationalEmbeddingDifferentials

section Source_ToricEuler


/-! The Euler derivation scaling the first coefficient family. Its action
on the actual ratio coordinates and tangent columns is computed directly. -/

open scoped BigOperators Matrix

namespace Sunlet.ToricPairAlgebra

open NormalizedVariations ToricDifferential

variable {ι Ω k : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  [Field k] [CharZero k] (o : Ω)

def eulerVelocity : Index (ι := ι) o → FunctionField (k := k) (ι := ι) o
  | (false, .inl a) => genericCoefficient o false a
  | _ => 0

def euler : Derivation k (FunctionField (k := k) (ι := ι) o) (FunctionField (k := k) (ι := ι) o) :=
  RationalPartials.vectorDerivative (eulerVelocity o)

@[simp] theorem euler_genericCoefficient (b : Bool) (a : ι) :
    euler (k := k) o (genericCoefficient o b a) = if b then 0 else genericCoefficient o b a := by
  change RationalPartials.vectorDerivative (eulerVelocity o)
    (RationalPartials.coordinateVariable (b, Sum.inl a)) = _
  rw [RationalPartials.vectorDerivative_variable]
  cases b <;> rfl

@[simp] theorem euler_genericTorus (b : Bool) (x : Ω) :
    euler (k := k) o (genericTorus (k := k) (ι := ι) o b x).val = 0 := by
  by_cases hx : x = o
  · subst x
    simp
  · simp only [genericTorus, dif_neg hx, Units.val_mk0]
    change RationalPartials.vectorDerivative (eulerVelocity o)
      (RationalPartials.coordinateVariable (b, Sum.inr ⟨x, hx⟩)) = 0
    rw [RationalPartials.vectorDerivative_variable]
    cases b <;> rfl

def genericPoint (π : ι → Equiv.Perm Ω) (b : Bool) : ι × Ω → FunctionField (k := k) (ι := ι) o :=
  fun ax => coordinate π (genericCoefficient (k := k) o b)
    (fun x => (genericTorus (k := k) (ι := ι) o b x).val) ax.1 ax.2

theorem euler_genericPoint (π : ι → Equiv.Perm Ω) (b : Bool) :
    DerivativeChords.vectorDerivative (euler (k := k) o) (genericPoint o π b) =
      if b then 0 else genericPoint o π b := by
  funext ax
  simp only [DerivativeChords.vectorDerivative, genericPoint, coordinate, ratio,
    (euler (k := k) o).leibniz, (euler (k := k) o).leibniz_div, euler_genericCoefficient,
    euler_genericTorus, smul_eq_mul, zero_mul, sub_self, zero_div, mul_zero, add_zero]
  cases b <;> simp [genericPoint, coordinate, ratio, mul_comm]

section FieldEuler

variable {F : Type*} [Field F] [CharZero F] [Algebra k F]

theorem derivative_basisVariation (D : Derivation k F F)
    (j : NormalizedVariations.Index ι Ω o) :
    (∀ a, D ((asVariation o (Pi.single j (1 : F))).1 a) = 0) ∧
      (∀ x, D ((asVariation o (Pi.single j (1 : F))).2 x) = 0) := by
  constructor
  · intro a
    simp [asVariation, Pi.single_apply, apply_ite, apply_dite]
  · intro x
    by_cases hx : x = o <;> simp [asVariation, Pi.single_apply, hx, apply_ite, apply_dite]

theorem euler_logVelocity (D : Derivation k F F) (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hU : ∀ b a, D (U b a) = if b then 0 else U b a)
    (hh : ∀ b x, D (h b x).val = 0) (b : Bool) :
    logarithmicVelocity D (U b) (fun x => (h b x).val) =
      if b then (0, 0) else (U false, 0) := by
  cases b <;> apply Prod.ext <;> funext x <;> simp [logarithmicVelocity, hU, hh]

/-- The Euler derivation preserves every column of the combined tangent
matrix up to the scalar zero or one. Consequently it preserves its entire
range, even when tangent-vector coefficients themselves vary. -/
theorem euler_tangent_columns
    (π : ι → Equiv.Perm Ω) (D : Derivation k F F)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hU : ∀ b a, D (U b a) = if b then 0 else U b a)
    (hh : ∀ b x, D (h b x).val = 0) :
    ∀ j : Index (ι := ι) o,
      DerivativeChords.vectorDerivative D
        (fun ax => LinearMap.toMatrix' (fieldPairDifferential o π U h) ax j) ∈
      LinearMap.range (fieldPairDifferential o π U h) := by
  intro j
  rcases j with ⟨b, j⟩
  have he : (fun ax => LinearMap.toMatrix' (fieldPairDifferential o π U h) ax (b, j)) =
      differential π (U b) (fun x => (h b x).val) (asVariation o (Pi.single j 1)) := by
    funext ax
    simp only [LinearMap.toMatrix'_apply, fieldPairDifferential_single]
  rw [he]
  have hd : DerivativeChords.vectorDerivative D
      (differential π (U b) (fun x => (h b x).val) (asVariation o (Pi.single j 1))) =
      hessian π (U b) (fun x => (h b x).val)
        (logarithmicVelocity D (U b) (fun x => (h b x).val)) (asVariation o (Pi.single j 1)) := by
    funext ax
    exact derivation_differential_column D π (U b) (fun x => (h b x).val)
      (fun x => Units.ne_zero (h b x)) _ (derivative_basisVariation o D j).1
      (derivative_basisVariation o D j).2 ax.1 ax.2
  rw [hd, euler_logVelocity D U h hU hh]
  cases b
  · change hessian π (U false) (fun x => (h false x).val) (U false, 0)
      (asVariation o (Pi.single j 1)) ∈ LinearMap.range (fieldPairDifferential o π U h)
    rw [radial_hessian]
    cases j with
    | inl a =>
      have hzero : differential π (U false) (fun x => (h false x).val)
          (0, (asVariation o (Pi.single (.inl a) (1 : F))).2) = 0 := by
        funext ax
        rcases ax with ⟨c, y⟩
        simp [differential_apply, asVariation, Pi.single_apply]
      rw [hzero]
      exact Submodule.zero_mem _
    | inr x =>
      refine ⟨Pi.single (false, Sum.inr x) 1, ?_⟩
      rw [fieldPairDifferential_single]
      apply congrArg (differential π (U false) (fun y => (h false y).val))
      apply Prod.ext
      · funext a
        exact asVariation_single_coefficient o (Sum.inr x) a
      · rfl
  · change hessian π (U true) (fun x => (h true x).val) (0, 0)
      (asVariation o (Pi.single j 1)) ∈ LinearMap.range (fieldPairDifferential o π U h)
    have hzero : hessian π (U true) (fun x => (h true x).val) (0, 0)
        (asVariation o (Pi.single j 1)) = 0 := by
      ext ax
      simp [hessian]
    rw [hzero]
    exact Submodule.zero_mem _

theorem euler_tangent_range
    (π : ι → Equiv.Perm Ω) (D : Derivation k F F)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hU : ∀ b a, D (U b a) = if b then 0 else U b a)
    (hh : ∀ b x, D (h b x).val = 0)
    (v : ι × Ω → F) (hv : v ∈ LinearMap.range (fieldPairDifferential o π U h)) :
    DerivativeChords.vectorDerivative D v ∈ LinearMap.range (fieldPairDifferential o π U h) := by
  let M := LinearMap.toMatrix' (fieldPairDifferential o π U h)
  have he : M.mulVecLin = fieldPairDifferential o π U h := by
    apply LinearMap.ext
    intro z
    exact LinearMap.toMatrix'_mulVec _ z
  have hc := euler_tangent_columns o π D U h hU hh
  have hc' : ∀ j, DerivativeChords.vectorDerivative D (fun ax => M ax j) ∈
      LinearMap.range M.mulVecLin := by
    intro j
    rw [he]
    exact hc j
  rw [← he] at hv ⊢
  exact DerivativeChords.derivative_mem_range_of_columns D M hc' v hv

end FieldEuler
end Sunlet.ToricPairAlgebra

end Source_ToricEuler

section Source_ToricMovingContact


/-! Differentiating actual tangent columns along a derivation gives contact
velocities. The statement concerns the literal ratio coordinate functions,
and the proof uses the already displayed first and second derivatives. -/


namespace Sunlet.ToricPairAlgebra

open NormalizedVariations ToricDifferential

variable {ι Ω k F : Type*} [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω] [Field k] [CharZero k]
  [Field F] [CharZero F] [Algebra k F] (o : Ω)

theorem normalized_logVelocity (D : Derivation k F F)
    (U : ι → F) (h : Ω → Fˣ) (hbase : h o = 1) :
    asVariation o (coordinates o (logarithmicVelocity D U (fun x => (h x).val))) =
      logarithmicVelocity D U (fun x => (h x).val) := by
  rw [asVariation_coordinates]
  apply Prod.ext
  · rfl
  · funext x
    simp [logarithmicVelocity, hbase]

/-- Stability of an actual tangent span under a derivation forces the
parameter velocity to satisfy all contact equations. -/
theorem moving_hessian_mem
    (π : ι → Equiv.Perm Ω) (D : Derivation k F F)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (T : Submodule F (ι × Ω → F))
    (hle : LinearMap.range (fieldPairDifferential o π U h) ≤ T)
    (hstable : ∀ z ∈ T, DerivativeChords.vectorDerivative D z ∈ T)
    (b : Bool) :
    ∀ w, normalizedHessian o π (U b) (fun x => (h b x).val)
      (coordinates o (logarithmicVelocity D (U b) (fun x => (h b x).val))) w ∈ T := by
  apply hessian_mem_of_basis
  intro w
  have hcol : differential π (U b) (fun x => (h b x).val)
      (asVariation o (Pi.single w 1)) ∈ T := by
    apply hle
    refine ⟨Pi.single (b, w) 1, ?_⟩
    exact fieldPairDifferential_single o π U h b w
  have hd := hstable _ hcol
  have he : DerivativeChords.vectorDerivative D
      (differential π (U b) (fun x => (h b x).val)
        (asVariation o (Pi.single w 1))) =
      normalizedHessian o π (U b) (fun x => (h b x).val)
        (coordinates o (logarithmicVelocity D (U b) (fun x => (h b x).val)))
        (Pi.single w 1) := by
    rw [normalizedHessian_apply, normalized_logVelocity o D (U b) (h b) (hbase b)]
    funext ax
    exact derivation_differential_column D π (U b) (fun x => (h b x).val)
      (fun x => Units.ne_zero (h b x)) _
      (derivative_basisVariation o D w).1 (derivative_basisVariation o D w).2 ax.1 ax.2
  rwa [he] at hd

/-- Once the sparse contact calculation has been established, every
derivation preserving the paired tangent range acts radially on each
actual ratio point. This is the infinitesimal step for the generic
identifiability proof. -/
theorem radial_derivative_of_stable_pair
    (π : ι → Equiv.Perm Ω) (D : Derivation k F F)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (hfaithful : Function.Injective (evaluate (k := k) o U h))
    (A B : Set ι) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (a₀ : ι) (ha₀ : a₀ ∈ A)
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B)
    (hspecial : ∀ v : ToricDifferential.Variation k ι Ω, v.2 o = 0 →
      (∀ w, hessian π (sparseCoefficients A) (fun _ => 1) v w ∈
        Contact.tangentSpan π o A B) →
      ∃ lam : k, v = lam • (sparseCoefficients A, (0 : Ω → k)))
    (hstable : ∀ z ∈ LinearMap.range (fieldPairDifferential o π U h),
      DerivativeChords.vectorDerivative D z ∈
        LinearMap.range (fieldPairDifferential o π U h)) (b : Bool) :
    ∃ lam : F, DerivativeChords.vectorDerivative D
      (fun ax : ι × Ω => coordinate π (U b) (fun x => (h b x).val) ax.1 ax.2) =
      lam • (fun ax : ι × Ω => coordinate π (U b) (fun x => (h b x).val) ax.1 ax.2) := by
  let v := logarithmicVelocity D (U b) (fun x => (h b x).val)
  obtain ⟨lam, hv⟩ := radial_at_either_faithful_parameter o U h hbase hfaithful
    π A B a₀ ha₀ hdis hmoves hAtwo hBtwo hAtrans hBtrans hspecial b
    (coordinates o v) (moving_hessian_mem o π D U h hbase _ le_rfl hstable b)
  have hv' : v = lam • (U b, (0 : Ω → F)) := by
    have hh := congrArg (asVariation o) hv
    rw [normalized_logVelocity o D (U b) (h b) (hbase b), map_smul] at hh
    have hr : asVariation o (Sum.elim (U b) (fun _ => (0 : F))) =
        (U b, (0 : Ω → F)) := by
      apply Prod.ext
      · rfl
      · funext x
        by_cases hx : x = o <;> simp [asVariation, hx]
    rwa [hr] at hh
  refine ⟨lam, ?_⟩
  funext ax
  rcases ax with ⟨a, x⟩
  change D (coordinate π (U b) (fun x => (h b x).val) a x) =
    lam * coordinate π (U b) (fun x => (h b x).val) a x
  rw [derivation_coordinate D π (U b) (fun x => (h b x).val)
    (fun x => Units.ne_zero (h b x))]
  change differential π (U b) (fun x => (h b x).val) v (a, x) = _
  rw [hv', map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, differential_apply, Pi.zero_apply,
    sub_self, mul_zero, add_zero, coordinate]
  ring

end Sunlet.ToricPairAlgebra

end Source_ToricMovingContact

section Source_ContactReindex


/-! Relabelling colors and points preserves the literal ratio map, its
two-summand tangent space, and radial contact. This supplies the transport
step needed by the complete finite exceptional cases. -/


namespace Sunlet.ContactReindex

open ToricDifferential

local instance preimageDecidable {α β : Type*} (f : α → β) (A : Set β)
    [DecidablePred (· ∈ A)] : DecidablePred (· ∈ f ⁻¹' A) :=
  fun x => inferInstanceAs (Decidable (f x ∈ A))

variable {ι Ω ι' Ω' K : Type*}
  [Fintype Ω] [Fintype Ω'] [DecidableEq ι] [DecidableEq Ω]
  [DecidableEq ι'] [DecidableEq Ω'] [Field K] [CharZero K]

def variation (ec : ι' ≃ ι) (ev : Ω' ≃ Ω) :
    Variation K ι Ω ≃ₗ[K] Variation K ι' Ω' where
  toFun v := (v.1 ∘ ec, v.2 ∘ ev)
  invFun v := (v.1 ∘ ec.symm, v.2 ∘ ev.symm)
  left_inv v := by ext x <;> simp
  right_inv v := by ext x <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem variation_apply (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (v : Variation K ι Ω) : variation ec ev v = (v.1 ∘ ec, v.2 ∘ ev) := rfl

theorem scale_reindex (ev : Ω' ≃ Ω) (o : Ω) (o' : Ω') (ho : ev o' = o) (x : Ω') :
    TwoRatioRigidity.scale o (ev x) = TwoRatioRigidity.scale o' x := by
  simp [TwoRatioRigidity.scale, ← ho]

theorem ratio_reindex (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (o : Ω) (o' : Ω') (ho : ev o' = o)
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x)) (a : ι') (x : Ω') :
    TwoRatioRigidity.ratio o (π (ec a)) (ev x) = TwoRatioRigidity.ratio o' (π' a) x := by
  unfold TwoRatioRigidity.ratio
  rw [← hπ, scale_reindex ev o o' ho, scale_reindex ev o o' ho]

theorem pairDifferential_reindex (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (o : Ω) (o' : Ω') (ho : ev o' = o)
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x))
    (A B : Set ι) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (v w : Variation K ι Ω) :
    (fun ax : ι' × Ω' => Contact.pairDifferential π o A B (v, w) (ec ax.1, ev ax.2)) =
      Contact.pairDifferential π' o' (ec ⁻¹' A) (ec ⁻¹' B)
        (variation ec ev v, variation ec ev w) := by
  funext ax
  rcases ax with ⟨a, x⟩
  simp only [Contact.pairDifferential_apply, variation_apply, Function.comp_apply,
    Set.mem_preimage, hπ, ratio_reindex ec ev π π' o o' ho hπ]

theorem mem_tangentSpan_reindex (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (o : Ω) (o' : Ω') (ho : ev o' = o)
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x))
    (A B : Set ι) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (t : ι × Ω → K) (ht : t ∈ Contact.tangentSpan π o A B) :
    (fun ax : ι' × Ω' => t (ec ax.1, ev ax.2)) ∈ Contact.tangentSpan π' o' (ec ⁻¹' A) (ec ⁻¹' B) := by
  obtain ⟨⟨v, w⟩, rfl⟩ := ht
  refine ⟨(variation ec ev v, variation ec ev w), ?_⟩
  exact (pairDifferential_reindex ec ev π π' o o' ho hπ A B v w).symm

theorem hessian_reindex (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x))
    (U : ι → K) (h : Ω → K) (v w : Variation K ι Ω) :
    (fun ax => hessian π U h v w (ec ax.1, ev ax.2)) =
      hessian π' (U ∘ ec) (h ∘ ev) (variation ec ev v) (variation ec ev w) := by
  funext ax
  simp [hessian, ratio, variation_apply, hπ]

/-- An exact contact calculation in relabelled coordinates gives the same
assertion in the original color and point types. -/
theorem radial_transport (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (o : Ω) (o' : Ω') (ho : ev o' = o)
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x))
    (A B : Set ι) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hnew : ∀ v : Variation K ι' Ω', v.2 o' = 0 →
      (∀ w, hessian π' (sparseCoefficients (ec ⁻¹' A)) (fun _ => 1) v w ∈
        Contact.tangentSpan π' o' (ec ⁻¹' A) (ec ⁻¹' B)) →
      ∃ lam : K, v = lam • (sparseCoefficients (ec ⁻¹' A), (0 : Ω' → K)))
    (v : Variation K ι Ω) (hbase : v.2 o = 0)
    (hcontact : ∀ w, hessian π (sparseCoefficients A) (fun _ => 1) v w ∈
      Contact.tangentSpan π o A B) :
    ∃ lam : K, v = lam • (sparseCoefficients A, (0 : Ω → K)) := by
  have hvbase : (variation ec ev v).2 o' = 0 := by
    simpa [variation_apply, ho] using hbase
  have hnewcontact : ∀ w : Variation K ι' Ω',
      hessian π' (sparseCoefficients (ec ⁻¹' A)) (fun _ => 1) (variation ec ev v) w ∈
        Contact.tangentSpan π' o' (ec ⁻¹' A) (ec ⁻¹' B) := by
    intro w
    have hh := mem_tangentSpan_reindex ec ev π π' o o' ho hπ A B _
      (hcontact ((variation ec ev).symm w))
    rw [hessian_reindex ec ev π π' hπ, LinearEquiv.apply_symm_apply] at hh
    change hessian π' (sparseCoefficients (ec ⁻¹' A)) (fun _ => 1)
      (variation ec ev v) w ∈ Contact.tangentSpan π' o' (ec ⁻¹' A) (ec ⁻¹' B) at hh
    exact hh
  obtain ⟨lam, hlam⟩ := hnew _ hvbase hnewcontact
  refine ⟨lam, (variation ec ev).injective ?_⟩
  rw [map_smul]
  have hr : variation ec ev (sparseCoefficients A, (0 : Ω → K)) =
      (sparseCoefficients (ec ⁻¹' A), (0 : Ω' → K)) := by
    apply Prod.ext
    · funext a
      rfl
    · rfl
  rw [hr]
  exact hlam

end Sunlet.ContactReindex

end Source_ContactReindex

section Source_FiniteWordReachability


/-! Finite words of actual permutation edges certify transitivity.
The words are data; every asserted endpoint and permitted color is checked
separately before this general theorem is applied. -/


namespace Sunlet

variable {ι Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def permutationWalk (π : ι → Equiv.Perm Ω) : List ι → Ω → Ω
  | [], x => x
  | a :: w, x => permutationWalk π w (π a x)

theorem colorConnected_permutationWalk (π : ι → Equiv.Perm Ω) (A : Set ι)
    (w : List ι) (hw : ∀ a ∈ w, a ∈ A) (x : Ω) :
    ColorConnected π A x (permutationWalk π w x) := by
  induction w generalizing x with
  | nil => exact colorConnected_refl π A x
  | cons a w ih =>
    exact Relation.EqvGen.trans _ _ _
      (colorConnected_step π A (hw a (by simp)) x)
      (ih (fun b hb => hw b (by simp [hb])) (π a x))

theorem transitiveFamily_of_words (π : ι → Equiv.Perm Ω) (A : Set ι) (o : Ω)
    (w : Ω → List ι) (hcolors : ∀ x a, a ∈ w x → a ∈ A)
    (hend : ∀ x, permutationWalk π (w x) o = x) : TransitiveFamily π A := by
  have hreach : ∀ x, ColorConnected π A o x := by
    intro x
    rw [← hend x]
    exact colorConnected_permutationWalk π A (w x) (hcolors x) o
  intro x y
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hreach x)) (hreach y)

end Sunlet

end Source_FiniteWordReachability
