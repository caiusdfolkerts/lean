module
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

/- BEGIN FourPapers/Universal/CoreComplete.lean -/
section

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

/- BEGIN SimplicialPoset.lean -/
section


/-!
# Finite simplicial posets and their canonical vertex sets

The definition is precisely the Boolean-lower-interval definition in the paper.
No global embedding into a Boolean lattice is assumed: distinct faces may have
the same vertices.  The canonical vertex set of a face consists of the atoms
below it.  It determines a subface only within a fixed Boolean interval.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The paper's definition of a finite simplicial poset. -/
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop :=
  ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))

/-- The canonical vertices, as atoms in the original poset. -/
def faceVertices (p : P) : Finset P :=
  univ.filter fun a => IsAtom a ∧ a ≤ p

@[simp] theorem mem_faceVertices {p a : P} :
    a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by
  simp [faceVertices]

@[simp] theorem faceVertices_bot : faceVertices (⊥ : P) = ∅ := by
  ext a
  simp only [mem_faceVertices]
  constructor
  · rintro ⟨ha, hle⟩
    exact (ha.ne_bot (le_bot_iff.mp hle)).elim
  · intro h
    simp at h

theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by
  intro p q hpq a ha
  rcases mem_faceVertices.mp ha with ⟨hat, hap⟩
  exact mem_faceVertices.mpr ⟨hat, hap.trans hpq⟩

/-- The atom corresponding to one coordinate in a Boolean chart. -/
def chartAtom {p : P} {n : ℕ} (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) : P :=
  (e.symm {i}).val

theorem chartAtom_isAtom {p : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) : IsAtom (chartAtom e i) :=
  IsAtom.of_isAtom_coe_Iic ((e.symm.isAtom_iff {i}).mpr (Finset.isAtom_singleton i))

theorem chartAtom_le {p : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) : chartAtom e i ≤ p :=
  (e.symm {i}).property

theorem chartAtom_le_iff {p : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) (x : Set.Iic p) :
    chartAtom e i ≤ x.val ↔ i ∈ e x := by
  change e.symm {i} ≤ x ↔ i ∈ e x
  rw [← e.le_iff_le]
  simp

theorem atom_eq_chartAtom {p a : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (ha : IsAtom a) (hap : a ≤ p) :
    ∃ i : Fin n, a = chartAtom e i := by
  have hea : IsAtom (e ⟨a, hap⟩) := (e.isAtom_iff _).mpr (ha.Iic hap)
  obtain ⟨i, hi⟩ := Finset.isAtom_iff.mp hea
  refine ⟨i, ?_⟩
  have he : e.symm (e ⟨a, hap⟩) = e.symm {i} := congrArg e.symm hi
  exact congrArg Subtype.val (by simpa using he)

/-- Inside one face, inclusion of canonical vertex sets is precisely the order. -/
theorem faceVertices_subset_iff (hs : IsSimplicialPoset P) {p x y : P}
    (hxp : x ≤ p) (hyp : y ≤ p) :
    faceVertices x ⊆ faceVertices y ↔ x ≤ y := by
  constructor
  · intro h
    obtain ⟨n, ⟨e⟩⟩ := hs p
    have he : e ⟨x, hxp⟩ ⊆ e ⟨y, hyp⟩ := by
      intro i hi
      have hix : chartAtom e i ∈ faceVertices x :=
        mem_faceVertices.mpr ⟨chartAtom_isAtom e i, (chartAtom_le_iff e i _).mpr hi⟩
      exact (chartAtom_le_iff e i _).mp (mem_faceVertices.mp (h hix)).2
    exact e.le_iff_le.mp he
  · exact fun h => faceVertices_mono h

theorem faceVertices_injective_below (hs : IsSimplicialPoset P) {p x y : P}
    (hxp : x ≤ p) (hyp : y ≤ p) (h : faceVertices x = faceVertices y) : x = y := by
  exact le_antisymm ((faceVertices_subset_iff hs hxp hyp).mp h.subset)
    ((faceVertices_subset_iff hs hyp hxp).mp h.symm.subset)

/-- Every subset of the vertices of a face occurs as exactly one subface. -/
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P)
    (hsu : s ⊆ faceVertices p) :
    ∃! x : Set.Iic p, faceVertices x.val = s := by
  obtain ⟨n, ⟨e⟩⟩ := hs p
  let t : Finset (Fin n) := univ.filter fun i => chartAtom e i ∈ s
  let x : Set.Iic p := e.symm t
  have hx : faceVertices x.val = s := by
    ext a
    constructor
    · intro ha
      obtain ⟨hat, hax⟩ := mem_faceVertices.mp ha
      obtain ⟨i, rfl⟩ := atom_eq_chartAtom e hat (hax.trans x.property)
      have hit : i ∈ t := by
        simpa [x] using (chartAtom_le_iff e i x).mp hax
      exact (mem_filter.mp hit).2
    · intro ha
      obtain ⟨hat, hap⟩ := mem_faceVertices.mp (hsu ha)
      obtain ⟨i, rfl⟩ := atom_eq_chartAtom e hat hap
      refine mem_faceVertices.mpr ⟨chartAtom_isAtom e i, ?_⟩
      apply (chartAtom_le_iff e i x).mpr
      simpa [x, t] using ha
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply Subtype.ext
  exact faceVertices_injective_below hs y.property x.property (hy.trans hx.symm)

theorem faceVertices_nonempty (hs : IsSimplicialPoset P) {p : P} (hp : p ≠ ⊥) :
    (faceVertices p).Nonempty := by
  by_contra h
  have he : faceVertices p = faceVertices (⊥ : P) := by
    simpa using Finset.not_nonempty_iff_eq_empty.mp h
  exact hp (faceVertices_injective_below hs le_rfl bot_le he)

theorem faceVertices_eq_empty_iff (hs : IsSimplicialPoset P) (p : P) :
    faceVertices p = ∅ ↔ p = ⊥ := by
  constructor
  · intro h
    exact faceVertices_injective_below hs le_rfl bot_le (by simpa using h)
  · rintro rfl
    exact faceVertices_bot

/-- The rank is the number of vertices in a Boolean face. -/
def faceRank (p : P) : ℕ := (faceVertices p).card

@[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by simp [faceRank]

theorem faceRank_strictMono (hs : IsSimplicialPoset P) :
    StrictMono (faceRank : P → ℕ) := by
  intro p q hpq
  apply Finset.card_lt_card
  refine (ssubset_iff_subset_ne).mpr ⟨faceVertices_mono hpq.le, ?_⟩
  intro h
  exact hpq.ne (faceVertices_injective_below hs hpq.le le_rfl h)

theorem faceRank_eq_of_orderIso {Q : Type*} [PartialOrder Q] [OrderBot Q] [Fintype Q]
    (e : P ≃o Q) (p : P) : faceRank (e p) = faceRank p := by
  have he : faceVertices (e p) = (faceVertices p).image e := by
    ext a
    simp only [mem_faceVertices, mem_image]
    constructor
    · rintro ⟨ha, hap⟩
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      exact ⟨(e.symm.isAtom_iff a).mpr ha, by simpa using e.symm.monotone hap⟩
    · rintro ⟨b, ⟨hb, hbp⟩, rfl⟩
      exact ⟨(e.isAtom_iff b).mpr hb, e.monotone hbp⟩
  simp only [faceRank, he, Finset.card_image_iff.mpr e.injective.injOn]

end FourPapers.Universal
end
end

/- BEGIN CoherentDiagrams.lean -/
section


/-!
# Coherent comparisons and actual inverse limits

The section module is the submodule of the product consisting of compatible
families.  Coherent stalk equivalences give an actual linear equivalence on this
inverse limit and on every relative restriction kernel.  No flatness condition
appears in this argument.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

universe u v w

variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]

/-- A contravariant diagram of modules on an ordered set. -/
structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x,
    res hrq (res hqp x) = res (hrq.trans hqp) x

attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module

variable {K P}

namespace ModuleDiagram

variable (D : ModuleDiagram K P)

/-- The inverse limit, realized as compatible families in the product module. -/
def sections : Submodule K (∀ p, D.obj p) where
  carrier := {x | ∀ p q (h : q ≤ p), D.res h (x p) = x q}
  zero_mem' := by intros; simp
  add_mem' := by
    intro x y hx hy p q h
    simpa using congrArg₂ (· + ·) (hx p q h) (hy p q h)
  smul_mem' := by
    intro c x hx p q h
    simpa using congrArg (c • ·) (hx p q h)

@[simp] theorem mem_sections (x : ∀ p, D.obj p) :
    x ∈ D.sections ↔ ∀ p q (h : q ≤ p), D.res h (x p) = x q := Iff.rfl

/-- Restriction to an arbitrary subset of objects with its inherited order. -/
abbrev restrict (Q : Set P) : ModuleDiagram K Q where
  obj p := D.obj p.val
  res h := D.res h
  res_refl p x := D.res_refl p.val x
  res_comp h₁ h₂ x := D.res_comp h₁ h₂ x

/-- Restrict a compatible family. -/
def restriction (Q : Set P) : D.sections →ₗ[K] (D.restrict Q).sections where
  toFun x := ⟨fun p => x.val p.val, by
    intro p q h
    exact x.property p.val q.val h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual relative module: the kernel of restriction. -/
def relative (Q : Set P) : Submodule K D.sections :=
  LinearMap.ker (D.restriction Q)

theorem mem_relative_iff (Q : Set P) (x : D.sections) :
    x ∈ D.relative Q ↔ ∀ p ∈ Q, x.val p = 0 := by
  change D.restriction Q x = 0 ↔ _
  constructor
  · intro h p hp
    exact congrArg (fun z : (D.restrict Q).sections => z.val ⟨p, hp⟩) h
  · intro h
    apply Subtype.ext
    funext p
    exact h p.val p.property

end ModuleDiagram

/-- A coherent family of linear equivalences. -/
structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)

namespace CoherentEquiv

variable {D E F : ModuleDiagram K P}

def refl (D : ModuleDiagram K P) : CoherentEquiv D D where
  component p := LinearEquiv.refl K (D.obj p)
  naturality _ _ _ _ := rfl

def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm

def trans (e : CoherentEquiv D E) (f : CoherentEquiv E F) : CoherentEquiv D F where
  component p := (e.component p).trans (f.component p)
  naturality p q h x := by
    change F.res h (f.component p (e.component p x)) =
      f.component q (e.component q (D.res h x))
    rw [f.naturality, e.naturality]

/-- A coherent family gives an isomorphism of its actual inverse-limit modules. -/
def sectionEquiv (e : CoherentEquiv D E) : D.sections ≃ₗ[K] E.sections where
  toFun x := ⟨fun p => e.component p (x.val p), by
    intro p q h
    rw [e.naturality, x.property p q h]⟩
  invFun x := ⟨fun p => (e.component p).symm (x.val p), by
    intro p q h
    change D.res h (e.symm.component p (x.val p)) =
      e.symm.component q (x.val q)
    exact (e.symm.naturality p q h (x.val p)).trans
      (congrArg (e.symm.component q) (x.property p q h))⟩
  left_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).symm_apply_apply (x.val p)
  right_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).apply_symm_apply (x.val p)
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (e.component p) (x.val p) (y.val p)
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (e.component p) c (x.val p)

@[simp] theorem sectionEquiv_apply (e : CoherentEquiv D E)
    (x : D.sections) (p : P) :
    (e.sectionEquiv x).val p = e.component p (x.val p) := rfl

def restrict (e : CoherentEquiv D E) (Q : Set P) :
    CoherentEquiv (D.restrict Q) (E.restrict Q) where
  component p := e.component p.val
  naturality p q h x := e.naturality p.val q.val h x

/-- The inverse-limit comparison commutes with every restriction. -/
theorem restriction_naturality (e : CoherentEquiv D E) (Q : Set P) (x : D.sections) :
    E.restriction Q (e.sectionEquiv x) =
      (e.restrict Q).sectionEquiv (D.restriction Q x) := rfl

/-- The same coherent family identifies every relative restriction kernel. -/
def relativeEquiv (e : CoherentEquiv D E) (Q : Set P) :
    D.relative Q ≃ₗ[K] E.relative Q where
  toFun x := ⟨e.sectionEquiv x.val, by
    have hx := (D.mem_relative_iff Q x.val).mp x.property
    rw [ModuleDiagram.mem_relative_iff]
    intro p hp
    simp [hx p hp]⟩
  invFun x := ⟨e.sectionEquiv.symm x.val, by
    have hx := (E.mem_relative_iff Q x.val).mp x.property
    rw [ModuleDiagram.mem_relative_iff]
    intro p hp
    change (e.component p).symm (x.val.val p) = 0
    simp [hx p hp]⟩
  left_inv x := by
    apply Subtype.ext
    exact e.sectionEquiv.symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact e.sectionEquiv.apply_symm_apply x.val
  map_add' x y := by
    apply Subtype.ext
    exact map_add e.sectionEquiv x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul e.sectionEquiv c x.val

end CoherentEquiv

end FourPapers.Universal
end
end

/- BEGIN PolynomialDiagram.lean -/
section


/-!
# The actual polynomial face diagram

The stalk at a face is the polynomial ring on its atoms. Restriction kills
precisely the variables outside the smaller face. The empty face is retained,
so its stalk is the coefficient ring rather than being omitted from the limit.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- The atoms of a specified face, viewed as actual elements of the poset. -/
abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}

instance (p : P) : Fintype (FaceVertex p) := Fintype.ofFinite _

def faceVertexInclusion {p q : P} (hqp : q ≤ p) : FaceVertex q ↪ FaceVertex p where
  toFun a := ⟨a.val, a.property.1, a.property.2.trans hqp⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : FaceVertex p => a.val) h)

abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K

/-- Restriction is an algebra homomorphism, not an abstract chosen linear map. -/
def polynomialRestriction {p q : P} (hqp : q ≤ p) :
    PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0

@[simp] theorem polynomialRestriction_X {p q : P} (hqp : q ≤ p)
    (a : FaceVertex p) :
    polynomialRestriction K hqp (X a) =
      if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0 := by
  classical
  simp [polynomialRestriction]

@[simp] theorem polynomialRestriction_C {p q : P} (hqp : q ≤ p) (c : K) :
    polynomialRestriction K hqp (C c) = C c := by
  simp [polynomialRestriction]

theorem polynomialRestriction_refl (p : P) :
    polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  simp [a.property.2]

theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) =
      polynomialRestriction K (hrq.trans hqp) := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  by_cases hq : a.val ≤ q
  · by_cases hr : a.val ≤ r <;> simp [hq, hr]
  · have hr : ¬ a.val ≤ r := fun h => hq (h.trans hrq)
    simp [hq, hr]

/-- Inclusion of a smaller polynomial ring is a section of face restriction. -/
theorem polynomialRestriction_rename {p q : P} (hqp : q ≤ p) :
    (polynomialRestriction K hqp).comp (rename (faceVertexInclusion hqp)) =
      AlgHom.id K (PolynomialStalk K q) := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, MvPolynomial.rename_X, AlgHom.id_apply]
  rw [polynomialRestriction_X]
  change (if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0) = X a
  rw [dif_pos a.property.2]

theorem polynomialRestriction_surjective {p q : P} (hqp : q ≤ p) :
    Function.Surjective (polynomialRestriction K hqp) := by
  intro f
  exact ⟨rename (faceVertexInclusion hqp) f,
    DFunLike.congr_fun (polynomialRestriction_rename K hqp) f⟩

/-- The polynomial rings and their actual face restrictions form a diagram. -/
abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f

/-- On a stalk, the universal rank parameters are elementary symmetric polynomials. -/
def polynomialParameter (p : P) (i : ℕ) : PolynomialStalk K p :=
  MvPolynomial.esymm (FaceVertex p) K i

/-- The top parameter is the product of every atom variable. -/
def polynomialTop (p : P) : PolynomialStalk K p :=
  ∏ a : FaceVertex p, X a

theorem polynomialTop_regular (p : P) : IsRegular (polynomialTop K p) :=
  MvPolynomial.isRegular_prod_X Finset.univ

theorem polynomialTop_mul_injective (p : P) :
    Function.Injective (fun f : PolynomialStalk K p => polynomialTop K p * f) :=
  (polynomialTop_regular K p).left

theorem polynomialTop_eq_parameter (p : P) :
    polynomialTop K p = polynomialParameter K p (Fintype.card (FaceVertex p)) := by
  classical
  unfold polynomialTop polynomialParameter MvPolynomial.esymm
  rw [← Finset.card_univ (α := FaceVertex p), Finset.powersetCard_self]
  simp

/-- Every proper subface omits an atom, even if the poset has repeated vertex sets
on distinct incomparable faces. Only the Boolean interval below the given face is used. -/
theorem exists_atom_not_le (hs : IsSimplicialPoset P) {p q : P} (hqp : q < p) :
    ∃ a : FaceVertex p, ¬ a.val ≤ q := by
  by_contra h
  push Not at h
  have hsub : faceVertices p ⊆ faceVertices q := by
    intro a ha
    obtain ⟨hat, hap⟩ := mem_faceVertices.mp ha
    exact mem_faceVertices.mpr ⟨hat, h ⟨a, hat, hap⟩⟩
  exact hqp.not_ge ((faceVertices_subset_iff hs le_rfl hqp.le).mp hsub)

theorem polynomialRestriction_top (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q < p) : polynomialRestriction K hqp.le (polynomialTop K p) = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_atom_not_le hs hqp
  simp only [polynomialTop, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [ha]

end FourPapers.Universal
end
end

/- BEGIN FaceRingPresentation.lean -/
section


/-!
# The original face-ring presentations

Both rings below are quotients of polynomial rings by their conventional
relations. In particular, the polynomial face ring is not defined to be the
barycentric module. Its comparison with the inverse-limit polynomial diagram
is a further theorem to establish.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}

instance : Fintype (NonzeroFace P) := Fintype.ofFinite _

/-- The meet of two faces in a specified common Boolean upper interval. -/
def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val

theorem faceMeetBelow_le_top (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceMeetBelow hs p q w hpw hqw ≤ w :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).property

theorem faceMeetBelow_vertices (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceVertices (faceMeetBelow hs p q w hpw hqw) = faceVertices p ∩ faceVertices q :=
  (existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose_spec.1

theorem faceMeetBelow_le_left (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceMeetBelow hs p q w hpw hqw ≤ p := by
  apply (faceVertices_subset_iff hs (faceMeetBelow_le_top hs p q w hpw hqw) hpw).mp
  rw [faceMeetBelow_vertices]
  exact Finset.inter_subset_left

theorem faceMeetBelow_le_right (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceMeetBelow hs p q w hpw hqw ≤ q := by
  apply (faceVertices_subset_iff hs (faceMeetBelow_le_top hs p q w hpw hqw) hqw).mp
  rw [faceMeetBelow_vertices]
  exact Finset.inter_subset_right

theorem le_faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) {a : P} (hap : a ≤ p) (haq : a ≤ q) :
    a ≤ faceMeetBelow hs p q w hpw hqw := by
  apply (faceVertices_subset_iff hs (hap.trans hpw)
    (faceMeetBelow_le_top hs p q w hpw hqw)).mp
  rw [faceMeetBelow_vertices]
  exact Finset.subset_inter (faceVertices_mono hap) (faceVertices_mono haq)

/-- The chosen common upper face does not affect the meet. -/
theorem faceMeetBelow_independent (hs : IsSimplicialPoset P) (p q w w' : P)
    (hpw : p ≤ w) (hqw : q ≤ w) (hpw' : p ≤ w') (hqw' : q ≤ w') :
    faceMeetBelow hs p q w hpw hqw = faceMeetBelow hs p q w' hpw' hqw' := by
  apply le_antisymm
  · exact le_faceMeetBelow hs p q w' hpw' hqw'
      (faceMeetBelow_le_left hs p q w hpw hqw)
      (faceMeetBelow_le_right hs p q w hpw hqw)
  · exact le_faceMeetBelow hs p q w hpw hqw
      (faceMeetBelow_le_left hs p q w' hpw' hqw')
      (faceMeetBelow_le_right hs p q w' hpw' hqw')

def IsMinimalCommonUpper (p q w : P) : Prop :=
  p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w

def minimalCommonUppers (p q : P) : Finset P :=
  univ.filter (IsMinimalCommonUpper p q)

@[simp] theorem mem_minimalCommonUppers (p q w : P) :
    w ∈ minimalCommonUppers p q ↔ IsMinimalCommonUpper p q w := by
  simp [minimalCommonUppers]

variable (K : Type*) [CommRing K]

abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K

/-- The bottom-face symbol is the scalar one, as in the original definition. -/
def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩

@[simp] theorem faceSymbol_bot : faceSymbol (P := P) K ⊥ = 1 := by
  simp [faceSymbol]

@[simp] theorem faceSymbol_nonzero (p : NonzeroFace P) :
    faceSymbol K p.val = X p := by
  simp [faceSymbol, p.property]

/-- All conventional straightening relations, with no additional relations.
Common-upper witnesses give the same meet, by the independence theorem above. -/
def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) :=
  {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w),
      f = faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨
    (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧
      f = faceSymbol K p * faceSymbol K q)}

def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span (faceRelations K hs)

/-- Stanley's face ring of the original simplicial poset. -/
abbrev FaceRing (hs : IsSimplicialPoset P) :=
  FacePolynomial (P := P) K ⧸ faceIdeal K hs

/-- The Stanley--Reisner ideal of the order complex, generated by incomparable pairs. -/
def barycentricIdeal : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span {f | ∃ p q : NonzeroFace P,
    ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}

abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K

def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)

def barycentricGenerator (p : P) : BarycentricRing (P := P) K :=
  Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)

/-- The universal parameters are sums of the actual rank-i face generators. -/
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p

def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p

def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs :=
  MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)

def barycentricParameterAction (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K :=
  MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)

end FourPapers.Universal

end
end

/- BEGIN RankWeight.lean -/
section


/-!
# The exact quadratic rank-weight filtration

The paper assigns rank `r` weight `r(2d-r)`. For a vertex exponent vector `a`,
the equivalent expression is `2d |a| - Σᵥ,𝓌 min(aᵥ,a𝓌)`. The overlap cost is
superadditive, so the rank weight is subadditive under polynomial multiplication.
These are the actual quadratic weights, not a replacement degree filtration.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

variable {V : Type*} [Fintype V]

def vertexDegree (a : V → ℕ) : ℕ := ∑ v, a v

def overlapCost (a : V → ℕ) : ℕ := ∑ v, ∑ w, min (a v) (a w)

def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)

def polynomialRankWeight (d : ℕ) (a : V → ℕ) : ℤ :=
  2 * (d : ℤ) * (vertexDegree a : ℤ) - (overlapCost a : ℤ)

@[simp] theorem vertexDegree_add (a b : V → ℕ) :
    vertexDegree (a + b) = vertexDegree a + vertexDegree b := by
  simp [vertexDegree, Finset.sum_add_distrib]

theorem min_add_superadditive (a b c d : ℕ) :
    min a b + min c d ≤ min (a + c) (b + d) :=
  le_min (add_le_add (min_le_left _ _) (min_le_left _ _))
    (add_le_add (min_le_right _ _) (min_le_right _ _))

theorem overlapCost_superadditive (a b : V → ℕ) :
    overlapCost a + overlapCost b ≤ overlapCost (a + b) := by
  calc
    overlapCost a + overlapCost b =
        ∑ v, ∑ w, (min (a v) (a w) + min (b v) (b w)) := by
      simp [overlapCost, Finset.sum_add_distrib]
    _ ≤ overlapCost (a + b) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact min_add_superadditive (a v) (a w) (b v) (b w)

theorem overlapCost_le_card_mul_degree (a : V → ℕ) :
    overlapCost a ≤ Fintype.card V * vertexDegree a := by
  calc
    overlapCost a ≤ ∑ v : V, ∑ _w : V, a v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum (fun w hw => min_le_left _ _)
    _ = Fintype.card V * vertexDegree a := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      rfl

theorem polynomialRankWeight_subadditive (d : ℕ) (a b : V → ℕ) :
    polynomialRankWeight d (a + b) ≤
      polynomialRankWeight d a + polynomialRankWeight d b := by
  have hc : (overlapCost a : ℤ) + overlapCost b ≤ overlapCost (a + b) := by
    exact_mod_cast overlapCost_superadditive a b
  simp only [polynomialRankWeight, vertexDegree_add, Nat.cast_add]
  nlinarith

theorem polynomialRankWeight_nonnegative (d : ℕ) (hd : Fintype.card V ≤ d)
    (a : V → ℕ) : 0 ≤ polynomialRankWeight d a := by
  have hc : (overlapCost a : ℤ) ≤ (Fintype.card V : ℤ) * vertexDegree a := by
    exact_mod_cast overlapCost_le_card_mul_degree a
  have hd' : (Fintype.card V : ℤ) ≤ d := by exact_mod_cast hd
  have ha : (0 : ℤ) ≤ vertexDegree a := Nat.cast_nonneg _
  have hdn : (0 : ℤ) ≤ d := Nat.cast_nonneg _
  unfold polynomialRankWeight
  nlinarith

def faceIndicator (s : Finset V) (v : V) : ℕ := by
  classical
  exact if v ∈ s then 1 else 0

@[simp] theorem vertexDegree_indicator (s : Finset V) :
    vertexDegree (faceIndicator s) = s.card := by
  classical
  simp [vertexDegree, faceIndicator]

theorem overlapCost_indicator (s : Finset V) :
    overlapCost (faceIndicator s) = s.card * s.card := by
  classical
  have hmin (v w : V) :
      min (faceIndicator s v) (faceIndicator s w) =
        faceIndicator s v * faceIndicator s w := by
    by_cases hv : v ∈ s <;> by_cases hw : w ∈ s <;> simp [faceIndicator, hv, hw]
  calc
    overlapCost (faceIndicator s) =
        ∑ v, ∑ w, faceIndicator s v * faceIndicator s w := by
      simp only [overlapCost, hmin]
    _ = vertexDegree (faceIndicator s) * vertexDegree (faceIndicator s) := by
      unfold vertexDegree
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
    _ = s.card * s.card := by rw [vertexDegree_indicator]

@[simp] theorem polynomialRankWeight_indicator (d : ℕ) (s : Finset V) :
    polynomialRankWeight d (faceIndicator s) = rankWeight d s.card := by
  rw [polynomialRankWeight, vertexDegree_indicator, overlapCost_indicator]
  simp only [Nat.cast_mul, rankWeight]
  ring

variable [DecidableEq V]

/-- The exact weight drop in the Boolean straightening relation. -/
theorem rankWeight_straightening_difference (d : ℕ) (s t : Finset V) :
    rankWeight d s.card + rankWeight d t.card -
        rankWeight d (s ∩ t).card - rankWeight d (s ∪ t).card =
      2 * ((s.card : ℤ) - (s ∩ t).card) * ((t.card : ℤ) - (s ∩ t).card) := by
  classical
  have hu : ((s ∪ t).card : ℤ) + (s ∩ t).card = (s.card : ℤ) + t.card := by
    exact_mod_cast Finset.card_union_add_card_inter s t
  have hu' : ((s ∪ t).card : ℤ) = (s.card : ℤ) + t.card - (s ∩ t).card := by
    linarith
  unfold rankWeight
  rw [hu']
  ring

theorem rankWeight_straightening_strict (d : ℕ) (s t : Finset V)
    (hst : ¬ s ⊆ t) (hts : ¬ t ⊆ s) :
    rankWeight d (s ∩ t).card + rankWeight d (s ∪ t).card <
      rankWeight d s.card + rankWeight d t.card := by
  classical
  have hs : (s ∩ t).card < s.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro he
    exact hst (by rw [← he]; exact Finset.inter_subset_right)
  have ht : (s ∩ t).card < t.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro he
    exact hts (by rw [← he]; exact Finset.inter_subset_left)
  have hs' : ((s ∩ t).card : ℤ) < s.card := by exact_mod_cast hs
  have ht' : ((s ∩ t).card : ℤ) < t.card := by exact_mod_cast ht
  have hpos := mul_pos (sub_pos.mpr hs') (sub_pos.mpr ht')
  have hd := rankWeight_straightening_difference d s t
  nlinarith

end FourPapers.Universal

end
end

/- BEGIN FaceIntervals.lean -/
section


/-! # Joins inside Boolean face intervals and exact straightening weights -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The smallest common upper face inside a specified Boolean interval. -/
def faceJoinBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∪ faceVertices q)
    (Finset.union_subset (faceVertices_mono hpw) (faceVertices_mono hqw))).choose).val

theorem faceJoinBelow_le_top (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceJoinBelow hs p q w hpw hqw ≤ w :=
  ((existsUnique_subface hs w (faceVertices p ∪ faceVertices q)
    (Finset.union_subset (faceVertices_mono hpw) (faceVertices_mono hqw))).choose).property

theorem faceJoinBelow_vertices (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceVertices (faceJoinBelow hs p q w hpw hqw) = faceVertices p ∪ faceVertices q :=
  (existsUnique_subface hs w (faceVertices p ∪ faceVertices q)
    (Finset.union_subset (faceVertices_mono hpw) (faceVertices_mono hqw))).choose_spec.1

theorem left_le_faceJoinBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : p ≤ faceJoinBelow hs p q w hpw hqw := by
  apply (faceVertices_subset_iff hs hpw (faceJoinBelow_le_top hs p q w hpw hqw)).mp
  rw [faceJoinBelow_vertices]
  exact Finset.subset_union_left

theorem right_le_faceJoinBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : q ≤ faceJoinBelow hs p q w hpw hqw := by
  apply (faceVertices_subset_iff hs hqw (faceJoinBelow_le_top hs p q w hpw hqw)).mp
  rw [faceJoinBelow_vertices]
  exact Finset.subset_union_right

theorem faceJoinBelow_le (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) {u : P} (hpu : p ≤ u) (hqu : q ≤ u)
    (huw : u ≤ w) : faceJoinBelow hs p q w hpw hqw ≤ u := by
  apply (faceVertices_subset_iff hs (faceJoinBelow_le_top hs p q w hpw hqw) huw).mp
  rw [faceJoinBelow_vertices]
  exact Finset.union_subset (faceVertices_mono hpu) (faceVertices_mono hqu)

theorem faceJoinBelow_minimal (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    IsMinimalCommonUpper p q (faceJoinBelow hs p q w hpw hqw) := by
  refine ⟨left_le_faceJoinBelow hs p q w hpw hqw,
    right_le_faceJoinBelow hs p q w hpw hqw, ?_⟩
  intro v hpv hqv hv
  exact le_antisymm hv (faceJoinBelow_le hs p q w hpw hqw hpv hqv
    (hv.trans (faceJoinBelow_le_top hs p q w hpw hqw)))

theorem minimalCommonUpper_eq_join (hs : IsSimplicialPoset P) {p q u w : P}
    (hu : IsMinimalCommonUpper p q u) (huw : u ≤ w) :
    u = faceJoinBelow hs p q w (hu.1.trans huw) (hu.2.1.trans huw) := by
  symm
  exact hu.2.2 _
    (left_le_faceJoinBelow hs p q w _ _)
    (right_le_faceJoinBelow hs p q w _ _)
    (faceJoinBelow_le hs p q w _ _ hu.1 hu.2.1 huw)

theorem minimalCommonUpper_vertices (hs : IsSimplicialPoset P) {p q u : P}
    (hu : IsMinimalCommonUpper p q u) :
    faceVertices u = faceVertices p ∪ faceVertices q := by
  rw [minimalCommonUpper_eq_join hs hu le_rfl]
  exact faceJoinBelow_vertices hs p q u _ _

/-- Exactly one minimal common upper face survives restriction to a face
containing both inputs. The other minimal uppers may be genuinely different
faces with the same vertex set. -/
theorem minimalCommonUppers_below_eq_singleton (hs : IsSimplicialPoset P)
    (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) :
    (minimalCommonUppers p q).filter (· ≤ w) =
      {faceJoinBelow hs p q w hpw hqw} := by
  ext u
  simp only [Finset.mem_filter, mem_minimalCommonUppers, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, huw⟩
    exact minimalCommonUpper_eq_join hs hu huw
  · rintro rfl
    exact ⟨faceJoinBelow_minimal hs p q w hpw hqw,
      faceJoinBelow_le_top hs p q w hpw hqw⟩

/-- Rank additivity in each actual straightening relation. -/
theorem faceRank_meet_add_upper (hs : IsSimplicialPoset P) {p q u : P}
    (hu : IsMinimalCommonUpper p q u) :
    faceRank (faceMeetBelow hs p q u hu.1 hu.2.1) + faceRank u =
      faceRank p + faceRank q := by
  unfold faceRank
  rw [faceMeetBelow_vertices, minimalCommonUpper_vertices hs hu, add_comm]
  exact Finset.card_union_add_card_inter _ _

/-- The strict weight decrease uses precisely `r(2d-r)`. -/
theorem face_straightening_weight_strict (hs : IsSimplicialPoset P)
    (d : ℕ) {p q u : P} (hu : IsMinimalCommonUpper p q u)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    rankWeight d (faceRank (faceMeetBelow hs p q u hu.1 hu.2.1)) +
        rankWeight d (faceRank u) <
      rankWeight d (faceRank p) + rankWeight d (faceRank q) := by
  unfold faceRank
  rw [faceMeetBelow_vertices, minimalCommonUpper_vertices hs hu]
  apply rankWeight_straightening_strict
  · exact fun h => hpq ((faceVertices_subset_iff hs hu.1 hu.2.1).mp h)
  · exact fun h => hqp ((faceVertices_subset_iff hs hu.2.1 hu.1).mp h)

end FourPapers.Universal
end
end

/- BEGIN FaceEvaluation.lean -/
section


/-!
# Evaluation of the original face ring in its polynomial stalks

Each face generator is sent to the product of its vertex variables when the
face is contained in the stalk, and to zero otherwise. The straightening
relations are proved to vanish, so the map descends from the original quotient.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- The vertices of `q` that occur in the ambient face `p`. -/
def stalkVertexSet (p q : P) : Finset (FaceVertex p) :=
  univ.filter fun a => a.val ≤ q

@[simp] theorem mem_stalkVertexSet (p q : P) (a : FaceVertex p) :
    a ∈ stalkVertexSet p q ↔ a.val ≤ q := by simp [stalkVertexSet]

@[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by
  ext a
  simp only [mem_stalkVertexSet]
  exact iff_of_false (fun ha => a.property.1.ne_bot (le_bot_iff.mp ha)) (by simp)

def faceProduct (p q : P) : PolynomialStalk K p :=
  ∏ a ∈ stalkVertexSet p q, X a

@[simp] theorem faceProduct_bot (p : P) : faceProduct K p (⊥ : P) = 1 := by
  simp [faceProduct]

def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0

@[simp] theorem faceValue_bot (p : P) : faceValue K p (⊥ : P) = 1 := by
  simp [faceValue]

theorem stalkVertexSet_meet (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    stalkVertexSet r (faceMeetBelow hs p q w hpw hqw) =
      stalkVertexSet r p ∩ stalkVertexSet r q := by
  ext a
  simp only [mem_stalkVertexSet, mem_inter]
  constructor
  · intro h
    exact ⟨h.trans (faceMeetBelow_le_left hs p q w hpw hqw),
      h.trans (faceMeetBelow_le_right hs p q w hpw hqw)⟩
  · rintro ⟨hp, hq⟩
    exact le_faceMeetBelow hs p q w hpw hqw hp hq

theorem stalkVertexSet_join (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    stalkVertexSet r (faceJoinBelow hs p q w hpw hqw) =
      stalkVertexSet r p ∪ stalkVertexSet r q := by
  ext a
  have hm (x : P) : a.val ∈ faceVertices x ↔ a.val ≤ x := by
    simp [a.property.1]
  simp only [mem_stalkVertexSet, mem_union]
  rw [← hm, faceJoinBelow_vertices, mem_union, hm, hm]

theorem faceProduct_straightening (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceProduct K r p * faceProduct K r q =
      faceProduct K r (faceMeetBelow hs p q w hpw hqw) *
        faceProduct K r (faceJoinBelow hs p q w hpw hqw) := by
  unfold faceProduct
  rw [stalkVertexSet_meet, stalkVertexSet_join]
  exact (Finset.prod_union_inter (f := fun a : FaceVertex r => (X a : PolynomialStalk K r))).symm.trans
    (mul_comm _ _)

theorem sum_faceValue_minimalCommonUppers (hs : IsSimplicialPoset P)
    (p q r : P) (hpr : p ≤ r) (hqr : q ≤ r) :
    (∑ u ∈ minimalCommonUppers p q, faceValue K r u) =
      faceProduct K r (faceJoinBelow hs p q r hpr hqr) := by
  unfold faceValue
  rw [← Finset.sum_filter, minimalCommonUppers_below_eq_singleton hs p q r hpr hqr]
  simp

theorem sum_faceValue_minimalCommonUppers_of_not_left (p q r : P) (hpr : ¬ p ≤ r) :
    (∑ u ∈ minimalCommonUppers p q, faceValue K r u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hur : ¬ u ≤ r := fun h => hpr (((mem_minimalCommonUppers p q u).mp hu).1.trans h)
  simp [faceValue, hur]

theorem sum_faceValue_minimalCommonUppers_of_not_right (p q r : P) (hqr : ¬ q ≤ r) :
    (∑ u ∈ minimalCommonUppers p q, faceValue K r u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hur : ¬ u ≤ r := fun h => hqr (((mem_minimalCommonUppers p q u).mp hu).2.1.trans h)
  simp [faceValue, hur]

theorem faceValue_straightening (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceValue K r p * faceValue K r q =
      faceValue K r (faceMeetBelow hs p q w hpw hqw) *
        ∑ u ∈ minimalCommonUppers p q, faceValue K r u := by
  by_cases hpr : p ≤ r
  · by_cases hqr : q ≤ r
    · have hmr : faceMeetBelow hs p q w hpw hqw ≤ r :=
        (faceMeetBelow_le_left hs p q w hpw hqw).trans hpr
      rw [sum_faceValue_minimalCommonUppers K hs p q r hpr hqr]
      simp only [faceValue, if_pos hpr, if_pos hqr, if_pos hmr]
      rw [faceMeetBelow_independent hs p q w r hpw hqw hpr hqr]
      exact faceProduct_straightening K hs p q r r hpr hqr
    · rw [sum_faceValue_minimalCommonUppers_of_not_right K p q r hqr]
      simp [faceValue, hqr]
  · rw [sum_faceValue_minimalCommonUppers_of_not_left K p q r hpr]
    simp [faceValue, hpr]

/-- Evaluation before taking the original face-ring quotient. -/
def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r :=
  MvPolynomial.aeval fun p => faceValue K r p.val

@[simp] theorem faceEvaluation_symbol (r p : P) :
    faceEvaluation K r (faceSymbol K p) = faceValue K r p := by
  by_cases hp : p = ⊥
  · subst p
    simp
  · simp [faceSymbol, hp, faceEvaluation]

theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P)
    {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    faceEvaluation K r f = 0 := by
  rcases hf with ⟨p, q, w, hpw, hqw, rfl⟩ | ⟨p, q, hnone, rfl⟩
  · simp only [map_sub, map_mul, map_sum, faceEvaluation_symbol]
    exact sub_eq_zero.mpr (faceValue_straightening K hs p q w r hpw hqw)
  · simp only [map_mul, faceEvaluation_symbol]
    by_cases hpr : p ≤ r
    · have hqr : ¬ q ≤ r := fun h => hnone ⟨r, hpr, h⟩
      simp [faceValue, hqr]
    · simp [faceValue, hpr]

/-- The map is defined on the conventional face-ring presentation. -/
def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) :
    FaceRing K hs →ₐ[K] PolynomialStalk K r :=
  Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)

@[simp] theorem faceRingEvaluation_generator (hs : IsSimplicialPoset P) (r p : P) :
    faceRingEvaluation K hs r (faceRingGenerator K hs p) = faceValue K r p :=
  faceEvaluation_symbol K r p

end FourPapers.Universal
end
end

/- BEGIN MonomialQuotient.lean -/
section


/-! # The actual monomial quotient and its standard monomial basis

The quotient in this file is the quotient of the ordinary multivariate polynomial
ring by the ideal generated by its forbidden monomials.  Its basis theorem is
proved from the coefficientwise membership theorem for monomial ideals.
-/

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace FourPapers.Universal

open Classical

variable {V K : Type*} [CommRing K]

/-- An allowed collection of exponent vectors is closed under divisibility. -/
def IsDivisorClosed (P : (V →₀ ℕ) → Prop) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → P b → P a

/-- The actual ideal generated by the forbidden monomials. -/
def forbiddenIdeal (P : (V →₀ ℕ) → Prop) : Ideal (MvPolynomial V K) :=
  Ideal.span ((fun a : V →₀ ℕ => MvPolynomial.monomial a (1 : K)) '' {a | ¬ P a})

lemma mem_forbiddenIdeal (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P)
    (f : MvPolynomial V K) :
    f ∈ forbiddenIdeal P ↔ ∀ a, P a → f.coeff a = 0 := by
  rw [forbiddenIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h a ha
    by_contra hc
    obtain ⟨b, hb, hba⟩ := h a (MvPolynomial.mem_support_iff.mpr hc)
    exact hb (hP hba ha)
  · intro h a ha
    refine ⟨a, ?_, le_rfl⟩
    intro hp
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hp)

/-- The usual monomial quotient algebra. -/
abbrev MonomialQuotient (P : (V →₀ ℕ) → Prop) :=
  MvPolynomial V K ⧸ forbiddenIdeal P

/-- Read off precisely the coefficients of the allowed monomials. -/
def standardCoefficients (P : (V →₀ ℕ) → Prop) :
    MvPolynomial V K →ₗ[K] ({a // P a} →₀ K) :=
  (Finsupp.lsubtypeDomain {a | P a}).comp
    (MvPolynomial.basisMonomials V K).repr.toLinearMap

@[simp] lemma standardCoefficients_apply (P : (V →₀ ℕ) → Prop)
    (f : MvPolynomial V K) (a : {a // P a}) :
    standardCoefficients P f a = f.coeff a.val := rfl

lemma standardCoefficients_surjective (P : (V →₀ ℕ) → Prop) :
    Function.Surjective (standardCoefficients (K := K) P) := by
  intro x
  refine ⟨(MvPolynomial.basisMonomials V K).repr.symm
    (Finsupp.mapDomain Subtype.val x), ?_⟩
  change (Finsupp.lsubtypeDomain (R := K) {a | P a})
    ((MvPolynomial.basisMonomials V K).repr
      ((MvPolynomial.basisMonomials V K).repr.symm
        (Finsupp.mapDomain Subtype.val x))) = x
  rw [LinearEquiv.apply_symm_apply]
  ext a
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective x a

lemma standardCoefficients_ker (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) :
    LinearMap.ker (standardCoefficients (K := K) P) =
      (forbiddenIdeal P).restrictScalars K := by
  ext f
  rw [LinearMap.mem_ker]
  change standardCoefficients P f = 0 ↔ f ∈ forbiddenIdeal P
  rw [mem_forbiddenIdeal P hP]
  constructor
  · intro h a ha
    exact congrArg (fun c => c ⟨a, ha⟩) h
  · intro h
    ext a
    exact h a.val a.property

/-- A coefficient equivalence on the genuine quotient, not on a surrogate vector
space.  It provides the standard monomial basis over every commutative ring. -/
def standardMonomialEquiv (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    MonomialQuotient (K := K) P ≃ₗ[K] ({a // P a} →₀ K) :=
  (Submodule.quotEquivOfEq _ _ (standardCoefficients_ker (K := K) P hP).symm).trans
    ((standardCoefficients (K := K) P).quotKerEquivOfSurjective
      (standardCoefficients_surjective (K := K) P))

@[simp] lemma standardMonomialEquiv_mk (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (f : MvPolynomial V K) :
    standardMonomialEquiv P hP (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      standardCoefficients P f := by
  rfl

/-- The allowed monomials form a basis of the actual quotient. -/
def standardMonomialBasis (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    Module.Basis {a // P a} K (MonomialQuotient (K := K) P) :=
  (Finsupp.basisSingleOne).map (standardMonomialEquiv P hP).symm

@[simp] lemma standardMonomialBasis_apply (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (a : {a // P a}) :
    standardMonomialBasis (K := K) P hP a =
      Ideal.Quotient.mk (forbiddenIdeal P) (MvPolynomial.monomial a.val 1) := by
  apply (standardMonomialEquiv (K := K) P hP).injective
  ext b
  simp [standardMonomialBasis, MvPolynomial.coeff_monomial,
    Finsupp.single_apply, Subtype.ext_iff]

end FourPapers.Universal
end
end

/- BEGIN PermutationFlags.lean -/
section


/-! # Full Boolean flags, descents, and their lexicographic order

The combinatorics in this file is independent of the coefficient ring. A vertex
ordering is an actual bijection, its prefixes are actual subsets, and a descent
has its usual adjacent-value meaning.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Finset Classical

variable {V : Type*} [LinearOrder V] {n : ℕ}

/-- A full flag, written by the order in which its vertices enter. -/
abbrev VertexOrdering (n : ℕ) (V : Type*) := Fin n ≃ V

/-- The prefix of rank `c+1`. -/
def orderingPrefix (σ : VertexOrdering n V) (c : Fin n) : Finset V :=
  (Finset.Iic c).image σ

@[simp] theorem mem_orderingPrefix (σ : VertexOrdering n V) (c : Fin n) (v : V) :
    v ∈ orderingPrefix σ c ↔ σ.symm v ≤ c := by
  constructor
  · intro hv
    obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
    have hie : i = σ.symm v := by
      apply σ.injective
      simpa using hiv
    simpa [hie] using hi
  · intro hv
    exact Finset.mem_image.mpr ⟨σ.symm v, Finset.mem_Iic.mpr hv, σ.apply_symm_apply v⟩

@[simp] theorem card_orderingPrefix (σ : VertexOrdering n V) (c : Fin n) :
    (orderingPrefix σ c).card = c.val + 1 := by
  rw [orderingPrefix, Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]

theorem orderingPrefix_nonempty (σ : VertexOrdering n V) (c : Fin n) :
    (orderingPrefix σ c).Nonempty := by
  exact Finset.card_pos.mp (by rw [card_orderingPrefix]; omega)

theorem orderingPrefix_mono (σ : VertexOrdering n V) : Monotone (orderingPrefix σ) := by
  intro i j hij v hv
  exact (mem_orderingPrefix σ j v).mpr ((mem_orderingPrefix σ i v).mp hv |>.trans hij)

/-- A descent after position `c`; the last position is never a descent. -/
def IsOrderingDescent (σ : VertexOrdering n V) (c : Fin n) : Prop :=
  ∃ h : c.val + 1 < n, σ ⟨c.val + 1, h⟩ < σ c

def orderingDescents (σ : VertexOrdering n V) : Finset (Fin n) :=
  Finset.univ.filter (IsOrderingDescent σ)

@[simp] theorem mem_orderingDescents (σ : VertexOrdering n V) (c : Fin n) :
    c ∈ orderingDescents σ ↔ IsOrderingDescent σ c := by
  simp [orderingDescents]

/-- An interval containing no adjacent descent is increasing. -/
theorem ordering_le_of_no_descent {σ : VertexOrdering n V} {i j : Fin n}
    (hij : i ≤ j)
    (h : ∀ c : Fin n, i ≤ c → c < j → ¬ IsOrderingDescent σ c) :
    σ i ≤ σ j := by
  have haux : ∀ (t : ℕ) (ht : t < n), i.val ≤ t → t ≤ j.val →
      σ i ≤ σ ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero =>
      intro ht hi hj
      have he : i = ⟨0, ht⟩ := Fin.ext (Nat.eq_zero_of_le_zero hi)
      simp [he]
    | succ t ih =>
      intro ht hi hj
      by_cases hie : i.val = t + 1
      · have he : i = ⟨t + 1, ht⟩ := Fin.ext hie
        simpa [he]
      · have hit : i.val ≤ t := by omega
        have htn : t < n := by omega
        have htj : t < j.val := by omega
        have hs : σ ⟨t, htn⟩ ≤ σ ⟨t + 1, ht⟩ := by
          apply le_of_not_gt
          intro hn
          exact h ⟨t, htn⟩ hit htj ⟨ht, hn⟩
        exact (ih htn hit (by omega)).trans hs
  exact haux j.val j.isLt hij le_rfl

theorem exists_orderingDescent_between {σ : VertexOrdering n V} {i j : Fin n}
    (hij : i < j) (hval : σ j < σ i) :
    ∃ c : Fin n, i ≤ c ∧ c < j ∧ IsOrderingDescent σ c := by
  by_contra hn
  have h : ∀ c : Fin n, i ≤ c → c < j → ¬ IsOrderingDescent σ c := by
    intro c hic hcj hc
    exact hn ⟨c, hic, hcj, hc⟩
  exact (not_le_of_gt hval) (ordering_le_of_no_descent hij.le h)

/-- Fixing all descent prefixes forces an ordering to be lexicographically no
earlier than the original ordering. This is the triangularity mechanism for
the descent-monomial basis. -/
theorem ordering_lex_le_of_descent_prefix {σ τ : VertexOrdering n V}
    (hprefix : ∀ c, IsOrderingDescent σ c → orderingPrefix τ c = orderingPrefix σ c) :
    toLex (fun i => σ i) ≤ toLex (fun i => τ i) := by
  by_contra hn
  have hlt : toLex (fun i => τ i) < toLex (fun i => σ i) := lt_of_not_ge hn
  obtain ⟨i, hearlier, hval⟩ := hlt
  let j : Fin n := σ.symm (τ i)
  have hjval : σ j = τ i := σ.apply_symm_apply (τ i)
  have hij : i < j := by
    by_contra hnij
    have hji : j ≤ i := le_of_not_gt hnij
    rcases lt_or_eq_of_le hji with hji | hji
    · have he : τ j = τ i := (hearlier j hji).trans hjval
      have hje := τ.injective he
      exact (ne_of_lt hji) hje
    · have he : τ i = σ i := by simpa [hji] using hjval.symm
      exact (ne_of_lt hval) he
  have hval' : σ j < σ i := by simpa [hjval] using hval
  obtain ⟨c, hic, hcj, hc⟩ := exists_orderingDescent_between hij hval'
  have hm : τ i ∈ orderingPrefix τ c := by
    simpa only [mem_orderingPrefix, Equiv.symm_apply_apply] using hic
  rw [hprefix c hc] at hm
  have hjc : j ≤ c := (mem_orderingPrefix σ c (τ i)).mp hm
  exact (not_le_of_gt hcj) hjc

/-- The preceding triangularity yields uniqueness of the increasing-block
refinement of a partially specified flag. -/
theorem ordering_eq_of_descent_prefixes {σ τ : VertexOrdering n V}
    (hστ : ∀ c, IsOrderingDescent σ c → orderingPrefix τ c = orderingPrefix σ c)
    (hτσ : ∀ c, IsOrderingDescent τ c → orderingPrefix σ c = orderingPrefix τ c) :
    σ = τ := by
  have he := le_antisymm (ordering_lex_le_of_descent_prefix hστ)
    (ordering_lex_le_of_descent_prefix hτσ)
  apply Equiv.ext
  exact congrFun (congrArg ofLex he)

section Weights

variable [Fintype V]

/-- Order the vertices by decreasing weight, resolving equal weights by the
original vertex order. This exists for every finite vertex set, including the
empty one. -/
theorem exists_weightOrdering (w : V → ℕ) :
    ∃ σ : VertexOrdering (Fintype.card V) V,
      ∀ i j, i < j → w (σ j) < w (σ i) ∨
        (w (σ i) = w (σ j) ∧ σ i < σ j) := by
  let code : V → (OrderDual ℕ ×ₗ V) := fun v => toLex (OrderDual.toDual (w v), v)
  have hcode : Function.Injective code := by
    intro v u h
    exact congrArg (fun x => (ofLex x).2) h
  obtain ⟨σ, hσ⟩ : ∃ σ : VertexOrdering (Fintype.card V) V,
      ∀ i j, i < j → code (σ i) < code (σ j) := by
    letI : LinearOrder V := LinearOrder.lift' code hcode
    let σ := Fintype.orderIsoFinOfCardEq V rfl
    refine ⟨σ.toEquiv, ?_⟩
    intro i j hij
    exact σ.strictMono hij
  refine ⟨σ, ?_⟩
  intro i j hij
  have hlt : code (σ i) < code (σ j) := hσ i j hij
  exact Prod.Lex.toLex_lt_toLex.mp hlt

def weightOrdering (w : V → ℕ) : VertexOrdering (Fintype.card V) V :=
  Classical.choose (exists_weightOrdering w)

theorem weightOrdering_order (w : V → ℕ) {i j : Fin (Fintype.card V)} (hij : i < j) :
    w (weightOrdering w j) < w (weightOrdering w i) ∨
      (w (weightOrdering w i) = w (weightOrdering w j) ∧
        weightOrdering w i < weightOrdering w j) :=
  Classical.choose_spec (exists_weightOrdering w) i j hij

theorem weightOrdering_antitone (w : V → ℕ) :
    Antitone (fun i => w (weightOrdering w i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · rcases weightOrdering_order w hij with hw | ⟨hw, _⟩
    · exact hw.le
    · exact hw.ge
  · exact le_rfl

theorem weightOrdering_descent_lt (w : V → ℕ) {c : Fin (Fintype.card V)}
    (hc : IsOrderingDescent (weightOrdering w) c) :
    ∃ h : c.val + 1 < Fintype.card V,
      w (weightOrdering w ⟨c.val + 1, h⟩) < w (weightOrdering w c) := by
  obtain ⟨h, hc⟩ := hc
  refine ⟨h, ?_⟩
  rcases weightOrdering_order w
    (show c < ⟨c.val + 1, h⟩ from Nat.lt_succ_self c.val) with hw | ⟨hw, ho⟩
  · exact hw
  · exact (not_lt_of_gt hc ho).elim

end Weights

/-- A set whose vertices all have greater weight than its complement is an
initial segment in every decreasing-weight ordering. -/
theorem orderingPrefix_eq_of_weight_separation (w : V → ℕ)
    (σ : VertexOrdering n V) (ha : Antitone (fun i => w (σ i)))
    (F : Finset V) (c : Fin n) (hcard : F.card = c.val + 1)
    (hsep : ∀ x ∈ F, ∀ y ∉ F, w y < w x) : orderingPrefix σ c = F := by
  have hsub : F ⊆ orderingPrefix σ c := by
    intro v hv
    let j := σ.symm v
    have hp : orderingPrefix σ j ⊆ F := by
      intro u hu
      by_contra hun
      have hju : w (σ j) ≤ w (σ (σ.symm u)) :=
        ha ((mem_orderingPrefix σ j u).mp hu)
      have huv : w v ≤ w u := by simpa [j] using hju
      exact (not_le_of_gt (hsep v hv u hun)) huv
    have hcj := Finset.card_le_card hp
    rw [card_orderingPrefix, hcard] at hcj
    apply (mem_orderingPrefix σ c v).mpr
    change j ≤ c
    omega
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [card_orderingPrefix, hcard])).symm

/-- Number of specified faces containing a vertex. -/
def flagScore (C : Finset (Finset V)) (v : V) : ℕ :=
  (C.filter (fun F => v ∈ F)).card

/-- A chain separates its vertices strictly by the number of faces containing
them. This avoids any choice of a maximal refinement. -/
theorem flagScore_lt_of_mem_notMem {C : Finset (Finset V)}
    (hC : ∀ F ∈ C, ∀ G ∈ C, F ⊆ G ∨ G ⊆ F)
    {F : Finset V} (hF : F ∈ C) {x y : V} (hx : x ∈ F) (hy : y ∉ F) :
    flagScore C y < flagScore C x := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro G hG
    obtain ⟨hGC, hyG⟩ := Finset.mem_filter.mp hG
    apply Finset.mem_filter.mpr
    refine ⟨hGC, ?_⟩
    rcases hC F hF G hGC with hFG | hGF
    · exact hFG hx
    · exact (hy (hGF hyG)).elim
  · intro he
    have hxF : F ∈ C.filter (fun G => x ∈ G) := Finset.mem_filter.mpr ⟨hF, hx⟩
    rw [← he] at hxF
    exact hy (Finset.mem_filter.mp hxF).2

theorem exists_mem_notMem_of_flagScore_lt {C : Finset (Finset V)} {x y : V}
    (h : flagScore C y < flagScore C x) :
    ∃ F ∈ C, x ∈ F ∧ y ∉ F := by
  by_contra hn
  have hsub : C.filter (fun F => x ∈ F) ⊆ C.filter (fun F => y ∈ F) := by
    intro F hF
    obtain ⟨hFC, hxF⟩ := Finset.mem_filter.mp hF
    refine Finset.mem_filter.mpr ⟨hFC, ?_⟩
    by_contra hyF
    exact hn ⟨F, hFC, hxF, hyF⟩
  exact (not_le_of_gt h) (Finset.card_le_card hsub)

end FourPapers.Universal
end
end

/- BEGIN BooleanBasis.lean -/
section


/-! # Boolean barycentric rings and their color structure

All rings below are genuine quotients of multivariate polynomial rings.
The coefficient ring is arbitrary and may have positive characteristic or
zero divisors.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]

/-- Nonempty faces of the Boolean simplex on `V`. -/
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}

/-- Rank minus one, to index the rank parameters by `Fin (card V)`. -/
def BooleanFace.color (F : BooleanFace V) : Fin (Fintype.card V) :=
  ⟨F.val.card - 1, by
    have hp : 0 < F.val.card := card_pos.mpr F.property
    have hb : F.val.card ≤ Fintype.card V := card_le_univ F.val
    omega⟩

@[simp] theorem BooleanFace.color_succ (F : BooleanFace V) :
    (BooleanFace.color F).val + 1 = F.val.card := by
  have hp : 0 < F.val.card := card_pos.mpr F.property
  simp only [BooleanFace.color]
  omega

theorem BooleanFace.card_eq_of_color_eq {F G : BooleanFace V}
    (h : (BooleanFace.color F) = G.color) : F.val.card = G.val.card := by
  have hv := congrArg Fin.val h
  have hF := F.color_succ
  have hG := G.color_succ
  omega

/-- The support of a standard barycentric monomial is a chain of faces. -/
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop :=
  ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val

theorem isChainExponent_divisorClosed : IsDivisorClosed (IsChainExponent (V := V)) := by
  intro a b hab hb F hF G hG
  exact hb F (Finsupp.support_mono hab hF) G (Finsupp.support_mono hab hG)

theorem isChainExponent_zero : IsChainExponent (0 : BooleanFace V →₀ ℕ) := by
  simp [IsChainExponent]

theorem isChainExponent_single (F : BooleanFace V) (m : ℕ) :
    IsChainExponent (Finsupp.single F m) := by
  intro G hG H hH
  have hGF : G = F := ((Finsupp.mem_support_single G F m).mp hG).1
  have hHF : H = F := ((Finsupp.mem_support_single H F m).mp hH).1
  subst G
  subst H
  exact Or.inl Subset.rfl

theorem eq_of_chain_of_color_eq {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) {F G : BooleanFace V}
    (hF : F ∈ a.support) (hG : G ∈ a.support) (hc : (BooleanFace.color F) = G.color) : F = G := by
  apply Subtype.ext
  have he := BooleanFace.card_eq_of_color_eq hc
  rcases ha F hF G hG with hFG | hGF
  · exact eq_of_subset_of_card_le hFG he.ge
  · exact (eq_of_subset_of_card_le hGF he.le).symm

/-- The usual Stanley--Reisner ring of the Boolean order complex. -/
abbrev BooleanBarycentricRing (V K : Type*) [Fintype V] [DecidableEq V] [CommRing K] :=
  MonomialQuotient (K := K) (IsChainExponent (V := V))

/-- Its genuine chain-monomial coefficient basis. -/
def booleanChainBasis :
    Module.Basis {a : BooleanFace V →₀ ℕ // IsChainExponent a} K
      (BooleanBarycentricRing V K) :=
  standardMonomialBasis IsChainExponent isChainExponent_divisorClosed

def faceVariable (F : BooleanFace V) : BooleanBarycentricRing V K :=
  Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent) (MvPolynomial.X F)

theorem chainMonomial_eq_zero {a : BooleanFace V →₀ ℕ} (ha : ¬ IsChainExponent a) :
    Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent)
      (MvPolynomial.monomial a 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨a, ha, rfl⟩

theorem faceVariable_mul_eq_zero {F G : BooleanFace V}
    (h : ¬ (F.val ⊆ G.val ∨ G.val ⊆ F.val)) :
    faceVariable (K := K) F * faceVariable G = 0 := by
  have hne : F ≠ G := by
    intro he
    subst G
    exact h (Or.inl Subset.rfl)
  have hn : ¬ IsChainExponent (Finsupp.single F 1 + Finsupp.single G 1) := by
    intro hc
    apply h
    apply hc F _ G _ <;>
      simp [Finsupp.mem_support_iff, hne, Ne.symm hne]
  simpa only [faceVariable, ← map_mul, MvPolynomial.X,
    MvPolynomial.monomial_mul, one_mul] using (chainMonomial_eq_zero (K := K) hn)

theorem sameColor_faceVariable_mul_eq_zero {F G : BooleanFace V}
    (hcolor : (BooleanFace.color F) = G.color) (hne : F ≠ G) :
    faceVariable (K := K) F * faceVariable G = 0 := by
  apply faceVariable_mul_eq_zero
  intro h
  apply hne
  apply Subtype.ext
  have he := BooleanFace.card_eq_of_color_eq hcolor
  rcases h with hFG | hGF
  · exact eq_of_subset_of_card_le hFG he.ge
  · exact (eq_of_subset_of_card_le hGF he.le).symm

def facesOfColor (c : Fin (Fintype.card V)) : Finset (BooleanFace V) :=
  Finset.univ.filter (fun F => (BooleanFace.color F) = c)

@[simp] theorem mem_facesOfColor (c : Fin (Fintype.card V)) (F : BooleanFace V) :
    F ∈ facesOfColor c ↔ (BooleanFace.color F) = c := by
  simp [facesOfColor]

/-- The paper's rank color sum, with `c` representing rank `c+1`. -/
def colorSum (c : Fin (Fintype.card V)) : BooleanBarycentricRing V K :=
  ∑ F ∈ facesOfColor c, faceVariable F

theorem colorSum_mul_faceVariable (F : BooleanFace V) :
    colorSum (K := K) (BooleanFace.color F) * faceVariable F = faceVariable F ^ 2 := by
  rw [colorSum, sum_mul]
  rw [Finset.sum_eq_single F]
  · exact (pow_two _).symm
  · intro G hG hGF
    apply sameColor_faceVariable_mul_eq_zero
    · exact (mem_facesOfColor _ _).mp hG
    · exact hGF
  · intro hF
    exact (hF ((mem_facesOfColor _ _).mpr rfl)).elim

/-- The unique face of a given color in a chain absorbs every further
factor of that color sum. This is integral and involves no division. -/
theorem colorSum_pow_mul_faceVariable (F : BooleanFace V) (m : ℕ) :
    colorSum (K := K) (BooleanFace.color F) ^ m * faceVariable F = faceVariable F ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      colorSum (BooleanFace.color F) ^ (m + 1) * faceVariable F =
          colorSum (BooleanFace.color F) ^ m * (colorSum (BooleanFace.color F) * faceVariable F) := by
            rw [pow_succ, mul_assoc]
      _ = colorSum (BooleanFace.color F) ^ m * (faceVariable F * faceVariable F) := by
            rw [colorSum_mul_faceVariable, pow_two]
      _ = faceVariable F ^ (m + 1) * faceVariable F := by rw [← mul_assoc, ih]
      _ = faceVariable F ^ (m + 1 + 1) := (pow_succ _ _).symm

/-- Powers of one color sum have coefficient one on every allowed pure
power. Mixed same-color products vanish in the actual quotient. -/
theorem colorSum_pow_succ (c : Fin (Fintype.card V)) (m : ℕ) :
    colorSum (K := K) c ^ (m + 1) =
      ∑ F ∈ facesOfColor c, faceVariable F ^ (m + 1) := by
  rw [pow_succ]
  conv_lhs => rhs; unfold colorSum
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  have hc := (mem_facesOfColor _ _).mp hF
  rw [← hc]
  exact colorSum_pow_mul_faceVariable F m

section Flags

variable [LinearOrder V]

def orderingFace (σ : VertexOrdering (Fintype.card V) V)
    (c : Fin (Fintype.card V)) : BooleanFace V :=
  ⟨orderingPrefix σ c, orderingPrefix_nonempty σ c⟩

@[simp] theorem orderingFace_color (σ : VertexOrdering (Fintype.card V) V)
    (c : Fin (Fintype.card V)) : (orderingFace σ c).color = c := by
  apply Fin.ext
  simp [BooleanFace.color, orderingFace]

theorem orderingFace_injective (σ : VertexOrdering (Fintype.card V) V) :
    Function.Injective (orderingFace σ) := by
  intro i j hij
  simpa using congrArg BooleanFace.color hij

def chainFaceSet (a : BooleanFace V →₀ ℕ) : Finset (Finset V) :=
  a.support.image Subtype.val

theorem chainFaceSet_chain {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    ∀ F ∈ chainFaceSet a, ∀ G ∈ chainFaceSet a, F ⊆ G ∨ G ⊆ F := by
  intro F hF G hG
  obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
  exact ha F' hF' G' hG'

/-- The increasing-block refinement of a chain. -/
def chainOrdering (a : BooleanFace V →₀ ℕ) : VertexOrdering (Fintype.card V) V :=
  weightOrdering (flagScore (chainFaceSet a))

theorem chainOrdering_prefix {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) :
    orderingPrefix (chainOrdering a) (BooleanFace.color F) = F.val := by
  apply orderingPrefix_eq_of_weight_separation (flagScore (chainFaceSet a))
    (chainOrdering a) (weightOrdering_antitone _) F.val (BooleanFace.color F)
  · exact F.color_succ.symm
  · intro x hx y hy
    exact flagScore_lt_of_mem_notMem (chainFaceSet_chain ha)
      (Finset.mem_image.mpr ⟨F, hF, rfl⟩) hx hy

theorem chainOrdering_face {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) :
    orderingFace (chainOrdering a) (BooleanFace.color F) = F :=
  Subtype.ext (chainOrdering_prefix ha hF)

def chainColorDegree (a : BooleanFace V →₀ ℕ) : Fin (Fintype.card V) →₀ ℕ :=
  Finsupp.mapDomain BooleanFace.color a

theorem chainColorDegree_apply {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) : chainColorDegree a (BooleanFace.color F) = a F := by
  apply Finsupp.mapDomain_apply' (a.support : Set (BooleanFace V)) a (Set.Subset.refl _)
  · intro F hF G hG hc
    exact eq_of_chain_of_color_eq ha hF hG hc
  · exact hF

theorem chainColorDegree_support {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    (chainColorDegree a).support = a.support.image BooleanFace.color := by
  apply Finsupp.mapDomain_support_of_injOn
  intro F hF G hG hc
  exact eq_of_chain_of_color_eq ha hF hG hc

theorem chainOrdering_descents {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    orderingDescents (chainOrdering a) ⊆ (chainColorDegree a).support := by
  intro c hc
  obtain ⟨hn, hw⟩ := weightOrdering_descent_lt (flagScore (chainFaceSet a))
    ((mem_orderingDescents _ _).mp hc)
  obtain ⟨G, hG, hx, hy⟩ := exists_mem_notMem_of_flagScore_lt hw
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hG
  have hpc := chainOrdering_prefix ha hF
  have hleft : c ≤ (BooleanFace.color F) := by
    have hm : chainOrdering a c ∈ orderingPrefix (chainOrdering a) (BooleanFace.color F) := by
      rw [hpc]
      exact hx
    simpa only [mem_orderingPrefix, Equiv.symm_apply_apply] using hm
  have hright : ¬ (⟨c.val + 1, hn⟩ : Fin (Fintype.card V)) ≤ (BooleanFace.color F) := by
    intro h
    apply hy
    rw [← hpc]
    simpa only [mem_orderingPrefix, chainOrdering, Equiv.symm_apply_apply] using h
  have hcol : (BooleanFace.color F) = c := by
    apply Fin.ext
    change (BooleanFace.color F).val = c.val
    change c.val ≤ (BooleanFace.color F).val at hleft
    change ¬ c.val + 1 ≤ (BooleanFace.color F).val at hright
    omega
  rw [chainColorDegree_support ha]
  exact Finset.mem_image.mpr ⟨F, hF, hcol⟩

/-- Put the prescribed multiplicity at each prefix of a full flag. -/
def prefixExponent (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) : BooleanFace V →₀ ℕ :=
  Finsupp.mapDomain (orderingFace σ) m

@[simp] theorem prefixExponent_support (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) :
    (prefixExponent σ m).support = m.support.image (orderingFace σ) :=
  Finsupp.mapDomain_support_of_injective (orderingFace_injective σ) m

theorem prefixExponent_isChain (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) : IsChainExponent (prefixExponent σ m) := by
  intro F hF G hG
  rw [prefixExponent_support] at hF hG
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
  rcases le_total i j with hij | hji
  · exact Or.inl (orderingPrefix_mono σ hij)
  · exact Or.inr (orderingPrefix_mono σ hji)

@[simp] theorem chainColorDegree_prefixExponent
    (σ : VertexOrdering (Fintype.card V) V) (m : Fin (Fintype.card V) →₀ ℕ) :
    chainColorDegree (prefixExponent σ m) = m := by
  rw [chainColorDegree, prefixExponent, ← Finsupp.mapDomain_fun_comp]
  simp only [orderingFace_color, Finsupp.mapDomain_fun_id]

theorem prefixExponent_chainColorDegree {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) :
    prefixExponent (chainOrdering a) (chainColorDegree a) = a := by
  rw [prefixExponent, chainColorDegree, ← Finsupp.mapDomain_fun_comp]
  calc
    Finsupp.mapDomain (fun F => orderingFace (chainOrdering a) (BooleanFace.color F)) a =
        Finsupp.mapDomain id a := by
          apply Finsupp.mapDomain_congr
          intro F hF
          exact chainOrdering_face ha hF
    _ = a := Finsupp.mapDomain_id

theorem chainOrdering_prefixExponent
    (σ : VertexOrdering (Fintype.card V) V) (m : Fin (Fintype.card V) →₀ ℕ)
    (hdesc : orderingDescents σ ⊆ m.support) :
    chainOrdering (prefixExponent σ m) = σ := by
  let a := prefixExponent σ m
  have ha : IsChainExponent a := prefixExponent_isChain σ m
  have hp : ∀ c ∈ m.support,
      orderingPrefix (chainOrdering a) c = orderingPrefix σ c := by
    intro c hc
    have hF : orderingFace σ c ∈ a.support := by
      rw [prefixExponent_support]
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have h := chainOrdering_prefix ha hF
    change orderingPrefix (chainOrdering a) (BooleanFace.color (orderingFace σ c)) =
      (orderingFace σ c).val at h
    rw [orderingFace_color] at h
    change orderingPrefix (chainOrdering a) c = orderingPrefix σ c at h
    exact h
  apply ordering_eq_of_descent_prefixes
  · intro c hc
    apply (hp c _).symm
    have hm := chainOrdering_descents ha ((mem_orderingDescents _ _).mpr hc)
    simpa only [a, chainColorDegree_prefixExponent] using hm
  · intro c hc
    exact hp c (hdesc ((mem_orderingDescents _ _).mpr hc))

/-- The full flag decomposition of every standard monomial, including all
multiplicities and the exact descent restriction. -/
def chainFlagEquiv :
    {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃
      {p : VertexOrdering (Fintype.card V) V × (Fin (Fintype.card V) →₀ ℕ) //
        orderingDescents p.1 ⊆ p.2.support} where
  toFun a := ⟨(chainOrdering a.val, chainColorDegree a.val), chainOrdering_descents a.property⟩
  invFun p := ⟨prefixExponent p.val.1 p.val.2, prefixExponent_isChain _ _⟩
  left_inv a := Subtype.ext (prefixExponent_chainColorDegree a.property)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact chainOrdering_prefixExponent _ _ p.property
    · exact chainColorDegree_prefixExponent _ _

end Flags

end FourPapers.Universal
end
end

/- BEGIN FaceBooleanInterval.lean -/
section


/-! # The canonical Boolean chart on the actual vertices of a face -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- Extending the actual local vertex subset recovers precisely the global
canonical vertex set, when the face lies below the ambient face. -/
theorem image_stalkVertexSet {p q : P} (hqp : q ≤ p) :
    (stalkVertexSet p q).image Subtype.val = faceVertices q := by
  ext a
  simp only [Finset.mem_image, mem_stalkVertexSet, mem_faceVertices]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property.1, hv⟩
  · rintro ⟨ha, haq⟩
    exact ⟨⟨a, ha, haq.trans hqp⟩, haq, rfl⟩

theorem stalkVertexSet_subset_iff (hs : IsSimplicialPoset P) {p q r : P}
    (hqp : q ≤ p) (hrp : r ≤ p) :
    stalkVertexSet p q ⊆ stalkVertexSet p r ↔ q ≤ r := by
  constructor
  · intro h
    apply (faceVertices_subset_iff hs hqp hrp).mp
    rw [← image_stalkVertexSet hqp, ← image_stalkVertexSet hrp]
    exact Finset.image_subset_image h
  · intro h a ha
    exact (mem_stalkVertexSet p r a).mpr (((mem_stalkVertexSet p q a).mp ha).trans h)

def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose

theorem subfaceOfVertexSet_vertices (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) :
    faceVertices (subfaceOfVertexSet hs p s).val = s.image Subtype.val :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose_spec.1

theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) :
    stalkVertexSet p (subfaceOfVertexSet hs p s).val = s := by
  have h := (image_stalkVertexSet (subfaceOfVertexSet hs p s).property).trans
    (subfaceOfVertexSet_vertices hs p s)
  exact Finset.image_injective Subtype.val_injective h

def faceBooleanInterval (hs : IsSimplicialPoset P) (p : P) :
    Set.Iic p ≃o Finset (FaceVertex p) where
  toFun q := stalkVertexSet p q.val
  invFun := subfaceOfVertexSet hs p
  left_inv q := by
    apply Subtype.ext
    apply faceVertices_injective_below hs (subfaceOfVertexSet hs p _).property q.property
    rw [subfaceOfVertexSet_vertices, image_stalkVertexSet q.property]
  right_inv := stalkVertexSet_subfaceOfVertexSet hs p
  map_rel_iff' := by
    intro q r
    exact stalkVertexSet_subset_iff hs q.property r.property

/-- Nonempty Boolean faces embed as actual nonzero subfaces of the original
poset. The embedding is confined to this Boolean interval. -/
def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) :
    BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun F := ⟨(subfaceOfVertexSet hs p F.val).val, by
    intro hbot
    have he := stalkVertexSet_subfaceOfVertexSet hs p F.val
    rw [hbot, stalkVertexSet_bot] at he
    exact F.property.ne_empty he.symm⟩
  inj' F G h := by
    apply Subtype.ext
    have he : (subfaceOfVertexSet hs p F.val).val =
        (subfaceOfVertexSet hs p G.val).val := congrArg (fun z : NonzeroFace P => z.val) h
    have hv := congrArg (stalkVertexSet p) he
    simpa only [stalkVertexSet_subfaceOfVertexSet] using hv

theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P)
    (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p :=
  (subfaceOfVertexSet hs p F.val).property

@[simp] theorem stalkVertexSet_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) (F : BooleanFace (FaceVertex p)) :
    stalkVertexSet p (booleanFaceInclusion hs p F).val = F.val :=
  stalkVertexSet_subfaceOfVertexSet hs p F.val

theorem booleanFaceInclusion_le_iff (hs : IsSimplicialPoset P) (p : P)
    (F G : BooleanFace (FaceVertex p)) :
    (booleanFaceInclusion hs p F).val ≤ (booleanFaceInclusion hs p G).val ↔ F.val ⊆ G.val := by
  rw [← stalkVertexSet_subset_iff hs (booleanFaceInclusion_le hs p F)
    (booleanFaceInclusion_le hs p G)]
  simp only [stalkVertexSet_booleanFaceInclusion]

end FourPapers.Universal
end
end

/- BEGIN BarycentricPresentation.lean -/
section


/-! # Chain monomials in the actual barycentric face ring -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- Exponents whose positive support is a chain of nonzero faces. -/
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop :=
  ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val

theorem barycentricAllowed_divisorClosed :
    IsDivisorClosed (BarycentricAllowed (P := P)) := by
  intro a b hab hb p hp q hq
  exact hb p (Finsupp.support_mono hab hp) q (Finsupp.support_mono hab hq)

theorem incomparable_pair_forbidden (p q : NonzeroFace P)
    (hpq : ¬ p.val ≤ q.val) (hqp : ¬ q.val ≤ p.val) :
    ¬ BarycentricAllowed (Finsupp.single p 1 + Finsupp.single q 1) := by
  have hne : p ≠ q := by rintro rfl; exact hpq le_rfl
  intro h
  have hp : p ∈ (Finsupp.single p 1 + Finsupp.single q 1).support := by
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne, Ne.symm hne]
  have hq : q ∈ (Finsupp.single p 1 + Finsupp.single q 1).support := by
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne, Ne.symm hne]
  exact (h p hp q hq).elim hpq hqp

theorem incomparable_pair_le {a : NonzeroFace P →₀ ℕ} (p q : NonzeroFace P)
    (hp : p ∈ a.support) (hq : q ∈ a.support) (hpq : p ≠ q) :
    Finsupp.single p 1 + Finsupp.single q 1 ≤ a := by
  intro v
  by_cases hvp : v = p
  · subst v
    simpa [Finsupp.single_apply, hpq, Ne.symm hpq] using
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  · by_cases hvq : v = q
    · subst v
      simpa [Finsupp.single_apply, hpq, Ne.symm hpq] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq)
    · simp [Finsupp.single_apply, hvp, hvq, Ne.symm hvp, Ne.symm hvq]

/-- The ordinary incomparable-pair presentation is exactly the forbidden-
monomial ideal. Thus the quotient basis is a theorem about the original ring. -/
theorem barycentricIdeal_eq_forbiddenIdeal :
    barycentricIdeal (P := P) K =
      forbiddenIdeal (K := K) (BarycentricAllowed (P := P)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨p, q, hpq, hqp, rfl⟩
    apply Ideal.subset_span
    refine ⟨Finsupp.single p 1 + Finsupp.single q 1,
      incomparable_pair_forbidden p q hpq hqp, ?_⟩
    simp [MvPolynomial.X, MvPolynomial.monomial_mul]
  · apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    unfold BarycentricAllowed at ha
    push Not at ha
    obtain ⟨p, hp, q, hq, hpq, hqp⟩ := ha
    have hne : p ≠ q := by rintro rfl; exact hpq le_rfl
    have hle := incomparable_pair_le p q hp hq hne
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hpair : (X p * X q : FacePolynomial (P := P) K) ∈ barycentricIdeal K :=
      Ideal.subset_span ⟨p, q, hpq, hqp, rfl⟩
    have hm : (MvPolynomial.monomial a (1 : K)) =
        (X p * X q) * MvPolynomial.monomial c 1 := by
      rw [hc]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul, add_assoc]
    change MvPolynomial.monomial a (1 : K) ∈ barycentricIdeal K
    rw [hm]
    exact Ideal.mul_mem_right _ _ hpair

end FourPapers.Universal

end
end

/- BEGIN StandardCarriers.lean -/
section


/-! # The smallest supporting face of an actual standard face monomial

The carrier is a face of the original poset, not merely its vertex set. Thus
repeated vertex sets on different faces are distinguished throughout.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] :=
  {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}

/-- Choose the largest-rank face in the chain, or the bottom face for the
empty chain. The following theorem characterizes this choice intrinsically. -/
def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥

theorem standardCarrier_le_iff (hs : IsSimplicialPoset P)
    (a : StandardFaceIndex P) (p : P) :
    standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by
  by_cases h : a.val.support.Nonempty
  · let q := (Finset.exists_max_image a.val.support
      (fun q : NonzeroFace P => faceRank q.val) h).choose
    have hq : q ∈ a.val.support :=
      (Finset.exists_max_image a.val.support
        (fun q : NonzeroFace P => faceRank q.val) h).choose_spec.1
    have hmax : ∀ r ∈ a.val.support, faceRank r.val ≤ faceRank q.val :=
      (Finset.exists_max_image a.val.support
        (fun q : NonzeroFace P => faceRank q.val) h).choose_spec.2
    have hrq : ∀ r ∈ a.val.support, r.val ≤ q.val := by
      intro r hr
      rcases a.property r hr q hq with hle | hge
      · exact hle
      · by_contra hn
        have hlt : q.val < r.val := lt_of_le_of_ne hge (Ne.symm (ne_of_not_le hn))
        exact (not_lt_of_ge (hmax r hr)) (faceRank_strictMono hs hlt)
    simp only [standardCarrier, dif_pos h]
    constructor
    · intro hqp r hr
      exact (hrq r hr).trans hqp
    · intro hall
      exact hall q hq
  · have he : a.val.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [standardCarrier, h, he]

theorem standardCarrier_mem_or_bot (a : StandardFaceIndex P) :
    standardCarrier a = ⊥ ∨ ∃ q ∈ a.val.support, standardCarrier a = q.val := by
  by_cases h : a.val.support.Nonempty
  · right
    let q := (Finset.exists_max_image a.val.support
      (fun q : NonzeroFace P => faceRank q.val) h).choose
    exact ⟨q, (Finset.exists_max_image a.val.support
      (fun q : NonzeroFace P => faceRank q.val) h).choose_spec.1,
      by simp [standardCarrier, h, q]⟩
  · exact Or.inl (by simp [standardCarrier, h])

theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P)
    (p : P) (q : NonzeroFace P) :
    q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by
  constructor
  · rintro ⟨F, rfl⟩
    exact booleanFaceInclusion_le hs p F
  · intro hqp
    have hn : (stalkVertexSet p q.val).Nonempty := by
      obtain ⟨v, hv⟩ := faceVertices_nonempty hs q.property
      obtain ⟨ha, haq⟩ := mem_faceVertices.mp hv
      exact ⟨⟨v, ha, haq.trans hqp⟩, (mem_stalkVertexSet p q.val ⟨v, ha, haq.trans hqp⟩).mpr haq⟩
    refine ⟨⟨stalkVertexSet p q.val, hn⟩, ?_⟩
    apply Subtype.ext
    apply faceVertices_injective_below hs
      (booleanFaceInclusion_le hs p _) hqp
    rw [← image_stalkVertexSet (booleanFaceInclusion_le hs p _),
      stalkVertexSet_booleanFaceInclusion, image_stalkVertexSet hqp]

theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) :
    BarycentricAllowed (a.mapDomain (booleanFaceInclusion hs p)) := by
  intro q hq r hr
  rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq hr
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hr
  rcases ha F hF G hG with hFG | hGF
  · exact Or.inl ((booleanFaceInclusion_le_iff hs p F G).mpr hFG)
  · exact Or.inr ((booleanFaceInclusion_le_iff hs p G F).mpr hGF)

theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) :
    IsChainExponent (a.comapDomain (booleanFaceInclusion hs p)
      (booleanFaceInclusion hs p).injective.injOn) := by
  intro F hF G hG
  have hFa : booleanFaceInclusion hs p F ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hF
  have hGa : booleanFaceInclusion hs p G ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hG
  rcases ha _ hFa _ hGa with hFG | hGF
  · exact Or.inl ((booleanFaceInclusion_le_iff hs p F G).mp hFG)
  · exact Or.inr ((booleanFaceInclusion_le_iff hs p G F).mp hGF)

abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}

/-- This is an exact equivalence of exponent indices, derived from the
canonical Boolean interval. No global Boolean-lattice embedding is assumed. -/
def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) :
    {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
  toFun a := ⟨⟨a.val.mapDomain (booleanFaceInclusion hs p),
    standardExponent_map_booleanFaceInclusion hs p a.property⟩, by
      apply (standardCarrier_le_iff hs _ p).mpr
      intro q hq
      rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact booleanFaceInclusion_le hs p F⟩
  invFun a := ⟨a.val.val.comapDomain (booleanFaceInclusion hs p)
    (booleanFaceInclusion hs p).injective.injOn,
    chainExponent_comap_booleanFaceInclusion hs p a.val.property⟩
  left_inv a := Subtype.ext
    (Finsupp.comapDomain_mapDomain _ (booleanFaceInclusion hs p).injective a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.mapDomain_comapDomain _ (booleanFaceInclusion hs p).injective
    intro q hq
    exact (booleanFaceInclusion_range_iff hs p q).mpr
      ((standardCarrier_le_iff hs a.val p).mp a.property q hq)

end FourPapers.Universal
end
end

/- BEGIN MonomialRestriction.lean -/
section


/-!
# Genuine face restrictions on monomial quotient rings

An embedding of variable sets gives a restriction homomorphism by killing its
complement. The compatibility hypothesis concerns only the two specified sets
of allowed exponents; no quotient is identified with a formal surrogate.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

variable {V W K : Type*} [CommRing K]

theorem killCompl_mem_forbiddenIdeal
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e))
    {f : MvPolynomial W K} (hf : f ∈ forbiddenIdeal P) :
    MvPolynomial.killCompl e.injective f ∈ forbiddenIdeal Q := by
  rw [mem_forbiddenIdeal Q hQ]
  intro a ha
  rw [MvPolynomial.coeff_killCompl]
  exact (mem_forbiddenIdeal P hP f).mp hf (a.mapDomain e) (allowed a ha)

/-- Restriction between the actual quotient algebras. -/
def monomialRestriction
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e)) :
    MonomialQuotient (K := K) P →ₐ[K] MonomialQuotient (K := K) Q :=
  Ideal.Quotient.liftₐ (forbiddenIdeal P)
    ((Ideal.Quotient.mkₐ K (forbiddenIdeal Q)).comp
      (MvPolynomial.killCompl e.injective)) (by
        intro f hf
        change Ideal.Quotient.mk (forbiddenIdeal Q)
          (MvPolynomial.killCompl e.injective f) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (killCompl_mem_forbiddenIdeal e P Q hP hQ allowed hf))

@[simp] theorem monomialRestriction_mk
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e)) (f : MvPolynomial W K) :
    monomialRestriction e P Q hP hQ allowed (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      Ideal.Quotient.mk (forbiddenIdeal Q) (MvPolynomial.killCompl e.injective f) := rfl

/-- Coefficients restrict exactly by extending exponent vectors by zero. -/
theorem monomialRestriction_coefficient
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e))
    (x : MonomialQuotient (K := K) P) (a : {a // Q a}) :
    standardMonomialEquiv Q hQ (monomialRestriction e P Q hP hQ allowed x) a =
      standardMonomialEquiv P hP x ⟨a.val.mapDomain e, allowed a.val a.property⟩ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [monomialRestriction_mk, standardMonomialEquiv_mk,
    standardCoefficients_apply, MvPolynomial.coeff_killCompl]

end FourPapers.Universal
end
end

/- BEGIN BooleanRestrictions.lean -/
section


/-! # Actual restrictions between Boolean barycentric face rings

An embedding of vertex sets induces the embedding of their nonempty faces.
Restriction kills every face not contained in the smaller vertex set.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {U V W K : Type*}
  [Fintype U] [Fintype V] [Fintype W]
  [DecidableEq U] [DecidableEq V] [DecidableEq W] [CommRing K]

def booleanFaceEmbedding (e : V ↪ W) : BooleanFace V ↪ BooleanFace W where
  toFun F := ⟨F.val.map e, F.property.map (f := e)⟩
  inj' F G h := Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))

@[simp] theorem booleanFaceEmbedding_val (e : V ↪ W) (F : BooleanFace V) :
    (booleanFaceEmbedding e F).val = F.val.map e := rfl

@[simp] theorem booleanFaceEmbedding_card (e : V ↪ W) (F : BooleanFace V) :
    (booleanFaceEmbedding e F).val.card = F.val.card := Finset.card_map _

@[simp] theorem booleanFaceEmbedding_refl (F : BooleanFace V) :
    booleanFaceEmbedding (Function.Embedding.refl V) F = F := by
  apply Subtype.ext
  simp [booleanFaceEmbedding]

@[simp] theorem booleanFaceEmbedding_trans (e : U ↪ V) (f : V ↪ W)
    (F : BooleanFace U) :
    booleanFaceEmbedding f (booleanFaceEmbedding e F) =
      booleanFaceEmbedding (e.trans f) F := by
  apply Subtype.ext
  exact Finset.map_map e f F.val

theorem isChainExponent_map_booleanFaceEmbedding (e : V ↪ W)
    {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    IsChainExponent (a.mapDomain (booleanFaceEmbedding e)) := by
  intro F hF G hG
  rw [Finsupp.mapDomain_support_of_injective (booleanFaceEmbedding e).injective] at hF hG
  obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
  rcases ha F' hF' G' hG' with hFG | hGF
  · exact Or.inl (Finset.map_subset_map.mpr hFG)
  · exact Or.inr (Finset.map_subset_map.mpr hGF)

def booleanRestriction (e : V ↪ W) :
    BooleanBarycentricRing W K →ₐ[K] BooleanBarycentricRing V K :=
  monomialRestriction (booleanFaceEmbedding e) IsChainExponent IsChainExponent
    isChainExponent_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => isChainExponent_map_booleanFaceEmbedding e ha)

@[simp] theorem booleanRestriction_mk (e : V ↪ W)
    (f : MvPolynomial (BooleanFace W) K) :
    booleanRestriction e (Ideal.Quotient.mk (forbiddenIdeal IsChainExponent) f) =
      Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
        (MvPolynomial.killCompl (booleanFaceEmbedding e).injective f) := rfl

theorem booleanRestriction_face_included (e : V ↪ W) (F : BooleanFace V) :
    booleanRestriction e (faceVariable (K := K) (booleanFaceEmbedding e F)) =
      faceVariable F := by
  unfold faceVariable
  rw [booleanRestriction_mk]
  congr 1
  have h := DFunLike.congr_fun
    (MvPolynomial.killCompl_comp_rename (R := K) (booleanFaceEmbedding e).injective)
    (MvPolynomial.X F)
  simpa only [AlgHom.comp_apply, MvPolynomial.rename_X, AlgHom.id_apply] using h

theorem booleanRestriction_face_outside (e : V ↪ W) (F : BooleanFace W)
    (hF : F ∉ Set.range (booleanFaceEmbedding e)) :
    booleanRestriction e (faceVariable (K := K) F) = 0 := by
  unfold faceVariable
  rw [booleanRestriction_mk]
  have h : MvPolynomial.killCompl (R := K) (booleanFaceEmbedding e).injective
      (MvPolynomial.X F) = 0 := by
    simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hF]
  rw [h, map_zero]

theorem booleanRestriction_coefficient (e : V ↪ W)
    (x : BooleanBarycentricRing W K)
    (a : {a : BooleanFace V →₀ ℕ // IsChainExponent a}) :
    (booleanChainBasis (K := K)).repr (booleanRestriction e x) a =
      (booleanChainBasis (K := K)).repr x
        ⟨a.val.mapDomain (booleanFaceEmbedding e),
          isChainExponent_map_booleanFaceEmbedding e a.property⟩ :=
  monomialRestriction_coefficient _ _ _ _ _ _ _ _

theorem booleanRestriction_refl :
    booleanRestriction (K := K) (Function.Embedding.refl V) =
      AlgHom.id K (BooleanBarycentricRing V K) := by
  apply AlgHom.ext
  intro x
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  rw [booleanRestriction_coefficient]
  congr 1
  apply Subtype.ext
  change Finsupp.mapDomain (booleanFaceEmbedding (Function.Embedding.refl V)) a.val = a.val
  have he : (booleanFaceEmbedding (Function.Embedding.refl V) : BooleanFace V → BooleanFace V) = id :=
    funext booleanFaceEmbedding_refl
  rw [he]
  exact Finsupp.mapDomain_id

theorem booleanRestriction_comp (e : U ↪ V) (f : V ↪ W) :
    (booleanRestriction (K := K) e).comp (booleanRestriction f) =
      booleanRestriction (e.trans f) := by
  apply AlgHom.ext
  intro x
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  change (booleanChainBasis (K := K)).repr
    (booleanRestriction e (booleanRestriction f x)) a = _
  rw [booleanRestriction_coefficient, booleanRestriction_coefficient,
    booleanRestriction_coefficient]
  congr 1
  apply Subtype.ext
  change Finsupp.mapDomain (booleanFaceEmbedding f)
    (Finsupp.mapDomain (booleanFaceEmbedding e) a.val) =
      Finsupp.mapDomain (booleanFaceEmbedding (e.trans f)) a.val
  rw [← Finsupp.mapDomain_fun_comp]
  apply Finsupp.mapDomain_congr
  intro F hF
  exact booleanFaceEmbedding_trans e f F

/-- Rank-indexed color sums include every rank, so they restrict without
changing the global parameter index when a face has fewer vertices. -/
def booleanRankParameter (r : ℕ) : BooleanBarycentricRing V K :=
  ∑ F : BooleanFace V, if F.val.card = r then faceVariable F else 0

theorem booleanRankParameter_color (c : Fin (Fintype.card V)) :
    booleanRankParameter (K := K) (c.val + 1) = colorSum c := by
  rw [booleanRankParameter, colorSum, facesOfColor, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  have he : F.val.card = c.val + 1 ↔ F.color = c := by
    constructor
    · intro h
      apply Fin.ext
      have hF := F.color_succ
      omega
    · rintro rfl
      exact F.color_succ.symm
  simp only [he]

theorem booleanRankParameter_above (r : ℕ) (hr : Fintype.card V < r) :
    booleanRankParameter (V := V) (K := K) r = 0 := by
  apply Finset.sum_eq_zero
  intro F hF
  have hc : F.val.card ≤ Fintype.card V := Finset.card_le_univ F.val
  have hn : F.val.card ≠ r := by omega
  simp [hn]

theorem booleanRestriction_rankParameter (e : V ↪ W) (r : ℕ) :
    booleanRestriction (K := K) e (booleanRankParameter r) =
      booleanRankParameter r := by
  rw [booleanRankParameter, map_sum]
  calc
    (∑ F : BooleanFace W,
        booleanRestriction e (if F.val.card = r then faceVariable F else 0)) =
        ∑ G : BooleanFace V,
          booleanRestriction e
            (if (booleanFaceEmbedding e G).val.card = r then
              faceVariable (booleanFaceEmbedding e G) else 0) := by
      symm
      apply Finset.sum_bij_ne_zero (fun G _ _ => booleanFaceEmbedding e G)
      · intro G hG hG0
        exact Finset.mem_univ _
      · intro G H hG hH hG0 hH0 he
        exact (booleanFaceEmbedding e).injective he
      · intro F hF hF0
        have hmem : F ∈ Set.range (booleanFaceEmbedding e) := by
          by_contra hn
          apply hF0
          split_ifs <;> simp [booleanRestriction_face_outside e F hn]
        obtain ⟨G, rfl⟩ := hmem
        exact ⟨G, Finset.mem_univ _, hF0, rfl⟩
      · intro G hG hG0
        rfl
    _ = booleanRankParameter r := by
      unfold booleanRankParameter
      apply Finset.sum_congr rfl
      intro G hG
      rw [booleanFaceEmbedding_card]
      split_ifs <;> simp [booleanRestriction_face_included]

end FourPapers.Universal
end
end

/- BEGIN CoefficientDiagram.lean -/
section


/-!
# Coefficientwise gluing on a finite face diagram

Each basis index has a smallest supporting face. Compatible local coefficient
families then glue to one finitely supported global coefficient family. This
proves the inverse-limit step without assuming that inverse limits commute with
tensor products or that the coefficient ring is a field.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)

def coefficientStalk (p : P) : Submodule K (I →₀ K) :=
  Finsupp.supported K K {i | carrier i ≤ p}

def coefficientRestriction {p q : P} (_hqp : q ≤ p) :
    coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q :=
  (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
    (coefficientStalk K carrier p).subtype

@[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p)
    (x : coefficientStalk K carrier p) (i : I) :
    (coefficientRestriction K carrier hqp x).val i =
      if carrier i ≤ q then x.val i else 0 := rfl

abbrev coefficientDiagram : ModuleDiagram K P where
  obj p := coefficientStalk K carrier p
  res h := coefficientRestriction K carrier h
  res_refl p x := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ p
    · simp [hi]
    · have hx := (Finsupp.mem_supported' K x.val).mp x.property i hi
      simp [hi, hx]
  res_comp := by
    intro p q r hqp hrq x
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ r
    · have hiq := hi.trans hrq
      simp [hi, hiq]
    · simp [hi]

def coefficientSection : (I →₀ K) →ₗ[K] (coefficientDiagram K carrier).sections where
  toFun x := ⟨fun p => Finsupp.restrictDom K K {i | carrier i ≤ p} x, by
    intro p q hqp
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (if carrier i ≤ q then (if carrier i ≤ p then x i else 0) else 0) =
      (if carrier i ≤ q then x i else 0)
    by_cases hi : carrier i ≤ q
    · have hip := hi.trans hqp
      simp [hi, hip]
    · simp [hi]⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (Finsupp.restrictDom K K {i | carrier i ≤ p}) x y
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (Finsupp.restrictDom K K {i | carrier i ≤ p}) c x

@[simp] theorem coefficientSection_apply (x : I →₀ K) (p : P) (i : I) :
    ((coefficientSection K carrier x).val p).val i =
      if carrier i ≤ p then x i else 0 := rfl

def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K :=
  (x.val (carrier i)).val i

theorem coefficientAtCarrier_eq (x : (coefficientDiagram K carrier).sections)
    (i : I) (p : P) (hip : carrier i ≤ p) :
    coefficientAtCarrier K carrier x i = (x.val p).val i := by
  have h := congrArg (fun z : coefficientStalk K carrier (carrier i) => z.val i)
    (x.property p (carrier i) hip)
  change (if carrier i ≤ carrier i then (x.val p).val i else 0) =
    (x.val (carrier i)).val i at h
  simpa only [if_pos le_rfl, coefficientAtCarrier] using h.symm

variable [Fintype P]

/-- Finiteness of the face poset, rather than finiteness of the monomial index
set, makes the assembled coefficient family finitely supported. -/
def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)

@[simp] theorem coefficientAssembly_apply (x : (coefficientDiagram K carrier).sections)
    (i : I) : coefficientAssembly K carrier x i = coefficientAtCarrier K carrier x i := rfl

theorem coefficientAssembly_section (x : I →₀ K) :
    coefficientAssembly K carrier (coefficientSection K carrier x) = x := by
  apply Finsupp.ext
  intro i
  simp [coefficientAtCarrier]

theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) :
    coefficientSection K carrier (coefficientAssembly K carrier x) = x := by
  apply Subtype.ext
  funext p
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hi : carrier i ≤ p
  · simp [hi, coefficientAtCarrier_eq K carrier x i p hi]
  · have hx := (Finsupp.mem_supported' K (x.val p).val).mp (x.val p).property i hi
    simp [hi, hx]

/-- The exact coefficient gluing equivalence for a finite diagram. -/
def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul

/-- Any actual diagram with these coherent coefficient coordinates has the
same explicit global basis. The required coherent coordinates remain an
explicit input and must be established for the relevant face rings. -/
def sectionsFromCoherentCoefficients (D : ModuleDiagram K P)
    (e : CoherentEquiv D (coefficientDiagram K carrier)) :
    D.sections ≃ₗ[K] (I →₀ K) :=
  e.sectionEquiv.trans (coefficientSectionEquiv K carrier).symm

end FourPapers.Universal
end
end

/- BEGIN BarycentricDiagram.lean -/
section


/-! # The actual Boolean barycentric stalk diagram of a simplicial poset -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

@[simp] theorem faceVertexInclusion_refl (p : P) :
    faceVertexInclusion (le_refl p) = Function.Embedding.refl (FaceVertex p) := by
  ext a
  rfl

@[simp] theorem faceVertexInclusion_trans {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (faceVertexInclusion hrq).trans (faceVertexInclusion hqp) =
      faceVertexInclusion (hrq.trans hqp) := by
  ext a
  rfl

abbrev BarycentricStalk (p : P) := BooleanBarycentricRing (FaceVertex p) K

abbrev barycentricDiagram : ModuleDiagram K P where
  obj p := BarycentricStalk K p
  res h := (booleanRestriction (K := K) (faceVertexInclusion h)).toLinearMap
  res_refl p x := by
    change booleanRestriction (K := K) (faceVertexInclusion (le_refl p)) x = x
    rw [faceVertexInclusion_refl, booleanRestriction_refl]
    rfl
  res_comp hqp hrq x := by
    change booleanRestriction (K := K) (faceVertexInclusion hrq)
      (booleanRestriction (faceVertexInclusion hqp) x) =
        booleanRestriction (faceVertexInclusion (hrq.trans hqp)) x
    have h := DFunLike.congr_fun
      (booleanRestriction_comp (K := K) (faceVertexInclusion hrq) (faceVertexInclusion hqp)) x
    simpa only [AlgHom.comp_apply, faceVertexInclusion_trans] using h

variable (hs : IsSimplicialPoset P)

theorem stalkVertexSet_image_inclusion {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (stalkVertexSet q r).map (faceVertexInclusion hqp) = stalkVertexSet p r := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    exact (mem_stalkVertexSet p r (faceVertexInclusion hqp w)).mpr
      ((mem_stalkVertexSet q r w).mp hw)
  · intro hv
    have hvr := (mem_stalkVertexSet p r v).mp hv
    exact Finset.mem_map.mpr ⟨⟨v.val, v.property.1, hvr.trans hrq⟩,
      (mem_stalkVertexSet q r ⟨v.val, v.property.1, hvr.trans hrq⟩).mpr hvr, Subtype.ext rfl⟩

theorem booleanFaceInclusion_naturality {p q : P} (hqp : q ≤ p)
    (F : BooleanFace (FaceVertex q)) :
    booleanFaceInclusion hs p (booleanFaceEmbedding (faceVertexInclusion hqp) F) =
      booleanFaceInclusion hs q F := by
  apply Subtype.ext
  apply faceVertices_injective_below hs (booleanFaceInclusion_le hs p _)
    ((booleanFaceInclusion_le hs q F).trans hqp)
  rw [← image_stalkVertexSet (booleanFaceInclusion_le hs p _),
    stalkVertexSet_booleanFaceInclusion]
  rw [← image_stalkVertexSet (booleanFaceInclusion_le hs q F),
    stalkVertexSet_booleanFaceInclusion]
  change (F.val.map (faceVertexInclusion hqp)).image Subtype.val = F.val.image Subtype.val
  ext v
  simp only [Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨faceVertexInclusion hqp u, ⟨u, hu, rfl⟩, rfl⟩

def barycentricStalkStandardBasis (p : P) :
    Module.Basis (StandardInside p) K (BarycentricStalk K p) :=
  (booleanChainBasis (V := FaceVertex p) (K := K)).reindex (standardInsideEquiv hs p)

def barycentricStandardCoordinates (p : P) :
    BarycentricStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p :=
  (barycentricStalkStandardBasis K hs p).repr.trans
    (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm

theorem barycentricStandardCoordinates_apply_of_inside (p : P)
    (x : BarycentricStalk K p) (a : StandardFaceIndex P) (ha : standardCarrier a ≤ p) :
    (barycentricStandardCoordinates K hs p x).val a =
      (booleanChainBasis (V := FaceVertex p) (K := K)).repr x
        ((standardInsideEquiv hs p).symm ⟨a, ha⟩) := by
  have h := congrArg (fun f : StandardInside p →₀ K => f ⟨a, ha⟩)
    ((Finsupp.supportedEquivFinsupp (R := K) (M := K) {b : StandardFaceIndex P | standardCarrier b ≤ p}).apply_symm_apply
      ((barycentricStalkStandardBasis K hs p).repr x))
  change (barycentricStandardCoordinates K hs p x).val a =
    ((barycentricStalkStandardBasis K hs p).repr x) ⟨a, ha⟩ at h
  rw [h]
  simp [barycentricStalkStandardBasis]

theorem local_chain_restriction_index {p q : P} (hqp : q ≤ p)
    (a : StandardFaceIndex P) (ha : standardCarrier a ≤ q) :
    (((standardInsideEquiv hs q).symm ⟨a, ha⟩).val.mapDomain
      (booleanFaceEmbedding (faceVertexInclusion hqp))) =
      ((standardInsideEquiv hs p).symm ⟨a, ha.trans hqp⟩).val := by
  apply Finsupp.mapDomain_injective (booleanFaceInclusion hs p).injective
  rw [← Finsupp.mapDomain_fun_comp]
  have he : (fun F => booleanFaceInclusion hs p
      (booleanFaceEmbedding (faceVertexInclusion hqp) F)) = booleanFaceInclusion hs q := by
    funext F
    exact booleanFaceInclusion_naturality hs hqp F
  rw [he]
  have hq := congrArg (fun z : StandardInside q => z.val.val)
    ((standardInsideEquiv hs q).apply_symm_apply ⟨a, ha⟩)
  have hp := congrArg (fun z : StandardInside p => z.val.val)
    ((standardInsideEquiv hs p).apply_symm_apply ⟨a, ha.trans hqp⟩)
  exact hq.trans hp.symm

theorem barycentricStandardCoordinates_naturality {p q : P} (hqp : q ≤ p)
    (x : BarycentricStalk K p) :
    coefficientRestriction K standardCarrier hqp (barycentricStandardCoordinates K hs p x) =
      barycentricStandardCoordinates K hs q
        (booleanRestriction (K := K) (faceVertexInclusion hqp) x) := by
  apply Subtype.ext
  ext a
  by_cases ha : standardCarrier a ≤ q
  · rw [coefficientRestriction_apply, if_pos ha,
      barycentricStandardCoordinates_apply_of_inside K hs p x a (ha.trans hqp),
      barycentricStandardCoordinates_apply_of_inside K hs q _ a ha,
      booleanRestriction_coefficient]
    congr 1
    apply Subtype.ext
    exact (local_chain_restriction_index hs hqp a ha).symm
  · rw [coefficientRestriction_apply, if_neg ha]
    symm
    exact (Finsupp.mem_supported' K _).mp
      (barycentricStandardCoordinates K hs q _).property a ha

def barycentricCoefficientEquiv :
    CoherentEquiv (barycentricDiagram (P := P) K)
      (coefficientDiagram K (standardCarrier (P := P))) where
  component := barycentricStandardCoordinates K hs
  naturality p q hqp x := barycentricStandardCoordinates_naturality K hs hqp x

def barycentricSectionCoordinates :
    (barycentricDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  sectionsFromCoherentCoefficients K standardCarrier (barycentricDiagram K)
    (barycentricCoefficientEquiv K hs)

end FourPapers.Universal
end
end

/- BEGIN FaceStraightening.lean -/
section


/-!
# Spanning by standard monomials in the original face-ring quotient

Every straightening step strictly lowers the paper's exact quadratic rank
weight. The proof terminates for arbitrary powers and arbitrary coefficient
rings. No standard-monomial-basis assertion is assumed.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- A single face exponent, with the bottom symbol interpreted as one. -/
def faceUnitExponent (p : P) : NonzeroFace P →₀ ℕ :=
  if hp : p = ⊥ then 0 else Finsupp.single ⟨p, hp⟩ 1

@[simp] theorem faceUnitExponent_bot : faceUnitExponent (⊥ : P) = 0 := by
  simp [faceUnitExponent]

@[simp] theorem faceUnitExponent_nonzero (p : NonzeroFace P) :
    faceUnitExponent p.val = Finsupp.single p 1 := by
  simp [faceUnitExponent, p.property]

def maximumFaceRank : ℕ := univ.sup (faceRank : P → ℕ)

theorem faceRank_le_maximum (p : P) : faceRank p ≤ maximumFaceRank (P := P) :=
  Finset.le_sup (mem_univ p)

def naturalFaceWeight (p : P) : ℕ :=
  faceRank p * (2 * maximumFaceRank (P := P) - faceRank p)

theorem naturalFaceWeight_cast (p : P) :
    (naturalFaceWeight p : ℤ) = rankWeight (maximumFaceRank (P := P)) (faceRank p) := by
  have hle : faceRank p ≤ 2 * maximumFaceRank (P := P) := by
    have h := faceRank_le_maximum p
    omega
  unfold naturalFaceWeight rankWeight
  rw [Nat.cast_mul, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]

@[simp] theorem naturalFaceWeight_bot : naturalFaceWeight (⊥ : P) = 0 := by
  simp [naturalFaceWeight]

def faceExponentWeight (a : NonzeroFace P →₀ ℕ) : ℕ :=
  ∑ p : NonzeroFace P, a p * naturalFaceWeight p.val

@[simp] theorem faceExponentWeight_add (a b : NonzeroFace P →₀ ℕ) :
    faceExponentWeight (a + b) = faceExponentWeight a + faceExponentWeight b := by
  simp [faceExponentWeight, add_mul, Finset.sum_add_distrib]

@[simp] theorem faceExponentWeight_single (p : NonzeroFace P) (m : ℕ) :
    faceExponentWeight (Finsupp.single p m) = m * naturalFaceWeight p.val := by
  simp [faceExponentWeight, Finsupp.single_apply]

@[simp] theorem faceExponentWeight_unit (p : P) :
    faceExponentWeight (faceUnitExponent p) = naturalFaceWeight p := by
  by_cases hp : p = ⊥
  · subst p
    simp [faceExponentWeight]
  · simp [faceUnitExponent, hp]

theorem naturalFaceWeight_straightening (hs : IsSimplicialPoset P)
    {p q u : P} (hu : IsMinimalCommonUpper p q u)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    naturalFaceWeight (faceMeetBelow hs p q u hu.1 hu.2.1) + naturalFaceWeight u <
      naturalFaceWeight p + naturalFaceWeight q := by
  have h := face_straightening_weight_strict hs (maximumFaceRank (P := P)) hu hpq hqp
  simp only [← naturalFaceWeight_cast] at h
  exact_mod_cast h

variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)

theorem faceRingMonomial_add (a b : NonzeroFace P →₀ ℕ) :
    faceRingMonomial K hs (a + b) = faceRingMonomial K hs a * faceRingMonomial K hs b := by
  unfold faceRingMonomial
  rw [← map_mul, monomial_mul, mul_one]

@[simp] theorem faceRingMonomial_unit (p : P) :
    faceRingMonomial K hs (faceUnitExponent p) = faceRingGenerator K hs p := by
  by_cases hp : p = ⊥
  · subst p
    simp [faceRingMonomial, faceRingGenerator]
  · simp [faceRingMonomial, faceUnitExponent, faceRingGenerator, faceSymbol, hp, MvPolynomial.X]

theorem faceRing_straightening (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) :
    faceRingGenerator K hs p * faceRingGenerator K hs q =
      faceRingGenerator K hs (faceMeetBelow hs p q w hpw hqw) *
        ∑ u ∈ minimalCommonUppers p q, faceRingGenerator K hs u := by
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (show
      faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u ∈ faceRelations K hs from
        Or.inl ⟨p, q, w, hpw, hqw, rfl⟩))
  change (Ideal.Quotient.mk (faceIdeal K hs)) _ = 0 at hz
  have hsum : (Ideal.Quotient.mk (faceIdeal K hs))
      (∑ u ∈ minimalCommonUppers p q, faceSymbol K u) =
      ∑ u ∈ minimalCommonUppers p q,
        (Ideal.Quotient.mk (faceIdeal K hs)) (faceSymbol K u) :=
    map_sum (Ideal.Quotient.mk (faceIdeal K hs)).toAddMonoidHom _ _
  simpa only [RingHom.map_sub, RingHom.map_mul, hsum,
    sub_eq_zero, faceRingGenerator] using hz

theorem faceRing_product_eq_zero (p q : P) (h : ¬ ∃ w, p ≤ w ∧ q ≤ w) :
    faceRingGenerator K hs p * faceRingGenerator K hs q = 0 := by
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (show faceSymbol K p * faceSymbol K q ∈ faceRelations K hs from
      Or.inr ⟨p, q, h, rfl⟩))
  change (Ideal.Quotient.mk (faceIdeal K hs)) _ = 0 at hz
  simpa only [RingHom.map_mul, faceRingGenerator] using hz

/-- The span is formed inside the original Stanley face-ring quotient. -/
def standardFaceSpan : Submodule K (FaceRing K hs) :=
  Submodule.span K {x | ∃ a, BarycentricAllowed (P := P) a ∧ x = faceRingMonomial K hs a}

theorem faceRingMonomial_mem_standardFaceSpan (a : NonzeroFace P →₀ ℕ) :
    faceRingMonomial K hs a ∈ standardFaceSpan K hs := by
  have hall : ∀ n : ℕ, ∀ a : NonzeroFace P →₀ ℕ,
      faceExponentWeight a = n → faceRingMonomial K hs a ∈ standardFaceSpan K hs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a han
      by_cases ha : BarycentricAllowed a
      · exact Submodule.subset_span ⟨a, ha, rfl⟩
      · unfold BarycentricAllowed at ha
        push Not at ha
        obtain ⟨p, hp, q, hq, hpq, hqp⟩ := ha
        have hne : p ≠ q := by rintro rfl; exact hpq le_rfl
        obtain ⟨c, hc⟩ := exists_add_of_le (incomparable_pair_le p q hp hq hne)
        have he : faceRingMonomial K hs a =
            (faceRingGenerator K hs p.val * faceRingGenerator K hs q.val) *
              faceRingMonomial K hs c := by
          rw [hc]
          rw [faceRingMonomial_add, faceRingMonomial_add]
          simp only [← faceUnitExponent_nonzero, faceRingMonomial_unit]
        by_cases hcommon : ∃ w, p.val ≤ w ∧ q.val ≤ w
        · obtain ⟨w, hpw, hqw⟩ := hcommon
          let meet := faceMeetBelow hs p.val q.val w hpw hqw
          have he' : faceRingMonomial K hs a =
              ∑ u ∈ minimalCommonUppers p.val q.val,
                faceRingMonomial K hs (faceUnitExponent meet + faceUnitExponent u + c) := by
            rw [he, faceRing_straightening K hs p.val q.val w hpw hqw]
            simp only [Finset.mul_sum, Finset.sum_mul, faceRingMonomial_add, faceRingMonomial_unit, meet]
          rw [he']
          apply Submodule.sum_mem
          intro u hu
          have hmu := (mem_minimalCommonUppers p.val q.val u).mp hu
          have hlt := naturalFaceWeight_straightening hs hmu hpq hqp
          have hmeet := faceMeetBelow_independent hs p.val q.val w u hpw hqw hmu.1 hmu.2.1
          have hsmall : faceExponentWeight (faceUnitExponent meet + faceUnitExponent u + c) < n := by
            rw [← han, hc]
            simp only [faceExponentWeight_add, faceExponentWeight_unit,
              faceExponentWeight_single, one_mul]
            change naturalFaceWeight (faceMeetBelow hs p.val q.val w hpw hqw) +
              naturalFaceWeight u + faceExponentWeight c <
                naturalFaceWeight p.val + naturalFaceWeight q.val + faceExponentWeight c
            rw [hmeet]
            exact Nat.add_lt_add_right hlt _
          exact ih _ hsmall _ rfl
        · rw [he, faceRing_product_eq_zero K hs p.val q.val hcommon, zero_mul]
          exact Submodule.zero_mem _
  exact hall (faceExponentWeight a) a rfl

/-- Standard monomials span for every coefficient ring, with every straightening
step justified in the original quotient. Independence is a separate theorem. -/
theorem standardFaceSpan_eq_top : standardFaceSpan K hs = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  clear hx
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
      have he : (monomial a c : FacePolynomial (P := P) K) = c • monomial a 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [he]
      change (Ideal.Quotient.mkₐ K (faceIdeal K hs)) (c • monomial a 1) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c (faceRingMonomial_mem_standardFaceSpan K hs a)
  | add f g hf hg =>
      simpa only [RingHom.map_add] using (standardFaceSpan K hs).add_mem hf hg

end FourPapers.Universal
end
end

/- BEGIN SubsetProducts.lean -/
section


/-! # Products of subset monomials and a strict quadratic rank

The square norm of a sum of indicator vectors counts pairwise intersections.
Its largest possible value, for prescribed subset sizes, is attained exactly
by chains. This integral calculation supplies the lower terms in the
polynomial descent-basis construction.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V T K : Type*} [Fintype V] [DecidableEq V] [Fintype T] [CommRing K]

def subsetExponent (F : Finset V) : V →₀ ℕ :=
  ∑ v ∈ F, Finsupp.single v 1

@[simp] theorem subsetExponent_apply (F : Finset V) (v : V) :
    subsetExponent F v = if v ∈ F then 1 else 0 := by
  simp [subsetExponent, Finsupp.single_apply]

def occurrenceExponent (F : T → Finset V) : V →₀ ℕ :=
  ∑ t, subsetExponent (F t)

@[simp] theorem occurrenceExponent_apply (F : T → Finset V) (v : V) :
    occurrenceExponent F v = ∑ t, if v ∈ F t then 1 else 0 := by
  simp [occurrenceExponent]

def quadraticRank (a : V →₀ ℕ) : ℕ :=
  ∑ v, a v * a v

def rankCapacity (d : T → ℕ) : ℕ :=
  ∑ s, ∑ t, min (d s) (d t)

theorem quadraticRank_occurrence (F : T → Finset V) :
    quadraticRank (occurrenceExponent F) = ∑ s, ∑ t, (F s ∩ F t).card := by
  simp only [quadraticRank, occurrenceExponent_apply]
  calc
    (∑ v : V, (∑ s : T, if v ∈ F s then 1 else 0) *
      (∑ t : T, if v ∈ F t then 1 else 0)) =
        ∑ v : V, ∑ s : T, ∑ t : T,
          (if v ∈ F s then 1 else 0) * (if v ∈ F t then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.sum_mul]
            simp only [Finset.mul_sum]
    _ = ∑ s : T, ∑ t : T, ∑ v : V,
        (if v ∈ F s then 1 else 0) * (if v ∈ F t then 1 else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
    _ = ∑ s, ∑ t, (F s ∩ F t).card := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      simp only [ite_mul, one_mul, zero_mul, ← ite_and]
      simp [← Finset.mem_inter]

theorem card_inter_le_min (F G : Finset V) :
    (F ∩ G).card ≤ min F.card G.card :=
  le_min (Finset.card_le_card Finset.inter_subset_left)
    (Finset.card_le_card Finset.inter_subset_right)

theorem card_inter_eq_min_iff (F G : Finset V) :
    (F ∩ G).card = min F.card G.card ↔ F ⊆ G ∨ G ⊆ F := by
  constructor
  · intro h
    rcases le_total F.card G.card with hFG | hGF
    · rw [min_eq_left hFG] at h
      have he : F ∩ G = F :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left h.ge
      exact Or.inl (he ▸ Finset.inter_subset_right)
    · rw [min_eq_right hGF] at h
      have he : F ∩ G = G :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right h.ge
      exact Or.inr (he ▸ Finset.inter_subset_left)
  · rintro (hFG | hGF)
    · rw [Finset.inter_eq_left.mpr hFG, min_eq_left (Finset.card_le_card hFG)]
    · rw [Finset.inter_eq_right.mpr hGF, min_eq_right (Finset.card_le_card hGF)]

theorem quadraticRank_occurrence_le (F : T → Finset V) :
    quadraticRank (occurrenceExponent F) ≤ rankCapacity (fun t => (F t).card) := by
  rw [quadraticRank_occurrence, rankCapacity]
  apply Finset.sum_le_sum
  intro s hs
  exact Finset.sum_le_sum (fun t ht => card_inter_le_min (F s) (F t))

theorem quadraticRank_occurrence_lt_of_not_chain (F : T → Finset V)
    (h : ∃ s t, ¬ (F s ⊆ F t ∨ F t ⊆ F s)) :
    quadraticRank (occurrenceExponent F) < rankCapacity (fun t => (F t).card) := by
  obtain ⟨s, t, hst⟩ := h
  rw [quadraticRank_occurrence, rankCapacity]
  apply Finset.sum_lt_sum
  · intro i hi
    exact Finset.sum_le_sum (fun j hj => card_inter_le_min (F i) (F j))
  · refine ⟨s, Finset.mem_univ _, ?_⟩
    apply Finset.sum_lt_sum
    · intro j hj
      exact card_inter_le_min (F s) (F j)
    · refine ⟨t, Finset.mem_univ _, ?_⟩
      exact lt_of_le_of_ne (card_inter_le_min (F s) (F t))
        (fun he => hst ((card_inter_eq_min_iff (F s) (F t)).mp he))

theorem quadraticRank_occurrence_eq_iff (F : T → Finset V) :
    quadraticRank (occurrenceExponent F) = rankCapacity (fun t => (F t).card) ↔
      ∀ s t, F s ⊆ F t ∨ F t ⊆ F s := by
  constructor
  · intro he s t
    by_contra hst
    have hlt := quadraticRank_occurrence_lt_of_not_chain F ⟨s, t, hst⟩
    omega
  · intro h
    rw [quadraticRank_occurrence, rankCapacity]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    exact (card_inter_eq_min_iff (F s) (F t)).mpr (h s t)

theorem subsetMonomial (F : Finset V) :
    MvPolynomial.monomial (subsetExponent F) (1 : K) =
      ∏ v ∈ F, (MvPolynomial.X v : MvPolynomial V K) := by
  rw [subsetExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem occurrenceMonomial (F : T → Finset V) :
    MvPolynomial.monomial (occurrenceExponent F) (1 : K) =
      ∏ t, ∏ v ∈ F t, (MvPolynomial.X v : MvPolynomial V K) := by
  rw [occurrenceExponent, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro t ht
  exact subsetMonomial (F t)

/-- Expand an arbitrary product of sums of subset monomials. The indexing
assignments retain repeated factors, so coefficients and multiplicities are
accounted for exactly over every commutative coefficient ring. -/
theorem subsetProductExpansion (choices : T → Finset (Finset V)) :
    (∏ t, ∑ F ∈ choices t, ∏ v ∈ F, (MvPolynomial.X v : MvPolynomial V K)) =
      ∑ f ∈ Fintype.piFinset choices,
        MvPolynomial.monomial (occurrenceExponent f) (1 : K) := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact (occurrenceMonomial f).symm

end FourPapers.Universal
end
end

/- BEGIN TriangularBasis.lean -/
section


/-! # Unitriangular changes of basis with a natural-valued rank

The index set may be infinite and the coefficient ring is arbitrary. Each
individual vector has finite support because it is represented in a genuine
module basis. The strict decrease of a natural-valued rank supplies the entire
termination argument.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset Submodule

variable {I K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

theorem linearIndependent_of_rank_triangular
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_contra hn
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
  have hsim : (l.support.image rank).Nonempty := hs.image rank
  let r := (l.support.image rank).max' hsim
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp (Finset.max'_mem _ hsim)
  have himax : ∀ j ∈ l.support, rank j ≤ rank i := by
    intro j hj
    rw [hir]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hc : (b.repr (Finsupp.linearCombination K v l)) i = l i := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hdiag, mul_one]
    · intro j hj hji
      rw [htri j i hji (himax j hj), mul_zero]
    · intro hni
      exact (hni hi).elim
  rw [hl, map_zero, Finsupp.zero_apply] at hc
  exact (Finsupp.mem_support_iff.mp hi) hc.symm

theorem span_eq_top_of_rank_triangular
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) :
    Submodule.span K (Set.range v) = ⊤ := by
  classical
  let S := Submodule.span K (Set.range v)
  have hb : ∀ n : ℕ, ∀ i, rank i = n → b i ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hir
      have hw : v i - b i ∈ S := by
        rw [← b.linearCombination_repr (v i - b i), Finsupp.linearCombination_apply,
          Finsupp.sum]
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.smul_mem
        have hji : j ≠ i := by
          intro he
          subst j
          have hnz := Finsupp.mem_support_iff.mp hj
          exact hnz (by simp [hdiag])
        have hjlt : rank j < n := by
          by_contra hnlt
          have hrij : rank i ≤ rank j := by omega
          have hnz := Finsupp.mem_support_iff.mp hj
          apply hnz
          simp [htri i j (Ne.symm hji) hrij, hji]
        exact ih (rank j) hjlt j rfl
      have hv : v i ∈ S := Submodule.subset_span ⟨i, rfl⟩
      have hh := S.sub_mem hv hw
      simpa only [sub_sub_cancel] using hh
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hb (rank i) i rfl

/-- A genuine module basis obtained from a unitriangular family, without a
field assumption or any finite-dimensionality assumption. -/
def rankTriangularBasis
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) :
    Module.Basis I K M :=
  Module.Basis.mk (linearIndependent_of_rank_triangular b v rank hdiag htri)
    (by rw [span_eq_top_of_rank_triangular b v rank hdiag htri])

@[simp] theorem rankTriangularBasis_apply
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) (i : I) :
    rankTriangularBasis b v rank hdiag htri i = v i :=
  Module.Basis.mk_apply _ _ _

end FourPapers.Universal
end
end

/- BEGIN ChainCoordinates.lean -/
section


/-! # Nested-face exponent vectors and ordinary vertex exponent vectors

The map sends one face variable to the squarefree product of its vertices.
Its inverse is the layer decomposition of a nonnegative integer vector.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The actual exponent map induced by `v_F ↦ ∏_{v∈F} x_v`. -/
def chainVertexMap : (BooleanFace V →₀ ℕ) →ₗ[ℕ] (V →₀ ℕ) :=
  Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)

@[simp] theorem chainVertexMap_apply (a : BooleanFace V →₀ ℕ) (v : V) :
    chainVertexMap a v = ∑ F ∈ a.support, if v ∈ F.val then a F else 0 := by
  simp only [chainVertexMap, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, subsetExponent_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]

theorem chainVertexMap_separates {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) {x y : V}
    (hx : x ∈ F.val) (hy : y ∉ F.val) : chainVertexMap a y < chainVertexMap a x := by
  rw [chainVertexMap_apply, chainVertexMap_apply]
  apply Finset.sum_lt_sum
  · intro G hG
    by_cases hyG : y ∈ G.val
    · have hxG : x ∈ G.val := by
        rcases ha F hF G hG with hFG | hGF
        · exact hFG hx
        · exact (hy (hGF hyG)).elim
      simp [hyG, hxG]
    · simp [hyG]
  · refine ⟨F, hF, ?_⟩
    simpa [hx, hy] using Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hF)

theorem exists_face_of_chainVertexMap_lt {a : BooleanFace V →₀ ℕ} {x y : V}
    (h : chainVertexMap a y < chainVertexMap a x) :
    ∃ F ∈ a.support, x ∈ F.val ∧ y ∉ F.val := by
  by_contra hn
  have hle : chainVertexMap a x ≤ chainVertexMap a y := by
    rw [chainVertexMap_apply, chainVertexMap_apply]
    apply Finset.sum_le_sum
    intro F hF
    by_cases hx : x ∈ F.val
    · have hy : y ∈ F.val := by
        by_contra hy
        exact hn ⟨F, hF, hx, hy⟩
      simp [hx, hy]
    · simp [hx]
  exact (not_le_of_gt h) hle

theorem weightOrdering_chainVertexMap_prefix {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) {F : BooleanFace V} (hF : F ∈ a.support) :
    orderingPrefix (weightOrdering (fun v => chainVertexMap a v)) F.color = F.val := by
  apply orderingPrefix_eq_of_weight_separation (fun v => chainVertexMap a v)
    _ (weightOrdering_antitone _) F.val F.color F.color_succ.symm
  intro x hx y hy
  exact chainVertexMap_separates ha hF hx hy

theorem weightOrdering_chainVertexMap_descents {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) :
    orderingDescents (weightOrdering (fun v => chainVertexMap a v)) ⊆
      (chainColorDegree a).support := by
  intro c hc
  obtain ⟨hn, hw⟩ := weightOrdering_descent_lt (fun v => chainVertexMap a v)
    ((mem_orderingDescents _ _).mp hc)
  obtain ⟨F, hF, hx, hy⟩ := exists_face_of_chainVertexMap_lt hw
  have hpc := weightOrdering_chainVertexMap_prefix ha hF
  have hleft : c ≤ F.color := by
    have hm : weightOrdering (fun v => chainVertexMap a v) c ∈
        orderingPrefix (weightOrdering (fun v => chainVertexMap a v)) F.color := by
      rw [hpc]
      exact hx
    simpa only [mem_orderingPrefix, Equiv.symm_apply_apply] using hm
  have hright : ¬ (⟨c.val + 1, hn⟩ : Fin (Fintype.card V)) ≤ F.color := by
    intro h
    apply hy
    rw [← hpc]
    simpa only [mem_orderingPrefix, Equiv.symm_apply_apply] using h
  have hcol : F.color = c := by
    apply Fin.ext
    change F.color.val = c.val
    change c.val ≤ F.color.val at hleft
    change ¬ c.val + 1 ≤ F.color.val at hright
    omega
  rw [chainColorDegree_support ha]
  exact Finset.mem_image.mpr ⟨F, hF, hcol⟩

theorem ordering_eq_chainOrdering {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    (σ : VertexOrdering (Fintype.card V) V)
    (hp : ∀ F ∈ a.support, orderingPrefix σ F.color = F.val)
    (hd : orderingDescents σ ⊆ (chainColorDegree a).support) : σ = chainOrdering a := by
  apply ordering_eq_of_descent_prefixes
  · intro c hc
    have hm := hd ((mem_orderingDescents _ _).mpr hc)
    rw [chainColorDegree_support ha] at hm
    obtain ⟨F, hF, hFc⟩ := Finset.mem_image.mp hm
    rw [← hFc, hp F hF, chainOrdering_prefix ha hF]
  · intro c hc
    have hm := chainOrdering_descents ha ((mem_orderingDescents _ _).mpr hc)
    rw [chainColorDegree_support ha] at hm
    obtain ⟨F, hF, hFc⟩ := Finset.mem_image.mp hm
    rw [← hFc, hp F hF, chainOrdering_prefix ha hF]

theorem chainOrdering_eq_weightOrdering {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) :
    chainOrdering a = weightOrdering (fun v => chainVertexMap a v) := by
  symm
  apply ordering_eq_chainOrdering ha
  · intro F hF
    exact weightOrdering_chainVertexMap_prefix ha hF
  · exact weightOrdering_chainVertexMap_descents ha

def vertexHeight (a : V →₀ ℕ) : ℕ := Finset.univ.sup (fun v => a v)

theorem vertexExponent_le_height (a : V →₀ ℕ) (v : V) : a v ≤ vertexHeight a :=
  Finset.le_sup (Finset.mem_univ v)

def exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) : BooleanFace V :=
  ⟨Finset.univ.filter (fun v => k.val < a v), by
    obtain ⟨v, hv, hkv⟩ := Finset.lt_sup_iff.mp k.isLt
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hkv⟩⟩⟩

@[simp] theorem mem_exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) (v : V) :
    v ∈ (exponentLayer a k).val ↔ k.val < a v := by
  simp [exponentLayer]

def layerExponent (a : V →₀ ℕ) : BooleanFace V →₀ ℕ :=
  ∑ k : Fin (vertexHeight a), Finsupp.single (exponentLayer a k) 1

theorem mem_layerExponent_support (a : V →₀ ℕ) (F : BooleanFace V) :
    F ∈ (layerExponent a).support ↔ ∃ k, exponentLayer a k = F := by
  rw [Finsupp.mem_support_iff]
  have he : layerExponent a F =
      (Finset.univ.filter (fun k : Fin (vertexHeight a) => exponentLayer a k = F)).card := by
    simp [layerExponent, Finsupp.single_apply]
  rw [he]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩
  · rintro ⟨k, hk⟩
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hk⟩⟩)

theorem layerExponent_isChain (a : V →₀ ℕ) : IsChainExponent (layerExponent a) := by
  intro F hF G hG
  obtain ⟨i, rfl⟩ := (mem_layerExponent_support a F).mp hF
  obtain ⟨j, rfl⟩ := (mem_layerExponent_support a G).mp hG
  rcases le_total i j with hij | hji
  · apply Or.inr
    intro v hv
    exact (mem_exponentLayer a i v).mpr
      (lt_of_le_of_lt hij ((mem_exponentLayer a j v).mp hv))
  · apply Or.inl
    intro v hv
    exact (mem_exponentLayer a j v).mpr
      (lt_of_le_of_lt hji ((mem_exponentLayer a i v).mp hv))

theorem chainVertexMap_layerExponent (a : V →₀ ℕ) : chainVertexMap (layerExponent a) = a := by
  ext v
  rw [layerExponent, map_sum]
  simp only [chainVertexMap, Finsupp.linearCombination_single, one_smul,
    Finsupp.finsetSum_apply, subsetExponent_apply, mem_exponentLayer]
  have hav := vertexExponent_le_height a v
  have he : (Finset.univ.filter (fun k : Fin (vertexHeight a) => k.val < a v)).card = a v := by
    have hset : Finset.univ.filter (fun k : Fin (vertexHeight a) => k.val < a v) =
        (Finset.range (a v)).attach.image (fun k =>
          (⟨k.val, lt_of_lt_of_le (Finset.mem_range.mp k.property) hav⟩ : Fin (vertexHeight a))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range]
      constructor
      · intro hk
        exact ⟨k.val, hk, rfl⟩
      · rintro ⟨j, hj, hjk⟩
        simpa only [← hjk] using hj
    rw [hset, Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact Subtype.ext (congrArg Fin.val hij)
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using he

def exponentIntCast {I : Type*} : (I →₀ ℕ) →+ (I →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp] theorem exponentIntCast_apply {I : Type*} (a : I →₀ ℕ) (i : I) :
    exponentIntCast a i = (a i : ℤ) := rfl

@[simp] theorem exponentIntCast_single {I : Type*} (i : I) (m : ℕ) :
    exponentIntCast (Finsupp.single i m) = Finsupp.single i (m : ℤ) := by
  classical
  ext j
  simp [Finsupp.single_apply]

theorem exponentIntCast_injective {I : Type*} :
    Function.Injective (exponentIntCast : (I →₀ ℕ) →+ (I →₀ ℤ)) := by
  intro a b h
  ext i
  exact Nat.cast_injective (congrArg (fun f : I →₀ ℤ => f i) h)

theorem exponentIntCast_smul {I : Type*} (m : ℕ) (a : I →₀ ℕ) :
    exponentIntCast (m • a) = (m : ℤ) • exponentIntCast a := by
  ext i
  simp [Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul]

theorem exponentIntCast_linearCombination {I : Type*} (w : I → V →₀ ℕ) (m : I →₀ ℕ) :
    exponentIntCast (Finsupp.linearCombination ℕ w m) =
      Finsupp.linearCombination ℤ (fun i => exponentIntCast (w i)) (exponentIntCast m) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single i m =>
    rw [Finsupp.linearCombination_single, exponentIntCast_single,
      Finsupp.linearCombination_single]
    exact exponentIntCast_smul m (w i)

def prefixIndicatorBasis (σ : VertexOrdering (Fintype.card V) V) :
    Module.Basis (Fin (Fintype.card V)) ℤ (V →₀ ℤ) :=
  rankTriangularBasis (Finsupp.basisSingleOne.reindex σ.symm)
    (fun c => exponentIntCast (subsetExponent (orderingPrefix σ c))) Fin.val
    (by
      intro c
      change exponentIntCast (subsetExponent (orderingPrefix σ c)) (σ c) = 1
      simp)
    (by
      intro i j hne hij
      change exponentIntCast (subsetExponent (orderingPrefix σ i)) (σ j) = 0
      have hn : ¬ j ≤ i := by
        intro hji
        exact hne (le_antisymm hij hji)
      simp [hn])

@[simp] theorem prefixIndicatorBasis_apply (σ : VertexOrdering (Fintype.card V) V)
    (c : Fin (Fintype.card V)) :
    prefixIndicatorBasis σ c = exponentIntCast (subsetExponent (orderingPrefix σ c)) :=
  rankTriangularBasis_apply _ _ _ _ _ _

theorem chainVertexMap_prefixExponent (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) :
    chainVertexMap (prefixExponent σ m) =
      Finsupp.linearCombination ℕ (fun c => subsetExponent (orderingPrefix σ c)) m := by
  exact Finsupp.linearCombination_mapDomain ℕ (orderingFace σ) m

theorem chainVertexMap_prefix_injective (σ : VertexOrdering (Fintype.card V) V) :
    Function.Injective (fun m => chainVertexMap (prefixExponent σ m)) := by
  intro m n h
  change chainVertexMap (prefixExponent σ m) = chainVertexMap (prefixExponent σ n) at h
  have hc := congrArg exponentIntCast h
  rw [chainVertexMap_prefixExponent, chainVertexMap_prefixExponent,
    exponentIntCast_linearCombination, exponentIntCast_linearCombination] at hc
  have hb := (prefixIndicatorBasis σ).linearIndependent
  change Function.Injective (Finsupp.linearCombination ℤ (prefixIndicatorBasis σ)) at hb
  apply exponentIntCast_injective
  apply hb
  have he : (prefixIndicatorBasis σ : Fin (Fintype.card V) → V →₀ ℤ) =
      (fun i => exponentIntCast (subsetExponent (orderingPrefix σ i))) :=
    funext (prefixIndicatorBasis_apply σ)
  rw [he]
  exact hc

theorem chainVertexMap_chain_injective :
    Function.Injective (fun a : {a : BooleanFace V →₀ ℕ // IsChainExponent a} =>
      chainVertexMap a.val) := by
  intro a b he
  change chainVertexMap a.val = chainVertexMap b.val at he
  have horder : chainOrdering a.val = chainOrdering b.val := by
    rw [chainOrdering_eq_weightOrdering a.property,
      chainOrdering_eq_weightOrdering b.property, he]
  have hcolors : chainColorDegree a.val = chainColorDegree b.val := by
    apply chainVertexMap_prefix_injective (chainOrdering a.val)
    change chainVertexMap (prefixExponent (chainOrdering a.val) (chainColorDegree a.val)) =
      chainVertexMap (prefixExponent (chainOrdering a.val) (chainColorDegree b.val))
    rw [prefixExponent_chainColorDegree a.property, horder,
      prefixExponent_chainColorDegree b.property]
    exact he
  apply Subtype.ext
  calc
    a.val = prefixExponent (chainOrdering a.val) (chainColorDegree a.val) :=
      (prefixExponent_chainColorDegree a.property).symm
    _ = prefixExponent (chainOrdering b.val) (chainColorDegree b.val) := by rw [horder, hcolors]
    _ = b.val := prefixExponent_chainColorDegree b.property

/-- Every ordinary vertex monomial has a unique factorization by nested
nonempty squarefree monomials. This is the exact chain/vertex correspondence. -/
def chainVertexEquiv : {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃ (V →₀ ℕ) where
  toFun a := chainVertexMap a.val
  invFun a := ⟨layerExponent a, layerExponent_isChain a⟩
  left_inv a := chainVertexMap_chain_injective (chainVertexMap_layerExponent (chainVertexMap a.val))
  right_inv := chainVertexMap_layerExponent

def chainLength (a : BooleanFace V →₀ ℕ) : ℕ := a.sum (fun _ m => m)

theorem chainVertexMap_le_length (a : BooleanFace V →₀ ℕ) (v : V) :
    chainVertexMap a v ≤ chainLength a := by
  rw [chainVertexMap_apply, chainLength, Finsupp.sum]
  apply Finset.sum_le_sum
  intro F hF
  split_ifs <;> omega

/-- Chain length is exactly the maximal exponent of the corresponding
ordinary monomial, including the zero monomial exponent vector. -/
theorem vertexHeight_chainVertexMap {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) : vertexHeight (chainVertexMap a) = chainLength a := by
  apply le_antisymm
  · exact Finset.sup_le (fun v hv => chainVertexMap_le_length a v)
  · by_cases hs : a.support.Nonempty
    · obtain ⟨F, hF⟩ := hs
      have hn : 0 < Fintype.card V := Nat.lt_of_le_of_lt (Nat.zero_le F.color.val) F.color.isLt
      let i : Fin (Fintype.card V) := ⟨0, hn⟩
      let v := chainOrdering a i
      have hall : ∀ G ∈ a.support, v ∈ G.val := by
        intro G hG
        rw [← chainOrdering_prefix ha hG]
        simp only [v, mem_orderingPrefix, Equiv.symm_apply_apply]
        exact Nat.zero_le _
      have he : chainVertexMap a v = chainLength a := by
        rw [chainVertexMap_apply, chainLength, Finsupp.sum]
        apply Finset.sum_congr rfl
        intro G hG
        simp [hall G hG]
      rw [← he]
      exact vertexExponent_le_height _ _
    · have he : a = 0 := by
        apply Finsupp.support_eq_empty.mp
        exact Finset.not_nonempty_iff_eq_empty.mp hs
      simp [he, chainLength]

section Unordered

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The vertex exponent map without any ordering of the vertex set. -/
def chainVertexMapUnordered : (BooleanFace W →₀ ℕ) →ₗ[ℕ] (W →₀ ℕ) :=
  Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)

@[simp] theorem chainVertexMapUnordered_apply (a : BooleanFace W →₀ ℕ) (v : W) :
    chainVertexMapUnordered a v = ∑ F ∈ a.support, if v ∈ F.val then a F else 0 := by
  simp only [chainVertexMapUnordered, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, subsetExponent_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]

/-- The nested-face factorization is intrinsic to a finite vertex set.
An auxiliary order is chosen solely to reuse the proof of injectivity; the
forward map is the explicit, order-independent incidence sum. -/
def chainVertexEquivUnordered :
    {a : BooleanFace W →₀ ℕ // IsChainExponent a} ≃ (W →₀ ℕ) := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact chainVertexEquiv

@[simp] theorem chainVertexEquivUnordered_apply
    (a : {a : BooleanFace W →₀ ℕ // IsChainExponent a}) :
    chainVertexEquivUnordered a = chainVertexMapUnordered a.val := rfl

@[simp] theorem chainVertexEquivUnordered_apply_apply
    (a : {a : BooleanFace W →₀ ℕ // IsChainExponent a}) (v : W) :
    chainVertexEquivUnordered a v =
      ∑ F ∈ a.val.support, if v ∈ F.val then a.val F else 0 :=
  chainVertexMapUnordered_apply a.val v

end Unordered

end FourPapers.Universal
end
end

/- BEGIN FaceMonomialCoordinates.lean -/
section


/-! # Exact monomial coordinates in each polynomial stalk -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The exponent vector of a product of actual face vertex products. -/
def stalkExponent (p : P) : (NonzeroFace P →₀ ℕ) →ₗ[ℕ] (FaceVertex p →₀ ℕ) :=
  Finsupp.linearCombination ℕ (fun q => subsetExponent (stalkVertexSet p q.val))

@[simp] theorem stalkExponent_apply (p : P) (a : NonzeroFace P →₀ ℕ)
    (v : FaceVertex p) :
    stalkExponent p a v = ∑ q ∈ a.support, if v.val ≤ q.val then a q else 0 := by
  simp only [stalkExponent, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, subsetExponent_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, mem_stalkVertexSet]

variable (K : Type*) [CommRing K]

theorem faceProduct_eq_monomial (p q : P) :
    faceProduct K p q = monomial (subsetExponent (stalkVertexSet p q)) 1 := by
  rw [subsetExponent, MvPolynomial.monomial_sum_one]
  simp only [faceProduct, MvPolynomial.X]

theorem faceEvaluation_monomial_of_inside (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    faceEvaluation K p (monomial a 1) = monomial (stalkExponent p a) 1 := by
  rw [faceEvaluation, MvPolynomial.aeval_monomial, map_one, one_mul]
  rw [stalkExponent, Finsupp.linearCombination_apply, MvPolynomial.monomial_finsupp_sum_index,
    MvPolynomial.C_1, one_mul]
  apply Finset.prod_congr rfl
  intro q hq
  simp only [faceValue, if_pos (ha q hq), faceProduct_eq_monomial,
    MvPolynomial.monomial_pow, one_pow]

theorem faceEvaluation_monomial_of_outside (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ¬ ∀ q ∈ a.support, q.val ≤ p) :
    faceEvaluation K p (monomial a 1) = 0 := by
  push Not at ha
  obtain ⟨q, hq, hqp⟩ := ha
  rw [faceEvaluation, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
  apply Finset.prod_eq_zero hq
  simp only [faceValue, if_neg hqp]
  exact zero_pow (Finsupp.mem_support_iff.mp hq)

theorem faceRingEvaluation_monomial (hs : IsSimplicialPoset P) (p : P)
    (a : StandardFaceIndex P) :
    faceRingEvaluation K hs p (faceRingMonomial K hs a.val) =
      if standardCarrier a ≤ p then monomial (stalkExponent p a.val) 1 else 0 := by
  change faceEvaluation K p (monomial a.val 1) = _
  by_cases ha : standardCarrier a ≤ p
  · rw [if_pos ha]
    exact faceEvaluation_monomial_of_inside K p a.val ((standardCarrier_le_iff hs a p).mp ha)
  · rw [if_neg ha]
    apply faceEvaluation_monomial_of_outside K p a.val
    exact fun h => ha ((standardCarrier_le_iff hs a p).mpr h)

variable {K}

/-- Inside one Boolean interval, the exponent map is the usual nested-subset
map. The arbitrary order used in its proof never changes this formula. -/
theorem stalkExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) (a : BooleanFace (FaceVertex p) →₀ ℕ) :
    stalkExponent p (a.mapDomain (booleanFaceInclusion hs p)) = chainVertexMapUnordered a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [Finsupp.mapDomain_add, map_add, ha, hb]
  | single F m =>
      simp only [Finsupp.mapDomain_single, stalkExponent, chainVertexMapUnordered,
        Finsupp.linearCombination_single, stalkVertexSet_booleanFaceInclusion]

/-- The actual exponent bijection between standard monomials supported in a
face and all vertex monomials of that face. -/
def standardVertexEquiv (hs : IsSimplicialPoset P) (p : P) :
    StandardInside p ≃ (FaceVertex p →₀ ℕ) :=
  (standardInsideEquiv hs p).symm.trans chainVertexEquivUnordered

@[simp] theorem standardVertexEquiv_apply (hs : IsSimplicialPoset P) (p : P)
    (a : StandardInside p) :
    standardVertexEquiv hs p a = stalkExponent p a.val.val := by
  change chainVertexMapUnordered ((standardInsideEquiv hs p).symm a).val = _
  rw [← stalkExponent_map_booleanFaceInclusion hs p]
  have he := congrArg (fun b : StandardInside p => b.val.val)
    ((standardInsideEquiv hs p).apply_symm_apply a)
  change Finsupp.mapDomain (booleanFaceInclusion hs p)
    ((standardInsideEquiv hs p).symm a).val = a.val.val at he
  exact congrArg (stalkExponent p) he

/-- Independence of the standard monomials in a stalk follows from an
explicit bijection of ordinary monomial exponent vectors. -/
def polynomialStandardBasis (hs : IsSimplicialPoset P) (p : P) :
    Module.Basis (StandardInside p) K (PolynomialStalk K p) :=
  (MvPolynomial.basisMonomials (FaceVertex p) K).reindex (standardVertexEquiv hs p).symm

@[simp] theorem polynomialStandardBasis_apply (hs : IsSimplicialPoset P) (p : P)
    (a : StandardInside p) :
    polynomialStandardBasis (K := K) hs p a = monomial (stalkExponent p a.val.val) 1 := by
  simp [polynomialStandardBasis]

theorem polynomialStandardBasis_eq_evaluation (hs : IsSimplicialPoset P) (p : P)
    (a : StandardInside p) :
    polynomialStandardBasis (K := K) hs p a =
      faceRingEvaluation K hs p (faceRingMonomial K hs a.val.val) := by
  rw [polynomialStandardBasis_apply, faceRingEvaluation_monomial, if_pos a.property]

end FourPapers.Universal
end
end

/- BEGIN PolynomialParameters.lean -/
section


/-! # Universal parameters commute with all face restrictions -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open MvPolynomial Finset

variable {V W : Type*} (K : Type*) [CommRing K]

@[simp] theorem killCompl_X_included (e : V ↪ W) (v : V) :
    MvPolynomial.killCompl (R := K) e.injective (X (e v)) = X v := by
  have h := DFunLike.congr_fun (MvPolynomial.killCompl_comp_rename (R := K) e.injective)
    (X v)
  simpa using h

theorem killCompl_X_outside (e : V ↪ W) (w : W) (hw : w ∉ Set.range e) :
    MvPolynomial.killCompl (R := K) e.injective (X w) = 0 := by
  classical
  rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hw]

theorem killCompl_prod_X_outside [Fintype V] (e : V ↪ W) (s : Finset W)
    (hs : ¬ s ⊆ univ.map e) :
    MvPolynomial.killCompl (R := K) e.injective (∏ w ∈ s, X w) = 0 := by
  classical
  obtain ⟨w, hw, hwout⟩ := Finset.not_subset.mp hs
  have hwrange : w ∉ Set.range e := by
    rintro ⟨v, rfl⟩
    exact hwout (Finset.mem_map.mpr ⟨v, mem_univ v, rfl⟩)
  rw [map_prod]
  exact Finset.prod_eq_zero hw (killCompl_X_outside K e w hwrange)

/-- Deleting any set of variables restricts elementary symmetric polynomials to
the same elementary symmetric polynomials in the surviving variables. -/
theorem killCompl_esymm [Fintype V] [Fintype W] (e : V ↪ W) (n : ℕ) :
    MvPolynomial.killCompl (R := K) e.injective (MvPolynomial.esymm W K n) =
      MvPolynomial.esymm V K n := by
  classical
  rw [MvPolynomial.esymm, map_sum]
  have hsub : powersetCard n (univ.map e) ⊆ powersetCard n (univ : Finset W) :=
    powersetCard_mono (by intro w hw; exact mem_univ w)
  calc
    ∑ s ∈ powersetCard n univ,
        MvPolynomial.killCompl (R := K) e.injective (∏ w ∈ s, X w) =
      ∑ s ∈ powersetCard n (univ.map e),
        MvPolynomial.killCompl (R := K) e.injective (∏ w ∈ s, X w) := by
      symm
      apply Finset.sum_subset hsub
      intro s hs hnot
      apply killCompl_prod_X_outside K e s
      intro hss
      exact hnot (mem_powersetCard.mpr ⟨hss, (mem_powersetCard.mp hs).2⟩)
    _ = MvPolynomial.esymm V K n := by
      simp [MvPolynomial.esymm, powersetCard_map, Finset.mapEmbedding_apply,
        map_prod]

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

theorem polynomialRestriction_eq_killCompl {p q : P} (hqp : q ≤ p) :
    polynomialRestriction K hqp =
      MvPolynomial.killCompl (R := K) (faceVertexInclusion hqp).injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  by_cases hq : a.val ≤ q
  · let b : FaceVertex q := ⟨a.val, a.property.1, hq⟩
    have hb : faceVertexInclusion hqp b = a := Subtype.ext rfl
    rw [polynomialRestriction_X, dif_pos hq]
    change X b = _
    simpa only [hb] using (killCompl_X_included K (faceVertexInclusion hqp) b).symm
  · have ha : a ∉ Set.range (faceVertexInclusion hqp) := by
      rintro ⟨b, hb⟩
      have hv : b.val = a.val := congrArg Subtype.val hb
      exact hq (hv ▸ b.property.2)
    rw [killCompl_X_outside K _ _ ha]
    simp [hq]

theorem polynomialRestriction_parameter {p q : P} (hqp : q ≤ p) (i : ℕ) :
    polynomialRestriction K hqp (polynomialParameter K p i) =
      polynomialParameter K q i := by
  rw [polynomialRestriction_eq_killCompl]
  exact killCompl_esymm K (faceVertexInclusion hqp) i

/-- The honest algebra map giving the global parameter-ring action on a stalk. -/
def polynomialParameterMap (d : ℕ) (p : P) :
    MvPolynomial (Fin d) K →ₐ[K] PolynomialStalk K p :=
  MvPolynomial.aeval fun i => polynomialParameter K p (i.val + 1)

theorem polynomialRestriction_parameterMap (d : ℕ) {p q : P} (hqp : q ≤ p) :
    (polynomialRestriction K hqp).comp (polynomialParameterMap K d p) =
      polynomialParameterMap K d q := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa [polynomialParameterMap] using polynomialRestriction_parameter K hqp (i.val + 1)

theorem polynomialRestriction_parameter_mul (d : ℕ) {p q : P} (hqp : q ≤ p)
    (a : MvPolynomial (Fin d) K) (f : PolynomialStalk K p) :
    polynomialRestriction K hqp (polynomialParameterMap K d p a * f) =
      polynomialParameterMap K d q a * polynomialRestriction K hqp f := by
  rw [map_mul]
  congr 1
  exact DFunLike.congr_fun (polynomialRestriction_parameterMap K d hqp) a

end FourPapers.Universal
end
end

/- BEGIN FaceEvaluationNaturality.lean -/
section


/-! # Natural restriction of the original face-ring evaluations -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem faceProduct_of_le {p q : P} (hqp : q ≤ p) :
    faceProduct K p q = ∏ v : FaceVertex q, X (faceVertexInclusion hqp v) := by
  unfold faceProduct
  apply Finset.prod_bij (fun v hv =>
    (⟨v.val, v.property.1, (mem_stalkVertexSet p q v).mp hv⟩ : FaceVertex q))
  · intro v hv
    exact mem_univ _
  · intro v hv w hw he
    exact Subtype.ext (congrArg (fun z : FaceVertex q => z.val) he)
  · intro v hv
    exact ⟨faceVertexInclusion hqp v,
      (mem_stalkVertexSet p q (faceVertexInclusion hqp v)).mpr v.property.2, rfl⟩
  · intro v hv
    rfl

theorem polynomialRestriction_faceProduct_of_le {p q r : P}
    (hqp : q ≤ p) (hrp : r ≤ p) (hrq : r ≤ q) :
    polynomialRestriction K hqp (faceProduct K p r) = faceProduct K q r := by
  rw [faceProduct_of_le K hrp, faceProduct_of_le K hrq, map_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [polynomialRestriction_X]
  change (if h : v.val ≤ q then X ⟨v.val, v.property.1, h⟩ else 0) =
    X (faceVertexInclusion hrq v)
  rw [dif_pos (v.property.2.trans hrq)]
  congr 1

include hs in
theorem polynomialRestriction_faceProduct_of_not_le {p q r : P}
    (hqp : q ≤ p) (hrp : r ≤ p) (hrq : ¬ r ≤ q) :
    polynomialRestriction K hqp (faceProduct K p r) = 0 := by
  have hn : ¬ faceVertices r ⊆ faceVertices q := by
    intro h
    exact hrq ((faceVertices_subset_iff hs hrp hqp).mp h)
  obtain ⟨v, hvr, hvq⟩ := Finset.not_subset.mp hn
  obtain ⟨hat, hvr⟩ := mem_faceVertices.mp hvr
  have hnq : ¬ v ≤ q := fun h => hvq (mem_faceVertices.mpr ⟨hat, h⟩)
  rw [faceProduct, map_prod]
  apply Finset.prod_eq_zero ((mem_stalkVertexSet p r ⟨v, hat, hvr.trans hrp⟩).mpr hvr :
    (⟨v, hat, hvr.trans hrp⟩ : FaceVertex p) ∈ stalkVertexSet p r)
  simp [hnq]

include hs in
theorem polynomialRestriction_faceValue {p q : P} (hqp : q ≤ p) (r : P) :
    polynomialRestriction K hqp (faceValue K p r) = faceValue K q r := by
  by_cases hrp : r ≤ p
  · by_cases hrq : r ≤ q
    · simp only [faceValue, if_pos hrp, if_pos hrq]
      exact polynomialRestriction_faceProduct_of_le K hqp hrp hrq
    · simp only [faceValue, if_pos hrp, if_neg hrq]
      exact polynomialRestriction_faceProduct_of_not_le K hs hqp hrp hrq
  · have hrq : ¬ r ≤ q := fun h => hrp (h.trans hqp)
    simp [faceValue, hrp, hrq]

include hs in
theorem faceEvaluation_naturality {p q : P} (hqp : q ≤ p) :
    (polynomialRestriction K hqp).comp (faceEvaluation K p) = faceEvaluation K q := by
  apply MvPolynomial.algHom_ext
  intro r
  simp only [AlgHom.comp_apply, faceEvaluation, MvPolynomial.aeval_X]
  exact polynomialRestriction_faceValue K hs hqp r.val

theorem faceRingEvaluation_naturality {p q : P} (hqp : q ≤ p)
    (f : FaceRing K hs) :
    polynomialRestriction K hqp (faceRingEvaluation K hs p f) =
      faceRingEvaluation K hs q f := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
  exact DFunLike.congr_fun (faceEvaluation_naturality K hs hqp) g

/-- The section map is induced by the conventional quotient presentation. -/
def faceRingSection : FaceRing K hs →ₗ[K] (polynomialDiagram (P := P) K).sections where
  toFun f := ⟨fun p => faceRingEvaluation K hs p f,
    fun p q hqp => faceRingEvaluation_naturality K hs hqp f⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact map_add (faceRingEvaluation K hs p) f g
  map_smul' c f := by
    apply Subtype.ext
    funext p
    exact map_smul (faceRingEvaluation K hs p) c f

@[simp] theorem faceRingSection_apply (f : FaceRing K hs) (p : P) :
    (faceRingSection K hs f).val p = faceRingEvaluation K hs p f := rfl

end FourPapers.Universal
end
end

/- BEGIN StandardFaceBasis.lean -/
section


/-! # The standard basis and inverse-limit theorem for the original face ring

The input ring is the original quotient by Stanley's face relations. Spanning
is proved by terminating straightening; independence and gluing are proved by
ordinary polynomial coefficients in actual Boolean intervals.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def polynomialStandardCoordinates (p : P) :
    PolynomialStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p :=
  (polynomialStandardBasis (K := K) hs p).repr.trans
    (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm

@[simp] theorem polynomialStandardCoordinates_basis (p : P) (a : StandardInside p) :
    (polynomialStandardCoordinates K hs p (polynomialStandardBasis hs p a)).val =
      Finsupp.single a.val 1 := by
  change ((Finsupp.supportedEquivFinsupp (R := K) (M := K)
      {b : StandardFaceIndex P | standardCarrier b ≤ p}).symm
        ((polynomialStandardBasis (K := K) hs p).repr
          (polynomialStandardBasis (K := K) hs p a))).val = _
  rw [Module.Basis.repr_self]
  let e := Finsupp.supportedEquivFinsupp (R := K) (M := K)
    {b : StandardFaceIndex P | standardCarrier b ≤ p}
  have hm : (Finsupp.single a.val (1 : K)) ∈
      Finsupp.supported K K {b : StandardFaceIndex P | standardCarrier b ≤ p} := by
    apply (Finsupp.mem_supported' K _).mpr
    intro b hb
    apply Finsupp.single_eq_of_ne
    intro hab
    subst b
    exact hb a.property
  let q : Finsupp.supported K K {b : StandardFaceIndex P | standardCarrier b ≤ p} :=
    ⟨Finsupp.single a.val 1, hm⟩
  have hq : e q = Finsupp.single a 1 := by
    ext b
    change (Finsupp.single a.val (1 : K)) b.val = (Finsupp.single a 1) b
    simp [Finsupp.single_apply, Subtype.ext_iff]
  have he : e.symm (Finsupp.single a 1) = q := by
    apply e.injective
    rw [e.apply_symm_apply, hq]
  exact congrArg Subtype.val he

theorem polynomialStandardCoordinates_evaluation (p : P) (a : StandardFaceIndex P) :
    (polynomialStandardCoordinates K hs p
      (faceRingEvaluation K hs p (faceRingMonomial K hs a.val))).val =
        if standardCarrier a ≤ p then Finsupp.single a 1 else 0 := by
  by_cases ha : standardCarrier a ≤ p
  · rw [if_pos ha, ← polynomialStandardBasis_eq_evaluation (K := K) hs p ⟨a, ha⟩]
    exact polynomialStandardCoordinates_basis K hs p ⟨a, ha⟩
  · rw [if_neg ha, faceRingEvaluation_monomial K hs p a, if_neg ha, LinearEquiv.map_zero]
    rfl

theorem polynomialStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (f : PolynomialStalk K p) :
    coefficientRestriction K standardCarrier hqp (polynomialStandardCoordinates K hs p f) =
      polynomialStandardCoordinates K hs q (polynomialRestriction K hqp f) := by
  suffices he : (coefficientRestriction K standardCarrier hqp).comp
      (polynomialStandardCoordinates K hs p).toLinearMap =
      (polynomialStandardCoordinates K hs q).toLinearMap.comp
        (polynomialRestriction K hqp).toLinearMap by
    exact DFunLike.congr_fun he f
  apply (polynomialStandardBasis (K := K) hs p).ext
  intro a
  apply Subtype.ext
  ext b
  change (coefficientRestriction K standardCarrier hqp
    (polynomialStandardCoordinates K hs p (polynomialStandardBasis hs p a))).val b =
      (polynomialStandardCoordinates K hs q
        (polynomialRestriction K hqp (polynomialStandardBasis hs p a))).val b
  rw [coefficientRestriction_apply, polynomialStandardCoordinates_basis]
  rw [polynomialStandardBasis_eq_evaluation (K := K) hs p a,
    faceRingEvaluation_naturality K hs hqp,
    polynomialStandardCoordinates_evaluation]
  by_cases hab : a.val = b
  · subst b
    by_cases ha : standardCarrier a.val ≤ q <;> simp [ha]
  · by_cases ha : standardCarrier a.val ≤ q <;>
      by_cases hb : standardCarrier b ≤ q <;>
        simp [ha, hb, Finsupp.single_apply, hab, Ne.symm hab]

/-- Coherent coordinates for the actual polynomial diagram. -/
def polynomialCoefficientEquiv :
    CoherentEquiv (polynomialDiagram (P := P) K)
      (coefficientDiagram K (standardCarrier (P := P))) where
  component := polynomialStandardCoordinates K hs
  naturality p q hqp f := polynomialStandardCoordinates_naturality K hs hqp f

/-- Explicit global standard coefficients of a compatible polynomial family. -/
def polynomialSectionCoordinates :
    (polynomialDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  sectionsFromCoherentCoefficients K standardCarrier (polynomialDiagram K)
    (polynomialCoefficientEquiv K hs)

def standardFaceCombination : (StandardFaceIndex P →₀ K) →ₗ[K] FaceRing K hs :=
  Finsupp.linearCombination K (fun a => faceRingMonomial K hs a.val)

theorem standardFaceCombination_surjective : Function.Surjective (standardFaceCombination K hs) := by
  rw [← LinearMap.range_eq_top, standardFaceCombination, Finsupp.range_linearCombination]
  have hrange : Set.range (fun a : StandardFaceIndex P => faceRingMonomial K hs a.val) =
      {x | ∃ a, BarycentricAllowed a ∧ x = faceRingMonomial K hs a} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [hrange]
  exact standardFaceSpan_eq_top K hs

theorem standardFaceCombination_coefficients (x : StandardFaceIndex P →₀ K) :
    polynomialSectionCoordinates K hs (faceRingSection K hs (standardFaceCombination K hs x)) = x := by
  have he : (polynomialSectionCoordinates K hs).toLinearMap.comp
      ((faceRingSection K hs).comp (standardFaceCombination K hs)) = LinearMap.id := by
    apply (Finsupp.basisSingleOne : Module.Basis (StandardFaceIndex P) K
      (StandardFaceIndex P →₀ K)).ext
    intro a
    change polynomialSectionCoordinates K hs
      (faceRingSection K hs (standardFaceCombination K hs (Finsupp.single a 1))) =
        Finsupp.single a 1
    have hc : standardFaceCombination K hs (Finsupp.single a 1) =
        faceRingMonomial K hs a.val := by simp [standardFaceCombination]
    rw [hc]
    apply (coefficientSectionEquiv K standardCarrier).injective
    simp only [polynomialSectionCoordinates, sectionsFromCoherentCoefficients,
      LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change (polynomialCoefficientEquiv K hs).sectionEquiv
      (faceRingSection K hs (faceRingMonomial K hs a.val)) =
        coefficientSection K standardCarrier (Finsupp.single a 1)
    apply Subtype.ext
    funext p
    apply Subtype.ext
    ext b
    change (polynomialStandardCoordinates K hs p
      (faceRingEvaluation K hs p (faceRingMonomial K hs a.val))).val b =
        if standardCarrier b ≤ p then (Finsupp.single a (1 : K)) b else 0
    rw [polynomialStandardCoordinates_evaluation]
    by_cases hab : a = b
    · subst b
      by_cases ha : standardCarrier a ≤ p <;> simp [ha]
    · by_cases ha : standardCarrier a ≤ p <;>
        by_cases hb : standardCarrier b ≤ p <;>
          simp [ha, hb, Finsupp.single_apply, hab, Ne.symm hab]
  exact DFunLike.congr_fun he x

/-- The original face ring has the claimed basis over every commutative ring. -/
def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (standardFaceCombination K hs)
    ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h,
      standardFaceCombination_surjective K hs⟩).symm

@[simp] theorem standardFaceBasis_apply (a : StandardFaceIndex P) :
    standardFaceBasis K hs a = faceRingMonomial K hs a.val := by
  change standardFaceCombination K hs (Finsupp.single a 1) = _
  simp [standardFaceCombination]

/-- The inverse-limit identification is proved for the original quotient. -/
def faceRingSectionEquiv : FaceRing K hs ≃ₗ[K] (polynomialDiagram (P := P) K).sections :=
  (standardFaceBasis K hs).repr.trans (polynomialSectionCoordinates K hs).symm

@[simp] theorem faceRingSectionEquiv_apply (f : FaceRing K hs) :
    faceRingSectionEquiv K hs f = faceRingSection K hs f := by
  obtain ⟨x, rfl⟩ := standardFaceCombination_surjective K hs f
  apply (polynomialSectionCoordinates K hs).injective
  rw [standardFaceCombination_coefficients]
  simp only [faceRingSectionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change (standardFaceBasis K hs).repr (standardFaceCombination K hs x) = x
  exact (LinearEquiv.ofBijective (standardFaceCombination K hs)
    ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h,
      standardFaceCombination_surjective K hs⟩).symm_apply_apply x

end FourPapers.Universal
end
end

/- BEGIN ScalarBasis.lean -/
section


/-! # Recover a basis over an algebra from its expanded coefficient basis -/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

variable {I J K A M : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

theorem linearCombination_bijective_of_scalar_basis
    (bA : Module.Basis J K A) (bM : Module.Basis (I × J) K M) (v : I → M)
    (h : ∀ p : I × J, bM p = bA p.2 • v p.1) :
    Function.Bijective (Finsupp.linearCombination A v) := by
  classical
  let q : (I × J →₀ K) → (I →₀ A) := fun f =>
    Finsupp.mapRange (Finsupp.linearCombination K bA) (map_zero _) f.curry
  have hbA : Function.Bijective (Finsupp.linearCombination K bA) := by
    constructor
    · intro x y hxy
      apply bA.repr.symm.injective
      simpa only [bA.repr_symm_apply] using hxy
    · intro a
      exact ⟨bA.repr a, bA.linearCombination_repr a⟩
  have hq : Function.Bijective q :=
    (Finsupp.mapRange_bijective _ _ hbA).comp Finsupp.curryEquiv.bijective
  have hbM : Function.Bijective
      (Finsupp.linearCombination K (fun p : I × J => bA p.2 • v p.1)) := by
    have he : (fun p : I × J => bA p.2 • v p.1) = bM := funext (fun p => (h p).symm)
    rw [he]
    constructor
    · intro x y hxy
      apply bM.repr.symm.injective
      simpa only [bM.repr_symm_apply] using hxy
    · intro x
      exact ⟨bM.repr x, bM.linearCombination_repr x⟩
  have hc (l : I × J →₀ K) :
      Finsupp.linearCombination K (fun p : I × J => bA p.2 • v p.1) l =
        Finsupp.linearCombination A v (q l) := by
    exact congrArg (fun f : (I × J →₀ K) →ₗ[K] M => f l)
      (Finsupp.linearCombination_smul (R := K) (S := A) (v := v) (w := bA))
  constructor
  · intro f g hfg
    obtain ⟨f', rfl⟩ := hq.surjective f
    obtain ⟨g', rfl⟩ := hq.surjective g
    exact congrArg q (hbM.injective (by simpa only [hc] using hfg))
  · intro x
    obtain ⟨l, hl⟩ := hbM.surjective x
    exact ⟨q l, (hc l).symm.trans hl⟩

/-- The algebra basis, constructed from an actual coefficient-ring basis of
all its scalar-monomial multiples. -/
def basisOfScalarBasis
    (bA : Module.Basis J K A) (bM : Module.Basis (I × J) K M) (v : I → M)
    (h : ∀ p : I × J, bM p = bA p.2 • v p.1) : Module.Basis I A M :=
  Module.Basis.ofRepr
    (LinearEquiv.ofBijective (Finsupp.linearCombination A v)
      (linearCombination_bijective_of_scalar_basis bA bM v h)).symm

@[simp] theorem basisOfScalarBasis_apply
    (bA : Module.Basis J K A) (bM : Module.Basis (I × J) K M) (v : I → M)
    (h : ∀ p : I × J, bM p = bA p.2 • v p.1) (i : I) :
    basisOfScalarBasis bA bM v h i = v i := by
  change Finsupp.linearCombination A v (Finsupp.single i 1) = v i
  simp

end FourPapers.Universal

end
end

/- BEGIN HomogeneousBasis.lean -/
section


/-! # A homogeneous change of basis has a homogeneous inverse

This holds over an arbitrary commutative ring and for arbitrary index sets.
It follows by comparing the actual coefficient projections for each degree.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical

variable {I J D K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def basisDegreeProjection (b : Module.Basis I K M) (degree : I → D) (d : D) :
    M →ₗ[K] M :=
  b.repr.symm.toLinearMap.comp
    (({
      toFun := fun f : I →₀ K => f.filter (fun i => degree i = d)
      map_add' := by
        intro f g
        ext i
        by_cases hi : degree i = d <;> simp [Finsupp.filter_apply, hi]
      map_smul' := by
        intro c f
        ext i
        by_cases hi : degree i = d <;> simp [Finsupp.filter_apply, hi]
    } : (I →₀ K) →ₗ[K] (I →₀ K)).comp b.repr.toLinearMap)

@[simp] theorem basisDegreeProjection_repr (b : Module.Basis I K M)
    (degree : I → D) (d : D) (x : M) (i : I) :
    b.repr (basisDegreeProjection b degree d x) i =
      if degree i = d then b.repr x i else 0 := by
  simp [basisDegreeProjection, Finsupp.filter_apply]

@[simp] theorem basisDegreeProjection_basis (b : Module.Basis I K M)
    (degree : I → D) (d : D) (i : I) :
    basisDegreeProjection b degree d (b i) = if degree i = d then b i else 0 := by
  apply b.repr.injective
  ext j
  by_cases hi : degree i = d
  · by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [basisDegreeProjection_repr, hi, Module.Basis.repr_self,
        Finsupp.single_apply, hji, Ne.symm hji]
  · by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [basisDegreeProjection_repr, hi, Module.Basis.repr_self,
        Finsupp.single_apply, hji, Ne.symm hji]

theorem basisDegreeProjection_eq_of_homogeneous
    (b : Module.Basis I K M) (c : Module.Basis J K M)
    (degree : I → D) (degree' : J → D)
    (h : ∀ i j, degree i ≠ degree' j → b.repr (c j) i = 0) (d : D) :
    basisDegreeProjection b degree d = basisDegreeProjection c degree' d := by
  apply c.ext
  intro j
  rw [basisDegreeProjection_basis]
  apply b.repr.injective
  ext i
  rw [basisDegreeProjection_repr]
  by_cases hj : degree' j = d
  · rw [if_pos hj]
    by_cases hi : degree i = d
    · rw [if_pos hi]
    · rw [if_neg hi]
      exact (h i j (by simpa only [hj] using hi)).symm
  · rw [if_neg hj, map_zero, Finsupp.zero_apply]
    by_cases hi : degree i = d
    · rw [if_pos hi]
      exact h i j (fun he => hj (he.symm.trans hi))
    · rw [if_neg hi]

/-- The inverse coefficient matrix has the same exact degree blocks. -/
theorem basis_repr_homogeneous_symm
    (b : Module.Basis I K M) (c : Module.Basis J K M)
    (degree : I → D) (degree' : J → D)
    (h : ∀ i j, degree i ≠ degree' j → b.repr (c j) i = 0)
    (i : I) (j : J) (hne : degree' j ≠ degree i) : c.repr (b i) j = 0 := by
  have he := congrArg (fun f : M →ₗ[K] M => c.repr (f (b i)) j)
    (basisDegreeProjection_eq_of_homogeneous b c degree degree' h (degree i))
  simpa [hne] using he

end FourPapers.Universal
end
end

/- BEGIN ChainWeight.lean -/
section


/-! # Equality with the paper's rank-weight filtration

For a chain of faces, the minimum of two vertex exponents counts exactly
the face factors containing both vertices. This identifies the quadratic
overlap formula with the original sum of face-rank weights.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem chain_membership_filters_comparable {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) (x y : V) :
    (∀ F ∈ a.support, x ∈ F.val → y ∈ F.val) ∨
      (∀ F ∈ a.support, y ∈ F.val → x ∈ F.val) := by
  by_cases h : ∀ F ∈ a.support, x ∈ F.val → y ∈ F.val
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨F, hF, hx, hy⟩ := h
    intro G hG hyG
    rcases ha F hF G hG with hFG | hGF
    · exact hFG hx
    · exact (hy (hGF hyG)).elim

theorem chainVertexMap_min {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) (x y : V) :
    min (chainVertexMap a x) (chainVertexMap a y) =
      ∑ F ∈ a.support, if x ∈ F.val ∧ y ∈ F.val then a F else 0 := by
  have one_direction (x y : V)
      (h : ∀ F ∈ a.support, x ∈ F.val → y ∈ F.val) :
      min (chainVertexMap a x) (chainVertexMap a y) =
        ∑ F ∈ a.support, if x ∈ F.val ∧ y ∈ F.val then a F else 0 := by
    have hle : chainVertexMap a x ≤ chainVertexMap a y := by
      rw [chainVertexMap_apply, chainVertexMap_apply]
      apply Finset.sum_le_sum
      intro F hF
      by_cases hx : x ∈ F.val
      · simp [hx, h F hF hx]
      · simp [hx]
    rw [min_eq_left hle, chainVertexMap_apply]
    apply Finset.sum_congr rfl
    intro F hF
    by_cases hx : x ∈ F.val
    · simp [hx, h F hF hx]
    · simp [hx]
  rcases chain_membership_filters_comparable ha x y with hxy | hyx
  · exact one_direction x y hxy
  · simpa only [min_comm, and_comm] using one_direction y x hyx

theorem vertexDegree_chainVertexMap (a : BooleanFace V →₀ ℕ) :
    vertexDegree (fun v => chainVertexMap a v) =
      ∑ F ∈ a.support, a F * F.val.card := by
  unfold vertexDegree
  simp only [chainVertexMap_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hF
  simp [mul_comm]

theorem overlapCost_chainVertexMap {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) :
    overlapCost (fun v => chainVertexMap a v) =
      ∑ F ∈ a.support, a F * (F.val.card * F.val.card) := by
  unfold overlapCost
  simp only [chainVertexMap_min ha]
  calc
    (∑ x : V, ∑ y : V, ∑ F ∈ a.support,
        if x ∈ F.val ∧ y ∈ F.val then a F else 0) =
        ∑ x : V, ∑ F ∈ a.support, ∑ y : V,
          if x ∈ F.val ∧ y ∈ F.val then a F else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ =
        ∑ F ∈ a.support, ∑ x : V, ∑ y : V,
          if x ∈ F.val ∧ y ∈ F.val then a F else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ F ∈ a.support, a F * (F.val.card * F.val.card) := by
      apply Finset.sum_congr rfl
      intro F hF
      simp only [ite_and]
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- The original face weight, with arbitrary ambient rank `d`. -/
def chainRankWeight (d : ℕ) (a : BooleanFace V →₀ ℕ) : ℤ :=
  ∑ F ∈ a.support, (a F : ℤ) * rankWeight d F.val.card

/-- Equality of the exact filtrations, for all chain monomials and every
ambient rank. No replacement by ordinary degree or chain length occurs. -/
theorem polynomialRankWeight_chainVertexMap (d : ℕ)
    {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    polynomialRankWeight d (fun v => chainVertexMap a v) = chainRankWeight d a := by
  rw [polynomialRankWeight, vertexDegree_chainVertexMap,
    overlapCost_chainVertexMap ha]
  simp only [Nat.cast_sum, Nat.cast_mul, chainRankWeight]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  unfold rankWeight
  ring

end FourPapers.Universal
end
end

/- BEGIN PolynomialWeightExpansion.lean -/
section


/-! # The strict polynomial weight drop for nonchain products -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T]

def occurrenceSet (F : T → Finset V) (v : V) : Finset T :=
  Finset.univ.filter (fun t => v ∈ F t)

@[simp] theorem occurrenceSet_card (F : T → Finset V) (v : V) :
    (occurrenceSet F v).card = occurrenceExponent F v := by
  simp [occurrenceSet, occurrenceExponent_apply]

@[simp] theorem occurrenceExponent_occurrenceSet (F : T → Finset V) (t : T) :
    occurrenceExponent (occurrenceSet F) t = (F t).card := by
  simp [occurrenceSet, occurrenceExponent_apply]

theorem overlapCost_occurrence_lower (F : T → Finset V) :
    (∑ t, (F t).card * (F t).card) ≤
      overlapCost (fun v => occurrenceExponent F v) := by
  have h := quadraticRank_occurrence_le (occurrenceSet F)
  simpa only [quadraticRank, occurrenceExponent_occurrenceSet,
    rankCapacity, occurrenceSet_card, overlapCost] using h

theorem occurrenceSet_not_chain (F : T → Finset V)
    (h : ∃ s t, ¬ (F s ⊆ F t ∨ F t ⊆ F s)) :
    ∃ x y : V, ¬ (occurrenceSet F x ⊆ occurrenceSet F y ∨
      occurrenceSet F y ⊆ occurrenceSet F x) := by
  obtain ⟨s, t, h⟩ := h
  have hst : ¬ F s ⊆ F t := fun hs => h (Or.inl hs)
  have hts : ¬ F t ⊆ F s := fun hs => h (Or.inr hs)
  obtain ⟨x, hxs, hxt⟩ := Finset.not_subset.mp hst
  obtain ⟨y, hyt, hys⟩ := Finset.not_subset.mp hts
  refine ⟨x, y, ?_⟩
  rintro (hxy | hyx)
  · have hs : s ∈ occurrenceSet F x := by simp [occurrenceSet, hxs]
    have := hxy hs
    exact hys (by simpa [occurrenceSet] using this)
  · have ht : t ∈ occurrenceSet F y := by simp [occurrenceSet, hyt]
    have := hyx ht
    exact hxt (by simpa [occurrenceSet] using this)

theorem overlapCost_occurrence_strict (F : T → Finset V)
    (h : ∃ s t, ¬ (F s ⊆ F t ∨ F t ⊆ F s)) :
    (∑ t, (F t).card * (F t).card) <
      overlapCost (fun v => occurrenceExponent F v) := by
  have h' := quadraticRank_occurrence_lt_of_not_chain
    (occurrenceSet F) (occurrenceSet_not_chain F h)
  simpa only [quadraticRank, occurrenceExponent_occurrenceSet,
    rankCapacity, occurrenceSet_card, overlapCost] using h'

theorem vertexDegree_occurrence (F : T → Finset V) :
    vertexDegree (fun v => occurrenceExponent F v) = ∑ t, (F t).card := by
  simp only [vertexDegree, occurrenceExponent_apply]
  rw [Finset.sum_comm]
  simp

theorem rankWeight_sum_formula (d : ℕ) (F : T → Finset V) :
    (∑ t, rankWeight d (F t).card) =
      2 * (d : ℤ) * (∑ t, (F t).card : ℕ) -
        (∑ t, (F t).card * (F t).card : ℕ) := by
  simp only [rankWeight, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem polynomialRankWeight_occurrence_le (d : ℕ) (F : T → Finset V) :
    polynomialRankWeight d (fun v => occurrenceExponent F v) ≤
      ∑ t, rankWeight d (F t).card := by
  have h : ((∑ t, (F t).card * (F t).card : ℕ) : ℤ) ≤
      (overlapCost (fun v => occurrenceExponent F v) : ℤ) := by
    exact_mod_cast overlapCost_occurrence_lower F
  rw [polynomialRankWeight, vertexDegree_occurrence, rankWeight_sum_formula]
  omega

theorem polynomialRankWeight_occurrence_lt_of_not_chain (d : ℕ) (F : T → Finset V)
    (h : ∃ s t, ¬ (F s ⊆ F t ∨ F t ⊆ F s)) :
    polynomialRankWeight d (fun v => occurrenceExponent F v) <
      ∑ t, rankWeight d (F t).card := by
  have h' : ((∑ t, (F t).card * (F t).card : ℕ) : ℤ) <
      (overlapCost (fun v => occurrenceExponent F v) : ℤ) := by
    exact_mod_cast overlapCost_occurrence_strict F h
  rw [polynomialRankWeight, vertexDegree_occurrence, rankWeight_sum_formula]
  omega

end FourPapers.Universal

end
end

/- BEGIN FullSupportIdeal.lean -/
section


/-! # Coefficient characterization of the product-of-variables ideal -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable (V : Type*) [Fintype V]

/-- The squarefree exponent using every variable. -/
def fullExponent : V →₀ ℕ := ∑ v : V, Finsupp.single v 1

@[simp] theorem fullExponent_apply (v : V) : fullExponent V v = 1 := by
  simp [fullExponent, Finsupp.sum_apply, Finsupp.single_apply]

theorem fullExponent_le_iff (a : V →₀ ℕ) :
    fullExponent V ≤ a ↔ a.support = univ := by
  constructor
  · intro h
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    apply Finsupp.mem_support_iff.mpr
    have hv : 1 ≤ a v := by simpa using h v
    omega
  · intro h v
    have hv : a v ≠ 0 := Finsupp.mem_support_iff.mp (h ▸ mem_univ v)
    simpa using Nat.one_le_iff_ne_zero.mpr hv

def OmitsVertex (a : V →₀ ℕ) : Prop := ¬ fullExponent V ≤ a

theorem omitsVertex_iff (a : V →₀ ℕ) : OmitsVertex V a ↔ a.support ≠ univ := by
  rw [OmitsVertex, fullExponent_le_iff]

theorem omitsVertex_divisorClosed : IsDivisorClosed (OmitsVertex V) := by
  intro a b hab hb ha
  exact hb (ha.trans hab)

variable (K : Type*) [CommRing K]

theorem full_monomial_eq_prod :
    (monomial (fullExponent V) (1 : K)) = ∏ v : V, X v := by
  rw [fullExponent, monomial_sum_one]
  rfl

/-- This is an equality of actual ideals in the polynomial ring. -/
theorem forbiddenIdeal_omitsVertex_eq :
    forbiddenIdeal (K := K) (OmitsVertex V) =
      Ideal.span {∏ v : V, (X v : MvPolynomial V K)} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    have hle : fullExponent V ≤ a := Classical.not_not.mp ha
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    apply Ideal.mem_span_singleton.mpr
    refine ⟨monomial c 1, ?_⟩
    rw [← full_monomial_eq_prod V K, monomial_mul, mul_one]
    exact congrArg (fun b => monomial b (1 : K)) hc
  · apply Ideal.span_le.mpr
    rintro f (rfl : f = _)
    rw [← full_monomial_eq_prod V K]
    exact Ideal.subset_span ⟨fullExponent V, by simp [OmitsVertex], rfl⟩

theorem mem_full_product_ideal_iff (f : MvPolynomial V K) :
    f ∈ Ideal.span {∏ v : V, (X v : MvPolynomial V K)} ↔
      ∀ a : V →₀ ℕ, a.support ≠ univ → f.coeff a = 0 := by
  rw [← forbiddenIdeal_omitsVertex_eq V K,
    mem_forbiddenIdeal (OmitsVertex V) (omitsVertex_divisorClosed V)]
  simp only [omitsVertex_iff]

end FourPapers.Universal
end
end

/- BEGIN PolynomialBooleanBoundary.lean -/
section


/-! # The polynomial Boolean boundary and its canonical section

This is the genuine quotient by the product of all vertex variables. The section
retains exactly the monomials omitting a vertex and is defined over every
commutative coefficient ring.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {V K : Type*} [Fintype V] [CommRing K]

abbrev PolynomialBoundaryRing (V K : Type*) [Fintype V] [CommRing K] :=
  MonomialQuotient (K := K) (OmitsVertex V)

def polynomialBooleanBoundaryMap : MvPolynomial V K →ₐ[K] PolynomialBoundaryRing V K :=
  Ideal.Quotient.mkₐ K (forbiddenIdeal (OmitsVertex V))

def polynomialBooleanBoundarySection :
    PolynomialBoundaryRing V K →ₗ[K] MvPolynomial V K :=
  (standardMonomialBasis (OmitsVertex V) (omitsVertex_divisorClosed V)).constr K
    (fun a => MvPolynomial.monomial a.val 1)

@[simp] theorem polynomialBooleanBoundarySection_basis
    (a : {a : V →₀ ℕ // OmitsVertex V a}) :
    polynomialBooleanBoundarySection
      (standardMonomialBasis (K := K) (OmitsVertex V) (omitsVertex_divisorClosed V) a) =
        MvPolynomial.monomial a.val 1 :=
  Module.Basis.constr_basis _ _ _ _

theorem polynomialBooleanBoundaryMap_section (x : PolynomialBoundaryRing V K) :
    polynomialBooleanBoundaryMap (polynomialBooleanBoundarySection x) = x := by
  have he : (polynomialBooleanBoundaryMap (V := V) (K := K)).toLinearMap.comp
      polynomialBooleanBoundarySection = LinearMap.id := by
    apply (standardMonomialBasis (OmitsVertex V) (omitsVertex_divisorClosed V)).ext
    intro a
    change polynomialBooleanBoundaryMap
      (polynomialBooleanBoundarySection
        (standardMonomialBasis (K := K) (OmitsVertex V) (omitsVertex_divisorClosed V) a)) = _
    rw [polynomialBooleanBoundarySection_basis, standardMonomialBasis_apply]
    rfl
  exact DFunLike.congr_fun he x

theorem polynomialBooleanBoundaryMap_surjective :
    Function.Surjective (polynomialBooleanBoundaryMap (V := V) (K := K)) :=
  fun x => ⟨polynomialBooleanBoundarySection x, polynomialBooleanBoundaryMap_section x⟩

theorem polynomialBooleanBoundaryMap_eq_zero_iff (f : MvPolynomial V K) :
    polynomialBooleanBoundaryMap f = 0 ↔
      ∃ g : MvPolynomial V K, (∏ v : V, X v) * g = f := by
  change Ideal.Quotient.mk (forbiddenIdeal (OmitsVertex V)) f = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, forbiddenIdeal_omitsVertex_eq V K,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.symm⟩

theorem polynomialBooleanBoundarySection_coefficient
    (x : PolynomialBoundaryRing V K) (a : V →₀ ℕ) :
    (polynomialBooleanBoundarySection x).coeff a =
      if h : OmitsVertex V a then
        (standardMonomialBasis (OmitsVertex V) (omitsVertex_divisorClosed V)).repr x ⟨a, h⟩
      else 0 := by
  let b := standardMonomialBasis (K := K) (OmitsVertex V) (omitsVertex_divisorClosed V)
  by_cases ha : OmitsVertex V a
  · rw [dif_pos ha]
    have he : (MvPolynomial.lcoeff K a).comp polynomialBooleanBoundarySection =
        (Finsupp.lapply ⟨a, ha⟩).comp b.repr.toLinearMap := by
      apply b.ext
      intro i
      change (polynomialBooleanBoundarySection (b i)).coeff a = b.repr (b i) ⟨a, ha⟩
      rw [polynomialBooleanBoundarySection_basis, Module.Basis.repr_self]
      simp [MvPolynomial.coeff_monomial, Finsupp.single_apply, Subtype.ext_iff, eq_comm]
    exact DFunLike.congr_fun he x
  · rw [dif_neg ha]
    have he : (MvPolynomial.lcoeff K a).comp polynomialBooleanBoundarySection = 0 := by
      apply b.ext
      intro i
      change (polynomialBooleanBoundarySection (b i)).coeff a = 0
      rw [polynomialBooleanBoundarySection_basis]
      have hai : i.val ≠ a := by intro hi; exact ha (hi ▸ i.property)
      simp [MvPolynomial.coeff_monomial, hai, Ne.symm hai]
    exact DFunLike.congr_fun he x

/-- The actual elementary-symmetric parameter action on a Boolean polynomial stalk. -/
def polynomialColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] MvPolynomial V K :=
  MvPolynomial.aeval (fun i => MvPolynomial.esymm V K (i.val + 1))

/-- Its induced action on the genuine boundary quotient. -/
def polynomialBoundaryColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] PolynomialBoundaryRing V K :=
  polynomialBooleanBoundaryMap.comp polynomialColorMap

@[simp] theorem polynomialBooleanBoundaryMap_parameter_mul
    (a : MvPolynomial (Fin (Fintype.card V)) K) (x : MvPolynomial V K) :
    polynomialBooleanBoundaryMap (polynomialColorMap a * x) =
      polynomialBoundaryColorMap a * polynomialBooleanBoundaryMap x := by
  rw [map_mul]
  rfl

end FourPapers.Universal
end
end

/- BEGIN MonomialCoordinate.lean -/
section


/-! # A free monomial coordinate and its actual quotient

If allowed exponents remain allowed after adding one specified coordinate,
that variable is a nonzerodivisor in the actual monomial quotient. Its quotient
has the exact basis of allowed monomials with zero in that coordinate.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical

variable {V K : Type*} [CommRing K]
variable (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) (t : V)

def IsFreeCoordinate : Prop := ∀ a, P a → P (a + Finsupp.single t 1)

def monomialCoordinate : MonomialQuotient (K := K) P :=
  Ideal.Quotient.mk (forbiddenIdeal P) (MvPolynomial.X t)

def coordinateExponentShift (ht : IsFreeCoordinate P t) : {a // P a} → {a // P a} :=
  fun a => ⟨a.val + Finsupp.single t 1, ht a.val a.property⟩

theorem coordinateExponentShift_injective (ht : IsFreeCoordinate P t) :
    Function.Injective (coordinateExponentShift P t ht) := by
  intro a b h
  apply Subtype.ext
  exact add_right_cancel (congrArg Subtype.val h)

@[simp] theorem standardMonomialBasis_repr_mk (f : MvPolynomial V K) (a : {a // P a}) :
    (standardMonomialBasis (K := K) P hP).repr
      (Ideal.Quotient.mk (forbiddenIdeal P) f) a = f.coeff a.val := rfl

theorem monomialCoordinate_mul_basis (ht : IsFreeCoordinate P t) (a : {a // P a}) :
    monomialCoordinate (K := K) P t * standardMonomialBasis P hP a =
      standardMonomialBasis P hP (coordinateExponentShift P t ht a) := by
  rw [standardMonomialBasis_apply, standardMonomialBasis_apply]
  unfold monomialCoordinate
  rw [← map_mul]
  simp [MvPolynomial.X, MvPolynomial.monomial_mul, coordinateExponentShift, add_comm]

theorem monomialCoordinate_mul_repr (ht : IsFreeCoordinate P t)
    (x : MonomialQuotient (K := K) P) :
    (standardMonomialBasis P hP).repr (monomialCoordinate P t * x) =
      Finsupp.mapDomain (coordinateExponentShift P t ht)
        ((standardMonomialBasis P hP).repr x) := by
  have h : (standardMonomialBasis (K := K) P hP).repr.toLinearMap.comp
        (LinearMap.mulLeft K (monomialCoordinate P t)) =
      (Finsupp.lmapDomain (R := K) (M := K) (coordinateExponentShift P t ht)).comp
        (standardMonomialBasis P hP).repr.toLinearMap := by
    apply (standardMonomialBasis P hP).ext
    intro a
    change (standardMonomialBasis P hP).repr
      (monomialCoordinate P t * standardMonomialBasis P hP a) =
        Finsupp.mapDomain (coordinateExponentShift P t ht)
          ((standardMonomialBasis P hP).repr (standardMonomialBasis P hP a))
    rw [monomialCoordinate_mul_basis P hP t ht, Module.Basis.repr_self,
      Module.Basis.repr_self, Finsupp.mapDomain_single]
  exact DFunLike.congr_fun h x

include hP in
theorem monomialCoordinate_mul_injective (ht : IsFreeCoordinate P t) :
    Function.Injective (fun x : MonomialQuotient (K := K) P => monomialCoordinate P t * x) := by
  intro x y hxy
  apply (standardMonomialBasis P hP).repr.injective
  apply Finsupp.mapDomain_injective (coordinateExponentShift_injective P t ht)
  rw [← monomialCoordinate_mul_repr P hP t ht,
    ← monomialCoordinate_mul_repr P hP t ht]
  exact congrArg (standardMonomialBasis P hP).repr hxy

def CoordinateBoundary (a : V →₀ ℕ) : Prop := P a ∧ a t = 0

include hP in
theorem coordinateBoundary_divisorClosed : IsDivisorClosed (CoordinateBoundary P t) := by
  intro a b hab hb
  refine ⟨hP hab hb.1, ?_⟩
  exact Nat.eq_zero_of_le_zero (by simpa only [hb.2] using hab t)

theorem forbiddenIdeal_le_coordinateBoundary :
    forbiddenIdeal (K := K) P ≤ forbiddenIdeal (CoordinateBoundary P t) := by
  apply Ideal.span_le.mpr
  rintro f ⟨a, ha, rfl⟩
  exact Ideal.subset_span ⟨a, (fun h => ha h.1), rfl⟩

/-- The actual quotient map obtained by setting the free coordinate to zero. -/
def coordinateBoundaryMap :
    MonomialQuotient (K := K) P →ₐ[K] MonomialQuotient (K := K) (CoordinateBoundary P t) :=
  Ideal.Quotient.factorₐ K (forbiddenIdeal_le_coordinateBoundary (K := K) P t)

@[simp] theorem coordinateBoundaryMap_mk (f : MvPolynomial V K) :
    coordinateBoundaryMap P t (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      Ideal.Quotient.mk (forbiddenIdeal (CoordinateBoundary P t)) f := rfl

theorem coordinateBoundaryMap_coefficient (x : MonomialQuotient (K := K) P)
    (a : {a // CoordinateBoundary P t a}) :
    (standardMonomialBasis (CoordinateBoundary P t)
      (coordinateBoundary_divisorClosed P hP t)).repr (coordinateBoundaryMap P t x) a =
        (standardMonomialBasis P hP).repr x ⟨a.val, a.property.1⟩ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem coordinateBoundaryMap_basis_zero (a : {a // P a}) (ha : a.val t = 0) :
    coordinateBoundaryMap P t (standardMonomialBasis (K := K) P hP a) =
      standardMonomialBasis (CoordinateBoundary P t)
        (coordinateBoundary_divisorClosed P hP t) ⟨a.val, a.property, ha⟩ := by
  rw [standardMonomialBasis_apply, coordinateBoundaryMap_mk,
    standardMonomialBasis_apply]

theorem coordinateBoundaryMap_coordinate :
    coordinateBoundaryMap P t (monomialCoordinate (K := K) P t) = 0 := by
  change Ideal.Quotient.mk (forbiddenIdeal (CoordinateBoundary P t))
    (MvPolynomial.X t) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨Finsupp.single t 1, ?_, rfl⟩
  intro h
  simpa [CoordinateBoundary] using h.2

/-- The coefficientwise section retains precisely the monomials with zero
in the distinguished coordinate. -/
def coordinateBoundarySection :
    MonomialQuotient (K := K) (CoordinateBoundary P t) →ₗ[K] MonomialQuotient (K := K) P :=
  (standardMonomialBasis (CoordinateBoundary P t)
    (coordinateBoundary_divisorClosed P hP t)).constr K
      (fun a => standardMonomialBasis P hP ⟨a.val, a.property.1⟩)

@[simp] theorem coordinateBoundarySection_basis
    (a : {a // CoordinateBoundary P t a}) :
    coordinateBoundarySection P hP t
      (standardMonomialBasis (K := K) (CoordinateBoundary P t)
        (coordinateBoundary_divisorClosed P hP t) a) =
      standardMonomialBasis P hP ⟨a.val, a.property.1⟩ :=
  Module.Basis.constr_basis _ _ _ _

theorem coordinateBoundaryMap_section :
    (coordinateBoundaryMap (K := K) P t).toLinearMap.comp
      (coordinateBoundarySection P hP t) = LinearMap.id := by
  apply (standardMonomialBasis (CoordinateBoundary P t)
    (coordinateBoundary_divisorClosed P hP t)).ext
  intro a
  change coordinateBoundaryMap P t
      (coordinateBoundarySection P hP t
        (standardMonomialBasis (K := K) (CoordinateBoundary P t)
          (coordinateBoundary_divisorClosed P hP t) a)) =
    standardMonomialBasis (CoordinateBoundary P t)
      (coordinateBoundary_divisorClosed P hP t) a
  rw [coordinateBoundarySection_basis]
  exact coordinateBoundaryMap_basis_zero P hP t ⟨a.val, a.property.1⟩ a.property.2

include hP in
theorem coordinateBoundaryMap_surjective :
    Function.Surjective (coordinateBoundaryMap (K := K) P t) := by
  intro x
  exact ⟨coordinateBoundarySection P hP t x,
    DFunLike.congr_fun (coordinateBoundaryMap_section P hP t) x⟩

def coordinateExponentPredecessor (a : {a // P a}) : {a // P a} :=
  ⟨a.val - Finsupp.single t 1, hP tsub_le_self a.property⟩

theorem coordinateExponentShift_predecessor (ht : IsFreeCoordinate P t)
    (a : {a // P a}) (ha : a.val t ≠ 0) :
    coordinateExponentShift P t ht (coordinateExponentPredecessor P hP t a) = a := by
  apply Subtype.ext
  apply tsub_add_cancel_of_le
  intro v
  by_cases hv : v = t
  · subst v
    simpa using Nat.one_le_iff_ne_zero.mpr ha
  · simp [Finsupp.single_apply, hv, Ne.symm hv]

/- Exactness at the actual quotient ring: the kernel is multiplication by
the distinguished variable, with no freeness assumption on the coefficient ring. -/
include hP in
theorem coordinateBoundaryMap_eq_zero_iff (ht : IsFreeCoordinate P t)
    (x : MonomialQuotient (K := K) P) :
    coordinateBoundaryMap P t x = 0 ↔ ∃ y, monomialCoordinate P t * y = x := by
  constructor
  · intro hx
    let b := standardMonomialBasis (K := K) P hP
    let f := b.repr x
    have hz (a : {a // P a}) (ha : a.val t = 0) : f a = 0 := by
      have h := coordinateBoundaryMap_coefficient (K := K) P hP t x
        ⟨a.val, a.property, ha⟩
      rw [hx, LinearEquiv.map_zero, Finsupp.zero_apply] at h
      exact h.symm
    refine ⟨b.repr.symm (Finsupp.mapDomain (coordinateExponentPredecessor P hP t) f), ?_⟩
    apply b.repr.injective
    rw [monomialCoordinate_mul_repr P hP t ht, LinearEquiv.apply_symm_apply]
    rw [← Finsupp.mapDomain_fun_comp]
    change Finsupp.mapDomain _ f = f
    calc
      Finsupp.mapDomain _ f = Finsupp.mapDomain id f := by
        apply Finsupp.mapDomain_congr
        intro a ha
        apply coordinateExponentShift_predecessor P hP t ht a
        intro hat
        exact Finsupp.mem_support_iff.mp ha (hz a hat)
      _ = f := Finsupp.mapDomain_id
  · rintro ⟨y, rfl⟩
    rw [map_mul, coordinateBoundaryMap_coordinate, zero_mul]

end FourPapers.Universal
end
end

/- BEGIN BooleanBoundary.lean -/
section


/-! # The top parameter and the proper Boolean boundary

This is the genuine quotient by the full-face variable. Its coefficientwise
section and exactness are established over arbitrary commutative rings.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V W K : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W] [CommRing K]

def booleanTopFace [Nonempty V] : BooleanFace V := ⟨Finset.univ, Finset.univ_nonempty⟩

@[simp] theorem booleanTopFace_val [Nonempty V] :
    (booleanTopFace (V := V)).val = Finset.univ := rfl

theorem isChainExponent_add_top [Nonempty V]
    {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    IsChainExponent (a + Finsupp.single booleanTopFace 1) := by
  intro F hF G hG
  by_cases hFt : F = booleanTopFace
  · subst F
    exact Or.inr (Finset.subset_univ G.val)
  by_cases hGt : G = booleanTopFace
  · subst G
    exact Or.inl (Finset.subset_univ F.val)
  have hFa : F ∈ a.support := by
    simpa [Finsupp.mem_support_iff, Finsupp.single_apply, hFt, Ne.symm hFt] using hF
  have hGa : G ∈ a.support := by
    simpa [Finsupp.mem_support_iff, Finsupp.single_apply, hGt, Ne.symm hGt] using hG
  exact ha F hFa G hGa

theorem booleanTop_isFreeCoordinate [Nonempty V] :
    IsFreeCoordinate (IsChainExponent (V := V)) booleanTopFace :=
  fun _ ha => isChainExponent_add_top ha

def booleanTop [Nonempty V] : BooleanBarycentricRing V K := faceVariable booleanTopFace

theorem booleanTop_mul_injective [Nonempty V] :
    Function.Injective (fun x : BooleanBarycentricRing V K => booleanTop * x) :=
  monomialCoordinate_mul_injective IsChainExponent isChainExponent_divisorClosed
    booleanTopFace booleanTop_isFreeCoordinate

theorem booleanRankParameter_top [Nonempty V] :
    booleanRankParameter (V := V) (K := K) (Fintype.card V) = booleanTop := by
  unfold booleanRankParameter
  rw [Finset.sum_eq_single (booleanTopFace (V := V))]
  · simp [booleanTop, booleanTopFace]
  · intro F hF hne
    have hn : F.val.card ≠ Fintype.card V := by
      intro he
      apply hne
      apply Subtype.ext
      exact Finset.eq_univ_of_card F.val he
    simp [hn]
  · intro h
    exact (h (Finset.mem_univ _)).elim

abbrev BooleanBoundaryAllowed [Nonempty V] (a : BooleanFace V →₀ ℕ) :=
  CoordinateBoundary IsChainExponent (booleanTopFace (V := V)) a

abbrev BooleanBoundaryRing (V K : Type*) [Fintype V] [DecidableEq V]
    [Nonempty V] [CommRing K] :=
  MonomialQuotient (K := K) (BooleanBoundaryAllowed (V := V))

theorem booleanBoundaryAllowed_iff [Nonempty V] (a : BooleanFace V →₀ ℕ) :
    BooleanBoundaryAllowed a ↔ IsChainExponent a ∧
      ∀ F ∈ a.support, F.val ≠ Finset.univ := by
  constructor
  · rintro ⟨ha, ht⟩
    refine ⟨ha, ?_⟩
    intro F hF he
    have hFt : F = booleanTopFace := Subtype.ext he
    subst F
    exact Finsupp.mem_support_iff.mp hF ht
  · rintro ⟨ha, hproper⟩
    refine ⟨ha, ?_⟩
    by_contra ht
    exact hproper booleanTopFace (Finsupp.mem_support_iff.mpr ht) rfl

def booleanBoundaryMap [Nonempty V] :
    BooleanBarycentricRing V K →ₐ[K] BooleanBoundaryRing V K :=
  coordinateBoundaryMap IsChainExponent booleanTopFace

def booleanBoundarySection [Nonempty V] :
    BooleanBoundaryRing V K →ₗ[K] BooleanBarycentricRing V K :=
  coordinateBoundarySection IsChainExponent isChainExponent_divisorClosed booleanTopFace

theorem booleanBoundaryMap_section [Nonempty V] (x : BooleanBoundaryRing V K) :
    booleanBoundaryMap (booleanBoundarySection x) = x :=
  DFunLike.congr_fun (coordinateBoundaryMap_section IsChainExponent
    isChainExponent_divisorClosed (booleanTopFace (V := V))) x

theorem booleanBoundaryMap_surjective [Nonempty V] :
    Function.Surjective (booleanBoundaryMap (V := V) (K := K)) :=
  coordinateBoundaryMap_surjective IsChainExponent isChainExponent_divisorClosed booleanTopFace

theorem booleanBoundaryMap_eq_zero_iff [Nonempty V] (x : BooleanBarycentricRing V K) :
    booleanBoundaryMap x = 0 ↔ ∃ y, booleanTop * y = x :=
  coordinateBoundaryMap_eq_zero_iff IsChainExponent isChainExponent_divisorClosed
    booleanTopFace booleanTop_isFreeCoordinate x

theorem booleanRestriction_top [Nonempty W] (e : V ↪ W)
    (he : ¬ Function.Surjective e) :
    booleanRestriction (K := K) e booleanTop = 0 := by
  apply booleanRestriction_face_outside
  rintro ⟨F, hF⟩
  apply he
  intro w
  have hw : w ∈ F.val.map e := by
    rw [← booleanFaceEmbedding_val e F, hF]
    exact Finset.mem_univ w
  obtain ⟨v, hv, hvw⟩ := Finset.mem_map.mp hw
  exact ⟨v, hvw⟩

/-- Every proper face restriction factors through the actual top-parameter
quotient. The displayed section is the explicit monomial section. -/
theorem booleanRestriction_boundarySection [Nonempty W] (e : V ↪ W)
    (he : ¬ Function.Surjective e) (x : BooleanBarycentricRing W K) :
    booleanRestriction e (booleanBoundarySection (booleanBoundaryMap x)) =
      booleanRestriction e x := by
  have hz : booleanBoundaryMap (x - booleanBoundarySection (booleanBoundaryMap x)) = 0 := by
    rw [map_sub, booleanBoundaryMap_section, sub_self]
  obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff _).mp hz
  have h := congrArg (booleanRestriction (K := K) e) hy
  rw [map_mul, booleanRestriction_top e he, zero_mul, map_sub] at h
  exact (sub_eq_zero.mp h.symm).symm

end FourPapers.Universal
end
end

/- BEGIN ParameterMaps.lean -/
section


/-!
# Exact linearity over the universal parameter ring

Commuting with the specified parameter multiplications is equivalent to
linearity over the polynomial parameter ring, acting through its actual
algebra homomorphisms. This interface does not replace parameter linearity by
linearity over the coefficient ring.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open MvPolynomial

variable {I K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]

/-- The full scalar compatibility for two specified parameter actions. -/
def IsParameterLinear (φ : MvPolynomial I K →ₐ[K] R)
    (ψ : MvPolynomial I K →ₐ[K] S) (f : R →ₗ[K] S) : Prop :=
  ∀ a x, f (φ a * x) = ψ a * f x

theorem isParameterLinear_iff_X (φ : MvPolynomial I K →ₐ[K] R)
    (ψ : MvPolynomial I K →ₐ[K] S) (f : R →ₗ[K] S) :
    IsParameterLinear φ ψ f ↔ ∀ i x, f (φ (X i) * x) = ψ (X i) * f x := by
  constructor
  · intro h i x
    exact h (X i) x
  · intro h a
    induction a using MvPolynomial.induction_on with
    | C c =>
        intro x
        have hφ : φ (C c) = algebraMap K R c := φ.commutes c
        have hψ : ψ (C c) = algebraMap K S c := ψ.commutes c
        rw [hφ, hψ, ← Algebra.smul_def, ← Algebra.smul_def]
        exact f.map_smul c x
    | add a b ha hb =>
        intro x
        simp only [map_add, add_mul, ha, hb]
    | mul_X a i ha =>
        intro x
        simp only [map_mul, mul_assoc, ha, h]

/-- A coefficient-linear equivalence commuting with each parameter. -/
structure ParameterEquiv (φ : MvPolynomial I K →ₐ[K] R)
    (ψ : MvPolynomial I K →ₐ[K] S) where
  toLinearEquiv : R ≃ₗ[K] S
  map_X_mul : ∀ i x,
    toLinearEquiv (φ (X i) * x) = ψ (X i) * toLinearEquiv x

namespace ParameterEquiv

variable {φ : MvPolynomial I K →ₐ[K] R} {ψ : MvPolynomial I K →ₐ[K] S}

theorem map_parameter_mul (e : ParameterEquiv φ ψ) (a : MvPolynomial I K) (x : R) :
    e.toLinearEquiv (φ a * x) = ψ a * e.toLinearEquiv x :=
  (isParameterLinear_iff_X φ ψ e.toLinearEquiv.toLinearMap).mpr e.map_X_mul a x

/-- The displayed compatibility yields an honest linear equivalence for the
parameter polynomial ring with the two specified scalar actions. -/
def overParameters (e : ParameterEquiv φ ψ) :
    letI := φ.toRingHom.toAlgebra
    letI := ψ.toRingHom.toAlgebra
    R ≃ₗ[MvPolynomial I K] S := by
  letI := φ.toRingHom.toAlgebra
  letI := ψ.toRingHom.toAlgebra
  exact
    { e.toLinearEquiv.toAddEquiv with
      map_smul' := fun a x => e.map_parameter_mul a x }

@[simp] theorem overParameters_apply (e : ParameterEquiv φ ψ) (x : R) :
    e.overParameters x = e.toLinearEquiv x := rfl

def symm (e : ParameterEquiv φ ψ) : ParameterEquiv ψ φ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_X_mul i y := by
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.apply_symm_apply, e.map_X_mul,
      e.toLinearEquiv.apply_symm_apply]

end ParameterEquiv

end FourPapers.Universal
end
end

/- BEGIN LeadingMaps.lean -/
section


/-! # Invertibility from the prescribed canonical leading symbols

The index set may be infinite and the coefficient ring may have zero divisors.
The natural-number rank makes every downward correction terminate.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

variable {I K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- An actual map has the prescribed leading symbol on every standard basis
vector, and every other coefficient has strictly lower rank. -/
def HasCanonicalLeading (b : Module.Basis I K M) (c : Module.Basis I K N)
    (rank : I → ℕ) (f : M →ₗ[K] N) : Prop :=
  (∀ i, c.repr (f (b i)) i = 1) ∧
    ∀ i j, i ≠ j → rank i ≤ rank j → c.repr (f (b i)) j = 0

/-- A map with those leading symbols is an actual isomorphism. -/
def canonicalLeadingEquiv (b : Module.Basis I K M) (c : Module.Basis I K N)
    (rank : I → ℕ) (f : M →ₗ[K] N) (hf : HasCanonicalLeading b c rank f) : M ≃ₗ[K] N :=
  b.repr.trans (rankTriangularBasis c (fun i => f (b i)) rank hf.1 hf.2).repr.symm

@[simp] theorem canonicalLeadingEquiv_basis (b : Module.Basis I K M) (c : Module.Basis I K N)
    (rank : I → ℕ) (f : M →ₗ[K] N) (hf : HasCanonicalLeading b c rank f) (i : I) :
    canonicalLeadingEquiv b c rank f hf (b i) = f (b i) := by
  simp only [canonicalLeadingEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Module.Basis.repr_symm_single, rankTriangularBasis_apply, one_smul]

@[simp] theorem canonicalLeadingEquiv_apply (b : Module.Basis I K M) (c : Module.Basis I K N)
    (rank : I → ℕ) (f : M →ₗ[K] N) (hf : HasCanonicalLeading b c rank f) (x : M) :
    canonicalLeadingEquiv b c rank f hf x = f x := by
  have he : (canonicalLeadingEquiv b c rank f hf).toLinearMap = f :=
    b.ext (canonicalLeadingEquiv_basis b c rank f hf)
  exact DFunLike.congr_fun he x

theorem canonicalLeading_bijective (b : Module.Basis I K M) (c : Module.Basis I K N)
    (rank : I → ℕ) (f : M →ₗ[K] N) (hf : HasCanonicalLeading b c rank f) :
    Function.Bijective f := by
  have he : (canonicalLeadingEquiv b c rank f hf : M → N) = f :=
    funext (canonicalLeadingEquiv_apply b c rank f hf)
  rw [← he]
  exact (canonicalLeadingEquiv b c rank f hf).bijective

end FourPapers.Universal
end
end

/- BEGIN CarrierBoundaryLift.lean -/
section


/-! # Boundary extension in the actual carrier coordinates

Only proper carriers are retained. The coefficient at an index is read at its
smallest supporting face. This is the finite boundary operation used in the
coherent induction; its leading-term assertion is proved coefficient by coefficient.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable {P I K : Type*} [PartialOrder P] [Fintype P] [CommRing K]

def stalkBoundaryRestriction (D : ModuleDiagram K P) (p : P) :
    D.obj p →ₗ[K] (D.restrict (Set.Iio p)).sections where
  toFun x := ⟨fun q => D.res q.property.le x, by
    intro q r h
    exact D.res_comp q.property.le h x⟩
  map_add' x y := by
    apply Subtype.ext
    funext q
    exact (D.res q.property.le).map_add x y
  map_smul' c x := by
    apply Subtype.ext
    funext q
    exact (D.res q.property.le).map_smul c x

variable (carrier : I → P)

def coefficientUnit (p : P) (i : I) (hi : carrier i ≤ p) : coefficientStalk K carrier p :=
  ⟨Finsupp.single i 1, (Finsupp.mem_supported' K _).mpr (by
    intro j hj
    apply Finsupp.single_eq_of_ne
    intro h
    subst j
    exact hj hi)⟩

@[simp] theorem coefficientUnit_apply (p : P) (i : I) (hi : carrier i ≤ p) (j : I) :
    (coefficientUnit (K := K) carrier p i hi).val j = if i = j then 1 else 0 := by
  simp [coefficientUnit, Finsupp.single_apply, eq_comm]

theorem coefficientRestriction_unit {p q : P} (hqp : q ≤ p) (i : I) (hi : carrier i ≤ p) :
    coefficientRestriction K carrier hqp (coefficientUnit carrier p i hi) =
      if h : carrier i ≤ q then coefficientUnit carrier q i h else 0 := by
  apply Subtype.ext
  ext j
  by_cases h : carrier i ≤ q
  · rw [dif_pos h]
    simp only [coefficientRestriction_apply, coefficientUnit_apply]
    by_cases hij : i = j
    · subst j
      simp [h]
    · simp [hij]
  · rw [dif_neg h]
    simp only [coefficientRestriction_apply, coefficientUnit_apply]
    by_cases hij : i = j
    · subst j
      simp [h]
    · simp [hij]

def coefficientBoundaryValue (p : P)
    (x : ((coefficientDiagram K carrier).restrict (Set.Iio p)).sections) (i : I) : K :=
  if h : carrier i < p then (x.val ⟨carrier i, h⟩).val i else 0

def coefficientBoundaryExtension (p : P) :
    ((coefficientDiagram K carrier).restrict (Set.Iio p)).sections →ₗ[K]
      coefficientStalk K carrier p where
  toFun x := ⟨Finsupp.onFinset
    (Finset.univ.biUnion fun q : Set.Iio p => (x.val q).val.support)
    (coefficientBoundaryValue carrier p x) (by
      intro i hi
      have hc : carrier i < p := by
        by_contra hn
        exact hi (by simp [coefficientBoundaryValue, hn])
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨carrier i, hc⟩, Finset.mem_univ _, ?_⟩
      apply Finsupp.mem_support_iff.mpr
      simpa only [coefficientBoundaryValue, dif_pos hc] using hi),
    (Finsupp.mem_supported' K _).mpr (by
      intro i hi
      change coefficientBoundaryValue carrier p x i = 0
      have hn : ¬ carrier i < p := fun h => hi h.le
      simp [coefficientBoundaryValue, hn])⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    change coefficientBoundaryValue carrier p (x + y) i =
      coefficientBoundaryValue carrier p x i + coefficientBoundaryValue carrier p y i
    unfold coefficientBoundaryValue
    split_ifs
    · rfl
    · simp
  map_smul' c x := by
    apply Subtype.ext
    ext i
    change coefficientBoundaryValue carrier p (c • x) i =
      c • coefficientBoundaryValue carrier p x i
    unfold coefficientBoundaryValue
    split_ifs
    · rfl
    · exact (smul_zero c).symm

@[simp] theorem coefficientBoundaryExtension_apply (p : P)
    (x : ((coefficientDiagram K carrier).restrict (Set.Iio p)).sections) (i : I) :
    (coefficientBoundaryExtension carrier p x).val i =
      if h : carrier i < p then (x.val ⟨carrier i, h⟩).val i else 0 := rfl

theorem coefficientBoundaryExtension_restrict (p : P)
    (x : ((coefficientDiagram K carrier).restrict (Set.Iio p)).sections) :
    stalkBoundaryRestriction (coefficientDiagram K carrier) p
      (coefficientBoundaryExtension carrier p x) = x := by
  apply Subtype.ext
  funext q
  apply Subtype.ext
  ext i
  change (coefficientRestriction K carrier q.property.le
    (coefficientBoundaryExtension carrier p x)).val i = (x.val q).val i
  rw [coefficientRestriction_apply, coefficientBoundaryExtension_apply]
  by_cases hi : carrier i ≤ q.val
  · rw [if_pos hi, dif_pos (hi.trans_lt q.property)]
    have h := congrArg (fun z : coefficientStalk K carrier (carrier i) => z.val i)
      (x.property q ⟨carrier i, hi.trans_lt q.property⟩ hi)
    change (if carrier i ≤ carrier i then (x.val q).val i else 0) =
      (x.val ⟨carrier i, hi.trans_lt q.property⟩).val i at h
    rw [if_pos le_rfl] at h
    exact h.symm
  · rw [if_neg hi]
    exact ((Finsupp.mem_supported' K _).mp (x.val q).property i hi).symm

/-- The precise leading-term hypothesis on already constructed proper faces. -/
def HasCarrierLeading (weight : I → ℤ) (p : P)
    (e : CoherentEquiv ((coefficientDiagram K carrier).restrict (Set.Iio p))
      ((coefficientDiagram K carrier).restrict (Set.Iio p))) : Prop :=
  ∀ (q : Set.Iio p) (i : I) (hi : carrier i ≤ q.val) (j : I),
    weight i ≤ weight j →
    (e.component q (coefficientUnit carrier q.val i hi)).val j = if i = j then 1 else 0

/-- The boundary extension preserves the canonical leading symbol of every
standard generator with proper carrier. No extension property is assumed. -/
theorem coefficientBoundaryExtension_leading (weight : I → ℤ) (p : P)
    (e : CoherentEquiv ((coefficientDiagram K carrier).restrict (Set.Iio p))
      ((coefficientDiagram K carrier).restrict (Set.Iio p)))
    (he : HasCarrierLeading carrier weight p e) (i : I) (hi : carrier i < p)
    (j : I) (hij : weight i ≤ weight j) :
    (coefficientBoundaryExtension carrier p
      (e.sectionEquiv (stalkBoundaryRestriction (coefficientDiagram K carrier) p
        (coefficientUnit carrier p i hi.le)))).val j = if i = j then 1 else 0 := by
  rw [coefficientBoundaryExtension_apply]
  by_cases hj : carrier j < p
  · rw [dif_pos hj]
    change (e.component ⟨carrier j, hj⟩
      (coefficientRestriction K carrier hj.le (coefficientUnit carrier p i hi.le))).val j = _
    rw [coefficientRestriction_unit]
    by_cases h : carrier i ≤ carrier j
    · rw [dif_pos h]
      exact he ⟨carrier j, hj⟩ i h j hij
    · rw [dif_neg h]
      have hn : i ≠ j := by intro h'; subst j; exact h le_rfl
      have hz := LinearEquiv.map_zero (e.component ⟨carrier j, hj⟩)
      have hz' := congrArg (fun z : coefficientStalk K carrier (carrier j) => z.val j) hz
      change (e.component ⟨carrier j, hj⟩ 0).val j = 0 at hz'
      rw [if_neg hn]
      exact hz'
  · rw [dif_neg hj]
    have hn : i ≠ j := by intro h'; subst j; exact hj hi
    simp [hn]

end FourPapers.Universal

end
end

/- BEGIN CoherentLifting.lean -/
section


/-!
# Finite coherent assembly from actual boundary lifts

The local lifting hypothesis must be proved for the polynomial and barycentric
stalks before this theorem supplies a face-ring comparison. The theorem also
carries arbitrary pointwise properties of the local equivalences, so grading,
parameter linearity, and prescribed leading symbols can be retained together.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {K P : Type*} [CommRing K] [PartialOrder P] [Fintype P]
variable {D E : ModuleDiagram K P}

abbrev rankCut (rank : P → ℕ) (n : ℕ) : Set P := {p | rank p < n}

theorem coherentEquiv_of_boundaryLifts
    (rank : P → ℕ) (hrank : StrictMono rank)
    (property : ∀ p, (D.obj p ≃ₗ[K] E.obj p) → Prop)
    (lift : ∀ p (e : CoherentEquiv (D.restrict (Set.Iio p)) (E.restrict (Set.Iio p))),
      (∀ q : Set.Iio p, property q.val (e.component q)) →
      ∃ f : D.obj p ≃ₗ[K] E.obj p, property p f ∧
        ∀ (q : Set.Iio p) x, E.res q.property.le (f x) =
          e.component q (D.res q.property.le x)) :
    ∃ e : CoherentEquiv D E, ∀ p, property p (e.component p) := by
  have cuts : ∀ n, ∃ e : CoherentEquiv (D.restrict (rankCut rank n))
      (E.restrict (rankCut rank n)),
      ∀ p : rankCut rank n, property p.val (e.component p) := by
    intro n
    induction n with
    | zero =>
        refine ⟨{ component := fun p => False.elim (Nat.not_lt_zero _ p.property)
                  naturality := by intro p; exact False.elim (Nat.not_lt_zero _ p.property) }, ?_⟩
        intro p
        exact False.elim (Nat.not_lt_zero _ p.property)
    | succ n ih =>
        obtain ⟨old, hold⟩ := ih
        let below (p : rankCut rank (n + 1)) (q : Set.Iio p.val) : rankCut rank n :=
          ⟨q.val, by
            have hq := hrank q.property
            have hp := p.property
            change rank p.val < n + 1 at hp
            change rank q.val < n
            omega⟩
        let boundary (p : rankCut rank (n + 1)) :
            CoherentEquiv (D.restrict (Set.Iio p.val)) (E.restrict (Set.Iio p.val)) :=
          { component := fun q => old.component (below p q)
            naturality := by
              intro q r h x
              exact old.naturality (below p q) (below p r) h x }
        have hboundary (p : rankCut rank (n + 1)) :
            ∀ q : Set.Iio p.val, property q.val ((boundary p).component q) := by
          intro q
          exact hold (below p q)
        let fresh (p : rankCut rank (n + 1)) : D.obj p.val ≃ₗ[K] E.obj p.val :=
          (lift p.val (boundary p) (hboundary p)).choose
        have hfresh (p : rankCut rank (n + 1)) :
            property p.val (fresh p) ∧
              ∀ (q : Set.Iio p.val) x,
                E.res q.property.le (fresh p x) =
                  (boundary p).component q (D.res q.property.le x) :=
          (lift p.val (boundary p) (hboundary p)).choose_spec
        let component (p : rankCut rank (n + 1)) : D.obj p.val ≃ₗ[K] E.obj p.val :=
          if h : rank p.val < n then old.component ⟨p.val, h⟩ else fresh p
        have naturality : ∀ (p q : rankCut rank (n + 1)) (h : q ≤ p) x,
            E.res h (component p x) = component q (D.res h x) := by
          intro p q hqp x
          by_cases hp : rank p.val < n
          · have hq : rank q.val < n := (hrank.monotone hqp).trans_lt hp
            dsimp only [component]
            rw [dif_pos hp, dif_pos hq]
            exact old.naturality ⟨p.val, hp⟩ ⟨q.val, hq⟩ hqp x
          · by_cases he : q = p
            · subst q
              simpa only [D.res_refl, E.res_refl]
            · have hqp' : q.val < p.val := lt_of_le_of_ne hqp (fun h => he (Subtype.ext h))
              have hq : rank q.val < n := by
                have hqr := hrank hqp'
                have hpr := p.property
                change rank p.val < n + 1 at hpr
                omega
              have h := (hfresh p).2 ⟨q.val, hqp'⟩ x
              dsimp only [component]
              rw [dif_neg hp, dif_pos hq]
              exact h
        refine ⟨{ component := component, naturality := naturality }, ?_⟩
        intro p
        by_cases hp : rank p.val < n
        · dsimp only [component]
          rw [dif_pos hp]
          exact hold ⟨p.val, hp⟩
        · dsimp only [component]
          rw [dif_neg hp]
          exact (hfresh p).1
  let n := Finset.univ.sup rank + 1
  have hn (p : P) : rank p < n :=
    Nat.lt_succ_of_le (Finset.le_sup (f := rank) (Finset.mem_univ p))
  obtain ⟨e, he⟩ := cuts n
  refine ⟨{ component := fun p => e.component ⟨p, hn p⟩
            naturality := fun p q h x => e.naturality ⟨p, hn p⟩ ⟨q, hn q⟩ h x }, ?_⟩
  intro p
  exact he ⟨p, hn p⟩

end FourPapers.Universal

end
end

/- BEGIN BooleanFreeness.lean -/
section


/-! # The color-sum descent basis of the Boolean barycentric ring -/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

abbrev ColorExponent (V : Type*) [Fintype V] := Fin (Fintype.card V) →₀ ℕ
abbrev BooleanChainExponent (V : Type*) [Fintype V] [DecidableEq V] :=
  {a : BooleanFace V →₀ ℕ // IsChainExponent a}

theorem booleanChainBasis_repr_sum {J : Type*} (s : Finset J)
    (f : J → BooleanBarycentricRing V K) :
    (booleanChainBasis (K := K)).repr (∑ j ∈ s, f j) =
      ∑ j ∈ s, (booleanChainBasis (K := K)).repr (f j) :=
  map_sum (booleanChainBasis (K := K)).repr.toAddMonoidHom f s

/-- Number of lexicographically later full flags. It strictly decreases
along every non-diagonal term in the Boolean straightening expansion. -/
def orderingRank (σ : VertexOrdering (Fintype.card V) V) : ℕ :=
  (Finset.univ.filter (fun τ : VertexOrdering (Fintype.card V) V =>
    toLex (fun i => σ i) < toLex (fun i => τ i))).card

theorem orderingRank_strictAnti {σ τ : VertexOrdering (Fintype.card V) V}
    (hστ : toLex (fun i => σ i) < toLex (fun i => τ i)) :
    orderingRank τ < orderingRank σ := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro υ hυ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hστ.trans (Finset.mem_filter.mp hυ).2⟩
  · intro he
    have hτ : τ ∈ Finset.univ.filter
        (fun υ : VertexOrdering (Fintype.card V) V =>
          toLex (fun i => σ i) < toLex (fun i => υ i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩
    rw [← he] at hτ
    exact (lt_irrefl _) (Finset.mem_filter.mp hτ).2

def descentColorExponent (σ : VertexOrdering (Fintype.card V) V) : ColorExponent V :=
  ∑ c ∈ orderingDescents σ, Finsupp.single c 1

@[simp] theorem descentColorExponent_apply
    (σ : VertexOrdering (Fintype.card V) V) (c : Fin (Fintype.card V)) :
    descentColorExponent σ c = if c ∈ orderingDescents σ then 1 else 0 := by
  simp [descentColorExponent, Finsupp.single_apply]

theorem descentColorExponent_le_iff
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    descentColorExponent σ ≤ m ↔ orderingDescents σ ⊆ m.support := by
  constructor
  · intro h c hc
    have hm := h c
    simp only [descentColorExponent_apply, if_pos hc] at hm
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h c
    by_cases hc : c ∈ orderingDescents σ
    · have hm := Finsupp.mem_support_iff.mp (h hc)
      simp only [descentColorExponent_apply, if_pos hc]
      omega
    · simp [descentColorExponent_apply, hc]

/-- Subtract exactly one copy of each descent color. This is a genuine
bijection onto unrestricted parameter exponents. -/
def flagParameterEquiv :
    {p : VertexOrdering (Fintype.card V) V × ColorExponent V //
      orderingDescents p.1 ⊆ p.2.support} ≃
      VertexOrdering (Fintype.card V) V × ColorExponent V where
  toFun p := (p.val.1, p.val.2 - descentColorExponent p.val.1)
  invFun p := ⟨(p.1, p.2 + descentColorExponent p.1),
    (descentColorExponent_le_iff _ _).mp (by
      intro c
      simp only [Finsupp.add_apply]
      omega)⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact tsub_add_cancel_of_le ((descentColorExponent_le_iff _ _).mpr p.property)
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact add_tsub_cancel_right _ _

def chainParameterEquiv : BooleanChainExponent V ≃
    VertexOrdering (Fintype.card V) V × ColorExponent V :=
  chainFlagEquiv.trans flagParameterEquiv

@[simp] theorem chainParameterEquiv_fst (a : BooleanChainExponent V) :
    (chainParameterEquiv a).1 = chainOrdering a.val := rfl

@[simp] theorem chainParameterEquiv_snd (a : BooleanChainExponent V) :
    (chainParameterEquiv a).2 =
      chainColorDegree a.val - descentColorExponent (chainOrdering a.val) := rfl

@[simp] theorem chainParameterEquiv_symm_val
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    (chainParameterEquiv.symm p).val =
      prefixExponent p.1 (p.2 + descentColorExponent p.1) := rfl

def descentVector (σ : VertexOrdering (Fintype.card V) V) : BooleanBarycentricRing V K :=
  ∏ c ∈ orderingDescents σ, faceVariable (orderingFace σ c)

def colorPower (m : ColorExponent V) : BooleanBarycentricRing V K :=
  ∏ c : Fin (Fintype.card V), colorSum c ^ m c

def parameterDescentVector
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    BooleanBarycentricRing V K :=
  colorPower p.2 * descentVector p.1

/-- One occurrence for every parameter factor, followed by the fixed descent
factors. Repetition is retained, so the expansion counts coefficients exactly. -/
abbrev DescentFactor (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :=
  (Σ c : Fin (Fintype.card V), Fin (m c)) ⊕ {c // c ∈ orderingDescents σ}

def descentFactorColor (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    DescentFactor σ m → Fin (Fintype.card V)
  | Sum.inl t => t.1
  | Sum.inr c => c.val

def descentFactorChoices (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    DescentFactor σ m → Finset (BooleanFace V)
  | Sum.inl t => facesOfColor t.1
  | Sum.inr c => {orderingFace σ c.val}

def leadingAssignment (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    DescentFactor σ m → BooleanFace V :=
  fun t => orderingFace σ (descentFactorColor σ m t)

def assignmentExponent {T : Type*} [Fintype T] (f : T → BooleanFace V) :
    BooleanFace V →₀ ℕ :=
  ∑ t, Finsupp.single (f t) 1

theorem descentFactorChoices_color
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V)
    (t : DescentFactor σ m) {F : BooleanFace V} (hF : F ∈ descentFactorChoices σ m t) :
    F.color = descentFactorColor σ m t := by
  cases t with
  | inl t => exact (mem_facesOfColor _ _).mp hF
  | inr c =>
    have he : F = orderingFace σ c.val := Finset.mem_singleton.mp hF
    simp [he, descentFactorColor]

theorem leadingAssignment_mem (σ : VertexOrdering (Fintype.card V) V)
    (m : ColorExponent V) :
    leadingAssignment σ m ∈ Fintype.piFinset (descentFactorChoices σ m) := by
  simp only [Fintype.mem_piFinset]
  intro t
  cases t with
  | inl t => simp [leadingAssignment, descentFactorColor, descentFactorChoices]
  | inr c => simp [leadingAssignment, descentFactorColor, descentFactorChoices]

@[simp] theorem assignmentExponent_apply {T : Type*} [Fintype T]
    (f : T → BooleanFace V) (F : BooleanFace V) :
    assignmentExponent f F = (Finset.univ.filter (fun t => f t = F)).card := by
  simp [assignmentExponent, Finsupp.single_apply]

theorem mem_assignmentExponent_support {T : Type*} [Fintype T]
    (f : T → BooleanFace V) (F : BooleanFace V) :
    F ∈ (assignmentExponent f).support ↔ ∃ t, f t = F := by
  rw [Finsupp.mem_support_iff, assignmentExponent_apply]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    exact ⟨t, (Finset.mem_filter.mp ht).2⟩
  · rintro ⟨t, ht⟩
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ht⟩⟩)

theorem descentFactorColor_sum (σ : VertexOrdering (Fintype.card V) V)
    (m : ColorExponent V) :
    (∑ t : DescentFactor σ m, Finsupp.single (descentFactorColor σ m t) 1) =
      m + descentColorExponent σ := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  change (∑ c : Fin (Fintype.card V), ∑ _ : Fin (m c), Finsupp.single c 1) +
      (∑ c : {c // c ∈ orderingDescents σ}, Finsupp.single c.val 1) = _
  rw [← Finset.sum_subtype (orderingDescents σ) (fun _ => Iff.rfl)
    (fun c => Finsupp.single c 1)]
  congr 1
  ext c
  simp [Finsupp.single_apply, Finsupp.smul_apply, smul_eq_mul]

theorem assignmentExponent_colorDegree
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V)
    {f : DescentFactor σ m → BooleanFace V}
    (hf : f ∈ Fintype.piFinset (descentFactorChoices σ m)) :
    chainColorDegree (assignmentExponent f) = m + descentColorExponent σ := by
  rw [chainColorDegree, assignmentExponent, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  rw [← descentFactorColor_sum σ m]
  apply Finset.sum_congr rfl
  intro t ht
  rw [descentFactorChoices_color σ m t ((Fintype.mem_piFinset.mp hf) t)]

theorem assignmentExponent_leading (σ : VertexOrdering (Fintype.card V) V)
    (m : ColorExponent V) :
    assignmentExponent (leadingAssignment σ m) =
      prefixExponent σ (m + descentColorExponent σ) := by
  have h := congrArg (Finsupp.mapDomain (orderingFace σ)) (descentFactorColor_sum σ m)
  simpa only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    prefixExponent, assignmentExponent, leadingAssignment] using h

theorem assignment_refines_descent_prefixes
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V)
    {f : DescentFactor σ m → BooleanFace V}
    (hf : f ∈ Fintype.piFinset (descentFactorChoices σ m))
    (ha : IsChainExponent (assignmentExponent f)) :
    ∀ c, IsOrderingDescent σ c →
      orderingPrefix (chainOrdering (assignmentExponent f)) c = orderingPrefix σ c := by
  intro c hc
  let t : DescentFactor σ m := Sum.inr ⟨c, (mem_orderingDescents σ c).mpr hc⟩
  have hft : f t = orderingFace σ c := by
    exact Finset.mem_singleton.mp ((Fintype.mem_piFinset.mp hf) t)
  have hs : orderingFace σ c ∈ (assignmentExponent f).support :=
    (mem_assignmentExponent_support f _).mpr ⟨t, hft⟩
  have h := chainOrdering_prefix ha hs
  rw [orderingFace_color] at h
  change orderingPrefix (chainOrdering (assignmentExponent f)) c = orderingPrefix σ c at h
  exact h

theorem assignment_eq_leading_of_same_ordering
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V)
    {f : DescentFactor σ m → BooleanFace V}
    (hf : f ∈ Fintype.piFinset (descentFactorChoices σ m))
    (ha : IsChainExponent (assignmentExponent f))
    (horder : chainOrdering (assignmentExponent f) = σ) : f = leadingAssignment σ m := by
  funext t
  have hs : f t ∈ (assignmentExponent f).support :=
    (mem_assignmentExponent_support f _).mpr ⟨t, rfl⟩
  have hface := chainOrdering_face ha hs
  rw [horder, descentFactorChoices_color σ m t ((Fintype.mem_piFinset.mp hf) t)] at hface
  exact hface.symm

theorem assignment_rank_lt
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V)
    {f : DescentFactor σ m → BooleanFace V}
    (hf : f ∈ Fintype.piFinset (descentFactorChoices σ m))
    (ha : IsChainExponent (assignmentExponent f))
    (hne : f ≠ leadingAssignment σ m) :
    orderingRank (chainOrdering (assignmentExponent f)) < orderingRank σ := by
  have hle := ordering_lex_le_of_descent_prefix
    (assignment_refines_descent_prefixes σ m hf ha)
  apply orderingRank_strictAnti
  apply lt_of_le_of_ne hle
  intro he
  have ho : chainOrdering (assignmentExponent f) = σ := by
    apply Equiv.ext
    intro i
    exact (congrFun (congrArg ofLex he) i).symm
  exact hne (assignment_eq_leading_of_same_ordering σ m hf ha ho)

def chainMonomial (a : BooleanFace V →₀ ℕ) : BooleanBarycentricRing V K :=
  Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent) (MvPolynomial.monomial a 1)

theorem chainMonomial_eq_basis {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    chainMonomial (K := K) a = booleanChainBasis ⟨a, ha⟩ := by
  exact (standardMonomialBasis_apply IsChainExponent isChainExponent_divisorClosed ⟨a, ha⟩).symm

theorem chainMonomial_eq_zero_of_not_chain {a : BooleanFace V →₀ ℕ}
    (ha : ¬ IsChainExponent a) : chainMonomial (K := K) a = 0 :=
  chainMonomial_eq_zero ha

theorem product_faceVariables {T : Type*} [Fintype T] (f : T → BooleanFace V) :
    (∏ t, faceVariable (K := K) (f t)) = chainMonomial (assignmentExponent f) := by
  rw [chainMonomial, assignmentExponent, MvPolynomial.monomial_sum_one, map_prod]
  rfl

theorem parameterDescentVector_eq_factorProduct
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    parameterDescentVector (K := K) (σ, m) =
      ∏ t : DescentFactor σ m,
        ∑ F ∈ descentFactorChoices σ m t, faceVariable F := by
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [descentFactorChoices, Finset.sum_singleton]
  rw [← Finset.prod_subtype (orderingDescents σ) (fun _ => Iff.rfl)
    (fun c => faceVariable (K := K) (orderingFace σ c))]
  simp [parameterDescentVector, colorPower, descentVector, colorSum]

theorem parameterDescentVector_expansion
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    parameterDescentVector (K := K) (σ, m) =
      ∑ f ∈ Fintype.piFinset (descentFactorChoices σ m),
        chainMonomial (assignmentExponent f) := by
  rw [parameterDescentVector_eq_factorProduct, Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact product_faceVariables f

def chainRank (a : BooleanChainExponent V) : ℕ := orderingRank (chainOrdering a.val)

theorem assignmentExponent_parameter_leading (a : BooleanChainExponent V) :
    assignmentExponent (leadingAssignment (chainParameterEquiv a).1
      (chainParameterEquiv a).2) = a.val := by
  rw [assignmentExponent_leading]
  exact congrArg Subtype.val (chainParameterEquiv.symm_apply_apply a)

theorem chainMonomial_repr_zero_of_lower_rank
    (a : BooleanFace V →₀ ℕ) (b : BooleanChainExponent V)
    (h : ∀ ha : IsChainExponent a, orderingRank (chainOrdering a) < chainRank b) :
    (booleanChainBasis (K := K)).repr (chainMonomial a) b = 0 := by
  by_cases ha : IsChainExponent a
  · rw [chainMonomial_eq_basis ha, Module.Basis.repr_self]
    have hne : (⟨a, ha⟩ : BooleanChainExponent V) ≠ b := by
      intro he
      subst b
      exact (lt_irrefl _) (h ha)
    simp [Finsupp.single_apply, hne]
  · rw [chainMonomial_eq_zero_of_not_chain ha, LinearEquiv.map_zero, Finsupp.zero_apply]

theorem parameterDescentVector_diagonal (a : BooleanChainExponent V) :
    (booleanChainBasis (K := K)).repr
      (parameterDescentVector (chainParameterEquiv a)) a = 1 := by
  let σ := (chainParameterEquiv a).1
  let m := (chainParameterEquiv a).2
  change (booleanChainBasis (K := K)).repr (parameterDescentVector (σ, m)) a = 1
  rw [parameterDescentVector_expansion]
  simp only [booleanChainBasis_repr_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (leadingAssignment σ m)]
  · rw [assignmentExponent_parameter_leading a, chainMonomial_eq_basis a.property,
      Module.Basis.repr_self, Finsupp.single_eq_same]
  · intro f hf hne
    apply chainMonomial_repr_zero_of_lower_rank
    intro ha
    exact assignment_rank_lt σ m hf ha hne
  · intro hn
    exact (hn (leadingAssignment_mem σ m)).elim

theorem parameterDescentVector_triangular (a b : BooleanChainExponent V)
    (hne : a ≠ b) (hrank : chainRank a ≤ chainRank b) :
    (booleanChainBasis (K := K)).repr
      (parameterDescentVector (chainParameterEquiv a)) b = 0 := by
  let σ := (chainParameterEquiv a).1
  let m := (chainParameterEquiv a).2
  change (booleanChainBasis (K := K)).repr (parameterDescentVector (σ, m)) b = 0
  rw [parameterDescentVector_expansion]
  simp only [booleanChainBasis_repr_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro f hf
  by_cases hfle : f = leadingAssignment σ m
  · subst f
    rw [assignmentExponent_parameter_leading a, chainMonomial_eq_basis a.property,
      Module.Basis.repr_self]
    simp [Finsupp.single_apply, hne]
  · apply chainMonomial_repr_zero_of_lower_rank
    intro ha
    exact (assignment_rank_lt σ m hf ha hfle).trans_le hrank

/-- All parameter-monomial multiples of all descent monomials form a basis
over the arbitrary coefficient ring. -/
def booleanParameterBasis :
    Module.Basis (VertexOrdering (Fintype.card V) V × ColorExponent V) K
      (BooleanBarycentricRing V K) :=
  (rankTriangularBasis booleanChainBasis
    (fun a => parameterDescentVector (chainParameterEquiv a)) chainRank
    parameterDescentVector_diagonal parameterDescentVector_triangular).reindex chainParameterEquiv

@[simp] theorem booleanParameterBasis_apply
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    booleanParameterBasis (K := K) p = parameterDescentVector p := by
  rw [booleanParameterBasis, Module.Basis.reindex_apply, rankTriangularBasis_apply,
    Equiv.apply_symm_apply]

/-- Each expanded parameter-descent vector has exactly its prescribed color
multidegree in the actual standard-monomial basis. -/
theorem parameterDescentVector_repr_color
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V)
    (a : BooleanChainExponent V)
    (hne : chainColorDegree a.val ≠ p.2 + descentColorExponent p.1) :
    (booleanChainBasis (K := K)).repr (parameterDescentVector p) a = 0 := by
  rw [parameterDescentVector_expansion]
  simp only [booleanChainBasis_repr_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro f hf
  by_cases ha : IsChainExponent (assignmentExponent f)
  · rw [chainMonomial_eq_basis ha, Module.Basis.repr_self]
    have hfa : (⟨assignmentExponent f, ha⟩ : BooleanChainExponent V) ≠ a := by
      intro he
      apply hne
      rw [← congrArg Subtype.val he]
      exact assignmentExponent_colorDegree p.1 p.2 hf
    simp [Finsupp.single_apply, hfa]
  · rw [chainMonomial_eq_zero_of_not_chain ha, LinearEquiv.map_zero, Finsupp.zero_apply]

/-- The inverse basis change preserves the same color multidegree. This
also proves preservation of every specified weight of the rank colors. -/
theorem booleanParameterBasis_repr_color
    (a : BooleanChainExponent V)
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V)
    (hne : p.2 + descentColorExponent p.1 ≠ chainColorDegree a.val) :
    (booleanParameterBasis (K := K)).repr (booleanChainBasis a) p = 0 := by
  apply basis_repr_homogeneous_symm booleanChainBasis booleanParameterBasis
    (fun a => chainColorDegree a.val)
    (fun p => p.2 + descentColorExponent p.1) _ a p hne
  intro b q hq
  rw [booleanParameterBasis_apply]
  exact parameterDescentVector_repr_color q b hq

/-- The specified parameter action is evaluation at the actual color sums. -/
def booleanColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] BooleanBarycentricRing V K :=
  MvPolynomial.aeval colorSum

instance (priority := 2000) booleanColorAlgebra :
    Algebra (MvPolynomial (Fin (Fintype.card V)) K) (BooleanBarycentricRing V K) :=
  (booleanColorMap (V := V) (K := K)).toRingHom.toAlgebra

instance (priority := 2000) booleanColorSMul :
    SMul (MvPolynomial (Fin (Fintype.card V)) K) (BooleanBarycentricRing V K) :=
  @Algebra.toSMul _ _ _ _ (booleanColorAlgebra (V := V) (K := K))

instance (priority := 2000) booleanColorModule :
    Module (MvPolynomial (Fin (Fintype.card V)) K) (BooleanBarycentricRing V K) :=
  @Algebra.toModule _ _ _ _ (booleanColorAlgebra (V := V) (K := K))

instance booleanColorTower : IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K)
    (BooleanBarycentricRing V K) :=
  IsScalarTower.of_algHom (booleanColorMap (V := V) (K := K))

theorem parameterDescentVector_eq_monomial_smul
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    parameterDescentVector (K := K) p =
      (MvPolynomial.monomial p.2 (1 : K)) • descentVector (K := K) p.1 := by
  rw [Algebra.smul_def]
  change colorPower p.2 * descentVector p.1 =
    MvPolynomial.aeval (colorSum (V := V) (K := K))
      (MvPolynomial.monomial p.2 (1 : K)) * descentVector p.1
  congr 1
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  exact (Finsupp.prod_fintype p.2 (fun c m => colorSum c ^ m) (fun c => pow_zero _)).symm

/-- Lemma 2.2 for the genuine Boolean barycentric face ring: the ordinary
descent monomials are a free basis over the prescribed color parameters,
over every commutative coefficient ring. -/
def booleanColorBasis :
    Module.Basis (VertexOrdering (Fintype.card V) V)
      (MvPolynomial (Fin (Fintype.card V)) K) (BooleanBarycentricRing V K) :=
  basisOfScalarBasis (MvPolynomial.basisMonomials (Fin (Fintype.card V)) K)
    booleanParameterBasis descentVector (by
      intro p
      rw [booleanParameterBasis_apply]
      simpa [MvPolynomial.basisMonomials, MvPolynomial.monomial] using parameterDescentVector_eq_monomial_smul (K := K) p)

@[simp] theorem booleanColorBasis_apply (σ : VertexOrdering (Fintype.card V) V) :
    booleanColorBasis (K := K) σ = descentVector σ :=
  basisOfScalarBasis_apply _ _ _ _ _

end FourPapers.Universal

end
end

/- BEGIN CanonicalPolynomialComparison.lean -/
section


/-! # The literal chain-monomial comparison and its quadratic weight filtration -/

noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def polynomialChainBasis : Module.Basis (BooleanChainExponent V) K (MvPolynomial V K) :=
  (MvPolynomial.basisMonomials V K).reindex chainVertexEquiv.symm

@[simp] theorem polynomialChainBasis_apply (a : BooleanChainExponent V) :
    polynomialChainBasis (K := K) a = monomial (chainVertexMap a.val) 1 := by
  simp [polynomialChainBasis, MvPolynomial.basisMonomials, MvPolynomial.monomial,
    chainVertexEquiv]

@[simp] theorem polynomialChainBasis_repr (f : MvPolynomial V K) (a : BooleanChainExponent V) :
    (polynomialChainBasis (K := K)).repr f a = f.coeff (chainVertexMap a.val) := by
  rw [polynomialChainBasis, Module.Basis.repr_reindex_apply]
  rfl

/-- The independently defined canonical linear comparison, before considering
the parameter action. -/
def canonicalBooleanPolynomial : BooleanBarycentricRing V K ≃ₗ[K] MvPolynomial V K :=
  (booleanChainBasis (V := V) (K := K)).repr.trans
    (polynomialChainBasis (V := V) (K := K)).repr.symm

@[simp] theorem canonicalBooleanPolynomial_basis (a : BooleanChainExponent V) :
    canonicalBooleanPolynomial (K := K) (booleanChainBasis a) =
      monomial (chainVertexMap a.val) 1 := by
  simp only [canonicalBooleanPolynomial, LinearEquiv.trans_apply,
    Module.Basis.repr_self, Module.Basis.repr_symm_single, one_smul,
    polynomialChainBasis_apply]

theorem canonicalBooleanPolynomial_coefficient (x : BooleanBarycentricRing V K)
    (a : BooleanChainExponent V) :
    (canonicalBooleanPolynomial x).coeff (chainVertexMap a.val) =
      (booleanChainBasis (K := K)).repr x a := by
  rw [← polynomialChainBasis_repr]
  change ((polynomialChainBasis (K := K)).repr
    ((polynomialChainBasis (K := K)).repr.symm ((booleanChainBasis (K := K)).repr x))) a = _
  rw [LinearEquiv.apply_symm_apply]

theorem canonicalBooleanPolynomial_chainMonomial (a : BooleanFace V →₀ ℕ) :
    canonicalBooleanPolynomial (K := K) (chainMonomial a) =
      if IsChainExponent a then monomial (chainVertexMap a) 1 else 0 := by
  by_cases ha : IsChainExponent a
  · rw [if_pos ha, chainMonomial_eq_basis ha, canonicalBooleanPolynomial_basis]
  · rw [if_neg ha, chainMonomial_eq_zero_of_not_chain ha, LinearEquiv.map_zero]

def polynomialWeightBelow (d : ℕ) (w : ℤ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a : V →₀ ℕ, w ≤ polynomialRankWeight d (fun v => a v) → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by
    intro f g hf hg a ha
    rw [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := by
    intro c f hf a ha
    rw [MvPolynomial.coeff_smul, hf a ha, smul_zero]

def polynomialWeightAtMost (d : ℕ) (w : ℤ) : Submodule K (MvPolynomial V K) :=
  polynomialWeightBelow d (w + 1)

theorem mem_polynomialWeightBelow (d : ℕ) (w : ℤ) (f : MvPolynomial V K) :
    f ∈ polynomialWeightBelow d w ↔
      ∀ a ∈ f.support, polynomialRankWeight d (fun v => a v) < w := by
  constructor
  · intro hf a ha
    by_contra hn
    exact MvPolynomial.mem_support_iff.mp ha (hf a (le_of_not_gt hn))
  · intro hf a ha
    by_contra hn
    exact (not_le_of_gt (hf a (MvPolynomial.mem_support_iff.mpr hn))) ha

theorem mem_polynomialWeightAtMost (d : ℕ) (w : ℤ) (f : MvPolynomial V K) :
    f ∈ polynomialWeightAtMost d w ↔
      ∀ a ∈ f.support, polynomialRankWeight d (fun v => a v) ≤ w := by
  rw [polynomialWeightAtMost, mem_polynomialWeightBelow]
  constructor
  · intro h a ha
    have h' := h a ha
    omega
  · intro h a ha
    have h' := h a ha
    omega

theorem polynomialWeightBelow_mono (d : ℕ) {w z : ℤ} (hwz : w ≤ z) :
    polynomialWeightBelow (V := V) (K := K) d w ≤ polynomialWeightBelow d z := by
  intro f hf a ha
  exact hf a (hwz.trans ha)

theorem monomial_mem_polynomialWeightBelow (d : ℕ) (w : ℤ) (a : V →₀ ℕ) (c : K)
    (ha : polynomialRankWeight d (fun v => a v) < w) :
    monomial a c ∈ polynomialWeightBelow d w := by
  intro b hb
  have hab : a ≠ b := by intro he; subst b; exact (not_le_of_gt ha) hb
  simp [MvPolynomial.coeff_monomial, hab]

theorem monomial_mem_polynomialWeightAtMost (d : ℕ) (w : ℤ) (a : V →₀ ℕ) (c : K)
    (ha : polynomialRankWeight d (fun v => a v) ≤ w) :
    monomial a c ∈ polynomialWeightAtMost d w :=
  monomial_mem_polynomialWeightBelow d (w + 1) a c (by omega)

theorem polynomialWeightBelow_mul (d : ℕ) (w z : ℤ) (f g : MvPolynomial V K)
    (hf : f ∈ polynomialWeightBelow d w) (hg : g ∈ polynomialWeightAtMost d z) :
    f * g ∈ polynomialWeightBelow d (w + z) := by
  rw [f.as_sum, g.as_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro a ha
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro b hb
  rw [MvPolynomial.monomial_mul_monomial]
  apply monomial_mem_polynomialWeightBelow
  have hfa := (mem_polynomialWeightBelow d w f).mp hf a ha
  have hgb := (mem_polynomialWeightAtMost d z g).mp hg b hb
  exact (polynomialRankWeight_subadditive d (fun v => a v) (fun v => b v)).trans_lt
    (add_lt_add_of_lt_of_le hfa hgb)

theorem polynomialWeightAtMost_mul (d : ℕ) (w z : ℤ) (f g : MvPolynomial V K)
    (hf : f ∈ polynomialWeightAtMost d w) (hg : g ∈ polynomialWeightAtMost d z) :
    f * g ∈ polynomialWeightAtMost d (w + z) := by
  have h := polynomialWeightBelow_mul d (w + 1) z f g hf hg
  simpa only [polynomialWeightAtMost, add_right_comm] using h

def booleanWeightAtMost (d : ℕ) (w : ℤ) : Submodule K (BooleanBarycentricRing V K) :=
  (polynomialWeightAtMost d w).comap canonicalBooleanPolynomial.toLinearMap

theorem booleanChainBasis_mem_weight (d : ℕ) (a : BooleanChainExponent V) :
    booleanChainBasis (K := K) a ∈ booleanWeightAtMost d (chainRankWeight d a.val) := by
  change canonicalBooleanPolynomial (K := K) (booleanChainBasis a) ∈
    polynomialWeightAtMost d (chainRankWeight d a.val)
  rw [canonicalBooleanPolynomial_basis]
  apply monomial_mem_polynomialWeightAtMost
  exact (polynomialRankWeight_chainVertexMap d a.property).le

theorem mem_booleanWeightAtMost (d : ℕ) (w : ℤ) (x : BooleanBarycentricRing V K) :
    x ∈ booleanWeightAtMost d w ↔
      ∀ a ∈ ((booleanChainBasis (K := K)).repr x).support, chainRankWeight d a.val ≤ w := by
  change canonicalBooleanPolynomial x ∈ polynomialWeightAtMost d w ↔ _
  rw [mem_polynomialWeightAtMost]
  constructor
  · intro h a ha
    have hm : chainVertexMap a.val ∈ (canonicalBooleanPolynomial x).support := by
      rw [MvPolynomial.mem_support_iff, canonicalBooleanPolynomial_coefficient]
      exact Finsupp.mem_support_iff.mp ha
    have hh := h (chainVertexMap a.val) hm
    simpa only [polynomialRankWeight_chainVertexMap d a.property] using hh
  · intro h b hb
    let a : BooleanChainExponent V := chainVertexEquiv.symm b
    have he : chainVertexMap a.val = b := chainVertexEquiv.apply_symm_apply b
    have hm : a ∈ ((booleanChainBasis (K := K)).repr x).support := by
      rw [Finsupp.mem_support_iff, ← canonicalBooleanPolynomial_coefficient, he]
      exact MvPolynomial.mem_support_iff.mp hb
    have hh := h a hm
    rw [← polynomialRankWeight_chainVertexMap d a.property, he] at hh
    exact hh

abbrev ExponentFactors (a : BooleanFace V →₀ ℕ) := Σ F : BooleanFace V, Fin (a F)

def exponentFactorFaces (a : BooleanFace V →₀ ℕ) (t : ExponentFactors a) : Finset V := t.1.val

theorem occurrenceExponent_exponentFactorFaces (a : BooleanFace V →₀ ℕ) :
    occurrenceExponent (exponentFactorFaces a) = chainVertexMap a := by
  ext v
  rw [occurrenceExponent_apply, Fintype.sum_sigma]
  change (∑ F : BooleanFace V, ∑ _t : Fin (a F), if v ∈ F.val then 1 else 0) =
    chainVertexMap a v
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [chainVertexMap_apply]
  simpa only [mul_ite, mul_one, mul_zero, Nat.cast_id, Finsupp.sum] using
    (Finsupp.sum_fintype a (fun F n => if v ∈ F.val then n else 0)
      (fun F => by simp)).symm

theorem exponentFactorFaces_weight (d : ℕ) (a : BooleanFace V →₀ ℕ) :
    (∑ t : ExponentFactors a, rankWeight d (exponentFactorFaces a t).card) =
      chainRankWeight d a := by
  simp only [Fintype.sum_sigma, exponentFactorFaces, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (∑ F : BooleanFace V, (a F : ℤ) * rankWeight d F.val.card) =
    a.sum (fun F n => (n : ℤ) * rankWeight d F.val.card)
  exact (Finsupp.sum_fintype a (fun F n => (n : ℤ) * rankWeight d F.val.card)
    (fun F => by simp)).symm

theorem exponentFactorFaces_not_chain (a : BooleanFace V →₀ ℕ)
    (ha : ¬ IsChainExponent a) :
    ∃ s t : ExponentFactors a,
      ¬ (exponentFactorFaces a s ⊆ exponentFactorFaces a t ∨
        exponentFactorFaces a t ⊆ exponentFactorFaces a s) := by
  unfold IsChainExponent at ha
  push_neg at ha
  obtain ⟨F, hF, G, hG, hFG, hGF⟩ := ha
  exact ⟨⟨F, ⟨0, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hF)⟩⟩,
    ⟨G, ⟨0, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hG)⟩⟩,
    fun h => h.elim hFG hGF⟩

theorem polynomialRankWeight_chainVertexMap_le (d : ℕ) (a : BooleanFace V →₀ ℕ) :
    polynomialRankWeight d (fun v => chainVertexMap a v) ≤ chainRankWeight d a := by
  have h := polynomialRankWeight_occurrence_le d (exponentFactorFaces a)
  simpa only [occurrenceExponent_exponentFactorFaces, exponentFactorFaces_weight] using h

theorem polynomialRankWeight_chainVertexMap_lt (d : ℕ) (a : BooleanFace V →₀ ℕ)
    (ha : ¬ IsChainExponent a) :
    polynomialRankWeight d (fun v => chainVertexMap a v) < chainRankWeight d a := by
  have h := polynomialRankWeight_occurrence_lt_of_not_chain d
    (exponentFactorFaces a) (exponentFactorFaces_not_chain a ha)
  simpa only [occurrenceExponent_exponentFactorFaces, exponentFactorFaces_weight] using h

end FourPapers.Universal

end
end

/- BEGIN CanonicalParameterComparison.lean -/
section


/-! # Exact leading terms of the elementary-symmetric parameter products -/

noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem canonicalBooleanPolynomial_sum {T : Type*} (s : Finset T)
    (f : T → BooleanBarycentricRing V K) :
    canonicalBooleanPolynomial (∑ t ∈ s, f t) =
      ∑ t ∈ s, canonicalBooleanPolynomial (f t) :=
  map_sum (canonicalBooleanPolynomial (V := V) (K := K)).toAddMonoidHom f s

def colorRankWeight (d : ℕ) (m : ColorExponent V) : ℤ :=
  m.sum (fun c n => (n : ℤ) * rankWeight d (c.val + 1))

@[simp] theorem colorRankWeight_zero (d : ℕ) :
    colorRankWeight (V := V) d 0 = 0 := by simp [colorRankWeight]

theorem colorRankWeight_add (d : ℕ) (m n : ColorExponent V) :
    colorRankWeight d (m + n) = colorRankWeight d m + colorRankWeight d n := by
  exact Finsupp.sum_add_index' (fun c => by simp) (fun c i j => by
    simp only [Nat.cast_add, add_mul])

theorem colorRankWeight_fintype (d : ℕ) (m : ColorExponent V) :
    colorRankWeight d m = ∑ c : Fin (Fintype.card V),
      (m c : ℤ) * rankWeight d (c.val + 1) :=
  Finsupp.sum_fintype m _ (fun c => by simp)

theorem colorRankWeight_chainColorDegree (d : ℕ) (a : BooleanFace V →₀ ℕ) :
    colorRankWeight d (chainColorDegree a) = chainRankWeight d a := by
  unfold colorRankWeight chainColorDegree
  rw [Finsupp.sum_mapDomain_index (fun c => by simp)
    (fun c i j => by simp only [Nat.cast_add, add_mul])]
  simp only [BooleanFace.color_succ, chainRankWeight, Finsupp.sum]

def polynomialFaceVariable (F : BooleanFace V) : MvPolynomial V K :=
  monomial (subsetExponent F.val) 1

theorem polynomialFaceVariable_eq_prod (F : BooleanFace V) :
    polynomialFaceVariable (K := K) F = ∏ v ∈ F.val, X v := by
  rw [polynomialFaceVariable, subsetExponent, MvPolynomial.monomial_sum_one]
  rfl

theorem esymm_eq_sum_polynomialFaceVariable (c : Fin (Fintype.card V)) :
    esymm V K (c.val + 1) =
      ∑ F ∈ facesOfColor c, polynomialFaceVariable F := by
  symm
  unfold esymm
  apply Finset.sum_bij (fun F _ => F.val)
  · intro F hF
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [← F.color_succ, (mem_facesOfColor _ _).mp hF]
  · intro F hF G hG he
    exact Subtype.ext he
  · intro F hF
    have hc := (Finset.mem_powersetCard.mp hF).2
    have hn : F.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨⟨F, hn⟩, ?_, rfl⟩
    apply (mem_facesOfColor c ⟨F, hn⟩).mpr
    apply Fin.ext
    have hs := BooleanFace.color_succ (⟨F, hn⟩ : BooleanFace V)
    simp only at hs
    omega
  · intro F hF
    exact polynomialFaceVariable_eq_prod F

theorem product_polynomialFaceVariables {T : Type*} [Fintype T] (f : T → BooleanFace V) :
    (∏ t, polynomialFaceVariable (K := K) (f t)) =
      monomial (chainVertexMap (assignmentExponent f)) 1 := by
  rw [assignmentExponent, map_sum]
  simp only [chainVertexMap, Finsupp.linearCombination_single, one_smul]
  rw [MvPolynomial.monomial_sum_one]
  rfl

def polynomialDescentVector (σ : VertexOrdering (Fintype.card V) V) :
    MvPolynomial V K :=
  ∏ c ∈ orderingDescents σ, polynomialFaceVariable (orderingFace σ c)

def polynomialParameterDescentVector
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V) : MvPolynomial V K :=
  (∏ c : Fin (Fintype.card V), esymm V K (c.val + 1) ^ p.2 c) *
    polynomialDescentVector p.1

theorem polynomialParameterDescentVector_eq_factorProduct
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    polynomialParameterDescentVector (K := K) (σ, m) =
      ∏ t : DescentFactor σ m,
        ∑ F ∈ descentFactorChoices σ m t, polynomialFaceVariable F := by
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [descentFactorChoices, Finset.sum_singleton]
  rw [← Finset.prod_subtype (orderingDescents σ) (fun _ => Iff.rfl)
    (fun c => polynomialFaceVariable (K := K) (orderingFace σ c))]
  simp only [← esymm_eq_sum_polynomialFaceVariable, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, polynomialParameterDescentVector,
    polynomialDescentVector]

theorem polynomialParameterDescentVector_expansion
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    polynomialParameterDescentVector (K := K) (σ, m) =
      ∑ f ∈ Fintype.piFinset (descentFactorChoices σ m),
        monomial (chainVertexMap (assignmentExponent f)) 1 := by
  rw [polynomialParameterDescentVector_eq_factorProduct, Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact product_polynomialFaceVariables f

theorem polynomialParameterDescentVector_leading (d : ℕ)
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    polynomialParameterDescentVector (K := K) (σ, m) -
      canonicalBooleanPolynomial (parameterDescentVector (σ, m)) ∈
        polynomialWeightBelow d (colorRankWeight d (m + descentColorExponent σ)) := by
  rw [polynomialParameterDescentVector_expansion, parameterDescentVector_expansion,
    canonicalBooleanPolynomial_sum, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro f hf
  rw [canonicalBooleanPolynomial_chainMonomial]
  by_cases ha : IsChainExponent (assignmentExponent f)
  · rw [if_pos ha, sub_self]
    exact Submodule.zero_mem _
  · rw [if_neg ha, sub_zero]
    apply monomial_mem_polynomialWeightBelow
    have h := polynomialRankWeight_chainVertexMap_lt d (assignmentExponent f) ha
    rw [← colorRankWeight_chainColorDegree, assignmentExponent_colorDegree σ m hf] at h
    exact h

theorem polynomialParameterDescentVector_parameter
    (σ : VertexOrdering (Fintype.card V) V) (m : ColorExponent V) :
    polynomialParameterDescentVector (K := K) (σ, m) =
      polynomialColorMap (monomial m 1) * polynomialDescentVector σ := by
  unfold polynomialParameterDescentVector polynomialColorMap
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  congr 1
  exact (Finsupp.prod_fintype m
    (fun c n => esymm V K (c.val + 1) ^ n) (fun c => pow_zero _)).symm

theorem polynomialWeightAtMost_one (d : ℕ) :
    (1 : MvPolynomial V K) ∈ polynomialWeightAtMost d 0 := by
  have h := monomial_mem_polynomialWeightAtMost (V := V) d 0 0 (1 : K)
    (by simp [polynomialRankWeight, vertexDegree, overlapCost])
  simpa using h

theorem polynomialWeightAtMost_pow (d : ℕ) (w : ℤ) (f : MvPolynomial V K)
    (hf : f ∈ polynomialWeightAtMost d w) (n : ℕ) :
    f ^ n ∈ polynomialWeightAtMost d ((n : ℤ) * w) := by
  induction n with
  | zero => simpa using polynomialWeightAtMost_one (V := V) (K := K) d
  | succ n ih =>
    have h := polynomialWeightAtMost_mul d ((n : ℤ) * w) w (f ^ n) f ih hf
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

theorem polynomialWeightAtMost_prod {T : Type*} (d : ℕ) (s : Finset T)
    (w : T → ℤ) (f : T → MvPolynomial V K)
    (hf : ∀ t ∈ s, f t ∈ polynomialWeightAtMost d (w t)) :
    (∏ t ∈ s, f t) ∈ polynomialWeightAtMost d (∑ t ∈ s, w t) := by
  induction s using Finset.induction_on with
  | empty => simpa using polynomialWeightAtMost_one (V := V) (K := K) d
  | @insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht]
    exact polynomialWeightAtMost_mul d _ _ _ _ (hf t (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem esymm_mem_polynomialWeightAtMost (d : ℕ) (c : Fin (Fintype.card V)) :
    esymm V K (c.val + 1) ∈ polynomialWeightAtMost d (rankWeight d (c.val + 1)) := by
  rw [esymm_eq_sum_polynomialFaceVariable]
  apply Submodule.sum_mem
  intro F hF
  apply monomial_mem_polynomialWeightAtMost
  have he : (fun v => subsetExponent F.val v) = faceIndicator F.val := by
    funext v
    simp [faceIndicator]
  rw [he, polynomialRankWeight_indicator, ← (mem_facesOfColor _ _).mp hF, F.color_succ]

theorem polynomialColorMap_monomial_weight (d : ℕ) (m : ColorExponent V) :
    polynomialColorMap (K := K) (monomial m 1) ∈
      polynomialWeightAtMost d (colorRankWeight d m) := by
  have he : polynomialColorMap (K := K) (monomial m 1) =
      ∏ c : Fin (Fintype.card V), esymm V K (c.val + 1) ^ m c := by
    unfold polynomialColorMap
    rw [MvPolynomial.aeval_monomial, map_one, one_mul]
    exact Finsupp.prod_fintype m
      (fun c n => esymm V K (c.val + 1) ^ n) (fun c => pow_zero _)
  rw [he, colorRankWeight_fintype]
  apply polynomialWeightAtMost_prod
  intro c hc
  exact polynomialWeightAtMost_pow d _ _ (esymm_mem_polynomialWeightAtMost d c) _

end FourPapers.Universal

end
end

/- BEGIN LocalBoundaryLift.lean -/
section


/-! # The actual parameter-linear Boolean-to-polynomial boundary lift

The map is defined on the proved descent basis, using the explicit polynomial
boundary section. Its reduction is exactly the prescribed boundary comparison.
Invertibility, filtration, and global assembly are separate proof obligations.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

def booleanBoundaryColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] BooleanBoundaryRing V K :=
  booleanBoundaryMap.comp booleanColorMap

/-- A genuinely parameter-linear comparison of the actual two boundary quotients. -/
abbrev LocalBoundaryComparison :=
  ParameterEquiv (booleanBoundaryColorMap (V := V) (K := K)) polynomialBoundaryColorMap

/-- The local lift is extended over the polynomial parameter ring, not merely
over the coefficient ring. -/
def booleanPolynomialBoundaryLift (e : LocalBoundaryComparison (V := V) (K := K)) :
    BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K := by
  letI := (polynomialColorMap (V := V) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := V) (K := K))
  exact ((booleanColorBasis (V := V) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card V)) K)
    (fun σ => polynomialBooleanBoundarySection
      (e.toLinearEquiv (booleanBoundaryMap (descentVector σ))))).restrictScalars K

@[simp] theorem booleanPolynomialBoundaryLift_basis
    (e : LocalBoundaryComparison (V := V) (K := K))
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanPolynomialBoundaryLift e (descentVector σ) =
      polynomialBooleanBoundarySection
        (e.toLinearEquiv (booleanBoundaryMap (descentVector σ))) := by
  letI := (polynomialColorMap (V := V) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := V) (K := K))
  change ((booleanColorBasis (V := V) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card V)) K)
    (fun τ => polynomialBooleanBoundarySection
      (e.toLinearEquiv (booleanBoundaryMap (descentVector τ))))) (descentVector σ) = _
  simpa only [booleanColorBasis_apply] using
    (Module.Basis.constr_basis (booleanColorBasis (V := V) (K := K))
      (MvPolynomial (Fin (Fintype.card V)) K)
      (fun τ => polynomialBooleanBoundarySection
        (e.toLinearEquiv (booleanBoundaryMap (descentVector τ)))) σ)

theorem booleanPolynomialBoundaryLift_parameter_mul
    (e : LocalBoundaryComparison (V := V) (K := K))
    (a : MvPolynomial (Fin (Fintype.card V)) K) (x : BooleanBarycentricRing V K) :
    booleanPolynomialBoundaryLift e (booleanColorMap a * x) =
      polynomialColorMap a * booleanPolynomialBoundaryLift e x := by
  letI := (polynomialColorMap (V := V) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := V) (K := K))
  let f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      MvPolynomial V K :=
    (booleanColorBasis (V := V) (K := K)).constr
      (MvPolynomial (Fin (Fintype.card V)) K)
      (fun σ => polynomialBooleanBoundarySection
        (e.toLinearEquiv (booleanBoundaryMap (descentVector σ))))
  change f (booleanColorMap a * x) = polynomialColorMap a * f x
  exact f.map_smul a x

/-- The lift agrees with the prescribed comparison on the complete actual
boundary quotient, not just on a collection of chosen generators. -/
theorem booleanPolynomialBoundaryLift_boundary
    (e : LocalBoundaryComparison (V := V) (K := K)) (x : BooleanBarycentricRing V K) :
    polynomialBooleanBoundaryMap (booleanPolynomialBoundaryLift e x) =
      e.toLinearEquiv (booleanBoundaryMap x) := by
  have he : (polynomialBooleanBoundaryMap (V := V) (K := K)).toLinearMap.comp
      (booleanPolynomialBoundaryLift e) =
      e.toLinearEquiv.toLinearMap.comp booleanBoundaryMap.toLinearMap := by
    apply (booleanParameterBasis (V := V) (K := K)).ext
    intro p
    change polynomialBooleanBoundaryMap
      (booleanPolynomialBoundaryLift e (booleanParameterBasis p)) =
        e.toLinearEquiv (booleanBoundaryMap (booleanParameterBasis p))
    rw [booleanParameterBasis_apply, parameterDescentVector_eq_monomial_smul,
      Algebra.smul_def]
    change polynomialBooleanBoundaryMap (booleanPolynomialBoundaryLift e
      (booleanColorMap (MvPolynomial.monomial p.2 1) * descentVector p.1)) =
      e.toLinearEquiv (booleanBoundaryMap
        (booleanColorMap (MvPolynomial.monomial p.2 1) * descentVector p.1))
    rw [booleanPolynomialBoundaryLift_parameter_mul,
      polynomialBooleanBoundaryMap_parameter_mul,
      booleanPolynomialBoundaryLift_basis, polynomialBooleanBoundaryMap_section, map_mul]
    exact (e.map_parameter_mul (MvPolynomial.monomial p.2 1)
      (booleanBoundaryMap (descentVector p.1))).symm
  exact DFunLike.congr_fun he x

theorem booleanPolynomialBoundaryLift_kernel
    (e : LocalBoundaryComparison (V := V) (K := K))
    (x : BooleanBarycentricRing V K) (hx : booleanPolynomialBoundaryLift e x = 0) :
    ∃ y, booleanTop * y = x := by
  apply (booleanBoundaryMap_eq_zero_iff x).mp
  apply e.toLinearEquiv.injective
  have h := booleanPolynomialBoundaryLift_boundary e x
  have hz : polynomialBooleanBoundaryMap (V := V) (K := K) 0 = 0 :=
    map_zero (polynomialBooleanBoundaryMap (V := V) (K := K)).toRingHom
  simpa only [hx, hz, LinearEquiv.map_zero] using h.symm

end FourPapers.Universal
end
end

/- BEGIN LocalCanonicalLift.lean -/
section


/-! # Canonical leading terms and invertibility of the genuine parameter lift -/

noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def HasDescentLeading (d : ℕ) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) : Prop :=
  ∀ σ : VertexOrdering (Fintype.card V) V,
    f (descentVector σ) - polynomialDescentVector σ ∈
      polynomialWeightBelow d (colorRankWeight d (descentColorExponent σ))

theorem parameterLinear_descent_leading (d : ℕ)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : HasDescentLeading d f)
    (p : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    f (parameterDescentVector p) - canonicalBooleanPolynomial (parameterDescentVector p) ∈
      polynomialWeightBelow d (colorRankWeight d (p.2 + descentColorExponent p.1)) := by
  have hm := polynomialColorMap_monomial_weight (V := V) (K := K) d p.2
  have h1 := polynomialWeightBelow_mul d
    (colorRankWeight d (descentColorExponent p.1)) (colorRankWeight d p.2)
    (f (descentVector p.1) - polynomialDescentVector p.1)
    (polynomialColorMap (monomial p.2 1)) (hd p.1) hm
  rw [← add_comm, ← colorRankWeight_add] at h1
  have h2 := polynomialParameterDescentVector_leading (K := K) d p.1 p.2
  have hsum := (polynomialWeightBelow (V := V) (K := K) d
    (colorRankWeight d (p.2 + descentColorExponent p.1))).add_mem h1 h2
  have he : f (parameterDescentVector p) -
      canonicalBooleanPolynomial (parameterDescentVector p) =
      (f (descentVector p.1) - polynomialDescentVector p.1) *
        polynomialColorMap (monomial p.2 1) +
        (polynomialParameterDescentVector p -
          canonicalBooleanPolynomial (parameterDescentVector p)) := by
    have hfp : f (parameterDescentVector p) =
        polynomialColorMap (monomial p.2 1) * f (descentVector p.1) := by
      rw [parameterDescentVector_eq_monomial_smul, Algebra.smul_def]
      exact hf _ _
    rw [hfp, polynomialParameterDescentVector_parameter]
    ring
  rw [he]
  exact hsum

theorem parameterLinear_chain_leading (d : ℕ)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : HasDescentLeading d f) (a : BooleanChainExponent V) :
    f (booleanChainBasis a) - canonicalBooleanPolynomial (booleanChainBasis a) ∈
      polynomialWeightBelow d (chainRankWeight d a.val) := by
  let b := booleanParameterBasis (V := V) (K := K)
  let x := booleanChainBasis (K := K) a
  let g : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K :=
    f - canonicalBooleanPolynomial.toLinearMap
  have hx : x = ∑ p ∈ (b.repr x).support, (b.repr x p) • b p := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (b.linearCombination_repr x).symm
  change g x ∈ _
  rw [hx]
  have hmap : g (∑ p ∈ (b.repr x).support, (b.repr x p) • b p) =
      ∑ p ∈ (b.repr x).support, g ((b.repr x p) • b p) :=
    map_sum g.toAddMonoidHom _ _
  rw [hmap]
  apply Submodule.sum_mem
  intro p hp
  rw [g.map_smul]
  apply Submodule.smul_mem
  have hc : p.2 + descentColorExponent p.1 = chainColorDegree a.val := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hp (booleanParameterBasis_repr_color a p h)
  have h := parameterLinear_descent_leading d f hf hd p
  rw [hc, colorRankWeight_chainColorDegree] at h
  simpa only [b, booleanParameterBasis_apply, g, LinearMap.sub_apply,
    LinearEquiv.coe_coe] using h

def chainWeightRank (d : ℕ) (a : BooleanChainExponent V) : ℕ :=
  (chainRankWeight d a.val).toNat

theorem chainRankWeight_nonnegative (d : ℕ) (hd : Fintype.card V ≤ d)
    (a : BooleanChainExponent V) : 0 ≤ chainRankWeight d a.val := by
  rw [← polynomialRankWeight_chainVertexMap d a.property]
  exact polynomialRankWeight_nonnegative d hd _

theorem chainWeightRank_le_iff (d : ℕ) (hd : Fintype.card V ≤ d)
    (a b : BooleanChainExponent V) :
    chainWeightRank d a ≤ chainWeightRank d b ↔
      chainRankWeight d a.val ≤ chainRankWeight d b.val := by
  unfold chainWeightRank
  have ha := chainRankWeight_nonnegative d hd a
  have hb := chainRankWeight_nonnegative d hd b
  omega

theorem parameterLinear_hasCanonicalLeading (d : ℕ) (hrank : Fintype.card V ≤ d)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : HasDescentLeading d f) :
    HasCanonicalLeading booleanChainBasis polynomialChainBasis (chainWeightRank d) f := by
  have hc (a b : BooleanChainExponent V)
      (hab : chainRankWeight d a.val ≤ chainRankWeight d b.val) :
      (polynomialChainBasis (K := K)).repr (f (booleanChainBasis a)) b =
        (polynomialChainBasis (K := K)).repr
          (canonicalBooleanPolynomial (booleanChainBasis a)) b := by
    have h := parameterLinear_chain_leading d f hf hd a
    have he := h (chainVertexMap b.val) (by
      simpa only [polynomialRankWeight_chainVertexMap d b.property] using hab)
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at he
    simpa only [polynomialChainBasis_repr] using he
  constructor
  · intro a
    rw [hc a a le_rfl, canonicalBooleanPolynomial_basis,
      ← polynomialChainBasis_apply, Module.Basis.repr_self]
    simp
  · intro a b hne hab
    rw [hc a b ((chainWeightRank_le_iff d hrank a b).mp hab),
      canonicalBooleanPolynomial_basis, ← polynomialChainBasis_apply,
      Module.Basis.repr_self]
    simp [Finsupp.single_apply, hne]

/-- The full parameter equivalence arising from an actual map with the specified
finite family of strict descent corrections. -/
def parameterLinearLeadingEquiv (d : ℕ) (hrank : Fintype.card V ≤ d)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : HasDescentLeading d f) :
    ParameterEquiv (booleanColorMap (V := V) (K := K)) polynomialColorMap where
  toLinearEquiv := LinearEquiv.ofBijective f
    (canonicalLeading_bijective booleanChainBasis polynomialChainBasis
      (chainWeightRank d) f (parameterLinear_hasCanonicalLeading d hrank f hf hd))
  map_X_mul i x := hf (X i) x

@[simp] theorem parameterLinearLeadingEquiv_apply (d : ℕ) (hrank : Fintype.card V ≤ d)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : HasDescentLeading d f) (x : BooleanBarycentricRing V K) :
    (parameterLinearLeadingEquiv d hrank f hf hd).toLinearEquiv x = f x := rfl

variable [Nonempty V]

def booleanPolynomialBoundaryLeadingEquiv (d : ℕ) (hrank : Fintype.card V ≤ d)
    (e : LocalBoundaryComparison (V := V) (K := K))
    (he : HasDescentLeading d (booleanPolynomialBoundaryLift e)) :
    ParameterEquiv (booleanColorMap (V := V) (K := K)) polynomialColorMap :=
  parameterLinearLeadingEquiv d hrank (booleanPolynomialBoundaryLift e)
    (booleanPolynomialBoundaryLift_parameter_mul e) he

theorem booleanPolynomialBoundaryLeadingEquiv_boundary (d : ℕ)
    (hrank : Fintype.card V ≤ d)
    (e : LocalBoundaryComparison (V := V) (K := K))
    (he : HasDescentLeading d (booleanPolynomialBoundaryLift e))
    (x : BooleanBarycentricRing V K) :
    polynomialBooleanBoundaryMap
      ((booleanPolynomialBoundaryLeadingEquiv d hrank e he).toLinearEquiv x) =
      e.toLinearEquiv (booleanBoundaryMap x) := by
  have h := parameterLinearLeadingEquiv_apply d hrank (booleanPolynomialBoundaryLift e)
    (booleanPolynomialBoundaryLift_parameter_mul e) he x
  exact (congrArg (polynomialBooleanBoundaryMap (V := V) (K := K)) h).trans
    (booleanPolynomialBoundaryLift_boundary e x)

end FourPapers.Universal

end
end

/- BEGIN ActualCarrierComparison.lean -/
section


/-! # The actual face diagrams and the canonical carrier comparison -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def standardRankWeight (d : ℕ) (a : StandardFaceIndex P) : ℤ :=
  a.val.sum (fun F n => (n : ℤ) * rankWeight d (faceRank F.val))

theorem faceRank_booleanFaceInclusion (p : P) (F : BooleanFace (FaceVertex p)) :
    faceRank (booleanFaceInclusion hs p F).val = F.val.card := by
  unfold faceRank
  rw [← image_stalkVertexSet (booleanFaceInclusion_le hs p F),
    stalkVertexSet_booleanFaceInclusion]
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem standardRankWeight_inside (d : ℕ) (p : P)
    [LinearOrder (FaceVertex p)]
    (a : BooleanChainExponent (FaceVertex p)) :
    standardRankWeight d ((standardInsideEquiv hs p) a).val = chainRankWeight d a.val := by
  change (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).sum
    (fun F n => (n : ℤ) * rankWeight d (faceRank F.val)) = _
  rw [Finsupp.sum_mapDomain_index (fun F => by simp)
    (fun F i j => by simp only [Nat.cast_add, add_mul])]
  simp only [faceRank_booleanFaceInclusion, chainRankWeight, Finsupp.sum]

def canonicalCarrierComparison :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) :=
  (barycentricCoefficientEquiv K hs).trans (polynomialCoefficientEquiv K hs).symm

theorem canonicalCarrierComparison_standardBasis (p : P) (a : StandardInside p) :
    (canonicalCarrierComparison K hs).component p (barycentricStalkStandardBasis K hs p a) =
      polynomialStandardBasis (K := K) hs p a := by
  apply (polynomialStandardCoordinates K hs p).injective
  change polynomialStandardCoordinates K hs p
    ((polynomialStandardCoordinates K hs p).symm
      (barycentricStandardCoordinates K hs p (barycentricStalkStandardBasis K hs p a))) = _
  rw [LinearEquiv.apply_symm_apply]
  change (Finsupp.supportedEquivFinsupp
    {b : StandardFaceIndex P | standardCarrier b ≤ p}).symm
      ((barycentricStalkStandardBasis K hs p).repr
        (barycentricStalkStandardBasis K hs p a)) =
    (Finsupp.supportedEquivFinsupp
    {b : StandardFaceIndex P | standardCarrier b ≤ p}).symm
      ((polynomialStandardBasis (K := K) hs p).repr
        (polynomialStandardBasis (K := K) hs p a))
  rw [Module.Basis.repr_self, Module.Basis.repr_self]

theorem barycentricStalkStandardBasis_local (p : P)
    (a : BooleanChainExponent (FaceVertex p)) :
    barycentricStalkStandardBasis K hs p ((standardInsideEquiv hs p) a) =
      booleanChainBasis a := by
  simp [barycentricStalkStandardBasis]

theorem canonicalCarrierComparison_chainBasis (p : P)
    [LinearOrder (FaceVertex p)] (a : BooleanChainExponent (FaceVertex p)) :
    (canonicalCarrierComparison K hs).component p (booleanChainBasis a) =
      monomial (chainVertexMap a.val) 1 := by
  rw [← barycentricStalkStandardBasis_local K hs p a,
    canonicalCarrierComparison_standardBasis, polynomialStandardBasis_apply]
  change monomial (stalkExponent p (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val)) 1 = _
  rw [stalkExponent_map_booleanFaceInclusion]
  rfl

theorem canonicalCarrierComparison_eq (p : P) [LinearOrder (FaceVertex p)] :
    (canonicalCarrierComparison K hs).component p =
      canonicalBooleanPolynomial (V := FaceVertex p) (K := K) := by
  apply LinearEquiv.toLinearMap_injective
  apply (booleanChainBasis (V := FaceVertex p) (K := K)).ext
  intro a
  exact (canonicalCarrierComparison_chainBasis K hs p a).trans
    (canonicalBooleanPolynomial_basis a).symm

theorem barycentricStandardCoordinates_basis (p : P) (a : StandardInside p) :
    barycentricStandardCoordinates K hs p (barycentricStalkStandardBasis K hs p a) =
      coefficientUnit standardCarrier p a.val a.property := by
  have h := canonicalCarrierComparison_standardBasis K hs p a
  have hc := congrArg (polynomialStandardCoordinates K hs p) h
  change polynomialStandardCoordinates K hs p
    ((polynomialStandardCoordinates K hs p).symm
      (barycentricStandardCoordinates K hs p (barycentricStalkStandardBasis K hs p a))) = _ at hc
  rw [LinearEquiv.apply_symm_apply] at hc
  apply Subtype.ext
  exact (congrArg Subtype.val hc).trans (polynomialStandardCoordinates_basis K hs p a)

theorem polynomialStandardCoordinates_unit (p : P) (a : StandardInside p) :
    polynomialStandardCoordinates K hs p (polynomialStandardBasis (K := K) hs p a) =
      coefficientUnit standardCarrier p a.val a.property := by
  apply Subtype.ext
  exact polynomialStandardCoordinates_basis K hs p a

theorem stalkBoundaryRestriction_naturality {D E : ModuleDiagram K P}
    (e : CoherentEquiv D E) (p : P) (x : D.obj p) :
    (e.restrict (Set.Iio p)).sectionEquiv (stalkBoundaryRestriction D p x) =
      stalkBoundaryRestriction E p (e.component p x) := by
  apply Subtype.ext
  funext q
  exact (e.naturality p q.val q.property.le x).symm

def polynomialCarrierBoundaryExtension (p : P) :
    ((polynomialDiagram K).restrict (Set.Iio p)).sections →ₗ[K] PolynomialStalk K p :=
  (polynomialStandardCoordinates K hs p).symm.toLinearMap.comp
    ((coefficientBoundaryExtension standardCarrier p).comp
      (((polynomialCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv.toLinearMap))

theorem polynomialCarrierBoundaryExtension_restrict (p : P)
    (x : ((polynomialDiagram K).restrict (Set.Iio p)).sections) :
    stalkBoundaryRestriction (polynomialDiagram K) p
      (polynomialCarrierBoundaryExtension K hs p x) = x := by
  apply (((polynomialCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv).injective
  rw [stalkBoundaryRestriction_naturality]
  change stalkBoundaryRestriction (coefficientDiagram K standardCarrier) p
    (polynomialStandardCoordinates K hs p
      ((polynomialStandardCoordinates K hs p).symm
        (coefficientBoundaryExtension standardCarrier p
          (((polynomialCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv x)))) = _
  rw [LinearEquiv.apply_symm_apply, coefficientBoundaryExtension_restrict]

def carrierConjugate (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    CoherentEquiv ((coefficientDiagram K standardCarrier).restrict (Set.Iio p))
      ((coefficientDiagram K standardCarrier).restrict (Set.Iio p)) :=
  (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).symm.trans e).trans
    ((polynomialCoefficientEquiv K hs).restrict (Set.Iio p))

def coherentBoundaryCorrection (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p :=
  (polynomialCarrierBoundaryExtension K hs p).comp
    (e.sectionEquiv.toLinearMap.comp (stalkBoundaryRestriction (barycentricDiagram K) p))

theorem coherentBoundaryCorrection_restrict (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p
      (coherentBoundaryCorrection K hs p e x) =
      e.sectionEquiv (stalkBoundaryRestriction (barycentricDiagram K) p x) :=
  polynomialCarrierBoundaryExtension_restrict K hs p _

theorem coherentBoundaryCorrection_coordinates (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p) :
    polynomialStandardCoordinates K hs p (coherentBoundaryCorrection K hs p e x) =
      coefficientBoundaryExtension standardCarrier p
        ((carrierConjugate K hs p e).sectionEquiv
          (stalkBoundaryRestriction (coefficientDiagram K standardCarrier) p
            (barycentricStandardCoordinates K hs p x))) := by
  have h : (carrierConjugate K hs p e).sectionEquiv
      (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv
        (stalkBoundaryRestriction (barycentricDiagram K) p x)) =
      (((polynomialCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv
        (e.sectionEquiv (stalkBoundaryRestriction (barycentricDiagram K) p x))) := by
    apply Subtype.ext
    funext q
    change polynomialStandardCoordinates K hs q.val
      (e.component q ((barycentricStandardCoordinates K hs q.val).symm
        (barycentricStandardCoordinates K hs q.val
          ((barycentricDiagram K).res q.property.le x)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [stalkBoundaryRestriction_naturality] at h
  change polynomialStandardCoordinates K hs p
    ((polynomialStandardCoordinates K hs p).symm
      (coefficientBoundaryExtension standardCarrier p
        (((polynomialCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv
          (e.sectionEquiv (stalkBoundaryRestriction (barycentricDiagram K) p x))))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (coefficientBoundaryExtension standardCarrier p) h.symm

theorem coherentBoundaryCorrection_leading (d : ℕ) (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : HasCarrierLeading standardCarrier (standardRankWeight d) p (carrierConjugate K hs p e))
    (a : StandardInside p) (ha : standardCarrier a.val < p)
    (b : StandardFaceIndex P) (hab : standardRankWeight d a.val ≤ standardRankWeight d b) :
    (polynomialStandardCoordinates K hs p
      (coherentBoundaryCorrection K hs p e (barycentricStalkStandardBasis K hs p a))).val b =
      if a.val = b then 1 else 0 := by
  rw [coherentBoundaryCorrection_coordinates, barycentricStandardCoordinates_basis]
  have h := coefficientBoundaryExtension_leading standardCarrier (standardRankWeight d) p
    (carrierConjugate K hs p e) he a.val ha b hab
  by_cases hab' : a.val = b
  · simpa only [if_pos hab'] using h
  · simpa only [if_neg hab'] using h

theorem polynomialStandardCoordinates_apply_of_inside (p : P)
    (x : PolynomialStalk K p) (a : StandardInside p) :
    (polynomialStandardCoordinates K hs p x).val a.val = x.coeff (stalkExponent p a.val.val) := by
  have h := congrArg (fun f : StandardInside p →₀ K => f a)
    ((Finsupp.supportedEquivFinsupp (R := K) (M := K)
      {b : StandardFaceIndex P | standardCarrier b ≤ p}).apply_symm_apply
        ((polynomialStandardBasis (K := K) hs p).repr x))
  change (polynomialStandardCoordinates K hs p x).val a.val =
    ((polynomialStandardBasis (K := K) hs p).repr x) a at h
  rw [h, polynomialStandardBasis, Module.Basis.repr_reindex_apply]
  simp only [Equiv.symm_symm, standardVertexEquiv_apply]
  rfl

theorem polynomialStandardCoordinates_chain (p : P) [LinearOrder (FaceVertex p)]
    (x : PolynomialStalk K p) (a : BooleanChainExponent (FaceVertex p)) :
    (polynomialStandardCoordinates K hs p x).val ((standardInsideEquiv hs p) a).val =
      x.coeff (chainVertexMap a.val) := by
  rw [polynomialStandardCoordinates_apply_of_inside]
  change x.coeff (stalkExponent p (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val)) = _
  rw [stalkExponent_map_booleanFaceInclusion]
  rfl

end FourPapers.Universal

end
end

/- BEGIN DescentCarrier.lean -/
section


/-! # Descent generators have proper carriers and the prescribed exact weights -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def descentChainIndex (σ : VertexOrdering (Fintype.card V) V) : BooleanChainExponent V :=
  ⟨prefixExponent σ (descentColorExponent σ), prefixExponent_isChain _ _⟩

theorem descentAssignmentExponent (σ : VertexOrdering (Fintype.card V) V) :
    assignmentExponent (fun c : {c // c ∈ orderingDescents σ} => orderingFace σ c.val) =
      prefixExponent σ (descentColorExponent σ) := by
  rw [assignmentExponent, ← Finset.sum_subtype (orderingDescents σ) (fun _ => Iff.rfl)
    (fun c => Finsupp.single (orderingFace σ c) 1)]
  rw [prefixExponent, descentColorExponent, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]

theorem descentVector_eq_chainBasis (σ : VertexOrdering (Fintype.card V) V) :
    descentVector (K := K) σ = booleanChainBasis (descentChainIndex σ) := by
  rw [descentVector, Finset.prod_subtype (orderingDescents σ) (fun _ => Iff.rfl)
    (fun c => faceVariable (K := K) (orderingFace σ c)), product_faceVariables,
    descentAssignmentExponent, chainMonomial_eq_basis (prefixExponent_isChain _ _)]
  rfl

theorem polynomialDescentVector_eq_monomial (σ : VertexOrdering (Fintype.card V) V) :
    polynomialDescentVector (K := K) σ = monomial (chainVertexMap (descentChainIndex σ).val) 1 := by
  rw [polynomialDescentVector, Finset.prod_subtype (orderingDescents σ) (fun _ => Iff.rfl)
    (fun c => polynomialFaceVariable (K := K) (orderingFace σ c)),
    product_polynomialFaceVariables, descentAssignmentExponent]
  rfl

theorem descentChainIndex_weight (d : ℕ) (σ : VertexOrdering (Fintype.card V) V) :
    chainRankWeight d (descentChainIndex σ).val = colorRankWeight d (descentColorExponent σ) := by
  rw [← colorRankWeight_chainColorDegree]
  change colorRankWeight d (chainColorDegree (prefixExponent σ (descentColorExponent σ))) = _
  rw [chainColorDegree_prefixExponent]

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (hs : IsSimplicialPoset P)

theorem card_faceVertex (p : P) : Fintype.card (FaceVertex p) = faceRank p := by
  exact Fintype.card_subtype (fun a : P => IsAtom a ∧ a ≤ p)

theorem descentChainIndex_carrier_lt (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)] (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    standardCarrier ((standardInsideEquiv hs p) (descentChainIndex σ)).val < p := by
  let a := ((standardInsideEquiv hs p) (descentChainIndex σ)).val
  have hproper : ∀ F ∈ a.val.support, faceRank F.val < faceRank p := by
    intro F hF
    change F ∈ (Finsupp.mapDomain (booleanFaceInclusion hs p)
      (prefixExponent σ (descentColorExponent σ))).support at hF
    rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    rw [prefixExponent_support] at hG
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hG
    have hd : c ∈ orderingDescents σ := by
      by_contra hn
      exact Finsupp.mem_support_iff.mp hc (by simp [descentColorExponent_apply, hn])
    obtain ⟨hn, hdesc⟩ := (mem_orderingDescents _ _).mp hd
    rw [faceRank_booleanFaceInclusion, ← card_faceVertex p]
    simpa only [orderingFace, card_orderingPrefix] using hn
  have hr : faceRank (standardCarrier a) < faceRank p := by
    rcases standardCarrier_mem_or_bot a with h | ⟨F, hF, he⟩
    · rw [h, faceRank_bot, ← card_faceVertex p]
      exact Fintype.card_pos
    · rw [he]
      exact hproper F hF
  apply lt_of_le_of_ne ((standardInsideEquiv hs p) (descentChainIndex σ)).property
  intro he
  exact (ne_of_lt hr) (congrArg faceRank he)

end FourPapers.Universal

end
end

/- BEGIN CoherentLocalExtension.lean -/
section


/-! # The actual parameter-linear extension of a coherent boundary comparison -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
variable (p : P) [LinearOrder (FaceVertex p)]

def coherentLocalExtension
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  exact ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun σ => coherentBoundaryCorrection K hs p e (descentVector σ))).restrictScalars K

@[simp] theorem coherentLocalExtension_basis
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    coherentLocalExtension K hs p e (descentVector σ) =
      coherentBoundaryCorrection K hs p e (descentVector σ) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  change ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun τ => coherentBoundaryCorrection K hs p e (descentVector τ))) (descentVector σ) = _
  simpa only [booleanColorBasis_apply] using
    (Module.Basis.constr_basis (booleanColorBasis (V := FaceVertex p) (K := K))
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun τ => coherentBoundaryCorrection K hs p e (descentVector τ)) σ)

theorem coherentLocalExtension_parameter_mul
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IsParameterLinear booleanColorMap polynomialColorMap (coherentLocalExtension K hs p e) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  let f :=
    (booleanColorBasis (V := FaceVertex p) (K := K)).constr
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun σ => coherentBoundaryCorrection K hs p e (descentVector σ))
  intro a x
  change f (booleanColorMap a * x) = polynomialColorMap a * f x
  exact f.map_smul a x

variable [Nonempty (FaceVertex p)]

theorem coherentLocalExtension_descent_leading (d : ℕ)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : HasCarrierLeading standardCarrier (standardRankWeight d) p (carrierConjugate K hs p e)) :
    HasDescentLeading d (coherentLocalExtension K hs p e) := by
  intro σ b hb
  let a := descentChainIndex σ
  let i := (standardInsideEquiv hs p) a
  let c : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm b
  let j := (standardInsideEquiv hs p) c
  have hcb : chainVertexMap c.val = b := chainVertexEquiv.apply_symm_apply b
  have hw : standardRankWeight d i.val ≤ standardRankWeight d j.val := by
    rw [standardRankWeight_inside hs d p a, standardRankWeight_inside hs d p c,
      descentChainIndex_weight]
    rw [← polynomialRankWeight_chainVertexMap d c.property, hcb]
    exact hb
  have hcorr := coherentBoundaryCorrection_leading K hs d p e he i
    (descentChainIndex_carrier_lt hs p σ) j.val hw
  have hid : barycentricStalkStandardBasis K hs p i = descentVector σ := by
    exact (barycentricStalkStandardBasis_local K hs p a).trans
      (descentVector_eq_chainBasis σ).symm
  have hip : polynomialStandardBasis (K := K) hs p i = polynomialDescentVector σ := by
    rw [polynomialStandardBasis_apply, polynomialDescentVector_eq_monomial]
    change monomial (stalkExponent p
      (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val)) 1 = _
    rw [stalkExponent_map_booleanFaceInclusion]
    rfl
  have hpoly := polynomialStandardCoordinates_basis K hs p i
  have hpolyj := congrArg (fun f : StandardFaceIndex P →₀ K => f j.val) hpoly
  rw [hip] at hpolyj
  have hcoord : (polynomialStandardCoordinates K hs p
      (coherentBoundaryCorrection K hs p e (descentVector σ))).val j.val =
      (polynomialStandardCoordinates K hs p (polynomialDescentVector σ)).val j.val := by
    rw [hid] at hcorr
    rw [hpolyj]
    by_cases hij : i.val = j.val
    · simpa only [if_pos hij, Finsupp.single_apply, hij, if_pos rfl] using hcorr
    · simpa only [if_neg hij, Finsupp.single_apply, Ne.symm hij] using hcorr
  change (coherentLocalExtension K hs p e (descentVector σ) - polynomialDescentVector σ).coeff b = 0
  rw [coherentLocalExtension_basis, MvPolynomial.coeff_sub, sub_eq_zero]
  change (polynomialStandardCoordinates K hs p
      (coherentBoundaryCorrection K hs p e (descentVector σ))).val
      ((standardInsideEquiv hs p) c).val =
      (polynomialStandardCoordinates K hs p (polynomialDescentVector σ)).val
        ((standardInsideEquiv hs p) c).val at hcoord
  rw [polynomialStandardCoordinates_chain, polynomialStandardCoordinates_chain, hcb] at hcoord
  exact hcoord

def coherentLocalParameterEquiv (d : ℕ) (hrank : Fintype.card (FaceVertex p) ≤ d)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : HasCarrierLeading standardCarrier (standardRankWeight d) p (carrierConjugate K hs p e)) :
    ParameterEquiv (booleanColorMap (V := FaceVertex p) (K := K)) polynomialColorMap :=
  parameterLinearLeadingEquiv d hrank (coherentLocalExtension K hs p e)
    (coherentLocalExtension_parameter_mul K hs p e)
    (coherentLocalExtension_descent_leading K hs p d e he)

end FourPapers.Universal

end
end

/- BEGIN RankParameterNaturality.lean -/
section


/-! # All rank parameters and descent-basis extensionality -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def IntertwinesAllRanks (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) : Prop :=
  ∀ i : ℕ, ∀ x, f (booleanRankParameter (i + 1) * x) = esymm V K (i + 1) * f x

theorem esymm_above_card (i : ℕ) (hi : Fintype.card V < i) :
    esymm V K i = 0 := by
  unfold esymm
  rw [Finset.powersetCard_eq_empty.mpr (by simpa using hi), Finset.sum_empty]

theorem parameterLinear_intertwinesAllRanks
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f) :
    IntertwinesAllRanks f := by
  intro i x
  by_cases hi : i < Fintype.card V
  · let c : Fin (Fintype.card V) := ⟨i, hi⟩
    have h := hf (X c) x
    rw [booleanColorMap, MvPolynomial.aeval_X, polynomialColorMap, MvPolynomial.aeval_X] at h
    rw [booleanRankParameter_color c]
    exact h
  · have hi' : Fintype.card V < i + 1 := by omega
    rw [booleanRankParameter_above _ hi', esymm_above_card _ hi', zero_mul,
      zero_mul, f.map_zero]

theorem parameterLinear_ext_descent {N : Type*} [CommRing N] [Algebra K N]
    (ψ : MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] N)
    (f g : BooleanBarycentricRing V K →ₗ[K] N)
    (hf : IsParameterLinear booleanColorMap ψ f)
    (hg : IsParameterLinear booleanColorMap ψ g)
    (he : ∀ σ : VertexOrdering (Fintype.card V) V, f (descentVector σ) = g (descentVector σ)) :
    f = g := by
  apply (booleanParameterBasis (V := V) (K := K)).ext
  intro p
  rw [booleanParameterBasis_apply, parameterDescentVector_eq_monomial_smul, Algebra.smul_def]
  change f (booleanColorMap (monomial p.2 1) * descentVector p.1) =
    g (booleanColorMap (monomial p.2 1) * descentVector p.1)
  rw [hf, hg, he]

end FourPapers.Universal

end
end

/- BEGIN CoherentLocalNaturality.lean -/
section


/-! # Full naturality of the actual local extension -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
variable (p : P) [LinearOrder (FaceVertex p)]

theorem coherentLocalExtension_intertwinesAllRanks
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IntertwinesAllRanks (coherentLocalExtension K hs p e) :=
  parameterLinear_intertwinesAllRanks _ (coherentLocalExtension_parameter_mul K hs p e)

set_option backward.isDefEq.respectTransparency false in
theorem coherentLocalExtension_naturality
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q ((booleanRankParameter (V := FaceVertex q.val) (K := K) (i + 1)) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (q : Set.Iio p) (x : BarycentricStalk K p) :
    polynomialRestriction K q.property.le (coherentLocalExtension K hs p e x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x) := by
  let F : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (polynomialRestriction K q.property.le).toLinearMap.comp (coherentLocalExtension K hs p e)
  let G : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (e.component q).toLinearMap.comp
      (booleanRestriction (K := K) (faceVertexInclusion q.property.le)).toLinearMap
  have hF : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change polynomialRestriction K q.property.le
      (coherentLocalExtension K hs p e (booleanColorMap (X c) * z)) = _
    erw [coherentLocalExtension_parameter_mul K hs p e, map_mul]
    rw [polynomialColorMap, MvPolynomial.aeval_X,
      polynomialParameterMap, MvPolynomial.aeval_X]
    change polynomialRestriction K q.property.le
      (esymm (FaceVertex p) K (c.val + 1)) *
      polynomialRestriction K q.property.le (coherentLocalExtension K hs p e z) =
      esymm (FaceVertex q.val) K (c.val + 1) *
      polynomialRestriction K q.property.le (coherentLocalExtension K hs p e z)
    congr 1
    exact polynomialRestriction_parameter K q.property.le (c.val + 1)
  have hG : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) G := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change e.component q (booleanRestriction (faceVertexInclusion q.property.le)
      (booleanColorMap (X c) * z)) = _
    erw [map_mul]
    have hb : booleanRestriction (K := K) (faceVertexInclusion q.property.le)
        (booleanColorMap (X c)) = booleanRankParameter (c.val + 1) := by
      have hc : booleanColorMap (K := K) (X c) = colorSum c := by
        rw [booleanColorMap, MvPolynomial.aeval_X]
        rfl
      have hcol := hc.trans (booleanRankParameter_color (K := K) c).symm
      exact (congrArg (booleanRestriction (K := K) (faceVertexInclusion q.property.le)) hcol).trans
        (booleanRestriction_rankParameter (K := K) (faceVertexInclusion q.property.le) (c.val + 1))
    erw [hb]
    rw [polynomialParameterMap, MvPolynomial.aeval_X]
    change e.component q (booleanRankParameter (c.val + 1) *
      booleanRestriction (faceVertexInclusion q.property.le) z) =
      polynomialParameter K q.val (c.val + 1) *
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) z)
    exact he q c.val (booleanRestriction (faceVertexInclusion q.property.le) z)
  have hfg : F = G := parameterLinear_ext_descent
    (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F G hF hG (by
      intro σ
      change polynomialRestriction K q.property.le
        (coherentLocalExtension K hs p e (descentVector σ)) = _
      rw [coherentLocalExtension_basis]
      have h := congrArg (fun y : ((polynomialDiagram K).restrict (Set.Iio p)).sections => y.val q)
        (coherentBoundaryCorrection_restrict K hs p e (descentVector σ))
      exact h)
  exact DFunLike.congr_fun hfg x

end FourPapers.Universal

end
end

/- BEGIN GlobalCanonicalProperty.lean -/
section

/-! # Carrying the canonical leading symbols through the finite face induction -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def HasStandardLeading (d : ℕ) (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) : Prop :=
  ∀ (a : StandardInside p) (b : StandardFaceIndex P),
    standardRankWeight d a.val ≤ standardRankWeight d b →
    (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).val b =
      if a.val = b then 1 else 0

theorem canonicalCarrierComparison_hasStandardLeading (d : ℕ) (p : P) :
    HasStandardLeading K hs d p ((canonicalCarrierComparison K hs).component p).toLinearMap := by
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    ((canonicalCarrierComparison K hs).component p (barycentricStalkStandardBasis K hs p a))).val b = _
  rw [canonicalCarrierComparison_standardBasis, polynomialStandardCoordinates_basis]
  by_cases h : a.val = b
  · simp only [Finsupp.single_apply, if_pos h, if_pos h.symm]
  · simp only [Finsupp.single_apply, if_neg h, if_neg (Ne.symm h)]

set_option backward.isDefEq.respectTransparency false in
theorem parameterLinear_hasStandardLeading (d : ℕ) (p : P) [LinearOrder (FaceVertex p)]
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : HasDescentLeading d f) : HasStandardLeading K hs d p f := by
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hw : chainRankWeight d u.val ≤ chainRankWeight d v.val := by
      rw [← standardRankWeight_inside hs d p u, ← standardRankWeight_inside hs d p v, hu, hv]
      exact hab
    have h := parameterLinear_chain_leading d f hf hd u (chainVertexMap v.val) (by
      simpa only [polynomialRankWeight_chainVertexMap d v.property] using hw)
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at h
    erw [canonicalBooleanPolynomial_basis] at h
    have hcoord := polynomialStandardCoordinates_chain K hs p (f (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u := by
      exact hu ▸ barycentricStalkStandardBasis_local K hs p u
    have heq : chainVertexMap u.val = chainVertexMap v.val ↔ a.val = b := by
      constructor
      · intro h'
        have huv : u = v := chainVertexEquiv.injective h'
        have hidx := congrArg (standardInsideEquiv hs p) huv
        rw [hu, hv] at hidx
        exact congrArg Subtype.val hidx
      · intro h'
        have hidx : a = (⟨b, hb⟩ : StandardInside p) := Subtype.ext h'
        have huv : u = v := (standardInsideEquiv hs p).injective (hu.trans (hidx.trans hv.symm))
        exact congrArg (fun z : BooleanChainExponent (FaceVertex p) => chainVertexMap z.val) huv
    erw [hsource]
    rw [hcoord]
    erw [h, MvPolynomial.coeff_monomial]
    by_cases h' : a.val = b
    · simp only [if_pos h', if_pos (heq.mpr h')]
    · simp only [if_neg h', if_neg (fun h => h' (heq.mp h))]
  · have hz := (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).property b hb
    have hn : a.val ≠ b := by intro h; subst b; exact hb a.property
    rw [if_neg hn]
    exact hz

set_option backward.isDefEq.respectTransparency false in
theorem carrierConjugate_hasLeading (d : ℕ) (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardLeading K hs d q.val (e.component q).toLinearMap) :
    HasCarrierLeading standardCarrier (standardRankWeight d) p (carrierConjugate K hs p e) := by
  intro q i hi j hij
  change (polynomialStandardCoordinates K hs q.val
    (e.component q ((barycentricStandardCoordinates K hs q.val).symm
      (coefficientUnit standardCarrier q.val i hi)))).val j = _
  rw [← barycentricStandardCoordinates_basis K hs q.val ⟨i, hi⟩,
    LinearEquiv.symm_apply_apply]
  have h := he q ⟨i, hi⟩ j hij
  by_cases hij' : i = j
  · simpa only [LinearEquiv.coe_coe, if_pos hij'] using h
  · simpa only [LinearEquiv.coe_coe, if_neg hij'] using h

theorem canonicalCarrierComparison_ranks_empty (p : P) [LinearOrder (FaceVertex p)]
    (hp : Fintype.card (FaceVertex p) = 0) :
    IntertwinesAllRanks ((canonicalCarrierComparison K hs).component p).toLinearMap := by
  intro i x
  have hn : Fintype.card (FaceVertex p) < i + 1 := by omega
  erw [booleanRankParameter_above _ hn, esymm_above_card _ hn, zero_mul, zero_mul]
  exact ((canonicalCarrierComparison K hs).component p).map_zero

set_option backward.isDefEq.respectTransparency false in
/-- The coherent finite-poset construction, on the two actual face diagrams,
with full rank-parameter linearity and the original canonical leading symbols. -/
theorem exists_coherent_parameter_comparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      ∀ p : P, HasStandardLeading K hs d p (e.component p).toLinearMap ∧
        (∀ i : ℕ, ∀ x : BarycentricStalk K p,
          e.component p (booleanRankParameter (i + 1) * x) =
            polynomialParameter K p (i + 1) * e.component p x) := by
  letI : ∀ p : P, LinearOrder (FaceVertex p) := fun p =>
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  let property (p : P) (f : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p) : Prop :=
    HasStandardLeading K hs d p f.toLinearMap ∧ IntertwinesAllRanks f.toLinearMap
  apply coherentEquiv_of_boundaryLifts (D := barycentricDiagram K) (E := polynomialDiagram K)
    faceRank (faceRank_strictMono hs) property
  intro p e he
  by_cases hp : p = ⊥
  · subst p
    refine ⟨(canonicalCarrierComparison K hs).component ⊥, ?_, ?_⟩
    · exact ⟨canonicalCarrierComparison_hasStandardLeading K hs d ⊥,
        canonicalCarrierComparison_ranks_empty K hs ⊥ (by rw [card_faceVertex, faceRank_bot])⟩
    · intro q x
      exact (not_lt_bot q.property).elim
  · have hpos : 0 < Fintype.card (FaceVertex p) := by
      rw [card_faceVertex]
      exact Finset.card_pos.mpr (faceVertices_nonempty hs hp)
    letI : Nonempty (FaceVertex p) := Fintype.card_pos_iff.mp hpos
    have hlead := carrierConjugate_hasLeading K hs d p e (fun q => (he q).1)
    have hr : Fintype.card (FaceVertex p) ≤ d := by rw [card_faceVertex]; exact hrank p
    let f := coherentLocalParameterEquiv K hs p d hr e hlead
    have happ (x : BarycentricStalk K p) : f.toLinearEquiv x = coherentLocalExtension K hs p e x := rfl
    have hmap : f.toLinearEquiv.toLinearMap = coherentLocalExtension K hs p e := by
      exact LinearMap.ext happ
    refine ⟨f.toLinearEquiv, ?_, ?_⟩
    · change HasStandardLeading K hs d p f.toLinearEquiv.toLinearMap ∧
        IntertwinesAllRanks f.toLinearEquiv.toLinearMap
      rw [hmap]
      exact ⟨parameterLinear_hasStandardLeading K hs d p _
        (coherentLocalExtension_parameter_mul K hs p e)
        (coherentLocalExtension_descent_leading K hs p d e hlead),
        coherentLocalExtension_intertwinesAllRanks K hs p e⟩
    · intro q x
      erw [happ]
      exact coherentLocalExtension_naturality K hs p e (fun q i x => (he q).2 i x) q x

end FourPapers.Universal

end
end

/- BEGIN GradedLocalExtension.lean -/
section

/-! # Ordinary degree of the actual coherent parameter extension

The degree is the sum of face ranks, with multiplicity. On a polynomial stalk
this is exactly ordinary monomial degree. These lemmas do not replace the
separate rank-weight filtration used for invertibility.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def colorOrdinaryDegree (m : ColorExponent V) : ℕ :=
  m.sum (fun c n => n * (c.val + 1))

def chainOrdinaryDegree (a : BooleanFace V →₀ ℕ) : ℕ :=
  a.sum (fun F n => n * F.val.card)

theorem colorOrdinaryDegree_add (m n : ColorExponent V) :
    colorOrdinaryDegree (m + n) = colorOrdinaryDegree m + colorOrdinaryDegree n :=
  Finsupp.sum_add_index' (fun c => by simp) (fun c i j => by simp only [add_mul])

theorem colorOrdinaryDegree_fintype (m : ColorExponent V) :
    colorOrdinaryDegree m = ∑ c : Fin (Fintype.card V), m c * (c.val + 1) :=
  Finsupp.sum_fintype m _ (fun c => by simp)

theorem colorOrdinaryDegree_chainColorDegree (a : BooleanFace V →₀ ℕ) :
    colorOrdinaryDegree (chainColorDegree a) = chainOrdinaryDegree a := by
  unfold colorOrdinaryDegree chainColorDegree
  rw [Finsupp.sum_mapDomain_index (fun c => by simp) (fun c i j => by simp only [add_mul])]
  simp only [BooleanFace.color_succ, chainOrdinaryDegree]

theorem vertexDegree_eq_chainOrdinaryDegree (a : BooleanFace V →₀ ℕ) :
    vertexDegree (fun v => chainVertexMap a v) = chainOrdinaryDegree a :=
  vertexDegree_chainVertexMap a

def polynomialDegreePiece (n : ℕ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a : V →₀ ℕ, vertexDegree (fun v => a v) ≠ n → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by
    intro f g hf hg a ha
    rw [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := by
    intro c f hf a ha
    rw [MvPolynomial.coeff_smul, hf a ha, smul_zero]

theorem polynomialDegreePiece_support (n : ℕ) (f : MvPolynomial V K)
    (hf : f ∈ polynomialDegreePiece n) (a : V →₀ ℕ) (ha : a ∈ f.support) :
    vertexDegree (fun v => a v) = n := by
  by_contra hn
  exact MvPolynomial.mem_support_iff.mp ha (hf a hn)

theorem monomial_mem_polynomialDegreePiece (a : V →₀ ℕ) (c : K) :
    monomial a c ∈ polynomialDegreePiece (vertexDegree (fun v => a v)) := by
  intro b hb
  have hne : a ≠ b := fun h => hb (h ▸ rfl)
  simp [MvPolynomial.coeff_monomial, hne]

theorem polynomialDegreePiece_mul (m n : ℕ) (f g : MvPolynomial V K)
    (hf : f ∈ polynomialDegreePiece m) (hg : g ∈ polynomialDegreePiece n) :
    f * g ∈ polynomialDegreePiece (m + n) := by
  rw [f.as_sum, g.as_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro a ha
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro b hb
  rw [MvPolynomial.monomial_mul_monomial]
  have hd : vertexDegree (fun v => (a + b) v) = m + n := by
    rw [show (fun v => (a + b) v) = (fun v => a v) + (fun v => b v) from rfl,
      vertexDegree_add, polynomialDegreePiece_support m f hf a ha,
      polynomialDegreePiece_support n g hg b hb]
  rw [← hd]
  exact monomial_mem_polynomialDegreePiece _ _

theorem polynomialDegreePiece_one : (1 : MvPolynomial V K) ∈ polynomialDegreePiece 0 := by
  have h := monomial_mem_polynomialDegreePiece (V := V) (0 : V →₀ ℕ) (1 : K)
  simpa [vertexDegree] using h

theorem polynomialDegreePiece_pow (m : ℕ) (f : MvPolynomial V K)
    (hf : f ∈ polynomialDegreePiece m) (n : ℕ) :
    f ^ n ∈ polynomialDegreePiece (n * m) := by
  induction n with
  | zero => simpa using (polynomialDegreePiece_one (V := V) (K := K))
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using polynomialDegreePiece_mul _ m (f ^ n) f ih hf

theorem polynomialDegreePiece_prod {T : Type*} (s : Finset T)
    (m : T → ℕ) (f : T → MvPolynomial V K)
    (hf : ∀ t ∈ s, f t ∈ polynomialDegreePiece (m t)) :
    (∏ t ∈ s, f t) ∈ polynomialDegreePiece (∑ t ∈ s, m t) := by
  induction s using Finset.induction_on with
  | empty => simpa using (polynomialDegreePiece_one (V := V) (K := K))
  | @insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht]
    exact polynomialDegreePiece_mul _ _ _ _ (hf t (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem esymm_mem_polynomialDegreePiece (c : Fin (Fintype.card V)) :
    esymm V K (c.val + 1) ∈ polynomialDegreePiece (c.val + 1) := by
  rw [esymm_eq_sum_polynomialFaceVariable]
  apply Submodule.sum_mem
  intro F hF
  have h := monomial_mem_polynomialDegreePiece (subsetExponent F.val) (1 : K)
  have he : (fun v => subsetExponent F.val v) = faceIndicator F.val := by
    funext v
    simp [faceIndicator]
  rw [he, vertexDegree_indicator, ← F.color_succ, (mem_facesOfColor _ _).mp hF] at h
  exact h

theorem polynomialColorMap_monomial_degree (m : ColorExponent V) :
    polynomialColorMap (K := K) (monomial m 1) ∈ polynomialDegreePiece (colorOrdinaryDegree m) := by
  have he : polynomialColorMap (K := K) (monomial m 1) =
      ∏ c : Fin (Fintype.card V), esymm V K (c.val + 1) ^ m c := by
    unfold polynomialColorMap
    rw [MvPolynomial.aeval_monomial, map_one, one_mul]
    exact Finsupp.prod_fintype m
      (fun c n => esymm V K (c.val + 1) ^ n) (fun c => pow_zero _)
  rw [he, colorOrdinaryDegree_fintype]
  apply polynomialDegreePiece_prod
  intro c hc
  exact polynomialDegreePiece_pow _ _ (esymm_mem_polynomialDegreePiece c) _

/-- Parameter linearity and the actual degrees of descent images suffice for
ordinary homogeneity on every standard chain monomial. -/
theorem parameterLinear_chain_degree
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (a : BooleanChainExponent V) :
    f (booleanChainBasis a) ∈ polynomialDegreePiece (chainOrdinaryDegree a.val) := by
  let b := booleanParameterBasis (V := V) (K := K)
  let x := booleanChainBasis (K := K) a
  have hx : x = ∑ p ∈ (b.repr x).support, (b.repr x p) • b p := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (b.linearCombination_repr x).symm
  change f x ∈ _
  rw [hx]
  have hmap : f (∑ p ∈ (b.repr x).support, (b.repr x p) • b p) =
      ∑ p ∈ (b.repr x).support, f ((b.repr x p) • b p) :=
    map_sum f.toAddMonoidHom _ _
  rw [hmap]
  apply Submodule.sum_mem
  intro p hp
  rw [f.map_smul]
  apply Submodule.smul_mem
  have hc : p.2 + descentColorExponent p.1 = chainColorDegree a.val := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hp (booleanParameterBasis_repr_color a p h)
  have hfp : f (parameterDescentVector p) =
      polynomialColorMap (monomial p.2 1) * f (descentVector p.1) := by
    rw [parameterDescentVector_eq_monomial_smul, Algebra.smul_def]
    exact hf _ _
  have hm := polynomialDegreePiece_mul _ _ _ _ (polynomialColorMap_monomial_degree (K := K) p.2)
    (hd p.1)
  rw [← colorOrdinaryDegree_add, hc, colorOrdinaryDegree_chainColorDegree, ← hfp] at hm
  simpa only [b, booleanParameterBasis_apply] using hm

end FourPapers.Universal

end
end

/- BEGIN GradedCarrierExtension.lean -/
section

/-! # Homogeneity is preserved by the literal carrier boundary lift -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def standardOrdinaryDegree (a : StandardFaceIndex P) : ℕ :=
  a.val.sum (fun F n => n * faceRank F.val)

theorem standardOrdinaryDegree_inside (p : P) [LinearOrder (FaceVertex p)]
    (a : BooleanChainExponent (FaceVertex p)) :
    standardOrdinaryDegree ((standardInsideEquiv hs p) a).val = chainOrdinaryDegree a.val := by
  change (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).sum
    (fun F n => n * faceRank F.val) = _
  rw [Finsupp.sum_mapDomain_index (fun F => by simp) (fun F i j => by simp only [add_mul])]
  simp only [faceRank_booleanFaceInclusion, chainOrdinaryDegree]

def HasStandardDegree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) : Prop :=
  ∀ (a : StandardInside p) (b : StandardFaceIndex P),
    standardOrdinaryDegree b ≠ standardOrdinaryDegree a.val →
    (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).val b = 0

theorem canonicalCarrierComparison_hasStandardDegree (p : P) :
    HasStandardDegree K hs p ((canonicalCarrierComparison K hs).component p).toLinearMap := by
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    ((canonicalCarrierComparison K hs).component p (barycentricStalkStandardBasis K hs p a))).val b = 0
  rw [canonicalCarrierComparison_standardBasis, polynomialStandardCoordinates_basis]
  have hne : a.val ≠ b := fun h => hab (h ▸ rfl)
  simp [Finsupp.single_apply, hne, Ne.symm hne]

theorem coherentBoundaryCorrection_standard_degree (p : P)
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q).toLinearMap) :
    HasStandardDegree K hs p (coherentBoundaryCorrection K hs p e) := by
  intro a b hab
  rw [coherentBoundaryCorrection_coordinates, barycentricStandardCoordinates_basis,
    coefficientBoundaryExtension_apply]
  by_cases hb : standardCarrier b < p
  · rw [dif_pos hb]
    change ((carrierConjugate K hs p e).component ⟨standardCarrier b, hb⟩
      (coefficientRestriction K standardCarrier hb.le
        (coefficientUnit standardCarrier p a.val a.property))).val b = 0
    rw [coefficientRestriction_unit]
    by_cases ha : standardCarrier a.val ≤ standardCarrier b
    · rw [dif_pos ha]
      change (polynomialStandardCoordinates K hs (standardCarrier b)
        (e.component ⟨standardCarrier b, hb⟩
          ((barycentricStandardCoordinates K hs (standardCarrier b)).symm
            (coefficientUnit standardCarrier (standardCarrier b) a.val ha)))).val b = 0
      rw [← barycentricStandardCoordinates_basis K hs (standardCarrier b) ⟨a.val, ha⟩,
        LinearEquiv.symm_apply_apply]
      exact he ⟨standardCarrier b, hb⟩ ⟨a.val, ha⟩ b hab
    · erw [dif_neg ha, LinearEquiv.map_zero]
      rfl
  · rw [dif_neg hb]

theorem descentChainIndex_degree (p : P) [LinearOrder (FaceVertex p)]
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    chainOrdinaryDegree (descentChainIndex σ).val =
      colorOrdinaryDegree (descentColorExponent σ) := by
  rw [← colorOrdinaryDegree_chainColorDegree]
  change colorOrdinaryDegree (chainColorDegree (prefixExponent σ (descentColorExponent σ))) = _
  rw [chainColorDegree_prefixExponent]

theorem coherentLocalExtension_descent_degree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q).toLinearMap)
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    coherentLocalExtension K hs p e (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  intro b hb
  let a := descentChainIndex σ
  let c : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm b
  have hcb : chainVertexMap c.val = b := chainVertexEquiv.apply_symm_apply b
  have hne : standardOrdinaryDegree ((standardInsideEquiv hs p) c).val ≠
      standardOrdinaryDegree ((standardInsideEquiv hs p) a).val := by
    erw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside, descentChainIndex_degree,
      ← vertexDegree_eq_chainOrdinaryDegree, hcb]
    exact hb
  have h := coherentBoundaryCorrection_standard_degree K hs p e he
    ((standardInsideEquiv hs p) a) ((standardInsideEquiv hs p) c).val hne
  erw [barycentricStalkStandardBasis_local, ← descentVector_eq_chainBasis,
    polynomialStandardCoordinates_chain, hcb] at h
  change (coherentLocalExtension K hs p e (descentVector σ)).coeff b = 0
  rw [coherentLocalExtension_basis]
  exact h

theorem coherentLocalExtension_hasStandardDegree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q).toLinearMap) :
    HasStandardDegree K hs p (coherentLocalExtension K hs p e) := by
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := parameterLinear_chain_degree (coherentLocalExtension K hs p e)
      (coherentLocalExtension_parameter_mul K hs p e)
      (coherentLocalExtension_descent_degree K hs p e he) u (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p
      (coherentLocalExtension K hs p e (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p
        (coherentLocalExtension K hs p e (barycentricStalkStandardBasis K hs p a))).property b hb

end FourPapers.Universal

end
end

/- BEGIN GlobalGradedComparison.lean -/
section

/-! # The graded coherent comparison on all actual face stalks -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

set_option backward.isDefEq.respectTransparency false in
/-- Finite coherent induction, with ordinary degree, full parameter action,
and the paper's exact rank-weight leading coefficients retained together. -/
theorem exists_graded_coherent_parameter_comparison (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      ∀ p : P, HasStandardLeading K hs d p (e.component p).toLinearMap ∧
        (∀ i : ℕ, ∀ x : BarycentricStalk K p,
          e.component p (booleanRankParameter (i + 1) * x) =
            polynomialParameter K p (i + 1) * e.component p x) ∧
        HasStandardDegree K hs p (e.component p).toLinearMap := by
  letI : ∀ p : P, LinearOrder (FaceVertex p) := fun p =>
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  let property (p : P) (f : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p) : Prop :=
    HasStandardLeading K hs d p f.toLinearMap ∧ IntertwinesAllRanks f.toLinearMap ∧
      HasStandardDegree K hs p f.toLinearMap
  apply coherentEquiv_of_boundaryLifts (D := barycentricDiagram K) (E := polynomialDiagram K)
    faceRank (faceRank_strictMono hs) property
  intro p e he
  by_cases hp : p = ⊥
  · subst p
    refine ⟨(canonicalCarrierComparison K hs).component ⊥, ?_, ?_⟩
    · exact ⟨canonicalCarrierComparison_hasStandardLeading K hs d ⊥,
        canonicalCarrierComparison_ranks_empty K hs ⊥ (by rw [card_faceVertex, faceRank_bot]),
        canonicalCarrierComparison_hasStandardDegree K hs ⊥⟩
    · intro q x
      exact (not_lt_bot q.property).elim
  · have hpos : 0 < Fintype.card (FaceVertex p) := by
      rw [card_faceVertex]
      exact Finset.card_pos.mpr (faceVertices_nonempty hs hp)
    letI : Nonempty (FaceVertex p) := Fintype.card_pos_iff.mp hpos
    have hlead := carrierConjugate_hasLeading K hs d p e (fun q => (he q).1)
    have hr : Fintype.card (FaceVertex p) ≤ d := by rw [card_faceVertex]; exact hrank p
    let f := coherentLocalParameterEquiv K hs p d hr e hlead
    have happ (x : BarycentricStalk K p) :
        f.toLinearEquiv x = coherentLocalExtension K hs p e x := rfl
    have hmap : f.toLinearEquiv.toLinearMap = coherentLocalExtension K hs p e := by
      exact LinearMap.ext happ
    refine ⟨f.toLinearEquiv, ?_, ?_⟩
    · change HasStandardLeading K hs d p f.toLinearEquiv.toLinearMap ∧
        IntertwinesAllRanks f.toLinearEquiv.toLinearMap ∧
        HasStandardDegree K hs p f.toLinearEquiv.toLinearMap
      rw [hmap]
      exact ⟨parameterLinear_hasStandardLeading K hs d p _
        (coherentLocalExtension_parameter_mul K hs p e)
        (coherentLocalExtension_descent_leading K hs p d e hlead),
        coherentLocalExtension_intertwinesAllRanks K hs p e,
        coherentLocalExtension_hasStandardDegree K hs p e (fun q => (he q).2.2)⟩
    · intro q x
      erw [happ]
      exact coherentLocalExtension_naturality K hs p e (fun q i x => (he q).2.1 i x) q x

end FourPapers.Universal

end
end

#print axioms FourPapers.Universal.exists_coherent_parameter_comparison
#print axioms FourPapers.Universal.exists_graded_coherent_parameter_comparison

end
end

/- BEGIN FourPapers/Universal/PaperComparison.lean -/
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/- BEGIN MonomialBaseChange.lean -/
section


/-! # Coefficient change and actual scalar extension of monomial quotients

The basis construction supplies explicit semilinear coefficient maps and an
actual tensor-product equivalence. Naturality is checked on genuine quotient
restrictions; no flatness hypothesis is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical

variable {V W K L : Type*} [CommRing K] [CommRing L]
variable (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) (h : K →+* L)

/-- Apply the coefficient homomorphism to the actual standard coefficients. -/
def monomialCoefficientMap :
    MonomialQuotient (K := K) P →ₛₗ[h] MonomialQuotient (K := L) P :=
  (standardMonomialEquiv (K := L) P hP).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap h.toSemilinearMap).comp
      (standardMonomialEquiv (K := K) P hP).toLinearMap)

@[simp] theorem monomialCoefficientMap_coordinates (x : MonomialQuotient (K := K) P) :
    standardMonomialEquiv P hP (monomialCoefficientMap P hP h x) =
      Finsupp.mapRange h h.map_zero (standardMonomialEquiv P hP x) := by
  simp [monomialCoefficientMap]

/-- The coefficient-coordinate map is precisely the usual coefficient map on
polynomial representatives, so it respects the intended quotient objects. -/
@[simp] theorem monomialCoefficientMap_mk (f : MvPolynomial V K) :
    monomialCoefficientMap P hP h (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      Ideal.Quotient.mk (forbiddenIdeal P) (MvPolynomial.map h f) := by
  apply (standardMonomialEquiv (K := L) P hP).injective
  rw [monomialCoefficientMap_coordinates, standardMonomialEquiv_mk,
    standardMonomialEquiv_mk]
  ext a
  simp only [Finsupp.mapRange_apply, standardCoefficients_apply, MvPolynomial.coeff_map]

@[simp] theorem monomialCoefficientMap_basis (a : {a // P a}) :
    monomialCoefficientMap P hP h (standardMonomialBasis (K := K) P hP a) =
      standardMonomialBasis (K := L) P hP a := by
  rw [standardMonomialBasis_apply, monomialCoefficientMap_mk,
    standardMonomialBasis_apply, MvPolynomial.map_monomial, map_one]

/-- The same explicit map is a homomorphism of the actual quotient rings. -/
def monomialCoefficientRingHom :
    MonomialQuotient (K := K) P →+* MonomialQuotient (K := L) P where
  toFun := monomialCoefficientMap P hP h
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    have he := monomialCoefficientMap_mk P hP h (1 : MvPolynomial V K)
    simpa only [map_one] using he
  map_mul' x y := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul (Ideal.Quotient.mk (forbiddenIdeal (K := K) P)) f g,
      monomialCoefficientMap_mk, monomialCoefficientMap_mk, monomialCoefficientMap_mk,
      map_mul (MvPolynomial.map h), map_mul]

/-- Actual face restriction commutes with every coefficient homomorphism. -/
theorem monomialCoefficientMap_restriction
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e))
    (x : MonomialQuotient (K := K) P) :
    monomialCoefficientMap Q hQ h (monomialRestriction e P Q hP hQ allowed x) =
      monomialRestriction e P Q hP hQ allowed (monomialCoefficientMap P hP h x) := by
  apply (standardMonomialEquiv (K := L) Q hQ).injective
  ext a
  rw [monomialCoefficientMap_coordinates, Finsupp.mapRange_apply,
    monomialRestriction_coefficient, monomialRestriction_coefficient,
    monomialCoefficientMap_coordinates, Finsupp.mapRange_apply]

section Tensor

variable [Algebra K L]
open scoped TensorProduct

/-- Scalar extension is an actual tensor-product equivalence, proved from
the standard monomial bases over the two coefficient rings. -/
def monomialTensorBaseChange :
    L ⊗[K] MonomialQuotient (K := K) P ≃ₗ[L] MonomialQuotient (K := L) P :=
  ((standardMonomialBasis (K := K) P hP).baseChange L).repr.trans
    (standardMonomialBasis (K := L) P hP).repr.symm

@[simp] theorem monomialTensorBaseChange_tmul (c : L)
    (x : MonomialQuotient (K := K) P) :
    monomialTensorBaseChange (K := K) (L := L) P hP (c ⊗ₜ[K] x) =
      c • monomialCoefficientMap P hP (algebraMap K L) x := by
  apply (standardMonomialBasis (K := L) P hP).repr.injective
  simp only [monomialTensorBaseChange, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  ext a
  rw [Module.Basis.baseChange_repr_tmul]
  change (standardMonomialEquiv (K := K) P hP x a) • c = _
  rw [map_smul, Finsupp.smul_apply]
  change (standardMonomialEquiv (K := K) P hP x a) • c =
    c * standardMonomialEquiv (K := L) P hP
      (monomialCoefficientMap P hP (algebraMap K L) x) a
  rw [monomialCoefficientMap_coordinates, Finsupp.mapRange_apply, Algebra.smul_def, mul_comm]

end Tensor

end FourPapers.Universal
end
end

/- BEGIN BasisBaseChange.lean -/
section


/-! # Explicit basis maps commute with coefficient change

These lemmas reduce scalar naturality to the images of the specified basis
vectors. They require neither flatness nor a tensor-product exactness claim.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

variable {I K L M N M' N' : Type*} [CommRing K] [CommRing L]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module L N]
  [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module L N']

/-- The inverse basis coordinates commute with coefficient change because
the basis vectors do; no choice made inside `Basis.repr` adds an assumption. -/
theorem basis_repr_baseChange (h : K →+* L)
    (bK : Module.Basis I K M) (bL : Module.Basis I L N)
    (f : M →ₛₗ[h] N) (hf : ∀ i, f (bK i) = bL i) (x : M) :
    bL.repr (f x) = Finsupp.mapRange h h.map_zero (bK.repr x) := by
  have he : bL.repr.toLinearMap.comp f =
      (Finsupp.mapRange.linearMap h.toSemilinearMap).comp bK.repr.toLinearMap := by
    apply bK.ext
    intro i
    simp [hf]
  exact DFunLike.congr_fun he x

/-- A map specified by an explicit basis-image family is natural under
coefficient change whenever that family is natural. -/
theorem basis_constr_baseChange (h : K →+* L)
    (bK : Module.Basis I K M) (bL : Module.Basis I L N)
    (f : M →ₛₗ[h] N) (g : M' →ₛₗ[h] N')
    (v : I → M') (w : I → N')
    (hf : ∀ i, f (bK i) = bL i) (hv : ∀ i, g (v i) = w i) (x : M) :
    g (bK.constr K v x) = bL.constr L w (f x) := by
  have he : g.comp (bK.constr K v) = (bL.constr L w).comp f := by
    apply bK.ext
    intro i
    simp [hf, hv]
  exact DFunLike.congr_fun he x

end FourPapers.Universal
end
end

/- BEGIN IntegralLinearExtension.lean -/
section

/-! # Extension of an integral comparison through its actual standard bases

This construction is valid over every commutative coefficient ring. It uses
finite-support coordinate sums, and its inverse is the extension of the
integral inverse; no flatness or field hypothesis is involved.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
variable {I J K M N M' N' : Type*} [CommRing K]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']

def integralLinearExtension (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (n : N →ₛₗ[Int.castRingHom K] N') (f : M →ₗ[ℤ] N) : M' →ₗ[K] N' :=
  b'.constr K (fun i => n (f (b i)))

@[simp] theorem integralLinearExtension_basis
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (n : N →ₛₗ[Int.castRingHom K] N') (f : M →ₗ[ℤ] N) (i : I) :
    integralLinearExtension b b' n f (b' i) = n (f (b i)) :=
  Module.Basis.constr_basis _ _ _ _

theorem integralLinearExtension_commutes
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (m : M →ₛₗ[Int.castRingHom K] M') (n : N →ₛₗ[Int.castRingHom K] N')
    (hm : ∀ i, m (b i) = b' i) (f : M →ₗ[ℤ] N) (x : M) :
    integralLinearExtension b b' n f (m x) = n (f x) := by
  have he : (integralLinearExtension b b' n f).comp m = n.comp f := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, hm, integralLinearExtension_basis]
  exact DFunLike.congr_fun he x

def integralEquivExtension
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (c : Module.Basis J ℤ N) (c' : Module.Basis J K N')
    (m : M →ₛₗ[Int.castRingHom K] M') (n : N →ₛₗ[Int.castRingHom K] N')
    (hm : ∀ i, m (b i) = b' i) (hn : ∀ j, n (c j) = c' j)
    (e : M ≃ₗ[ℤ] N) : M' ≃ₗ[K] N' := by
  let f := integralLinearExtension b b' n e.toLinearMap
  let g := integralLinearExtension c c' m e.symm.toLinearMap
  have hgf : g.comp f = LinearMap.id := by
    apply b'.ext
    intro i
    change g (f (b' i)) = b' i
    rw [integralLinearExtension_basis]
    rw [integralLinearExtension_commutes c c' n m hn]
    change m (e.symm (e (b i))) = b' i
    rw [LinearEquiv.symm_apply_apply]
    exact hm i
  have hfg : f.comp g = LinearMap.id := by
    apply c'.ext
    intro j
    change f (g (c' j)) = c' j
    rw [integralLinearExtension_basis]
    rw [integralLinearExtension_commutes b b' m n hm]
    change n (e (e.symm (c j))) = c' j
    rw [LinearEquiv.apply_symm_apply]
    exact hn j
  exact { f with
    invFun := g
    left_inv := fun x => DFunLike.congr_fun hgf x
    right_inv := fun x => DFunLike.congr_fun hfg x }

@[simp] theorem integralEquivExtension_apply
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (c : Module.Basis J ℤ N) (c' : Module.Basis J K N')
    (m : M →ₛₗ[Int.castRingHom K] M') (n : N →ₛₗ[Int.castRingHom K] N')
    (hm : ∀ i, m (b i) = b' i) (hn : ∀ j, n (c j) = c' j)
    (e : M ≃ₗ[ℤ] N) (x : M') :
    integralEquivExtension b b' c c' m n hm hn e x =
      integralLinearExtension b b' n e.toLinearMap x := rfl

/-- Every commuting integral operator extends to the corresponding actual
operator after coefficient change. -/
theorem integralLinearExtension_intertwines
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (m : M →ₛₗ[Int.castRingHom K] M') (n : N →ₛₗ[Int.castRingHom K] N')
    (hm : ∀ i, m (b i) = b' i) (f : M →ₗ[ℤ] N)
    (a : M →ₗ[ℤ] M) (a' : M' →ₗ[K] M')
    (z : N →ₗ[ℤ] N) (z' : N' →ₗ[K] N')
    (ha : ∀ x, a' (m x) = m (a x))
    (hz : ∀ y, z' (n y) = n (z y))
    (hf : f.comp a = z.comp f) :
    (integralLinearExtension b b' n f).comp a' =
      z'.comp (integralLinearExtension b b' n f) := by
  apply b'.ext
  intro i
  change integralLinearExtension b b' n f (a' (b' i)) =
    z' (integralLinearExtension b b' n f (b' i))
  rw [← hm i, ha, integralLinearExtension_commutes b b' m n hm,
    integralLinearExtension_commutes b b' m n hm, hz]
  exact congrArg n (DFunLike.congr_fun hf (b i))

end FourPapers.Universal

end
end

/- BEGIN BarycentricSection.lean -/
section


/-! # The inverse-limit identification for the conventional barycentric quotient -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def barycentricPresentationEquiv :
    BarycentricRing (P := P) K ≃ₐ[K]
      MonomialQuotient (K := K) (BarycentricAllowed (P := P)) :=
  Ideal.quotientEquivAlgOfEq K (barycentricIdeal_eq_forbiddenIdeal K)

def barycentricMonomialEquiv :
    BarycentricRing (P := P) K ≃ₗ[K] (StandardFaceIndex P →₀ K) :=
  (barycentricPresentationEquiv K).toLinearEquiv.trans
    (standardMonomialEquiv BarycentricAllowed barycentricAllowed_divisorClosed)

@[simp] theorem barycentricMonomialEquiv_mk (f : FacePolynomial (P := P) K) :
    barycentricMonomialEquiv K (Ideal.Quotient.mk (barycentricIdeal K) f) =
      standardCoefficients BarycentricAllowed f := by
  rfl

/-- Actual face restriction sends precisely the generators below the chosen
face to their Boolean-interval generators and kills all others. -/
def barycentricRingEvaluation (p : P) :
    BarycentricRing (P := P) K →ₐ[K] BarycentricStalk K p :=
  (monomialRestriction (booleanFaceInclusion hs p) BarycentricAllowed IsChainExponent
    barycentricAllowed_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha)).comp
      (barycentricPresentationEquiv K).toAlgHom

theorem barycentricRingEvaluation_coefficient (p : P) (x : BarycentricRing (P := P) K)
    (a : StandardFaceIndex P) (ha : standardCarrier a ≤ p) :
    (booleanChainBasis (V := FaceVertex p) (K := K)).repr
      (barycentricRingEvaluation K hs p x) ((standardInsideEquiv hs p).symm ⟨a, ha⟩) =
      barycentricMonomialEquiv K x a := by
  change (standardMonomialEquiv IsChainExponent isChainExponent_divisorClosed)
      (monomialRestriction (booleanFaceInclusion hs p) BarycentricAllowed IsChainExponent
        barycentricAllowed_divisorClosed isChainExponent_divisorClosed
        (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha)
        (barycentricPresentationEquiv K x))
      ((standardInsideEquiv hs p).symm ⟨a, ha⟩) = _
  rw [monomialRestriction_coefficient]
  have he := (standardInsideEquiv hs p).apply_symm_apply ⟨a, ha⟩
  have hidx := congrArg (fun z : StandardInside p => z.val) he
  exact congrArg (fun b => barycentricMonomialEquiv K x b) hidx

theorem barycentricRingEvaluation_coordinates (p : P) (x : BarycentricRing (P := P) K) :
    barycentricStandardCoordinates K hs p (barycentricRingEvaluation K hs p x) =
      (coefficientSection K standardCarrier (barycentricMonomialEquiv K x)).val p := by
  apply Subtype.ext
  ext a
  by_cases ha : standardCarrier a ≤ p
  · rw [barycentricStandardCoordinates_apply_of_inside K hs p _ a ha,
      coefficientSection_apply, if_pos ha]
    exact barycentricRingEvaluation_coefficient K hs p x a ha
  · rw [coefficientSection_apply, if_neg ha]
    exact (Finsupp.mem_supported' K _).mp
      (barycentricStandardCoordinates K hs p _).property a ha

/-- The equivalence is constructed from proven coefficient-gluing, and its
component formula below identifies it with the original face restrictions. -/
def barycentricRingSectionEquiv :
    BarycentricRing (P := P) K ≃ₗ[K] (barycentricDiagram (P := P) K).sections :=
  (barycentricMonomialEquiv K).trans (barycentricSectionCoordinates K hs).symm

@[simp] theorem barycentricRingSectionEquiv_apply (x : BarycentricRing (P := P) K) (p : P) :
    (barycentricRingSectionEquiv K hs x).val p = barycentricRingEvaluation K hs p x := by
  apply (barycentricStandardCoordinates K hs p).injective
  rw [barycentricRingEvaluation_coordinates]
  have h := (barycentricSectionCoordinates K hs).apply_symm_apply
    (barycentricMonomialEquiv K x)
  have hc := congrArg (coefficientSection K standardCarrier) h
  change (coefficientSection K standardCarrier)
      (barycentricSectionCoordinates K hs (barycentricRingSectionEquiv K hs x)) = _ at hc
  have hr := coefficientSection_assembly K standardCarrier
    ((barycentricCoefficientEquiv K hs).sectionEquiv (barycentricRingSectionEquiv K hs x))
  rw [show coefficientSection K standardCarrier
      (barycentricSectionCoordinates K hs (barycentricRingSectionEquiv K hs x)) =
      (barycentricCoefficientEquiv K hs).sectionEquiv (barycentricRingSectionEquiv K hs x) from hr] at hc
  exact congrArg (fun z : (coefficientDiagram K standardCarrier).sections => z.val p) hc

end FourPapers.Universal
end
end

/- BEGIN BasisWeightComparison.lean -/
section

/-! # Exact filtration statements from the canonical coefficient matrix

Weights are integers and the basis index set can be infinite. Finiteness is
used only for the support of each individual vector, as supplied by its basis
representation.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable {I K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

def basisWeightLevel (b : Module.Basis I K M) (w : I → ℤ) (n : ℤ) : Submodule K M where
  carrier := {x | ∀ i, n ≤ w i → b.repr x i = 0}
  zero_mem' := by intro i hi; simp
  add_mem' := by intro x y hx hy i hi; simp only [map_add, Finsupp.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by intro a x hx i hi; simp only [map_smul, Finsupp.smul_apply, hx i hi, smul_zero]

theorem basisWeightLevel_support (b : Module.Basis I K M) (w : I → ℤ)
    (n : ℤ) (x : M) (hx : x ∈ basisWeightLevel b w n) (i : I) (hi : i ∈ (b.repr x).support) :
    w i < n := by
  by_contra hn
  exact Finsupp.mem_support_iff.mp hi (hx i (le_of_not_gt hn))

def canonicalBasisEquiv (b : Module.Basis I K M) (c : Module.Basis I K N) : M ≃ₗ[K] N :=
  b.repr.trans c.repr.symm

@[simp] theorem canonicalBasisEquiv_repr (b : Module.Basis I K M)
    (c : Module.Basis I K N) (x : M) : c.repr (canonicalBasisEquiv b c x) = b.repr x := by
  exact c.repr.apply_symm_apply (b.repr x)

theorem basis_repr_linear_map (b : Module.Basis I K M) (c : Module.Basis I K N)
    (f : M →ₗ[K] N) (x : M) (j : I) :
    c.repr (f x) j = ∑ i ∈ (b.repr x).support, (b.repr x i) * (c.repr (f (b i)) j) := by
  conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

def HasWeightLeading (b : Module.Basis I K M) (c : Module.Basis I K N)
    (w : I → ℤ) (f : M →ₗ[K] N) : Prop :=
  ∀ i j, w i ≤ w j → c.repr (f (b i)) j = if i = j then 1 else 0

theorem weightLeading_coefficient_of_maximal (b : Module.Basis I K M)
    (c : Module.Basis I K N) (w : I → ℤ) (f : M →ₗ[K] N)
    (hf : HasWeightLeading b c w f) (x : M) (j : I)
    (hj : ∀ i ∈ (b.repr x).support, w i ≤ w j) :
    c.repr (f x) j = b.repr x j := by
  rw [basis_repr_linear_map, Finset.sum_eq_single j]
  · rw [hf j j le_rfl, if_pos rfl, mul_one]
  · intro i hi hij
    rw [hf i j (hj i hi), if_neg hij, mul_zero]
  · intro hj'
    rw [Finsupp.notMem_support_iff.mp hj', zero_mul]

theorem weightLeading_mem_iff (b : Module.Basis I K M) (c : Module.Basis I K N)
    (w : I → ℤ) (f : M →ₗ[K] N) (hf : HasWeightLeading b c w f)
    (n : ℤ) (x : M) : f x ∈ basisWeightLevel c w n ↔ x ∈ basisWeightLevel b w n := by
  constructor
  · intro hx j hj
    by_contra hn
    have hjmem : j ∈ (b.repr x).support := Finsupp.mem_support_iff.mpr hn
    have hs : (b.repr x).support.Nonempty := ⟨j, hjmem⟩
    have himage := hs.image w
    obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp (Finset.max'_mem _ himage)
    have himax : ∀ k ∈ (b.repr x).support, w k ≤ w i := by
      intro k hk
      rw [hir]
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    have hcoeff := weightLeading_coefficient_of_maximal b c w f hf x i himax
    rw [hx i (hj.trans (himax j hjmem))] at hcoeff
    exact Finsupp.mem_support_iff.mp hi hcoeff.symm
  · intro hx j hj
    rw [basis_repr_linear_map]
    apply Finset.sum_eq_zero
    intro i hi
    have hwi := basisWeightLevel_support b w n x hx i hi
    have hij : i ≠ j := by intro h; subst j; exact (not_le_of_gt hwi) hj
    rw [hf i j (hwi.le.trans hj), if_neg hij, mul_zero]

theorem weightLeading_error_lower (b : Module.Basis I K M) (c : Module.Basis I K N)
    (w : I → ℤ) (f : M →ₗ[K] N) (hf : HasWeightLeading b c w f)
    (n : ℤ) (x : M) (hx : x ∈ basisWeightLevel b w (n + 1)) :
    f x - canonicalBasisEquiv b c x ∈ basisWeightLevel c w n := by
  intro j hj
  rw [map_sub, Finsupp.sub_apply, canonicalBasisEquiv_repr, sub_eq_zero]
  apply weightLeading_coefficient_of_maximal b c w f hf x j
  intro i hi
  have hwi := basisWeightLevel_support b w (n + 1) x hx i hi
  omega

abbrev weightFiltrationGrade (F : ℤ → Submodule K M) (n : ℤ) :=
  (F (n + 1)) ⧸ (F n).comap (F (n + 1)).subtype

def weightFiltrationLevelEquiv (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e : M ≃ₗ[K] N) (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (n : ℤ) : F n ≃ₗ[K] G n where
  toFun x := ⟨e x.val, (he n x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (he n (e.symm y.val)).mp (by
    rw [LinearEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e.map_smul a x.val)

theorem weightFiltrationLevelEquiv_lower (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e : M ≃ₗ[K] N) (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (n : ℤ) :
    ((F n).comap (F (n + 1)).subtype).map
      (weightFiltrationLevelEquiv F G e he (n + 1)).toLinearMap =
        (G n).comap (G (n + 1)).subtype := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (he n x.val).mpr hx
  · intro hy
    refine ⟨(weightFiltrationLevelEquiv F G e he (n + 1)).symm y, ?_,
      (weightFiltrationLevelEquiv F G e he (n + 1)).apply_symm_apply y⟩
    change e.symm y.val ∈ F n
    exact (he n (e.symm y.val)).mp (by rw [LinearEquiv.apply_symm_apply]; exact hy)

def weightFiltrationGradeEquiv (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e : M ≃ₗ[K] N) (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (n : ℤ) :
    weightFiltrationGrade F n ≃ₗ[K] weightFiltrationGrade G n :=
  Submodule.Quotient.equiv _ _ (weightFiltrationLevelEquiv F G e he (n + 1))
    (weightFiltrationLevelEquiv_lower F G e he n)

theorem weightFiltrationGradeEquiv_eq_of_error_lower
    (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (e f : M ≃ₗ[K] N)
    (he : ∀ n x, e x ∈ G n ↔ x ∈ F n) (hf : ∀ n x, f x ∈ G n ↔ x ∈ F n)
    (n : ℤ) (herr : ∀ x ∈ F (n + 1), e x - f x ∈ G n) :
    weightFiltrationGradeEquiv F G e he n = weightFiltrationGradeEquiv F G f hf n := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective ((F n).comap (F (n + 1)).subtype) x
  change Submodule.Quotient.mk (weightFiltrationLevelEquiv F G e he (n + 1) y) =
    Submodule.Quotient.mk (weightFiltrationLevelEquiv F G f hf (n + 1) y)
  apply (Submodule.Quotient.eq _).mpr
  exact herr y.val y.property

end FourPapers.Universal

end
end

/- BEGIN StalkCoefficientChange.lean -/
section

/-! # Coefficient change on the actual two face diagrams -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {V W K L : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W] [CommRing K] [CommRing L]

def booleanCoefficientChange (h : K →+* L) :
    BooleanBarycentricRing V K →ₛₗ[h] BooleanBarycentricRing V L :=
  monomialCoefficientMap IsChainExponent isChainExponent_divisorClosed h

@[simp] theorem booleanCoefficientChange_basis (h : K →+* L)
    (a : BooleanChainExponent V) :
    booleanCoefficientChange h (booleanChainBasis (K := K) a) = booleanChainBasis (K := L) a :=
  monomialCoefficientMap_basis IsChainExponent isChainExponent_divisorClosed h a

theorem booleanCoefficientChange_mul (h : K →+* L)
    (x y : BooleanBarycentricRing V K) :
    booleanCoefficientChange h (x * y) = booleanCoefficientChange h x * booleanCoefficientChange h y :=
  (monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h).map_mul x y

@[simp] theorem booleanCoefficientChange_face (h : K →+* L) (F : BooleanFace V) :
    booleanCoefficientChange h (faceVariable (K := K) F) = faceVariable (K := L) F := by
  unfold faceVariable booleanCoefficientChange
  rw [monomialCoefficientMap_mk, MvPolynomial.map_X]

theorem booleanCoefficientChange_parameter (h : K →+* L) (i : ℕ) :
    booleanCoefficientChange h (booleanRankParameter (V := V) (K := K) i) =
      booleanRankParameter (V := V) (K := L) i := by
  unfold booleanRankParameter
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hi : F.val.card = i
  · simp only [if_pos hi, booleanCoefficientChange_face]
  · simp only [if_neg hi, map_zero]

theorem booleanCoefficientChange_restriction (h : K →+* L) (e : V ↪ W)
    (x : BooleanBarycentricRing W K) :
    booleanCoefficientChange h (booleanRestriction e x) =
      booleanRestriction e (booleanCoefficientChange h x) :=
  monomialCoefficientMap_restriction h (booleanFaceEmbedding e) IsChainExponent IsChainExponent
    isChainExponent_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => isChainExponent_map_booleanFaceEmbedding e ha) x

def polynomialCoefficientChange (h : K →+* L) :
    MvPolynomial V K →ₛₗ[h] MvPolynomial V L where
  toFun := MvPolynomial.map h
  map_add' := (MvPolynomial.map h).map_add
  map_smul' c f := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

@[simp] theorem polynomialCoefficientChange_eq (h : K →+* L) (f : MvPolynomial V K) :
    polynomialCoefficientChange h f = MvPolynomial.map h f := rfl

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (hs : IsSimplicialPoset P)

theorem booleanCoefficientChange_standardBasis (h : K →+* L) (p : P) (a : StandardInside p) :
    booleanCoefficientChange h (barycentricStalkStandardBasis K hs p a) =
      barycentricStalkStandardBasis L hs p a := by
  simp only [barycentricStalkStandardBasis, Module.Basis.reindex_apply]
  exact booleanCoefficientChange_basis h _

theorem polynomialCoefficientChange_standardBasis (h : K →+* L) (p : P) (a : StandardInside p) :
    polynomialCoefficientChange h (polynomialStandardBasis (K := K) hs p a) =
      polynomialStandardBasis (K := L) hs p a := by
  rw [polynomialStandardBasis_apply, polynomialStandardBasis_apply,
    polynomialCoefficientChange_eq, MvPolynomial.map_monomial, map_one]

theorem polynomialCoefficientChange_coordinates (h : K →+* L) (p : P)
    (x : PolynomialStalk K p) (a : StandardFaceIndex P) :
    (polynomialStandardCoordinates L hs p (polynomialCoefficientChange h x)).val a =
      h ((polynomialStandardCoordinates K hs p x).val a) := by
  by_cases ha : standardCarrier a ≤ p
  · have hL := polynomialStandardCoordinates_apply_of_inside L hs p
      (polynomialCoefficientChange h x) ⟨a, ha⟩
    have hK := polynomialStandardCoordinates_apply_of_inside K hs p x ⟨a, ha⟩
    rw [hL, hK, polynomialCoefficientChange_eq, MvPolynomial.coeff_map]
  · have hL := (Finsupp.mem_supported' L _).mp
      (polynomialStandardCoordinates L hs p (polynomialCoefficientChange h x)).property a ha
    have hK := (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p x).property a ha
    rw [hL, hK, h.map_zero]

theorem polynomialCoefficientChange_restriction (h : K →+* L) {p q : P} (hqp : q ≤ p)
    (x : PolynomialStalk K p) :
    polynomialCoefficientChange h (polynomialRestriction K hqp x) =
      polynomialRestriction L hqp (polynomialCoefficientChange h x) := by
  have he : (MvPolynomial.map h).comp (polynomialRestriction K hqp).toRingHom =
      (polynomialRestriction L hqp).toRingHom.comp (MvPolynomial.map h) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.map h (polynomialRestriction K hqp (C c)) =
        polynomialRestriction L hqp (MvPolynomial.map h (C c))
      simp only [polynomialRestriction_C, MvPolynomial.map_C]
    · intro a
      change MvPolynomial.map h (polynomialRestriction K hqp (X a)) =
        polynomialRestriction L hqp (MvPolynomial.map h (X a))
      simp only [MvPolynomial.map_X, polynomialRestriction_X]
      split_ifs <;> simp only [MvPolynomial.map_X, map_zero]
  simpa only [polynomialCoefficientChange_eq, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using DFunLike.congr_fun he x

end Poset
end FourPapers.Universal

end
end

/- BEGIN IntegralCoherentComparison.lean -/
section

/-! # A single integral coherent comparison and all its coefficient changes

The maps over an arbitrary ring are defined by extending the actual integral
matrix in the standard bases. Consequently their scalar naturality is a
theorem about the usual coefficient maps, not an additional hypothesis.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def integralStalkComparison (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) :
    BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p :=
  integralEquivExtension
    (barycentricStalkStandardBasis ℤ hs p) (barycentricStalkStandardBasis K hs p)
    (polynomialStandardBasis (K := ℤ) hs p) (polynomialStandardBasis (K := K) hs p)
    (booleanCoefficientChange (Int.castRingHom K)) (polynomialCoefficientChange (Int.castRingHom K))
    (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p)
    (polynomialCoefficientChange_standardBasis hs (Int.castRingHom K) p) e

theorem integralStalkComparison_commutes (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk ℤ p) :
    integralStalkComparison K hs p e (booleanCoefficientChange (Int.castRingHom K) x) =
      polynomialCoefficientChange (Int.castRingHom K) (e x) := by
  rw [integralStalkComparison, integralEquivExtension_apply]
  exact integralLinearExtension_commutes
    (barycentricStalkStandardBasis ℤ hs p) (barycentricStalkStandardBasis K hs p)
    (booleanCoefficientChange (Int.castRingHom K)) (polynomialCoefficientChange (Int.castRingHom K))
    (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p) e.toLinearMap x

@[simp] theorem integralStalkComparison_basis (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (a : StandardInside p) :
    integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a) =
      polynomialCoefficientChange (Int.castRingHom K) (e (barycentricStalkStandardBasis ℤ hs p a)) := by
  rw [← booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a]
  exact integralStalkComparison_commutes K hs p e _

def integralCoherentComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ)) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component p := integralStalkComparison K hs p (e.component p)
  naturality p q hqp x := by
    have hf : (polynomialRestriction K hqp).toLinearMap.comp
        (integralStalkComparison K hs p (e.component p)).toLinearMap =
        (integralStalkComparison K hs q (e.component q)).toLinearMap.comp
          (booleanRestriction (K := K) (faceVertexInclusion hqp)).toLinearMap := by
      apply (barycentricStalkStandardBasis K hs p).ext
      intro a
      change polynomialRestriction K hqp
        (integralStalkComparison K hs p (e.component p) (barycentricStalkStandardBasis K hs p a)) =
        integralStalkComparison K hs q (e.component q)
          (booleanRestriction (faceVertexInclusion hqp) (barycentricStalkStandardBasis K hs p a))
      rw [integralStalkComparison_basis,
        ← polynomialCoefficientChange_restriction (Int.castRingHom K) hqp]
      have hn := e.naturality p q hqp (barycentricStalkStandardBasis ℤ hs p a)
      change polynomialRestriction ℤ hqp (e.component p (barycentricStalkStandardBasis ℤ hs p a)) =
        e.component q (booleanRestriction (faceVertexInclusion hqp)
          (barycentricStalkStandardBasis ℤ hs p a)) at hn
      rw [hn, ← integralStalkComparison_commutes,
        booleanCoefficientChange_restriction, booleanCoefficientChange_standardBasis]
    exact DFunLike.congr_fun hf x

theorem integralStalkComparison_leading (d : ℕ) (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p)
    (he : HasStandardLeading ℤ hs d p e.toLinearMap) :
    HasStandardLeading K hs d p (integralStalkComparison K hs p e).toLinearMap := by
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    (integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a))).val b = _
  rw [integralStalkComparison_basis, polynomialCoefficientChange_coordinates]
  have hh := he a b hab
  change (polynomialStandardCoordinates ℤ hs p
    (e (barycentricStalkStandardBasis ℤ hs p a))).val b = _ at hh
  rw [hh]
  split_ifs <;> simp

theorem integralStalkComparison_degree (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p)
    (he : HasStandardDegree ℤ hs p e.toLinearMap) :
    HasStandardDegree K hs p (integralStalkComparison K hs p e).toLinearMap := by
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    (integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a))).val b = 0
  rw [integralStalkComparison_basis, polynomialCoefficientChange_coordinates]
  have hh := he a b hab
  change (polynomialStandardCoordinates ℤ hs p
    (e (barycentricStalkStandardBasis ℤ hs p a))).val b = 0 at hh
  rw [hh, map_zero]

theorem integralStalkComparison_parameters (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p)
    (he : ∀ i : ℕ, ∀ x : BarycentricStalk ℤ p,
      e (booleanRankParameter (i + 1) * x) = polynomialParameter ℤ p (i + 1) * e x)
    (i : ℕ) (x : BarycentricStalk K p) :
    integralStalkComparison K hs p e (booleanRankParameter (i + 1) * x) =
      polynomialParameter K p (i + 1) * integralStalkComparison K hs p e x := by
  have hf : (integralStalkComparison K hs p e).toLinearMap.comp
      (LinearMap.mulLeft K (booleanRankParameter (V := FaceVertex p) (K := K) (i + 1))) =
      (LinearMap.mulLeft K (polynomialParameter K p (i + 1))).comp
        (integralStalkComparison K hs p e).toLinearMap := by
    apply (barycentricStalkStandardBasis K hs p).ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply]
    rw [← booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a,
      ← booleanCoefficientChange_parameter (Int.castRingHom K) (i + 1),
      ← booleanCoefficientChange_mul, integralStalkComparison_commutes,
      integralStalkComparison_commutes, he]
    simp only [polynomialCoefficientChange_eq, map_mul, polynomialParameter, MvPolynomial.map_esymm]
  exact DFunLike.congr_fun hf x

variable {L : Type*} [CommRing L]

theorem integralStalkComparison_baseChange (h : K →+* L) (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk K p) :
    polynomialCoefficientChange h (integralStalkComparison K hs p e x) =
      integralStalkComparison L hs p e (booleanCoefficientChange h x) := by
  have hpoly (y : PolynomialStalk ℤ p) :
      polynomialCoefficientChange h (polynomialCoefficientChange (Int.castRingHom K) y) =
        polynomialCoefficientChange (Int.castRingHom L) y := by
    simp only [polynomialCoefficientChange_eq, MvPolynomial.map_map]
    rw [show h.comp (Int.castRingHom K) = Int.castRingHom L from Subsingleton.elim _ _]
  exact basis_constr_baseChange h
    (barycentricStalkStandardBasis K hs p) (barycentricStalkStandardBasis L hs p)
    (booleanCoefficientChange h) (polynomialCoefficientChange h)
    (fun a => polynomialCoefficientChange (Int.castRingHom K)
      (e (barycentricStalkStandardBasis ℤ hs p a)))
    (fun a => polynomialCoefficientChange (Int.castRingHom L)
      (e (barycentricStalkStandardBasis ℤ hs p a)))
    (booleanCoefficientChange_standardBasis hs h p) (fun a => hpoly _) x

/-- Existence of one integral coherent system whose actual coefficient
extensions retain degree, every parameter action, and canonical leading terms. -/
theorem exists_integral_graded_coherent_comparison (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ),
      ∀ p : P,
        HasStandardLeading K hs d p ((integralCoherentComparison K hs e).component p).toLinearMap ∧
        (∀ i : ℕ, ∀ x : BarycentricStalk K p,
          (integralCoherentComparison K hs e).component p (booleanRankParameter (i + 1) * x) =
            polynomialParameter K p (i + 1) * (integralCoherentComparison K hs e).component p x) ∧
        HasStandardDegree K hs p ((integralCoherentComparison K hs e).component p).toLinearMap := by
  obtain ⟨e, he⟩ := exists_graded_coherent_parameter_comparison ℤ hs d hrank
  refine ⟨e, fun p => ?_⟩
  exact ⟨integralStalkComparison_leading K hs d p (e.component p) (he p).1,
    integralStalkComparison_parameters K hs p (e.component p) (he p).2.1,
    integralStalkComparison_degree K hs p (e.component p) (he p).2.2⟩

end FourPapers.Universal

end
end

/- BEGIN RankFaceSums.lean -/
section

/-! # Exact enumeration of rank-selected faces in a Boolean interval -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (hs : IsSimplicialPoset P)

theorem card_stalkVertexSet {p q : P} (hqp : q ≤ p) :
    (stalkVertexSet p q).card = faceRank q := by
  have h := Finset.card_image_of_injective (stalkVertexSet p q) Subtype.val_injective
  rw [image_stalkVertexSet hqp] at h
  exact h.symm

def rankFacesBelow (p : P) (i : ℕ) : Finset P :=
  Finset.univ.filter (fun q => q ≤ p ∧ faceRank q = i)

theorem rankFacesBelow_image (p : P) (i : ℕ) (hi : 0 < i) :
    rankFacesBelow p i =
      (Finset.univ.filter (fun F : BooleanFace (FaceVertex p) => F.val.card = i)).image
        (fun F => (booleanFaceInclusion hs p F).val) := by
  ext q
  simp only [rankFacesBelow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hqp, hqi⟩
    let F : BooleanFace (FaceVertex p) := ⟨stalkVertexSet p q, Finset.card_pos.mp (by
      rw [card_stalkVertexSet hqp, hqi]
      exact hi)⟩
    refine ⟨F, ?_, ?_⟩
    · exact (card_stalkVertexSet hqp).trans hqi
    · have h : (⟨(booleanFaceInclusion hs p F).val, booleanFaceInclusion_le hs p F⟩ : Set.Iic p) =
          ⟨q, hqp⟩ := by
        apply (faceBooleanInterval hs p).injective
        change stalkVertexSet p (booleanFaceInclusion hs p F).val = stalkVertexSet p q
        rw [stalkVertexSet_booleanFaceInclusion]
      exact congrArg Subtype.val h
  · rintro ⟨F, hFi, rfl⟩
    exact ⟨booleanFaceInclusion_le hs p F, (faceRank_booleanFaceInclusion hs p F).trans hFi⟩

theorem sum_rank_faces_below {M : Type*} [AddCommMonoid M] (p : P) (i : ℕ)
    (hi : 0 < i) (g : P → M) (hg : ∀ q, ¬ q ≤ p → g q = 0) :
    (∑ q ∈ Finset.univ.filter (fun q => faceRank q = i), g q) =
      ∑ F : BooleanFace (FaceVertex p), if F.val.card = i then g (booleanFaceInclusion hs p F).val else 0 := by
  have hcut : (∑ q ∈ Finset.univ.filter (fun q => faceRank q = i), g q) =
      ∑ q ∈ rankFacesBelow p i, g q := by
    simp only [rankFacesBelow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqp : q ≤ p
    · simp only [hqp, true_and]
    · simp only [hqp, false_and, if_false, hg q hqp, ite_self]
  rw [hcut, rankFacesBelow_image hs p i hi, Finset.sum_image]
  · exact Finset.sum_filter _ _
  · intro F hF G hG he
    exact (booleanFaceInclusion hs p).injective (Subtype.ext he)

end FourPapers.Universal

end
end

/- BEGIN OriginalParameterEvaluation.lean -/
section

/-! # The original rank sums restrict to the stated local parameters -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem barycentricRingEvaluation_included (p : P) (F : BooleanFace (FaceVertex p)) :
    barycentricRingEvaluation K hs p (barycentricGenerator K (booleanFaceInclusion hs p F).val) =
      faceVariable F := by
  change Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
    (MvPolynomial.killCompl (booleanFaceInclusion hs p).injective
      (faceSymbol K (booleanFaceInclusion hs p F).val)) = _
  rw [faceSymbol_nonzero]
  have h := MvPolynomial.killCompl_rename_app (R := K) (booleanFaceInclusion hs p).injective (X F)
  simp only [MvPolynomial.rename_X] at h
  rw [h]
  rfl

theorem barycentricRingEvaluation_outside (p q : P) (hqp : ¬ q ≤ p) :
    barycentricRingEvaluation K hs p (barycentricGenerator K q) = 0 := by
  have hq : q ≠ ⊥ := by intro h; subst q; exact hqp bot_le
  have hn : (⟨q, hq⟩ : NonzeroFace P) ∉ Set.range (booleanFaceInclusion hs p) := by
    rintro ⟨F, hF⟩
    have h := booleanFaceInclusion_le hs p F
    rw [hF] at h
    exact hqp h
  change Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
    (MvPolynomial.killCompl (booleanFaceInclusion hs p).injective (faceSymbol K q)) = 0
  rw [faceSymbol, dif_neg hq]
  simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hn, map_zero]

theorem barycentricRingEvaluation_parameter (p : P) (i : ℕ) (hi : 0 < i) :
    barycentricRingEvaluation K hs p (barycentricRankParameter K i) =
      booleanRankParameter (V := FaceVertex p) (K := K) i := by
  rw [barycentricRankParameter, map_sum]
  rw [sum_rank_faces_below hs p i hi
    (fun q => barycentricRingEvaluation K hs p (barycentricGenerator K q))
    (barycentricRingEvaluation_outside K hs p)]
  simp only [barycentricRingEvaluation_included, booleanRankParameter]

theorem sum_booleanFaces_card_product {V : Type*} [Fintype V] [DecidableEq V]
    (i : ℕ) (hi : 0 < i) :
    (∑ F : BooleanFace V, if F.val.card = i then (∏ v ∈ F.val, (X v : MvPolynomial V K)) else 0) =
      esymm V K i := by
  rw [← Finset.sum_filter, esymm]
  apply Finset.sum_bij (fun F _ => F.val)
  · intro F hF
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hF).2⟩
  · intro F hF G hG h
    exact Subtype.ext h
  · intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    have hn : s.Nonempty := Finset.card_pos.mp (by rw [hc]; exact hi)
    exact ⟨⟨s, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩
  · intro F hF
    rfl

theorem faceRingEvaluation_parameter (p : P) (i : ℕ) (hi : 0 < i) :
    faceRingEvaluation K hs p (faceRankParameter K hs i) = polynomialParameter K p i := by
  rw [faceRankParameter, map_sum]
  simp only [faceRingEvaluation_generator]
  rw [sum_rank_faces_below hs p i hi (faceValue K p) (by
    intro q hq
    simp [faceValue, hq])]
  have he (F : BooleanFace (FaceVertex p)) :
      faceValue K p (booleanFaceInclusion hs p F).val =
        ∏ v ∈ F.val, (X v : PolynomialStalk K p) := by
    rw [faceValue, if_pos (booleanFaceInclusion_le hs p F), faceProduct,
      stalkVertexSet_booleanFaceInclusion]
  simp only [he]
  exact sum_booleanFaces_card_product K i hi

end FourPapers.Universal

end
end

/- BEGIN OriginalComparison.lean -/
section

/-! # The comparison on the original quotient rings and relative kernels -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def originalComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) :
    BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs :=
  ((barycentricRingSectionEquiv K hs).trans e.sectionEquiv).trans (faceRingSectionEquiv K hs).symm

theorem originalComparison_evaluation
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (x : BarycentricRing (P := P) K) (p : P) :
    faceRingEvaluation K hs p (originalComparison K hs e x) =
      e.component p (barycentricRingEvaluation K hs p x) := by
  have h : faceRingSectionEquiv K hs (originalComparison K hs e x) =
      e.sectionEquiv (barycentricRingSectionEquiv K hs x) := by
    simp only [originalComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have h' := congrArg (fun s : (polynomialDiagram (P := P) K).sections => s.val p) h
  simpa only [faceRingSectionEquiv_apply, faceRingSection_apply, CoherentEquiv.sectionEquiv_apply,
    barycentricRingSectionEquiv_apply] using h'

def originalParameterComparison (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p : P, ∀ i : ℕ, ∀ x : BarycentricStalk K p,
      e.component p (booleanRankParameter (i + 1) * x) =
        polynomialParameter K p (i + 1) * e.component p x) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) where
  toLinearEquiv := originalComparison K hs e
  map_X_mul i x := by
    simp only [barycentricParameterAction, faceParameterAction, MvPolynomial.aeval_X]
    apply (faceRingSectionEquiv K hs).injective
    apply Subtype.ext
    funext p
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      originalComparison_evaluation, map_mul,
      barycentricRingEvaluation_parameter K hs p (i.val + 1) (Nat.succ_pos _),
      faceRingEvaluation_parameter K hs p (i.val + 1) (Nat.succ_pos _)]
    exact he p i.val (barycentricRingEvaluation K hs p x)

def barycentricRelative (Q : Set P) : Submodule K (BarycentricRing (P := P) K) where
  carrier := {x | ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0}
  zero_mem' := by intro p hp; exact map_zero _
  add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
  smul_mem' := by intro c x hx p hp; rw [map_smul, hx p hp, smul_zero]

def faceRelative (Q : Set P) : Submodule K (FaceRing K hs) where
  carrier := {x | ∀ p ∈ Q, faceRingEvaluation K hs p x = 0}
  zero_mem' := by intro p hp; exact map_zero _
  add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
  smul_mem' := by intro c x hx p hp; rw [map_smul, hx p hp, smul_zero]

/-- The relative comparison is the restriction of the same global map to the
actual kernel of all face restrictions in the specified set. -/
def originalRelativeComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) (Q : Set P) :
    barycentricRelative K hs Q ≃ₗ[K] faceRelative K hs Q where
  toFun x := ⟨originalComparison K hs e x.val, by
    intro p hp
    rw [originalComparison_evaluation, x.property p hp, LinearEquiv.map_zero]⟩
  invFun y := ⟨(originalComparison K hs e).symm y.val, by
    intro p hp
    apply (e.component p).injective
    rw [LinearEquiv.map_zero, ← originalComparison_evaluation, LinearEquiv.apply_symm_apply]
    exact y.property p hp⟩
  left_inv x := Subtype.ext ((originalComparison K hs e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((originalComparison K hs e).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((originalComparison K hs e).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((originalComparison K hs e).map_smul c x.val)

def universalIntegralComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ) :=
  (exists_graded_coherent_parameter_comparison ℤ hs d hrank).choose

theorem universalIntegralComparison_spec (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P) :
    HasStandardLeading ℤ hs d p ((universalIntegralComparison hs d hrank).component p).toLinearMap ∧
      (∀ i : ℕ, ∀ x : BarycentricStalk ℤ p,
        (universalIntegralComparison hs d hrank).component p (booleanRankParameter (i + 1) * x) =
          polynomialParameter ℤ p (i + 1) * (universalIntegralComparison hs d hrank).component p x) ∧
      HasStandardDegree ℤ hs p ((universalIntegralComparison hs d hrank).component p).toLinearMap :=
  (exists_graded_coherent_parameter_comparison ℤ hs d hrank).choose_spec p

def universalCoherentComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) :=
  integralCoherentComparison K hs (universalIntegralComparison hs d hrank)

def universalOriginalParameterComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) :=
  originalParameterComparison K hs d (universalCoherentComparison K hs d hrank) (fun p =>
    integralStalkComparison_parameters K hs p
      ((universalIntegralComparison hs d hrank).component p)
      (universalIntegralComparison_spec hs d hrank p).2.1)

theorem universalCoherentComparison_spec (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P) :
    HasStandardLeading K hs d p ((universalCoherentComparison K hs d hrank).component p).toLinearMap ∧
      (∀ i : ℕ, ∀ x : BarycentricStalk K p,
        (universalCoherentComparison K hs d hrank).component p (booleanRankParameter (i + 1) * x) =
          polynomialParameter K p (i + 1) * (universalCoherentComparison K hs d hrank).component p x) ∧
      HasStandardDegree K hs p ((universalCoherentComparison K hs d hrank).component p).toLinearMap := by
  let e := universalIntegralComparison hs d hrank
  have he := universalIntegralComparison_spec hs d hrank p
  exact ⟨integralStalkComparison_leading K hs d p (e.component p) he.1,
    integralStalkComparison_parameters K hs p (e.component p) he.2.1,
    integralStalkComparison_degree K hs p (e.component p) he.2.2⟩

theorem universalCoherentComparison_baseChange {L : Type*} [CommRing L]
    (h : K →+* L) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P)
    (x : BarycentricStalk K p) :
    polynomialCoefficientChange h ((universalCoherentComparison K hs d hrank).component p x) =
      (universalCoherentComparison L hs d hrank).component p (booleanCoefficientChange h x) :=
  integralStalkComparison_baseChange K hs h p
    ((universalIntegralComparison hs d hrank).component p) x

end FourPapers.Universal

end
end

/- BEGIN OriginalRelativeParameters.lean -/
section

/-! # Full parameter linearity on the original relative modules -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def barycentricRelativeParameters (d : ℕ) (Q : Set P) :
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    Submodule (MvPolynomial (Fin d) K) (BarycentricRing (P := P) K) := by
  letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
  exact {
    carrier := {x | ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0}
    zero_mem' := by intro p hp; exact map_zero _
    add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
    smul_mem' := by
      intro a x hx p hp
      change barycentricRingEvaluation K hs p (barycentricParameterAction K d a * x) = 0
      rw [map_mul, hx p hp, mul_zero] }

def faceRelativeParameters (d : ℕ) (Q : Set P) :
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    Submodule (MvPolynomial (Fin d) K) (FaceRing K hs) := by
  letI := (faceParameterAction K hs d).toRingHom.toAlgebra
  exact {
    carrier := {x | ∀ p ∈ Q, faceRingEvaluation K hs p x = 0}
    zero_mem' := by intro p hp; exact map_zero _
    add_mem' := by intro x y hx hy p hp; rw [map_add, hx p hp, hy p hp, add_zero]
    smul_mem' := by
      intro a x hx p hp
      change faceRingEvaluation K hs p (faceParameterAction K hs d a * x) = 0
      rw [map_mul, hx p hp, mul_zero] }

def originalRelativeParameterComparison (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p : P, ∀ i : ℕ, ∀ x : BarycentricStalk K p,
      e.component p (booleanRankParameter (i + 1) * x) =
        polynomialParameter K p (i + 1) * e.component p x) (Q : Set P) :
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    barycentricRelativeParameters K hs d Q ≃ₗ[MvPolynomial (Fin d) K] faceRelativeParameters K hs d Q := by
  letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
  letI := (faceParameterAction K hs d).toRingHom.toAlgebra
  exact {
    (originalRelativeComparison K hs e Q).toAddEquiv with
    map_smul' := fun a x => Subtype.ext
      ((originalParameterComparison K hs d e he).map_parameter_mul a x.val) }

def universalOriginalRelativeParameterComparison (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (Q : Set P) :
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    barycentricRelativeParameters K hs d Q ≃ₗ[MvPolynomial (Fin d) K] faceRelativeParameters K hs d Q :=
  originalRelativeParameterComparison K hs d (universalCoherentComparison K hs d hrank)
    (fun p => (universalCoherentComparison_spec K hs d hrank p).2.1) Q

end FourPapers.Universal

end
end

/- BEGIN OriginalLeadingDegree.lean -/
section

/-! # The actual global standard-monomial coefficients of the comparison -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def barycentricGlobalStandardBasis :
    Module.Basis (StandardFaceIndex P) K (BarycentricRing (P := P) K) :=
  Module.Basis.ofRepr (barycentricMonomialEquiv K)

@[simp] theorem barycentricGlobalStandardBasis_coordinates (a : StandardFaceIndex P) :
    barycentricMonomialEquiv K (barycentricGlobalStandardBasis K a) = Finsupp.single a 1 := by
  exact (barycentricMonomialEquiv K).apply_symm_apply (Finsupp.single a 1)

theorem polynomialSectionCoordinates_atCarrier
    (x : (polynomialDiagram (P := P) K).sections) (a : StandardFaceIndex P) :
    polynomialSectionCoordinates K hs x a =
      (polynomialStandardCoordinates K hs (standardCarrier a) (x.val (standardCarrier a))).val a := rfl

theorem standardFaceBasis_repr_atCarrier (x : FaceRing K hs) (a : StandardFaceIndex P) :
    (standardFaceBasis K hs).repr x a =
      (polynomialStandardCoordinates K hs (standardCarrier a)
        (faceRingEvaluation K hs (standardCarrier a) x)).val a := by
  have h : (standardFaceBasis K hs).repr x =
      polynomialSectionCoordinates K hs (faceRingSection K hs x) := by
    rw [← faceRingSectionEquiv_apply]
    simp only [faceRingSectionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [h, polynomialSectionCoordinates_atCarrier]
  rfl

theorem barycentricRingEvaluation_globalBasis (p : P) (a : StandardFaceIndex P) :
    barycentricRingEvaluation K hs p (barycentricGlobalStandardBasis K a) =
      if h : standardCarrier a ≤ p then barycentricStalkStandardBasis K hs p ⟨a, h⟩ else 0 := by
  apply (barycentricStandardCoordinates K hs p).injective
  rw [barycentricRingEvaluation_coordinates, barycentricGlobalStandardBasis_coordinates]
  by_cases ha : standardCarrier a ≤ p
  · rw [dif_pos ha, barycentricStandardCoordinates_basis]
    apply Subtype.ext
    ext b
    rw [coefficientSection_apply, coefficientUnit_apply]
    by_cases hab : a = b
    · subst b
      simp only [if_pos ha, Finsupp.single_eq_same, if_pos rfl, ite_true]
    · simp only [Finsupp.single_apply, if_neg hab, if_neg (Ne.symm hab), ite_self]
  · rw [dif_neg ha, LinearEquiv.map_zero]
    apply Subtype.ext
    ext b
    rw [coefficientSection_apply]
    by_cases hab : a = b
    · subst b
      simp only [if_neg ha]
      rfl
    · simp only [Finsupp.single_apply, if_neg hab, if_neg (Ne.symm hab), ite_self]
      rfl

theorem originalComparison_leading (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p, HasStandardLeading K hs d p (e.component p).toLinearMap)
    (a b : StandardFaceIndex P) (hab : standardRankWeight d a ≤ standardRankWeight d b) :
    (standardFaceBasis K hs).repr
      (originalComparison K hs e (barycentricGlobalStandardBasis K a)) b =
        if a = b then 1 else 0 := by
  rw [standardFaceBasis_repr_atCarrier, originalComparison_evaluation,
    barycentricRingEvaluation_globalBasis]
  by_cases ha : standardCarrier a ≤ standardCarrier b
  · rw [dif_pos ha]
    exact he (standardCarrier b) ⟨a, ha⟩ b hab
  · rw [dif_neg ha, LinearEquiv.map_zero, LinearEquiv.map_zero]
    have hne : a ≠ b := by intro h; subst b; exact ha le_rfl
    rw [if_neg hne]
    rfl

theorem originalComparison_degree
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p, HasStandardDegree K hs p (e.component p).toLinearMap)
    (a b : StandardFaceIndex P)
    (hab : standardOrdinaryDegree b ≠ standardOrdinaryDegree a) :
    (standardFaceBasis K hs).repr
      (originalComparison K hs e (barycentricGlobalStandardBasis K a)) b = 0 := by
  rw [standardFaceBasis_repr_atCarrier, originalComparison_evaluation,
    barycentricRingEvaluation_globalBasis]
  by_cases ha : standardCarrier a ≤ standardCarrier b
  · rw [dif_pos ha]
    exact he (standardCarrier b) ⟨a, ha⟩ b hab
  · rw [dif_neg ha, LinearEquiv.map_zero, LinearEquiv.map_zero]
    rfl

theorem universalOriginalParameterComparison_leading (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (a b : StandardFaceIndex P)
    (hab : standardRankWeight d a ≤ standardRankWeight d b) :
    (standardFaceBasis K hs).repr
      ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv
        (barycentricGlobalStandardBasis K a)) b = if a = b then 1 else 0 :=
  originalComparison_leading K hs d (universalCoherentComparison K hs d hrank)
    (fun p => (universalCoherentComparison_spec K hs d hrank p).1) a b hab

theorem universalOriginalParameterComparison_degree (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (a b : StandardFaceIndex P)
    (hab : standardOrdinaryDegree b ≠ standardOrdinaryDegree a) :
    (standardFaceBasis K hs).repr
      ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv
        (barycentricGlobalStandardBasis K a)) b = 0 :=
  originalComparison_degree K hs (universalCoherentComparison K hs d hrank)
    (fun p => (universalCoherentComparison_spec K hs d hrank p).2.2) a b hab

end FourPapers.Universal

end
end

/- BEGIN OriginalAssociatedGraded.lean -/
section

/-! # The actual rank-weight associated graded map is the canonical one -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def originalBarycentricWeightLevel (d : ℕ) (n : ℤ) :
    Submodule K (BarycentricRing (P := P) K) :=
  basisWeightLevel (barycentricGlobalStandardBasis K) (standardRankWeight d) n

def originalFaceWeightLevel (d : ℕ) (n : ℤ) : Submodule K (FaceRing K hs) :=
  basisWeightLevel (standardFaceBasis K hs) (standardRankWeight d) n

def canonicalOriginalComparison : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs :=
  canonicalBasisEquiv (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)

set_option backward.isDefEq.respectTransparency false in
theorem universalOriginalParameterComparison_hasWeightLeading (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    HasWeightLeading (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
      (standardRankWeight d)
      (universalOriginalParameterComparison K hs d hrank).toLinearEquiv.toLinearMap := by
  intro a b hab
  have h := universalOriginalParameterComparison_leading K hs d hrank a b hab
  by_cases he : a = b
  · simpa only [LinearEquiv.coe_coe, if_pos he] using h
  · simpa only [LinearEquiv.coe_coe, if_neg he] using h

theorem canonicalOriginalComparison_filtered (d : ℕ) (n : ℤ) (x : BarycentricRing (P := P) K) :
    canonicalOriginalComparison K hs x ∈ originalFaceWeightLevel K hs d n ↔
      x ∈ originalBarycentricWeightLevel K d n := by
  change (∀ i, n ≤ standardRankWeight d i →
    (standardFaceBasis K hs).repr (canonicalBasisEquiv
      (barycentricGlobalStandardBasis K) (standardFaceBasis K hs) x) i = 0) ↔ _
  rw [canonicalBasisEquiv_repr]
  rfl

theorem universalOriginalParameterComparison_filtered (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) (x : BarycentricRing (P := P) K) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x ∈
      originalFaceWeightLevel K hs d n ↔ x ∈ originalBarycentricWeightLevel K d n :=
  weightLeading_mem_iff (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
    (standardRankWeight d) (universalOriginalParameterComparison K hs d hrank).toLinearEquiv.toLinearMap
    (universalOriginalParameterComparison_hasWeightLeading K hs d hrank) n x

theorem universalOriginalParameterComparison_error_lower (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) (x : BarycentricRing (P := P) K)
    (hx : x ∈ originalBarycentricWeightLevel K d (n + 1)) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x - canonicalOriginalComparison K hs x ∈
      originalFaceWeightLevel K hs d n :=
  weightLeading_error_lower (barycentricGlobalStandardBasis K) (standardFaceBasis K hs)
    (standardRankWeight d) (universalOriginalParameterComparison K hs d hrank).toLinearEquiv.toLinearMap
    (universalOriginalParameterComparison_hasWeightLeading K hs d hrank) n x hx

/-- This equality is between actual quotient maps on consecutive filtration
levels. The canonical standard-monomial map is defined independently. -/
theorem universalOriginalParameterComparison_associatedGrade (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) :
    weightFiltrationGradeEquiv (originalBarycentricWeightLevel (P := P) K d)
      (originalFaceWeightLevel K hs d)
      (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
      (universalOriginalParameterComparison_filtered K hs d hrank) n =
    weightFiltrationGradeEquiv (originalBarycentricWeightLevel (P := P) K d)
      (originalFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
      (canonicalOriginalComparison_filtered K hs d) n :=
  weightFiltrationGradeEquiv_eq_of_error_lower _ _ _ _
    (universalOriginalParameterComparison_filtered K hs d hrank)
    (canonicalOriginalComparison_filtered K hs d) n
    (universalOriginalParameterComparison_error_lower K hs d hrank n)

end FourPapers.Universal

end
end

/- BEGIN OriginalCoefficientChange.lean -/
section

/-! # The scalar-change square on the original quotient presentations -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable {K L : Type*} [CommRing K] [CommRing L]
variable (hs : IsSimplicialPoset P) (h : K →+* L)

theorem map_faceSymbol (p : P) : MvPolynomial.map h (faceSymbol K p) = faceSymbol L p := by
  unfold faceSymbol
  split_ifs <;> simp only [map_one, MvPolynomial.map_X]

theorem map_faceRelation {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    MvPolynomial.map h f ∈ faceRelations L hs := by
  rcases hf with ⟨p, q, w, hpw, hqw, rfl⟩ | ⟨p, q, hnone, rfl⟩
  · left
    refine ⟨p, q, w, hpw, hqw, ?_⟩
    simp only [map_sub, map_mul, map_sum, map_faceSymbol]
  · right
    refine ⟨p, q, hnone, ?_⟩
    simp only [map_mul, map_faceSymbol]

def originalFaceCoefficientChange : FaceRing K hs →+* FaceRing L hs :=
  Ideal.quotientMap (faceIdeal L hs) (MvPolynomial.map h) (by
    apply Ideal.span_le.mpr
    intro f hf
    exact Ideal.subset_span (map_faceRelation hs h hf))

@[simp] theorem originalFaceCoefficientChange_mk (f : FacePolynomial (P := P) K) :
    originalFaceCoefficientChange hs h (Ideal.Quotient.mk (faceIdeal K hs) f) =
      Ideal.Quotient.mk (faceIdeal L hs) (MvPolynomial.map h f) := rfl

def originalBarycentricCoefficientChange : BarycentricRing (P := P) K →+* BarycentricRing (P := P) L :=
  (barycentricPresentationEquiv L).symm.toRingHom.comp
    ((monomialCoefficientRingHom BarycentricAllowed barycentricAllowed_divisorClosed h).comp
      (barycentricPresentationEquiv K).toRingHom)

@[simp] theorem originalBarycentricCoefficientChange_mk (f : FacePolynomial (P := P) K) :
    originalBarycentricCoefficientChange (P := P) h (Ideal.Quotient.mk (barycentricIdeal K) f) =
      Ideal.Quotient.mk (barycentricIdeal L) (MvPolynomial.map h f) := by
  change (barycentricPresentationEquiv L).symm
    (monomialCoefficientMap BarycentricAllowed barycentricAllowed_divisorClosed h
      (Ideal.Quotient.mk (forbiddenIdeal BarycentricAllowed) f)) = _
  rw [monomialCoefficientMap_mk]
  rfl

theorem map_faceValue (p q : P) : MvPolynomial.map h (faceValue K p q) = faceValue L p q := by
  unfold faceValue faceProduct
  split_ifs <;> simp only [map_prod, MvPolynomial.map_X, map_zero]

theorem originalFaceCoefficientChange_evaluation (p : P) (x : FaceRing K hs) :
    faceRingEvaluation L hs p (originalFaceCoefficientChange hs h x) =
      polynomialCoefficientChange h (faceRingEvaluation K hs p x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change faceEvaluation L p (MvPolynomial.map h f) = MvPolynomial.map h (faceEvaluation K p f)
  have he : (faceEvaluation L p).toRingHom.comp (MvPolynomial.map h) =
      (MvPolynomial.map h).comp (faceEvaluation K p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.map_C,
        faceEvaluation, MvPolynomial.aeval_C]
      exact (MvPolynomial.map_C h c).symm
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.map_X,
        faceEvaluation, MvPolynomial.aeval_X, map_faceValue]
  exact DFunLike.congr_fun he f

theorem originalBarycentricCoefficientChange_evaluation (p : P) (x : BarycentricRing (P := P) K) :
    barycentricRingEvaluation L hs p (originalBarycentricCoefficientChange h x) =
      booleanCoefficientChange h (barycentricRingEvaluation K hs p x) := by
  change monomialRestriction (booleanFaceInclusion hs p) BarycentricAllowed IsChainExponent
    barycentricAllowed_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha)
    (barycentricPresentationEquiv L ((barycentricPresentationEquiv L).symm
      (monomialCoefficientMap BarycentricAllowed barycentricAllowed_divisorClosed h
        (barycentricPresentationEquiv K x)))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (monomialCoefficientMap_restriction h (booleanFaceInclusion hs p)
    BarycentricAllowed IsChainExponent barycentricAllowed_divisorClosed
    isChainExponent_divisorClosed
    (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha) _).symm

/-- The one integral comparison commutes with every coefficient homomorphism
on the original quotient rings, with their usual polynomial coefficient maps. -/
theorem universalOriginalParameterComparison_baseChange (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (x : BarycentricRing (P := P) K) :
    originalFaceCoefficientChange hs h
      ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv x) =
    (universalOriginalParameterComparison L hs d hrank).toLinearEquiv
      (originalBarycentricCoefficientChange h x) := by
  apply (faceRingSectionEquiv L hs).injective
  apply Subtype.ext
  funext p
  simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
  change faceRingEvaluation L hs p
    (originalFaceCoefficientChange hs h
      (originalComparison K hs (universalCoherentComparison K hs d hrank) x)) =
    faceRingEvaluation L hs p
      (originalComparison L hs (universalCoherentComparison L hs d hrank)
        (originalBarycentricCoefficientChange h x))
  rw [originalFaceCoefficientChange_evaluation, originalComparison_evaluation,
    originalComparison_evaluation, originalBarycentricCoefficientChange_evaluation]
  exact universalCoherentComparison_baseChange K hs h d hrank p _

end FourPapers.Universal

end
end

/- BEGIN PresentationDegree.lean -/
section

/-! # Ordinary grading from the actual homogeneous polynomial presentations

The usual degree-n piece of a quotient is the image of the weighted
homogeneous polynomial submodule. The lemmas below identify that actual
image with the standard-basis degree block, without a dimension argument.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {I V K M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

def basisOrdinaryDegreePiece (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) : Submodule K M where
  carrier := {x | ∀ i, degree i ≠ n → b.repr x i = 0}
  zero_mem' := by intro i hi; simp
  add_mem' := by intro x y hx hy i hi; simp only [map_add, Finsupp.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by intro c x hx i hi; simp only [map_smul, Finsupp.smul_apply, hx i hi, smul_zero]

theorem weightedPresentationPiece_eq (q : MvPolynomial V K →ₗ[K] M)
    (b : Module.Basis I K M) (a : I → V →₀ ℕ) (w : V → ℕ) (degree : I → ℕ)
    (hb : ∀ i, q (monomial (a i) 1) = b i)
    (hd : ∀ i, Finsupp.weight w (a i) = degree i)
    (hm : ∀ t r i, degree i ≠ Finsupp.weight w t → b.repr (q (monomial t r)) i = 0)
    (n : ℕ) :
    (weightedHomogeneousSubmodule K w n).map q = basisOrdinaryDegreePiece b degree n := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    intro i hi
    rw [f.as_sum]
    simp only [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro t ht
    apply hm t (f.coeff t) i
    rw [hf (MvPolynomial.mem_support_iff.mp ht)]
    exact hi
  · intro hx
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    have hdi : degree i = n := by
      by_contra hn
      exact Finsupp.mem_support_iff.mp hi (hx i hn)
    exact ⟨monomial (a i) 1, isWeightedHomogeneous_monomial w (a i) 1 ((hd i).trans hdi), hb i⟩

theorem basisOrdinaryDegreePiece_map (b : Module.Basis I K M) (c : Module.Basis I K N)
    (degree : I → ℕ) (f : M →ₗ[K] N)
    (hf : ∀ i j, degree j ≠ degree i → c.repr (f (b i)) j = 0)
    (n : ℕ) (x : M) (hx : x ∈ basisOrdinaryDegreePiece b degree n) :
    f x ∈ basisOrdinaryDegreePiece c degree n := by
  intro j hj
  rw [basis_repr_linear_map]
  apply Finset.sum_eq_zero
  intro i hi
  have hdi : degree i = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (hx i hn)
  rw [hf i j (by rw [hdi]; exact hj), mul_zero]

theorem basisOrdinaryDegreePiece_equiv_iff (b : Module.Basis I K M) (c : Module.Basis I K N)
    (degree : I → ℕ) (e : M ≃ₗ[K] N)
    (he : ∀ i j, degree j ≠ degree i → c.repr (e (b i)) j = 0)
    (n : ℕ) (x : M) :
    e x ∈ basisOrdinaryDegreePiece c degree n ↔ x ∈ basisOrdinaryDegreePiece b degree n := by
  have hi : ∀ i j, degree j ≠ degree i → b.repr (e.symm (c i)) j = 0 := by
    intro i j hij
    have h := basis_repr_homogeneous_symm c (b.map e) degree degree
      (fun k l hkl => by simpa only [Module.Basis.map_apply] using he l k hkl) i j hij
    exact h
  constructor
  · intro hx
    have h := basisOrdinaryDegreePiece_map c b degree e.symm.toLinearMap hi n (e x) hx
    change e.symm (e x) ∈ basisOrdinaryDegreePiece b degree n at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  · exact basisOrdinaryDegreePiece_map b c degree e.toLinearMap he n x

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)

def originalPolynomialDegree (a : NonzeroFace P →₀ ℕ) : ℕ :=
  a.sum (fun q n => n * faceRank q.val)

theorem originalPolynomialDegree_eq_weight (a : NonzeroFace P →₀ ℕ) :
    originalPolynomialDegree a = Finsupp.weight (fun q : NonzeroFace P => faceRank q.val) a := by
  simp only [originalPolynomialDegree, Finsupp.weight_apply, smul_eq_mul]

theorem stalkExponent_ordinaryDegree (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    vertexDegree (fun v => stalkExponent p a v) = originalPolynomialDegree a := by
  unfold vertexDegree originalPolynomialDegree
  simp only [stalkExponent_apply, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  change (∑ _v ∈ stalkVertexSet p q.val, a q) = a q * faceRank q.val
  rw [Finset.sum_const, nsmul_eq_mul, card_stalkVertexSet (ha q hq), Nat.mul_comm]
  rfl

theorem originalFace_monomial_degree (a : NonzeroFace P →₀ ℕ) (r : K)
    (b : StandardFaceIndex P) (hb : standardOrdinaryDegree b ≠ originalPolynomialDegree a) :
    (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a r)) b = 0 := by
  change (standardFaceBasis K hs).repr
    ((Ideal.Quotient.mkₐ K (faceIdeal K hs)) (monomial a r)) b = 0
  have hmono : monomial a r = r • monomial a (1 : K) := by
    rw [← (monomial a).map_smul, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, Finsupp.smul_apply]
  suffices h : (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0 by
    change r • (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0
    rw [h, smul_zero]
  rw [standardFaceBasis_repr_atCarrier, polynomialStandardCoordinates_apply_of_inside
    K hs (standardCarrier b) _ ⟨b, le_rfl⟩]
  change (faceEvaluation K (standardCarrier b) (monomial a 1)).coeff
    (stalkExponent (standardCarrier b) b.val) = 0
  by_cases ha : ∀ q ∈ a.support, q.val ≤ standardCarrier b
  · rw [faceEvaluation_monomial_of_inside K _ a ha, MvPolynomial.coeff_monomial]
    apply if_neg
    intro he
    have hd := congrArg (fun t : FaceVertex (standardCarrier b) →₀ ℕ => vertexDegree (fun v => t v)) he
    rw [stalkExponent_ordinaryDegree _ a ha,
      stalkExponent_ordinaryDegree _ b.val ((standardCarrier_le_iff hs b _).mp le_rfl)] at hd
    exact hb hd.symm
  · rw [faceEvaluation_monomial_of_outside K _ a ha]
    rfl

/-- The conventional degree piece is the image of the actual homogeneous
polynomials in the original presentation. -/
def usualFaceDegreePiece (n : ℕ) : Submodule K (FaceRing K hs) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap

theorem usualFaceDegreePiece_eq (n : ℕ) :
    usualFaceDegreePiece K hs n =
      basisOrdinaryDegreePiece (standardFaceBasis K hs) standardOrdinaryDegree n := by
  apply weightedPresentationPiece_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · intro a
    exact (standardFaceBasis_apply K hs a).symm
  · intro a
    exact (originalPolynomialDegree_eq_weight a.val).symm
  · intro a r b hb
    apply originalFace_monomial_degree K hs a r b
    simpa only [originalPolynomialDegree_eq_weight] using hb

def usualBarycentricDegreePiece (n : ℕ) : Submodule K (BarycentricRing (P := P) K) :=
  (weightedHomogeneousSubmodule K (fun q : NonzeroFace P => faceRank q.val) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap

theorem barycentricGlobalStandardBasis_monomial (a : StandardFaceIndex P) :
    Ideal.Quotient.mk (barycentricIdeal (P := P) K) (monomial a.val 1) =
      barycentricGlobalStandardBasis K a := by
  apply (barycentricMonomialEquiv K).injective
  rw [barycentricMonomialEquiv_mk, barycentricGlobalStandardBasis_coordinates]
  ext b
  rw [standardCoefficients_apply, MvPolynomial.coeff_monomial, Finsupp.single_apply]
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl]
  · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    simp only [if_neg hab, if_neg hval]

theorem usualBarycentricDegreePiece_eq (n : ℕ) :
    usualBarycentricDegreePiece (P := P) K n =
      basisOrdinaryDegreePiece (barycentricGlobalStandardBasis K) standardOrdinaryDegree n := by
  apply weightedPresentationPiece_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · exact barycentricGlobalStandardBasis_monomial K
  · intro a
    exact (originalPolynomialDegree_eq_weight a.val).symm
  · intro a r b hb
    change standardCoefficients BarycentricAllowed (monomial a r) b = 0
    rw [standardCoefficients_apply, MvPolynomial.coeff_monomial]
    apply if_neg
    intro hab
    subst a
    exact hb (originalPolynomialDegree_eq_weight b.val)

/-- Ordinary grading in the conventional quotient presentation, in both
directions of the actual parameter equivalence. -/
theorem universalOriginalParameterComparison_usualDegree (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℕ) (x : BarycentricRing (P := P) K) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x ∈
      usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n := by
  rw [usualFaceDegreePiece_eq, usualBarycentricDegreePiece_eq]
  exact basisOrdinaryDegreePiece_equiv_iff
    (barycentricGlobalStandardBasis K) (standardFaceBasis K hs) standardOrdinaryDegree
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
    (universalOriginalParameterComparison_degree K hs d hrank) n x

end Poset
end FourPapers.Universal

end
end

/- BEGIN RestrictionKernels.lean -/
section

/-! # Conventional restriction ideals and the relative comparison

Restriction to a lower ideal kills the outside face generators.  The statements
below identify the kernel of this actual quotient map with the joint kernel of
the polynomial stalk restrictions.  The bottom symbol is included: a genuinely
empty lower ideal has zero quotient, whereas the lower ideal containing only the
bottom face has the constant coefficient ring.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def faceRestrictionIdeal (Q : Set P) : Ideal (FaceRing K hs) :=
  Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = faceRingGenerator K hs p}

def barycentricRestrictionIdeal (Q : Set P) : Ideal (BarycentricRing (P := P) K) :=
  Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = barycentricGenerator K p}

abbrev faceRestrictionQuotient (Q : Set P) := FaceRing K hs ⧸ faceRestrictionIdeal K hs Q
abbrev barycentricRestrictionQuotient (Q : Set P) :=
  BarycentricRing (P := P) K ⧸ barycentricRestrictionIdeal K Q

def faceRestrictionMap (Q : Set P) :
    FaceRing K hs →ₐ[K] faceRestrictionQuotient K hs Q :=
  Ideal.Quotient.mkₐ K (faceRestrictionIdeal K hs Q)

def barycentricRestrictionMap (Q : Set P) :
    BarycentricRing (P := P) K →ₐ[K] barycentricRestrictionQuotient K Q :=
  Ideal.Quotient.mkₐ K (barycentricRestrictionIdeal K Q)

theorem monomial_factor_at_support (a : NonzeroFace P →₀ ℕ) (q : NonzeroFace P)
    (hq : q ∈ a.support) :
    (monomial a (1 : K) : FacePolynomial K) =
      X q * monomial (a - Finsupp.single q 1) 1 := by
  have hle : Finsupp.single q 1 ≤ a :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq))
  rw [MvPolynomial.X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle]

theorem faceBasis_mem_restrictionIdeal (Q : Set P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∉ Q) :
    standardFaceBasis K hs a ∈ faceRestrictionIdeal K hs Q := by
  rcases standardCarrier_mem_or_bot a with hb | ⟨q, hq, he⟩
  · have h1 : (1 : FaceRing K hs) ∈ faceRestrictionIdeal K hs Q := by
      have hm : faceRingGenerator K hs ⊥ ∈ faceRestrictionIdeal K hs Q :=
        Ideal.subset_span ⟨⊥, by simpa only [hb] using ha, rfl⟩
      simpa only [faceRingGenerator, faceSymbol_bot, map_one] using hm
    simpa only [mul_one] using (faceRestrictionIdeal K hs Q).mul_mem_left
      (standardFaceBasis K hs a) h1
  · rw [standardFaceBasis_apply]
    change Ideal.Quotient.mk (faceIdeal K hs) (monomial a.val 1) ∈ _
    rw [monomial_factor_at_support K a.val q hq, map_mul]
    apply (faceRestrictionIdeal K hs Q).mul_mem_right
    have hm : faceRingGenerator K hs q.val ∈ faceRestrictionIdeal K hs Q :=
      Ideal.subset_span ⟨q.val, by simpa only [he] using ha, rfl⟩
    simpa only [faceRingGenerator, faceSymbol_nonzero] using hm

theorem barycentricBasis_mem_restrictionIdeal (Q : Set P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∉ Q) :
    barycentricGlobalStandardBasis K a ∈ barycentricRestrictionIdeal K Q := by
  rcases standardCarrier_mem_or_bot a with hb | ⟨q, hq, he⟩
  · have h1 : (1 : BarycentricRing (P := P) K) ∈ barycentricRestrictionIdeal K Q := by
      have hm : barycentricGenerator K ⊥ ∈ barycentricRestrictionIdeal K Q :=
        Ideal.subset_span ⟨⊥, by simpa only [hb] using ha, rfl⟩
      simpa only [barycentricGenerator, faceSymbol_bot, map_one] using hm
    simpa only [mul_one] using (barycentricRestrictionIdeal K Q).mul_mem_left
      (barycentricGlobalStandardBasis K a) h1
  · rw [← barycentricGlobalStandardBasis_monomial]
    rw [monomial_factor_at_support K a.val q hq, map_mul]
    apply (barycentricRestrictionIdeal K Q).mul_mem_right
    have hm : barycentricGenerator K q.val ∈ barycentricRestrictionIdeal K Q :=
      Ideal.subset_span ⟨q.val, by simpa only [he] using ha, rfl⟩
    simpa only [barycentricGenerator, faceSymbol_nonzero] using hm

theorem faceRestrictionIdeal_mem_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : FaceRing K hs) :
    x ∈ faceRestrictionIdeal K hs Q ↔ ∀ p ∈ Q, faceRingEvaluation K hs p x = 0 := by
  constructor
  · intro hx p hp
    have hker : faceRestrictionIdeal K hs Q ≤ RingHom.ker (faceRingEvaluation K hs p).toRingHom := by
      apply Ideal.span_le.mpr
      rintro y ⟨q, hq, rfl⟩
      change faceRingEvaluation K hs p (faceRingGenerator K hs q) = 0
      rw [faceRingEvaluation_generator, faceValue, if_neg (fun h => hq (hQ h hp))]
    exact hker hx
  · intro hx
    rw [← (standardFaceBasis K hs).linearCombination_repr x,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (faceRestrictionIdeal K hs Q).sum_mem
    intro a ha
    have hout : standardCarrier a ∉ Q := by
      intro hin
      have hz := hx (standardCarrier a) hin
      have hc : (standardFaceBasis K hs).repr x a = 0 := by
        rw [standardFaceBasis_repr_atCarrier, hz, LinearEquiv.map_zero]
        rfl
      exact Finsupp.mem_support_iff.mp ha hc
    exact (faceRestrictionIdeal K hs Q).smul_of_tower_mem
      ((standardFaceBasis K hs).repr x a) (faceBasis_mem_restrictionIdeal K hs Q a hout)

theorem barycentricRestrictionIdeal_mem_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K) :
    x ∈ barycentricRestrictionIdeal K Q ↔ ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0 := by
  constructor
  · intro hx p hp
    have hker : barycentricRestrictionIdeal K Q ≤ RingHom.ker (barycentricRingEvaluation K hs p).toRingHom := by
      apply Ideal.span_le.mpr
      rintro y ⟨q, hq, rfl⟩
      change barycentricRingEvaluation K hs p (barycentricGenerator K q) = 0
      exact barycentricRingEvaluation_outside K hs p q (fun h => hq (hQ h hp))
    exact hker hx
  · intro hx
    rw [← (barycentricGlobalStandardBasis K).linearCombination_repr x,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply (barycentricRestrictionIdeal K Q).sum_mem
    intro a ha
    have hout : standardCarrier a ∉ Q := by
      intro hin
      have hz := hx (standardCarrier a) hin
      have hc : (barycentricGlobalStandardBasis K).repr x a = 0 := by
        change barycentricMonomialEquiv K x a = 0
        rw [← barycentricRingEvaluation_coefficient K hs (standardCarrier a) x a le_rfl,
          hz, map_zero]
        rfl
      exact Finsupp.mem_support_iff.mp ha hc
    exact (barycentricRestrictionIdeal K Q).smul_of_tower_mem
      ((barycentricGlobalStandardBasis K).repr x a)
      (barycentricBasis_mem_restrictionIdeal K Q a hout)

theorem faceRestrictionMap_eq_zero_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : FaceRing K hs) :
    faceRestrictionMap K hs Q x = 0 ↔ ∀ p ∈ Q, faceRingEvaluation K hs p x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.trans (faceRestrictionIdeal_mem_iff K hs Q hQ x)

theorem barycentricRestrictionMap_eq_zero_iff (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K) :
    barycentricRestrictionMap K Q x = 0 ↔ ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.trans (barycentricRestrictionIdeal_mem_iff K hs Q hQ x)

/-- The actual global parameter equivalence identifies the conventional
restriction kernels, simultaneously for every lower ideal. -/
theorem universalOriginalParameterComparison_restrictionKernel (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
    (x : BarycentricRing (P := P) K) :
    faceRestrictionMap K hs Q ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv x) = 0 ↔
      barycentricRestrictionMap K Q x = 0 := by
  rw [faceRestrictionMap_eq_zero_iff K hs Q hQ,
    barycentricRestrictionMap_eq_zero_iff K hs Q hQ]
  constructor
  · intro hx p hp
    have hh := hx p hp
    rw [show (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x =
        originalComparison K hs (universalCoherentComparison K hs d hrank) x from rfl,
      originalComparison_evaluation] at hh
    exact ((universalCoherentComparison K hs d hrank).component p).injective
      (hh.trans ((universalCoherentComparison K hs d hrank).component p).map_zero.symm)
  · intro hx p hp
    change faceRingEvaluation K hs p
      (originalComparison K hs (universalCoherentComparison K hs d hrank) x) = 0
    rw [originalComparison_evaluation, hx p hp, LinearEquiv.map_zero]

end FourPapers.Universal

end
end

/- BEGIN PresentationWeight.lean -/
section

/-! # The rank-weight filtration of the polynomial presentations

The filtration is defined before quotienting, by the weights of the actual
generators.  Its equality with the standard-chain basis filtration is proved
using the genuine polynomial stalk evaluations and the overlap inequality.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {I V K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def presentationWeightLevel (w : (V →₀ ℕ) → ℤ) (n : ℤ) : Submodule K (MvPolynomial V K) where
  carrier := {f | ∀ a, n ≤ w a → f.coeff a = 0}
  zero_mem' := by intro a ha; simp
  add_mem' := by intro f g hf hg a ha; simp only [MvPolynomial.coeff_add, hf a ha, hg a ha, add_zero]
  smul_mem' := by intro c f hf a ha; simp only [coeff_smul, hf a ha, smul_zero]

theorem weightedPresentationFiltration_eq (q : MvPolynomial V K →ₗ[K] M)
    (b : Module.Basis I K M) (a : I → V →₀ ℕ)
    (w : (V →₀ ℕ) → ℤ) (weight : I → ℤ)
    (hb : ∀ i, q (monomial (a i) 1) = b i)
    (hd : ∀ i, w (a i) = weight i)
    (hm : ∀ t r i, w t < weight i → b.repr (q (monomial t r)) i = 0) (n : ℤ) :
    (presentationWeightLevel w n).map q = basisWeightLevel b weight n := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    intro i hi
    rw [f.as_sum]
    simp only [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro t ht
    apply hm t (f.coeff t) i
    have hn : w t < n := lt_of_not_ge (fun h => MvPolynomial.mem_support_iff.mp ht (hf t h))
    exact hn.trans_le hi
  · intro hx
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    refine ⟨monomial (a i) 1, ?_, hb i⟩
    intro t ht
    rw [coeff_monomial]
    apply if_neg
    intro he
    subst t
    exact Finsupp.mem_support_iff.mp hi (hx i (by simpa only [hd] using ht))

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)

def originalPolynomialWeight (d : ℕ) (a : NonzeroFace P →₀ ℕ) : ℤ :=
  a.sum (fun q n => (n : ℤ) * rankWeight d (faceRank q.val))

abbrev OriginalExponentFactors (a : NonzeroFace P →₀ ℕ) :=
  Σ q : NonzeroFace P, Fin (a q)

def originalFactorFaces (p : P) (a : NonzeroFace P →₀ ℕ)
    (t : OriginalExponentFactors a) : Finset (FaceVertex p) := stalkVertexSet p t.1.val

theorem originalFactorFaces_occurrence (p : P) (a : NonzeroFace P →₀ ℕ) :
    occurrenceExponent (originalFactorFaces p a) = stalkExponent p a := by
  ext v
  rw [occurrenceExponent_apply, Fintype.sum_sigma]
  simp only [originalFactorFaces, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mem_stalkVertexSet, mul_ite, mul_one, mul_zero]
  rw [stalkExponent_apply]
  exact (Finsupp.sum_fintype a (fun q n => if v.val ≤ q.val then n else 0)
    (fun q => by simp)).symm

theorem originalFactorFaces_weight (d : ℕ) (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    (∑ t : OriginalExponentFactors a, rankWeight d (originalFactorFaces p a t).card) =
      originalPolynomialWeight d a := by
  simp only [Fintype.sum_sigma, originalFactorFaces, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [originalPolynomialWeight, Finsupp.sum_fintype _ _ (fun q => by simp)]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqa : a q = 0
  · simp only [hqa, Nat.cast_zero, zero_mul]
  · rw [card_stalkVertexSet (ha q (Finsupp.mem_support_iff.mpr hqa))]

theorem stalkExponent_rankWeight_le (d : ℕ) (p : P) (a : NonzeroFace P →₀ ℕ)
    (ha : ∀ q ∈ a.support, q.val ≤ p) :
    polynomialRankWeight d (fun v => stalkExponent p a v) ≤ originalPolynomialWeight d a := by
  have h := polynomialRankWeight_occurrence_le d (originalFactorFaces p a)
  simpa only [originalFactorFaces_occurrence, originalFactorFaces_weight d p a ha] using h

include hs in
theorem stalkExponent_standardRankWeight (d : ℕ) (p : P) (a : StandardInside p) :
    polynomialRankWeight d (fun v => stalkExponent p a.val.val v) = standardRankWeight d a.val := by
  letI : LinearOrder (FaceVertex p) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  let b := (standardInsideEquiv hs p).symm a
  have he := (standardInsideEquiv hs p).apply_symm_apply a
  have hw := standardRankWeight_inside hs d p b
  rw [he] at hw
  have hexp : stalkExponent p a.val.val = chainVertexMap b.val := by
    rw [← standardVertexEquiv_apply hs p a]
    rfl
  rw [hexp, polynomialRankWeight_chainVertexMap d b.property]
  exact hw.symm

theorem originalFace_monomial_weight (d : ℕ) (a : NonzeroFace P →₀ ℕ) (r : K)
    (b : StandardFaceIndex P) (hb : originalPolynomialWeight d a < standardRankWeight d b) :
    (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a r)) b = 0 := by
  change (standardFaceBasis K hs).repr
    ((Ideal.Quotient.mkₐ K (faceIdeal K hs)) (monomial a r)) b = 0
  have hmono : monomial a r = r • monomial a (1 : K) := by
    rw [← (monomial a).map_smul, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, Finsupp.smul_apply]
  suffices h : (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0 by
    change r • (standardFaceBasis K hs).repr
      (Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)) b = 0
    rw [h, smul_zero]
  rw [standardFaceBasis_repr_atCarrier, polynomialStandardCoordinates_apply_of_inside
    K hs (standardCarrier b) _ ⟨b, le_rfl⟩]
  change (faceEvaluation K (standardCarrier b) (monomial a 1)).coeff
    (stalkExponent (standardCarrier b) b.val) = 0
  by_cases ha : ∀ q ∈ a.support, q.val ≤ standardCarrier b
  · rw [faceEvaluation_monomial_of_inside K _ a ha, MvPolynomial.coeff_monomial]
    apply if_neg
    intro he
    have hw := stalkExponent_rankWeight_le d (standardCarrier b) a ha
    rw [he, stalkExponent_standardRankWeight hs d (standardCarrier b) ⟨b, le_rfl⟩] at hw
    exact (not_lt_of_ge hw) hb
  · rw [faceEvaluation_monomial_of_outside K _ a ha]
    rfl

def usualFaceWeightLevel (d : ℕ) (n : ℤ) : Submodule K (FaceRing K hs) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (faceIdeal K hs)).toLinearMap

def usualBarycentricWeightLevel (d : ℕ) (n : ℤ) : Submodule K (BarycentricRing (P := P) K) :=
  (presentationWeightLevel (originalPolynomialWeight (P := P) d) n).map
    (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).toLinearMap

theorem usualFaceWeightLevel_eq (d : ℕ) (n : ℤ) :
    usualFaceWeightLevel K hs d n = originalFaceWeightLevel K hs d n := by
  apply weightedPresentationFiltration_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · intro a
    exact (standardFaceBasis_apply K hs a).symm
  · intro a
    rfl
  · exact originalFace_monomial_weight K hs d

theorem usualBarycentricWeightLevel_eq (d : ℕ) (n : ℤ) :
    usualBarycentricWeightLevel (P := P) K d n = originalBarycentricWeightLevel K d n := by
  apply weightedPresentationFiltration_eq _ _ (fun a : StandardFaceIndex P => a.val)
  · exact barycentricGlobalStandardBasis_monomial K
  · intro a
    rfl
  · intro a r b hb
    change standardCoefficients BarycentricAllowed (monomial a r) b = 0
    rw [standardCoefficients_apply, MvPolynomial.coeff_monomial]
    apply if_neg
    intro he
    subst a
    exact (lt_irrefl (standardRankWeight d b)) hb

/-- Preservation and reflection of the actual filtration induced by assigning
weight `r(2d-r)` to a rank-r generator in the original presentations. -/
theorem universalOriginalParameterComparison_usualWeight (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) (x : BarycentricRing (P := P) K) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n := by
  rw [usualFaceWeightLevel_eq, usualBarycentricWeightLevel_eq]
  exact universalOriginalParameterComparison_filtered K hs d hrank n x

end Poset
end FourPapers.Universal

end
end

/- BEGIN LowerIdealPresentation.lean -/
section

/-! # The original face-ring presentation of a lower subposet

A nonempty lower ideal contains the bottom face.  Its intervals and atoms are
identified explicitly with the ambient ones.  Stalk restriction then gives a
homomorphism to its original Stanley quotient, with the usual generator formula.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

structure FaceLowerIdeal (P : Type*) [PartialOrder P] [OrderBot P] where
  carrier : Set P
  lower : ∀ ⦃p q : P⦄, p ≤ q → q ∈ carrier → p ∈ carrier
  bot_mem : (⊥ : P) ∈ carrier

instance : CoeSort (FaceLowerIdeal P) (Type _) := ⟨fun Q => Q.carrier⟩
instance (Q : FaceLowerIdeal P) : PartialOrder Q := inferInstanceAs (PartialOrder Q.carrier)
instance (Q : FaceLowerIdeal P) : Fintype Q := Fintype.ofFinite _
instance (Q : FaceLowerIdeal P) : OrderBot Q where
  bot := ⟨⊥, Q.bot_mem⟩
  bot_le _ := bot_le

def lowerIdealIntervalEquiv (Q : FaceLowerIdeal P) (q : Q) : Set.Iic q ≃o Set.Iic q.val where
  toFun a := ⟨a.val.val, a.property⟩
  invFun a := ⟨⟨a.val, Q.lower a.property q.property⟩, a.property⟩
  left_inv a := rfl
  right_inv a := rfl
  map_rel_iff' := Iff.rfl

theorem lowerIdealIsSimplicial (hs : IsSimplicialPoset P) (Q : FaceLowerIdeal P) :
    IsSimplicialPoset Q := by
  intro q
  obtain ⟨n, ⟨e⟩⟩ := hs q.val
  exact ⟨n, ⟨(lowerIdealIntervalEquiv Q q).trans e⟩⟩

theorem lowerIdeal_isAtom_iff (Q : FaceLowerIdeal P) (a : Q) : IsAtom a ↔ IsAtom a.val := by
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨fun h => ha (Subtype.ext h), ?_⟩
    intro b hb
    have h := hmin ⟨b, Q.lower hb.le a.property⟩ hb
    exact congrArg Subtype.val h
  · rintro ⟨ha, hmin⟩
    exact ⟨fun h => ha (congrArg Subtype.val h),
      fun b hb => Subtype.ext (hmin b.val hb)⟩

def lowerIdealVertexEquiv (Q : FaceLowerIdeal P) (q : Q) : FaceVertex q ≃ FaceVertex q.val where
  toFun a := ⟨a.val.val, (lowerIdeal_isAtom_iff Q a.val).mp a.property.1, a.property.2⟩
  invFun a := ⟨⟨a.val, Q.lower a.property.2 q.property⟩,
    (lowerIdeal_isAtom_iff Q _).mpr a.property.1, a.property.2⟩
  left_inv a := rfl
  right_inv a := rfl

variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def lowerIdealPolynomialEquiv (Q : FaceLowerIdeal P) (q : Q) :
    PolynomialStalk K q.val ≃ₐ[K] PolynomialStalk K q :=
  MvPolynomial.renameEquiv K (lowerIdealVertexEquiv Q q).symm

theorem lowerIdealPolynomialEquiv_restriction (Q : FaceLowerIdeal P) {p q : Q}
    (hqp : q ≤ p) (f : PolynomialStalk K p.val) :
    polynomialRestriction K hqp (lowerIdealPolynomialEquiv K Q p f) =
      lowerIdealPolynomialEquiv K Q q (polynomialRestriction K (show q.val ≤ p.val from hqp) f) := by
  have he : (polynomialRestriction K hqp).comp (lowerIdealPolynomialEquiv K Q p).toAlgHom =
      (lowerIdealPolynomialEquiv K Q q).toAlgHom.comp
        (polynomialRestriction K (show q.val ≤ p.val from hqp)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, lowerIdealPolynomialEquiv,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, polynomialRestriction_X]
    by_cases h : a.val ≤ q.val
    · have hh : ((lowerIdealVertexEquiv Q p).symm a).val ≤ q := h
      rw [dif_pos hh, dif_pos h, MvPolynomial.rename_X]
      rfl
    · have hh : ¬ ((lowerIdealVertexEquiv Q p).symm a).val ≤ q := h
      rw [dif_neg hh, dif_neg h, map_zero]
  exact DFunLike.congr_fun he f

def lowerIdealPolynomialSections (Q : FaceLowerIdeal P) :
    FaceRing K hs →ₗ[K] (polynomialDiagram (P := Q) K).sections where
  toFun x := ⟨fun q => lowerIdealPolynomialEquiv K Q q (faceRingEvaluation K hs q.val x), by
    intro p q hqp
    change polynomialRestriction K hqp
      (lowerIdealPolynomialEquiv K Q p (faceRingEvaluation K hs p.val x)) =
        lowerIdealPolynomialEquiv K Q q (faceRingEvaluation K hs q.val x)
    rw [lowerIdealPolynomialEquiv_restriction]
    have hh := (faceRingSection K hs x).property p.val q.val hqp
    exact congrArg (lowerIdealPolynomialEquiv K Q q) hh⟩
  map_add' x y := by
    apply Subtype.ext
    funext q
    simp only [map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    funext q
    simp only [map_smul]
    rfl

def lowerIdealFaceRestrictionLinear (Q : FaceLowerIdeal P) :
    FaceRing K hs →ₗ[K] FaceRing K (lowerIdealIsSimplicial hs Q) :=
  (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).symm.toLinearMap.comp
    (lowerIdealPolynomialSections K hs Q)

theorem lowerIdealFaceRestriction_evaluation (Q : FaceLowerIdeal P) (q : Q) (x : FaceRing K hs) :
    faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q (lowerIdealFaceRestrictionLinear K hs Q x) =
      lowerIdealPolynomialEquiv K Q q (faceRingEvaluation K hs q.val x) := by
  have hh := (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).apply_symm_apply
    (lowerIdealPolynomialSections K hs Q x)
  have hc := congrArg (fun s : (polynomialDiagram (P := Q) K).sections => s.val q) hh
  have hc' : faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
      ((faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).symm
        (lowerIdealPolynomialSections K hs Q x)) =
      (lowerIdealPolynomialSections K hs Q x).val q := by
    simpa only [faceRingSectionEquiv_apply, faceRingSection_apply] using hc
  change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
      ((faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).symm
        (lowerIdealPolynomialSections K hs Q x)) = _
  exact hc'.trans (by rfl)

def lowerIdealFaceRestriction (Q : FaceLowerIdeal P) :
    FaceRing K hs →ₐ[K] FaceRing K (lowerIdealIsSimplicial hs Q) where
  toFun := lowerIdealFaceRestrictionLinear K hs Q
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      lowerIdealFaceRestriction_evaluation, map_one]
  map_mul' x y := by
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      lowerIdealFaceRestriction_evaluation, map_mul]
  commutes' c := by
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply,
      lowerIdealFaceRestriction_evaluation, AlgHom.commutes, AlgEquiv.commutes]

theorem lowerIdealPolynomialEquiv_faceProduct (Q : FaceLowerIdeal P) (q p : Q) :
    lowerIdealPolynomialEquiv K Q q (faceProduct K q.val p.val) = faceProduct K q p := by
  simp only [lowerIdealPolynomialEquiv, MvPolynomial.renameEquiv_apply,
    faceProduct, map_prod, MvPolynomial.rename_X]
  apply Finset.prod_bij (fun a _ => (lowerIdealVertexEquiv Q q).symm a)
  · intro a ha
    exact (mem_stalkVertexSet q p _).mpr ((mem_stalkVertexSet q.val p.val a).mp ha)
  · intro a ha b hb he
    exact (lowerIdealVertexEquiv Q q).symm.injective he
  · intro b hb
    refine ⟨lowerIdealVertexEquiv Q q b, ?_, ?_⟩
    · exact (mem_stalkVertexSet q.val p.val _).mpr ((mem_stalkVertexSet q p b).mp hb)
    · exact (lowerIdealVertexEquiv Q q).symm_apply_apply b
  · intro a ha
    rfl

theorem lowerIdealFaceRestriction_generator_inside (Q : FaceLowerIdeal P) (p : Q) :
    lowerIdealFaceRestriction K hs Q (faceRingGenerator K hs p.val) =
      faceRingGenerator K (lowerIdealIsSimplicial hs Q) p := by
  apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
  apply Subtype.ext
  funext q
  simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
  change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
    (lowerIdealFaceRestrictionLinear K hs Q (faceRingGenerator K hs p.val)) = _
  rw [lowerIdealFaceRestriction_evaluation, faceRingEvaluation_generator,
    faceRingEvaluation_generator]
  by_cases h : p ≤ q
  · have hh : p.val ≤ q.val := h
    simp only [faceValue, if_pos h, if_pos hh]
    exact lowerIdealPolynomialEquiv_faceProduct K Q q p
  · have hh : ¬ p.val ≤ q.val := h
    simp only [faceValue, if_neg h, if_neg hh, map_zero]

theorem lowerIdealFaceRestriction_eq_zero_iff (Q : FaceLowerIdeal P) (x : FaceRing K hs) :
    lowerIdealFaceRestriction K hs Q x = 0 ↔ ∀ p ∈ Q.carrier, faceRingEvaluation K hs p x = 0 := by
  constructor
  · intro hx p hp
    have hh := congrArg (faceRingEvaluation K (lowerIdealIsSimplicial hs Q) ⟨p, hp⟩) hx
    change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) ⟨p, hp⟩
      (lowerIdealFaceRestrictionLinear K hs Q x) = _ at hh
    rw [lowerIdealFaceRestriction_evaluation, map_zero] at hh
    exact (lowerIdealPolynomialEquiv K Q ⟨p, hp⟩).injective
      (hh.trans (map_zero _).symm)
  · intro hx
    apply (faceRingSectionEquiv K (lowerIdealIsSimplicial hs Q)).injective
    apply Subtype.ext
    funext q
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
    change faceRingEvaluation K (lowerIdealIsSimplicial hs Q) q
      (lowerIdealFaceRestrictionLinear K hs Q x) = _
    rw [lowerIdealFaceRestriction_evaluation, hx q.val q.property, map_zero, map_zero]

theorem lowerIdealFaceRestriction_generator_outside (Q : FaceLowerIdeal P)
    (p : P) (hp : p ∉ Q.carrier) :
    lowerIdealFaceRestriction K hs Q (faceRingGenerator K hs p) = 0 := by
  rw [lowerIdealFaceRestriction_eq_zero_iff]
  intro q hq
  rw [faceRingEvaluation_generator, faceValue, if_neg (fun h => hp (Q.lower h hq))]

/-- The kernel of restriction to the smaller poset's original Stanley
presentation is precisely the conventional outside-generator ideal. -/
theorem lowerIdealFaceRestriction_ker (Q : FaceLowerIdeal P) :
    RingHom.ker (lowerIdealFaceRestriction K hs Q).toRingHom = faceRestrictionIdeal K hs Q.carrier := by
  ext x
  exact (lowerIdealFaceRestriction_eq_zero_iff K hs Q x).trans
    (faceRestrictionIdeal_mem_iff K hs Q.carrier Q.lower x).symm

end FourPapers.Universal

end
end

/- BEGIN LowerIdealBarycentric.lean -/
section

/-! # Both conventional lower-ideal targets and their quotient identifications -/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def lowerIdealNonzeroEmbedding (Q : FaceLowerIdeal P) : NonzeroFace Q ↪ NonzeroFace P where
  toFun q := ⟨q.val.val, fun h => q.property (Subtype.ext h)⟩
  inj' p q h := Subtype.ext (Subtype.ext (congrArg (fun a : NonzeroFace P => a.val) h))

theorem lowerIdealNonzeroEmbedding_range (Q : FaceLowerIdeal P) (p : NonzeroFace P) :
    p ∈ Set.range (lowerIdealNonzeroEmbedding Q) ↔ p.val ∈ Q.carrier := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.val.property
  · intro hp
    refine ⟨⟨⟨p.val, hp⟩, fun h => p.property (congrArg Subtype.val h)⟩, rfl⟩

theorem lowerIdealFaceRestriction_surjective (Q : FaceLowerIdeal P) :
    Function.Surjective (lowerIdealFaceRestriction K hs Q) := by
  have he : (lowerIdealFaceRestriction K hs Q).comp
      ((Ideal.Quotient.mkₐ K (faceIdeal K hs)).comp
        (MvPolynomial.rename (lowerIdealNonzeroEmbedding Q))) =
      Ideal.Quotient.mkₐ K (faceIdeal K (lowerIdealIsSimplicial hs Q)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X]
    have hh := lowerIdealFaceRestriction_generator_inside K hs Q q.val
    have hsym : faceSymbol K q.val.val = X (lowerIdealNonzeroEmbedding Q q) :=
      faceSymbol_nonzero K (lowerIdealNonzeroEmbedding Q q)
    change lowerIdealFaceRestriction K hs Q
      (Ideal.Quotient.mk (faceIdeal K hs) (X (lowerIdealNonzeroEmbedding Q q))) =
        Ideal.Quotient.mk (faceIdeal K (lowerIdealIsSimplicial hs Q)) (X q)
    simpa only [faceRingGenerator, hsym, faceSymbol_nonzero] using hh
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk (faceIdeal K hs) (MvPolynomial.rename (lowerIdealNonzeroEmbedding Q) f), ?_⟩
  exact DFunLike.congr_fun he f

/-- The quotient killing outside generators is the original Stanley face ring
of the lower subposet, as an actual algebra equivalence. -/
def lowerIdealFaceQuotientEquiv (Q : FaceLowerIdeal P) :
    faceRestrictionQuotient K hs Q.carrier ≃ₐ[K] FaceRing K (lowerIdealIsSimplicial hs Q) :=
  (Ideal.quotientEquivAlgOfEq K (lowerIdealFaceRestriction_ker K hs Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lowerIdealFaceRestriction_surjective K hs Q))

theorem lowerIdealChainEmbedding (Q : FaceLowerIdeal P) (a : NonzeroFace Q →₀ ℕ)
    (ha : BarycentricAllowed a) :
    BarycentricAllowed (a.mapDomain (lowerIdealNonzeroEmbedding Q)) := by
  intro p hp q hq
  rw [Finsupp.mapDomain_support_of_injective (lowerIdealNonzeroEmbedding Q).injective] at hp hq
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
  exact ha p' hp' q' hq'

def lowerIdealBarycentricRestriction (Q : FaceLowerIdeal P) :
    BarycentricRing (P := P) K →ₐ[K] BarycentricRing (P := Q) K :=
  (barycentricPresentationEquiv (P := Q) K).symm.toAlgHom.comp
    ((monomialRestriction (lowerIdealNonzeroEmbedding Q) BarycentricAllowed BarycentricAllowed
      barycentricAllowed_divisorClosed barycentricAllowed_divisorClosed
      (lowerIdealChainEmbedding Q)).comp (barycentricPresentationEquiv K).toAlgHom)

@[simp] theorem lowerIdealBarycentricRestriction_mk (Q : FaceLowerIdeal P)
    (f : FacePolynomial (P := P) K) :
    lowerIdealBarycentricRestriction K Q (Ideal.Quotient.mk (barycentricIdeal K) f) =
      Ideal.Quotient.mk (barycentricIdeal (P := Q) K)
        (MvPolynomial.killCompl (lowerIdealNonzeroEmbedding Q).injective f) := rfl

theorem lowerIdealBarycentricRestriction_generator_inside (Q : FaceLowerIdeal P) (p : Q) :
    lowerIdealBarycentricRestriction K Q (barycentricGenerator K p.val) =
      barycentricGenerator K p := by
  by_cases hp : p = ⊥
  · subst p
    change lowerIdealBarycentricRestriction K Q (barycentricGenerator K (⊥ : P)) =
      barycentricGenerator K (⊥ : Q)
    simp only [barycentricGenerator, faceSymbol_bot, map_one]
  · have hpp : p.val ≠ ⊥ := fun h => hp (Subtype.ext h)
    rw [barycentricGenerator, lowerIdealBarycentricRestriction_mk, faceSymbol, dif_neg hpp]
    change Ideal.Quotient.mk (barycentricIdeal (P := Q) K)
      (MvPolynomial.killCompl (lowerIdealNonzeroEmbedding Q).injective
        (X (lowerIdealNonzeroEmbedding Q ⟨p, hp⟩))) = _
    have hh := MvPolynomial.killCompl_rename_app (R := K)
      (lowerIdealNonzeroEmbedding Q).injective (X ⟨p, hp⟩)
    simp only [MvPolynomial.rename_X] at hh
    rw [hh]
    simp only [barycentricGenerator, faceSymbol, dif_neg hp]

theorem lowerIdealBarycentricRestriction_generator_outside (Q : FaceLowerIdeal P)
    (p : P) (hp : p ∉ Q.carrier) :
    lowerIdealBarycentricRestriction K Q (barycentricGenerator K p) = 0 := by
  have hpb : p ≠ ⊥ := fun h => hp (h ▸ Q.bot_mem)
  have hn : (⟨p, hpb⟩ : NonzeroFace P) ∉ Set.range (lowerIdealNonzeroEmbedding Q) :=
    fun h => hp ((lowerIdealNonzeroEmbedding_range Q _).mp h)
  rw [barycentricGenerator, lowerIdealBarycentricRestriction_mk, faceSymbol, dif_neg hpb]
  simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hn, map_zero]

theorem lowerIdealBarycentricRestriction_coefficient (Q : FaceLowerIdeal P)
    (x : BarycentricRing (P := P) K) (a : StandardFaceIndex Q) :
    barycentricMonomialEquiv (P := Q) K (lowerIdealBarycentricRestriction K Q x) a =
      barycentricMonomialEquiv K x
        ⟨a.val.mapDomain (lowerIdealNonzeroEmbedding Q), lowerIdealChainEmbedding Q a.val a.property⟩ := by
  change standardMonomialEquiv BarycentricAllowed barycentricAllowed_divisorClosed
    ((barycentricPresentationEquiv (P := Q) K)
      ((barycentricPresentationEquiv (P := Q) K).symm
        (monomialRestriction (lowerIdealNonzeroEmbedding Q) BarycentricAllowed BarycentricAllowed
          barycentricAllowed_divisorClosed barycentricAllowed_divisorClosed
          (lowerIdealChainEmbedding Q) (barycentricPresentationEquiv K x)))) a = _
  rw [AlgEquiv.apply_symm_apply]
  exact monomialRestriction_coefficient (lowerIdealNonzeroEmbedding Q)
    BarycentricAllowed BarycentricAllowed barycentricAllowed_divisorClosed
    barycentricAllowed_divisorClosed (lowerIdealChainEmbedding Q) _ a

def lowerIdealChainLift (Q : FaceLowerIdeal P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∈ Q.carrier) : StandardFaceIndex Q :=
  ⟨a.val.comapDomain (lowerIdealNonzeroEmbedding Q) (lowerIdealNonzeroEmbedding Q).injective.injOn, by
    intro p hp q hq
    apply a.property (lowerIdealNonzeroEmbedding Q p) ?_ (lowerIdealNonzeroEmbedding Q q) ?_
    · simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hp
    · simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hq⟩

include hs in
theorem lowerIdealChainLift_map (Q : FaceLowerIdeal P) (a : StandardFaceIndex P)
    (ha : standardCarrier a ∈ Q.carrier) :
    (lowerIdealChainLift Q a ha).val.mapDomain (lowerIdealNonzeroEmbedding Q) = a.val := by
  apply Finsupp.mapDomain_comapDomain _ (lowerIdealNonzeroEmbedding Q).injective
  intro p hp
  apply (lowerIdealNonzeroEmbedding_range Q p).mpr
  exact Q.lower ((standardCarrier_le_iff hs a _).mp le_rfl p hp) ha

include hs in
theorem barycentricRestrictionIdeal_mem_iff_coefficient (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K) :
    x ∈ barycentricRestrictionIdeal K Q ↔
      ∀ a : StandardFaceIndex P, standardCarrier a ∈ Q → barycentricMonomialEquiv K x a = 0 := by
  rw [barycentricRestrictionIdeal_mem_iff K hs Q hQ]
  constructor
  · intro hx a ha
    rw [← barycentricRingEvaluation_coefficient K hs (standardCarrier a) x a le_rfl,
      hx _ ha, map_zero]
    rfl
  · intro hx p hp
    apply (barycentricStandardCoordinates K hs p).injective
    rw [barycentricRingEvaluation_coordinates, map_zero]
    apply Subtype.ext
    ext a
    rw [coefficientSection_apply]
    by_cases ha : standardCarrier a ≤ p
    · rw [if_pos ha, hx a (hQ ha hp)]
      rfl
    · rw [if_neg ha]
      rfl

include hs in
theorem lowerIdealBarycentricRestriction_ker (Q : FaceLowerIdeal P) :
    RingHom.ker (lowerIdealBarycentricRestriction K Q).toRingHom = barycentricRestrictionIdeal K Q.carrier := by
  ext x
  constructor
  · intro hx
    change lowerIdealBarycentricRestriction K Q x = 0 at hx
    rw [barycentricRestrictionIdeal_mem_iff_coefficient K hs Q.carrier Q.lower]
    intro a ha
    have hh := lowerIdealBarycentricRestriction_coefficient K Q x (lowerIdealChainLift Q a ha)
    have he : (⟨(lowerIdealChainLift Q a ha).val.mapDomain (lowerIdealNonzeroEmbedding Q),
        lowerIdealChainEmbedding Q _ (lowerIdealChainLift Q a ha).property⟩ : StandardFaceIndex P) = a :=
      Subtype.ext (lowerIdealChainLift_map hs Q a ha)
    rw [hx, map_zero, Finsupp.zero_apply, he] at hh
    exact hh.symm
  · intro hx
    have hker : barycentricRestrictionIdeal K Q.carrier ≤
        RingHom.ker (lowerIdealBarycentricRestriction K Q).toRingHom := by
      apply Ideal.span_le.mpr
      rintro y ⟨p, hp, rfl⟩
      exact lowerIdealBarycentricRestriction_generator_outside K Q p hp
    exact hker hx

theorem lowerIdealBarycentricRestriction_surjective (Q : FaceLowerIdeal P) :
    Function.Surjective (lowerIdealBarycentricRestriction K Q) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk (barycentricIdeal (P := P) K)
    (MvPolynomial.rename (lowerIdealNonzeroEmbedding Q) f), ?_⟩
  rw [lowerIdealBarycentricRestriction_mk,
    MvPolynomial.killCompl_rename_app (lowerIdealNonzeroEmbedding Q).injective]

def lowerIdealBarycentricQuotientEquiv (Q : FaceLowerIdeal P) :
    barycentricRestrictionQuotient K Q.carrier ≃ₐ[K] BarycentricRing (P := Q) K :=
  (Ideal.quotientEquivAlgOfEq K (lowerIdealBarycentricRestriction_ker K hs Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lowerIdealBarycentricRestriction_surjective K Q))

theorem universalOriginalParameterComparison_lowerIdealKernel (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (Q : FaceLowerIdeal P)
    (x : BarycentricRing (P := P) K) :
    lowerIdealFaceRestriction K hs Q
        ((universalOriginalParameterComparison K hs d hrank).toLinearEquiv x) = 0 ↔
      lowerIdealBarycentricRestriction K Q x = 0 := by
  change _ ∈ RingHom.ker (lowerIdealFaceRestriction K hs Q).toRingHom ↔
    x ∈ RingHom.ker (lowerIdealBarycentricRestriction K Q).toRingHom
  rw [lowerIdealFaceRestriction_ker, lowerIdealBarycentricRestriction_ker K hs]
  exact (Ideal.Quotient.eq_zero_iff_mem.symm).trans
    ((universalOriginalParameterComparison_restrictionKernel K hs d hrank Q.carrier Q.lower x).trans
      Ideal.Quotient.eq_zero_iff_mem)

end FourPapers.Universal

end
end

/- BEGIN OriginalTensorBaseChange.lean -/
section

/-! # Actual tensor extension from the integral quotient rings

The comparison family commutes with usual coefficient maps.  Here these maps
are identified with the canonical maps into genuine tensor-product scalar
extensions, using the already established integral standard bases.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical MvPolynomial
open scoped TensorProduct
variable {I M N K : Type*} [CommRing K]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module K N]

def additiveIntegralSemilinear (f : M →+ N) : M →ₛₗ[Int.castRingHom K] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    exact map_intCast_smul f ℤ K c x

def integralBasisTensorEquiv (b : Module.Basis I ℤ M) (c : Module.Basis I K N) :
    K ⊗[ℤ] M ≃ₗ[K] N :=
  (b.baseChange K).repr.trans c.repr.symm

theorem integralBasisTensorEquiv_tmul
    (b : Module.Basis I ℤ M) (c : Module.Basis I K N)
    (f : M →ₛₗ[Int.castRingHom K] N) (hf : ∀ i, f (b i) = c i)
    (a : K) (x : M) :
    integralBasisTensorEquiv b c (a ⊗ₜ[ℤ] x) = a • f x := by
  apply c.repr.injective
  simp only [integralBasisTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext i
  rw [Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
    basis_repr_baseChange (Int.castRingHom K) b c f hf, Finsupp.mapRange_apply]
  change (b.repr x i) • a = a * (b.repr x i : K)
  rw [Algebra.smul_def, mul_comm]
  rfl

section Poset
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K) (hs : IsSimplicialPoset P)

theorem originalFaceCoefficientChange_standardBasis {L : Type*} [CommRing L]
    (h : K →+* L) (a : StandardFaceIndex P) :
    originalFaceCoefficientChange hs h (standardFaceBasis K hs a) = standardFaceBasis L hs a := by
  rw [standardFaceBasis_apply, standardFaceBasis_apply]
  change originalFaceCoefficientChange hs h
    (Ideal.Quotient.mk (faceIdeal K hs) (monomial a.val 1)) = _
  rw [originalFaceCoefficientChange_mk, MvPolynomial.map_monomial, map_one]
  rfl

theorem originalBarycentricCoefficientChange_standardBasis {L : Type*} [CommRing L]
    (h : K →+* L) (a : StandardFaceIndex P) :
    originalBarycentricCoefficientChange h (barycentricGlobalStandardBasis K a) =
      barycentricGlobalStandardBasis L a := by
  rw [← barycentricGlobalStandardBasis_monomial, ← barycentricGlobalStandardBasis_monomial,
    originalBarycentricCoefficientChange_mk, MvPolynomial.map_monomial, map_one]

def faceIntegralTensorEquiv :
    K ⊗[ℤ] FaceRing ℤ hs ≃ₗ[K] FaceRing K hs :=
  integralBasisTensorEquiv (standardFaceBasis ℤ hs) (standardFaceBasis K hs)

def barycentricIntegralTensorEquiv :
    K ⊗[ℤ] BarycentricRing (P := P) ℤ ≃ₗ[K] BarycentricRing (P := P) K :=
  integralBasisTensorEquiv (barycentricGlobalStandardBasis ℤ) (barycentricGlobalStandardBasis K)

@[simp] theorem faceIntegralTensorEquiv_tmul (a : K) (x : FaceRing ℤ hs) :
    faceIntegralTensorEquiv K hs (a ⊗ₜ[ℤ] x) =
      a • originalFaceCoefficientChange hs (Int.castRingHom K) x :=
  integralBasisTensorEquiv_tmul (standardFaceBasis ℤ hs) (standardFaceBasis K hs)
    (additiveIntegralSemilinear (originalFaceCoefficientChange hs (Int.castRingHom K)).toAddMonoidHom)
    (originalFaceCoefficientChange_standardBasis ℤ hs (Int.castRingHom K)) a x

@[simp] theorem barycentricIntegralTensorEquiv_tmul (a : K)
    (x : BarycentricRing (P := P) ℤ) :
    barycentricIntegralTensorEquiv K (a ⊗ₜ[ℤ] x) =
      a • originalBarycentricCoefficientChange (Int.castRingHom K) x :=
  integralBasisTensorEquiv_tmul (barycentricGlobalStandardBasis ℤ) (barycentricGlobalStandardBasis K)
    (additiveIntegralSemilinear (originalBarycentricCoefficientChange (Int.castRingHom K)).toAddMonoidHom)
    (originalBarycentricCoefficientChange_standardBasis ℤ (Int.castRingHom K)) a x

/-- The family is the genuine tensor extension of its integral member.  No
flatness condition is used: both coefficient rings have the same proven basis. -/
theorem universalOriginalParameterComparison_tensorBaseChange (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d)
    (z : K ⊗[ℤ] BarycentricRing (P := P) ℤ) :
    (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
        (barycentricIntegralTensorEquiv K z) =
      faceIntegralTensorEquiv K hs
        ((universalOriginalParameterComparison ℤ hs d hrank).toLinearEquiv.toLinearMap.baseChange K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [barycentricIntegralTensorEquiv_tmul, LinearEquiv.map_smul,
        LinearMap.baseChange_tmul, faceIntegralTensorEquiv_tmul]
      exact congrArg (fun y => a • y)
        (universalOriginalParameterComparison_baseChange hs (Int.castRingHom K) d hrank x).symm

end Poset
end FourPapers.Universal

end
end

/- BEGIN TheoremOne.lean -/
section

/-! # Theorem 1.1 on the original presentations

All structure fields below are conclusions.  The only mathematical hypotheses
are finiteness, Boolean lower intervals, a commutative coefficient ring, and an
upper bound on face rank.  In particular the coefficient ring need not be a
field, reduced, nonzero, or flat over the integers.

The direction of the equivalence is barycentric to original; its inverse gives
the orientation displayed in the paper.  The grading and filtration are images
of the actual weighted polynomial pieces under the quotient presentations.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open scoped TensorProduct
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem canonicalOriginalComparison_usualFiltered (d : ℕ) (n : ℤ)
    (x : BarycentricRing (P := P) K) :
    canonicalOriginalComparison K hs x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n := by
  rw [usualFaceWeightLevel_eq, usualBarycentricWeightLevel_eq]
  exact canonicalOriginalComparison_filtered K hs d n x

/-- Equality of the induced maps on actual successive quotient modules of the
filtration assigned to the generators in the original polynomial presentations. -/
theorem universalOriginalParameterComparison_usualAssociatedGrade (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) (n : ℤ) :
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d)
      (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
      (universalOriginalParameterComparison_usualWeight K hs d hrank) n =
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
      (canonicalOriginalComparison_usualFiltered K hs d) n := by
  apply weightFiltrationGradeEquiv_eq_of_error_lower
  intro x hx
  rw [usualFaceWeightLevel_eq]
  rw [usualBarycentricWeightLevel_eq] at hx
  exact universalOriginalParameterComparison_error_lower K hs d hrank n x hx

/-- A faithful package of every assertion of Theorem 1.1.  The parameter actions
in `parameterEquiv` send the variable indexed by `i : Fin d` to the sum of the
face generators of rank `i+1`.  Its `overParameters` is an ordinary linear
equivalence over `MvPolynomial (Fin d) K` with exactly those scalar actions. -/
structure TheoremOneComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) where
  parameterEquiv : ParameterEquiv (barycentricParameterAction (P := P) K d)
    (faceParameterAction K hs d)
  stalkEquiv : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)
  evaluation_compat : ∀ (x : BarycentricRing (P := P) K) (p : P),
    faceRingEvaluation K hs p (parameterEquiv.toLinearEquiv x) =
      stalkEquiv.component p (barycentricRingEvaluation K hs p x)
  graded : ∀ (n : ℕ) (x : BarycentricRing (P := P) K),
    parameterEquiv.toLinearEquiv x ∈ usualFaceDegreePiece K hs n ↔
      x ∈ usualBarycentricDegreePiece K n
  filtered : ∀ (n : ℤ) (x : BarycentricRing (P := P) K),
    parameterEquiv.toLinearEquiv x ∈ usualFaceWeightLevel K hs d n ↔
      x ∈ usualBarycentricWeightLevel K d n
  associatedGrade : ∀ n : ℤ,
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d) parameterEquiv.toLinearEquiv filtered n =
    weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
      (usualFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
      (canonicalOriginalComparison_usualFiltered K hs d) n
  relativeEquiv : ∀ Q : Set P,
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    barycentricRelativeParameters K hs d Q ≃ₗ[MvPolynomial (Fin d) K]
      faceRelativeParameters K hs d Q
  relative_apply : ∀ (Q : Set P) (x : barycentricRelative K hs Q),
    (relativeEquiv Q x).val = parameterEquiv.toLinearEquiv x.val
  lowerIdealKernel : ∀ (Q : FaceLowerIdeal P) (x : BarycentricRing (P := P) K),
    lowerIdealFaceRestriction K hs Q (parameterEquiv.toLinearEquiv x) = 0 ↔
      lowerIdealBarycentricRestriction K Q x = 0
  everyRestrictionKernel : ∀ (Q : Set P)
    (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (x : BarycentricRing (P := P) K),
    faceRestrictionMap K hs Q (parameterEquiv.toLinearEquiv x) = 0 ↔
      barycentricRestrictionMap K Q x = 0
  integral : ∀ z : K ⊗[ℤ] BarycentricRing (P := P) ℤ,
    parameterEquiv.toLinearEquiv (barycentricIntegralTensorEquiv K z) =
      faceIntegralTensorEquiv K hs
        ((universalOriginalParameterComparison ℤ hs d hrank).toLinearEquiv.toLinearMap.baseChange K z)

/-- The single coherent integral construction, extended by scalars and then
identified with the ordinary quotient presentations. -/
def theoremOneComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    TheoremOneComparison K hs d hrank where
  parameterEquiv := universalOriginalParameterComparison K hs d hrank
  stalkEquiv := universalCoherentComparison K hs d hrank
  evaluation_compat := originalComparison_evaluation K hs
    (universalCoherentComparison K hs d hrank)
  graded := universalOriginalParameterComparison_usualDegree K hs d hrank
  filtered := universalOriginalParameterComparison_usualWeight K hs d hrank
  associatedGrade := universalOriginalParameterComparison_usualAssociatedGrade K hs d hrank
  relativeEquiv := universalOriginalRelativeParameterComparison K hs d hrank
  relative_apply := fun _ _ => rfl
  lowerIdealKernel := universalOriginalParameterComparison_lowerIdealKernel K hs d hrank
  everyRestrictionKernel := universalOriginalParameterComparison_restrictionKernel K hs d hrank
  integral := universalOriginalParameterComparison_tensorBaseChange K hs d hrank

/-- **Theorem 1.1.**  A coherent graded parameter-module equivalence, integral
base change, the prescribed associated graded map, and every relative kernel,
for every finite simplicial poset and every commutative coefficient ring. -/
theorem theorem_1_1 (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    Nonempty (TheoremOneComparison K hs d hrank) :=
  ⟨theoremOneComparison K hs d hrank⟩

/-- The actual polynomial-parameter-module isomorphism in the paper's displayed
direction.  Grading, filtration and coherence are supplied by `theorem_1_1`. -/
def theoremOneParameterModuleEquiv (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    letI := (faceParameterAction K hs d).toRingHom.toAlgebra
    letI := (barycentricParameterAction (P := P) K d).toRingHom.toAlgebra
    FaceRing K hs ≃ₗ[MvPolynomial (Fin d) K] BarycentricRing (P := P) K :=
  (theoremOneComparison K hs d hrank).parameterEquiv.symm.overParameters

end FourPapers.Universal

end
end

#print axioms FourPapers.Universal.universalOriginalParameterComparison

#print axioms FourPapers.Universal.universalCoherentComparison_spec

#print axioms FourPapers.Universal.universalCoherentComparison_baseChange

#print axioms FourPapers.Universal.originalRelativeComparison

#print axioms FourPapers.Universal.universalOriginalRelativeParameterComparison

#print axioms FourPapers.Universal.universalOriginalParameterComparison_leading

#print axioms FourPapers.Universal.universalOriginalParameterComparison_degree

#print axioms FourPapers.Universal.universalOriginalParameterComparison_associatedGrade

#print axioms FourPapers.Universal.universalOriginalParameterComparison_baseChange

#print axioms FourPapers.Universal.universalOriginalParameterComparison_usualDegree

#print axioms FourPapers.Universal.faceRestrictionIdeal_mem_iff

#print axioms FourPapers.Universal.barycentricRestrictionIdeal_mem_iff

#print axioms FourPapers.Universal.universalOriginalParameterComparison_restrictionKernel

#print axioms FourPapers.Universal.usualFaceWeightLevel_eq

#print axioms FourPapers.Universal.usualBarycentricWeightLevel_eq

#print axioms FourPapers.Universal.universalOriginalParameterComparison_usualWeight

#print axioms FourPapers.Universal.lowerIdealFaceRestriction_generator_inside

#print axioms FourPapers.Universal.lowerIdealFaceRestriction_generator_outside

#print axioms FourPapers.Universal.lowerIdealFaceRestriction_ker

#print axioms FourPapers.Universal.lowerIdealFaceQuotientEquiv

#print axioms FourPapers.Universal.lowerIdealBarycentricQuotientEquiv

#print axioms FourPapers.Universal.universalOriginalParameterComparison_lowerIdealKernel

#print axioms FourPapers.Universal.faceIntegralTensorEquiv_tmul

#print axioms FourPapers.Universal.barycentricIntegralTensorEquiv_tmul

#print axioms FourPapers.Universal.universalOriginalParameterComparison_tensorBaseChange

#print axioms FourPapers.Universal.universalOriginalParameterComparison_usualAssociatedGrade

#print axioms FourPapers.Universal.theorem_1_1

#print axioms FourPapers.Universal.theoremOneParameterModuleEquiv

end
end

/- BEGIN FourPapers/Universal/PrimeCycleFlags.lean -/
section

section
/-! # A prime cycle has no fixed sufficiently fine rank flag

The moved vertices are exactly `ZMod p`; the remaining `r` vertices are fixed.
A nonidentity translation is transitive on the moved vertices because p is
prime.  A flag whose successive rank gaps are less than p therefore cannot
be fixed.  All statements quantify over arbitrary prime p and every r > 0.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
variable (p r : ℕ) [Fact p.Prime]

abbrev PrimeCycleVertex := ZMod p ⊕ Fin r
abbrev PrimeCycleGroup := Multiplicative (ZMod p)

def primeCyclePermutation : PrimeCycleGroup p →* Equiv.Perm (PrimeCycleVertex p r) where
  toFun g := Equiv.sumCongr (Equiv.addLeft g.toAdd) (Equiv.refl (Fin r))
  map_one' := by
    ext x
    rcases x with x | x <;> simp
  map_mul' g h := by
    ext x
    rcases x with x | x <;> simp [add_assoc]

@[simp] theorem primeCyclePermutation_inl (g : PrimeCycleGroup p) (a : ZMod p) :
    primeCyclePermutation p r g (.inl a) = .inl (g.toAdd + a) := rfl

@[simp] theorem primeCyclePermutation_inr (g : PrimeCycleGroup p) (a : Fin r) :
    primeCyclePermutation p r g (.inr a) = .inr a := rfl

/-- Every nonidentity translation is transitive on the moved vertices. -/
theorem primeCycle_fixed_subset_all_moved (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (F : Finset (PrimeCycleVertex p r))
    (hF : F.image (primeCyclePermutation p r g) = F)
    (a : ZMod p) (ha : Sum.inl a ∈ F) : ∀ b : ZMod p, Sum.inl b ∈ F := by
  have hg0 : g.toAdd ≠ 0 := by
    intro h
    apply hg
    exact congrArg Multiplicative.ofAdd h
  have hstep : ∀ x ∈ F, primeCyclePermutation p r g x ∈ F := by
    intro x hx
    rw [← hF]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hn : ∀ n : ℕ, Sum.inl ((n : ZMod p) * g.toAdd + a) ∈ F := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      have hh := hstep _ ih
      simpa only [primeCyclePermutation_inl, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_assoc, add_left_comm] using hh
  intro b
  obtain ⟨n, hn'⟩ := ZMod.natCast_zmod_surjective ((b - a) / g.toAdd)
  have he : (n : ZMod p) * g.toAdd + a = b := by
    rw [hn', div_mul_cancel₀ _ hg0, sub_add_cancel]
  exact he ▸ hn n

def movedVertices : Finset (PrimeCycleVertex p r) := Finset.univ.image Sum.inl

@[simp] theorem movedVertices_card : (movedVertices p r).card = p := by
  rw [movedVertices, Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_univ, ZMod.card]

/-- A rank set has a preceding selected rank within distance p.  Rank zero
is the empty face and need not belong to the selected set. -/
def PrimeFineRanks (p : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, 0 < n → ∃ m, m < n ∧ (m = 0 ∨ m ∈ S) ∧ n - m < p

/-- A literal chain of subsets with exactly the prescribed ranks. -/
structure RankFlag (V : Type*) (S : Finset ℕ) where
  face : {i : ℕ // i ∈ S} → Finset V
  card : ∀ i, (face i).card = i.val
  nested : ∀ i j, i.val ≤ j.val → face i ⊆ face j

theorem primeCycle_fixed_flag_no_moved (S : Finset ℕ) (hS : PrimeFineRanks p S)
    (F : RankFlag (PrimeCycleVertex p r) S)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfixed : ∀ i, (F.face i).image (primeCyclePermutation p r g) = F.face i) :
    ∀ i (a : ZMod p), Sum.inl a ∉ F.face i := by
  have hmain : ∀ n, ∀ hn : n ∈ S, ∀ a : ZMod p, Sum.inl a ∉ F.face ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn a ha
      have hn0 : 0 < n := by
        have hp := Finset.card_pos.mpr ⟨Sum.inl a, ha⟩
        rwa [F.card] at hp
      obtain ⟨m, hmn, hm, hgap⟩ := hS n hn hn0
      have hall : movedVertices p r ⊆ F.face ⟨n, hn⟩ := by
        rintro x hx
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
        exact primeCycle_fixed_subset_all_moved p r g hg _ (hfixed ⟨n, hn⟩) a ha b
      rcases hm with rfl | hm
      · have hp := Finset.card_le_card hall
        rw [movedVertices_card, F.card] at hp
        change p ≤ n at hp
        omega
      · have hnone : Disjoint (movedVertices p r) (F.face ⟨m, hm⟩) := by
          apply Finset.disjoint_left.mpr
          intro x hx hxm
          obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
          exact ih m hmn hm b hxm
        have hsub : movedVertices p r ⊆ F.face ⟨n, hn⟩ \ F.face ⟨m, hm⟩ := by
          intro x hx
          exact Finset.mem_sdiff.mpr ⟨hall hx, Finset.disjoint_left.mp hnone hx⟩
        have hp := Finset.card_le_card hsub
        rw [movedVertices_card, Finset.card_sdiff_of_subset (F.nested _ _ hmn.le),
          F.card, F.card] at hp
        change p ≤ n - m at hp
        omega
  intro i a
  exact hmain i.val i.property a

/-- With the full rank selected, the preceding statement excludes every
nonidentity stabilizer of the actual rank flag. -/
theorem primeCycle_rankFlag_not_fixed (S : Finset ℕ) (hS : PrimeFineRanks p S)
    (htop : p + r ∈ S) (F : RankFlag (PrimeCycleVertex p r) S)
    (g : PrimeCycleGroup p) (hg : g ≠ 1) :
    ¬ ∀ i, (F.face i).image (primeCyclePermutation p r g) = F.face i := by
  intro hfixed
  have hcard : (F.face ⟨p + r, htop⟩).card = Fintype.card (PrimeCycleVertex p r) := by
    rw [F.card, Fintype.card_sum, ZMod.card, Fintype.card_fin]
  have hfull : F.face ⟨p + r, htop⟩ = Finset.univ :=
    (F.face ⟨p + r, htop⟩).eq_univ_of_card hcard
  have hnone := primeCycle_fixed_flag_no_moved p r S hS F g hg hfixed ⟨p + r, htop⟩ 0
  exact hnone (by rw [hfull]; exact Finset.mem_univ _)

/-- These are exactly the positive coefficient ranks of
`(1+T^p) ∏(1+b_i T)` for algebraically independent b_i. -/
def primeCycleActiveRanks : Finset ℕ :=
  (Finset.Icc 1 r) ∪ Finset.Icc p (p + r)

theorem primeCycleActiveRanks_fine (hr : 0 < r) :
    PrimeFineRanks p (primeCycleActiveRanks p r) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  intro n hn hn0
  rcases Finset.mem_union.mp hn with hn | hn
  · have hn' := Finset.mem_Icc.mp hn
    refine ⟨n - 1, by omega, ?_, by omega⟩
    by_cases he : n = 1
    · left
      omega
    · right
      apply Finset.mem_union_left
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · have hn' := Finset.mem_Icc.mp hn
    by_cases he : n = p
    · by_cases hrp : r < p
      · refine ⟨r, by omega, Or.inr ?_, by omega⟩
        exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hr, le_rfl⟩)
      · refine ⟨p - 1, by omega, Or.inr ?_, by omega⟩
        exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · refine ⟨n - 1, by omega, Or.inr ?_, by omega⟩
      exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem primeCycleActiveRanks_top : p + r ∈ primeCycleActiveRanks p r :=
  Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨Nat.le_add_right p r, le_rfl⟩)

/-- The concrete prime-cycle active ranks have no fixed flag. -/
theorem primeCycleActiveFlag_not_fixed (hr : 0 < r)
    (F : RankFlag (PrimeCycleVertex p r) (primeCycleActiveRanks p r))
    (g : PrimeCycleGroup p) (hg : g ≠ 1) :
    ¬ ∀ i, (F.face i).image (primeCyclePermutation p r g) = F.face i :=
  primeCycle_rankFlag_not_fixed p r _ (primeCycleActiveRanks_fine p r hr)
    (primeCycleActiveRanks_top p r) F g hg

end FourPapers.Universal

#print axioms FourPapers.Universal.primeCycle_fixed_subset_all_moved

#print axioms FourPapers.Universal.primeCycleActiveRanks_fine

#print axioms FourPapers.Universal.primeCycleActiveFlag_not_fixed

end
end
end

/- BEGIN FourPapers/Universal/ColorfulMonomials.lean -/
section

section
/-! # Proper coloring and the actual color-graded monomial basis

The indexing equivalence in this file uses the usual sum of vertex exponents
of each color.  Its inverse assigns the given color exponent to the unique
vertex of that color in a face.  It applies to arbitrary finite properly
colored complexes, including rank-colored order complexes.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable {V C : Type*} [Fintype V] [Fintype C]

structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)

namespace ProperlyColoredComplex
variable (D : ProperlyColoredComplex V C)

def allowed (a : V →₀ ℕ) : Prop := D.face a.support

theorem allowed_divisorClosed : IsDivisorClosed D.allowed := by
  intro a b hab hb
  exact D.downward (Finsupp.support_mono hab) hb

def colorDegree (a : V →₀ ℕ) : C →₀ ℕ := a.mapDomain D.color

theorem colorDegree_support (a : V →₀ ℕ) :
    (D.colorDegree a).support = a.support.image D.color :=
  Finsupp.support_mapDomain_of_nonneg (fun _ => Nat.zero_le _) D.color

theorem colorDegree_at_vertex (a : V →₀ ℕ) (ha : D.allowed a) (v : V)
    (hv : v ∈ a.support) : D.colorDegree a (D.color v) = a v := by
  exact Finsupp.mapDomain_apply' (a.support : Set V) a (fun _ h => h)
    (D.proper a.support ha) hv

abbrev FaceWithColors (S : Finset C) :=
  {s : Finset V // D.face s ∧ s.image D.color = S}

abbrev MonomialOfColorDegree (β : C →₀ ℕ) :=
  {a : V →₀ ℕ // D.allowed a ∧ D.colorDegree a = β}

def exponentOnFace (β : C →₀ ℕ) (s : Finset V) : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => if v ∈ s then β (D.color v) else 0)

@[simp] theorem exponentOnFace_apply (β : C →₀ ℕ) (s : Finset V) (v : V) :
    D.exponentOnFace β s v = if v ∈ s then β (D.color v) else 0 := rfl

theorem exponentOnFace_support (β : C →₀ ℕ) (s : D.FaceWithColors β.support) :
    (D.exponentOnFace β s.val).support = s.val := by
  ext v
  rw [Finsupp.mem_support_iff, exponentOnFace_apply]
  by_cases hv : v ∈ s.val
  · rw [if_pos hv]
    have hc : D.color v ∈ β.support := by
      rw [← s.property.2]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact iff_of_true (Finsupp.mem_support_iff.mp hc) hv
  · simp [hv]

theorem exponentOnFace_allowed (β : C →₀ ℕ) (s : D.FaceWithColors β.support) :
    D.allowed (D.exponentOnFace β s.val) := by
  unfold allowed
  rw [exponentOnFace_support]
  exact s.property.1

theorem exponentOnFace_colorDegree (β : C →₀ ℕ) (s : D.FaceWithColors β.support) :
    D.colorDegree (D.exponentOnFace β s.val) = β := by
  ext i
  by_cases hi : i ∈ β.support
  · have his : i ∈ s.val.image D.color := s.property.2.symm ▸ hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp his
    rw [D.colorDegree_at_vertex _ (D.exponentOnFace_allowed β s) v
      (by rw [D.exponentOnFace_support]; exact hv), exponentOnFace_apply, if_pos hv]
  · have hi' : i ∉ (D.colorDegree (D.exponentOnFace β s.val)).support := by
      rw [D.colorDegree_support, D.exponentOnFace_support, s.property.2]
      exact hi
    rw [Finsupp.notMem_support_iff.mp hi', Finsupp.notMem_support_iff.mp hi]

/-- The genuine color degree piece is indexed by faces having exactly the
positive colors, for arbitrary exponents and arbitrary coefficient rings. -/
def monomialColorEquiv (β : C →₀ ℕ) :
    D.MonomialOfColorDegree β ≃ D.FaceWithColors β.support where
  toFun a := ⟨a.val.support, a.property.1, by
    rw [← D.colorDegree_support, a.property.2]⟩
  invFun s := ⟨D.exponentOnFace β s.val, D.exponentOnFace_allowed β s,
    D.exponentOnFace_colorDegree β s⟩
  left_inv a := by
    apply Subtype.ext
    ext v
    rw [D.exponentOnFace_apply]
    by_cases hv : v ∈ a.val.support
    · rw [if_pos hv]
      have hh := congrArg (fun γ : C →₀ ℕ => γ (D.color v)) a.property.2
      exact hh.symm.trans (D.colorDegree_at_vertex a.val a.property.1 v hv)
    · rw [if_neg hv, Finsupp.notMem_support_iff.mp hv]
  right_inv s := Subtype.ext (D.exponentOnFace_support β s)

variable (K : Type*) [CommRing K]

abbrev Ring := MonomialQuotient (K := K) D.allowed

def monomial (a : V →₀ ℕ) : D.Ring K :=
  Ideal.Quotient.mk (forbiddenIdeal D.allowed) (MvPolynomial.monomial a (1 : K))

def colorParameter (i : C) : D.Ring K :=
  ∑ v ∈ Finset.univ.filter (fun v => D.color v = i),
    Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X v)

theorem monomial_eq_zero_of_forbidden (a : V →₀ ℕ) (ha : ¬ D.allowed a) :
    D.monomial K a = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨a, ha, rfl⟩

theorem variable_mul_monomial (v : V) (a : V →₀ ℕ) :
    Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X v) * D.monomial K a =
      D.monomial K (Finsupp.single v 1 + a) := by
  rw [monomial, ← map_mul]
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  rfl

theorem color_collision_forbidden (a : V →₀ ℕ) (ha : D.allowed a)
    (v w : V) (hw : w ∈ a.support) (hc : D.color v = D.color w) (hne : v ≠ w) :
    ¬ D.allowed (Finsupp.single v 1 + a) := by
  intro hall
  have hface : D.face ((Finsupp.single v 1 + a).support) := hall
  have hproper := D.proper ((Finsupp.single v 1 + a).support) hface
  have hv : v ∈ (Finsupp.single v 1 + a).support := by
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hw' : w ∈ (Finsupp.single v 1 + a).support :=
    Finsupp.support_mono (le_add_self : a ≤ Finsupp.single v 1 + a) hw
  exact hne (hproper hv hw' hc)

/-- Once a color is already present, multiplication by its color sum raises
exactly the exponent of its unique vertex; every other summand is a nonface. -/
theorem colorParameter_mul_of_present (a : V →₀ ℕ) (ha : D.allowed a)
    (w : V) (hw : w ∈ a.support) :
    D.colorParameter K (D.color w) * D.monomial K a =
      D.monomial K (Finsupp.single w 1 + a) := by
  rw [colorParameter, Finset.sum_mul]
  rw [Finset.sum_eq_single w]
  · exact D.variable_mul_monomial K w a
  · intro v hv hvw
    rw [D.variable_mul_monomial]
    exact D.monomial_eq_zero_of_forbidden K _
      (D.color_collision_forbidden a ha v w hw (Finset.mem_filter.mp hv).2 hvw)
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ w, rfl⟩)).elim

end ProperlyColoredComplex

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The rank-selected order complex, with its actual proper rank coloring. -/
def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ProperlyColoredComplex (NonzeroFace P) (Fin d) where
  face s := ∀ p ∈ s, ∀ q ∈ s, p.val ≤ q.val ∨ q.val ≤ p.val
  downward := by
    intro s t hst ht p hp q hq
    exact ht p (hst hp) q (hst hq)
  color p := ⟨faceRank p.val - 1, by
    have hpos : 0 < faceRank p.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr p.property)
    have hbound := hrank p.val
    omega⟩
  proper s hs' p hp q hq he := by
    have hpos (v : NonzeroFace P) : 0 < faceRank v.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr v.property)
    have hr : faceRank p.val = faceRank q.val := by
      have hh := congrArg Fin.val he
      have hp' := hpos p
      have hq' := hpos q
      dsimp at hh
      omega
    apply Subtype.ext
    rcases hs' p hp q hq with hpq | hqp
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hpq hn))) hr
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hqp (Ne.symm hn)))) hr.symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/FiniteOrbitObstruction.lean -/
section

section

/-! # A direct modular obstruction from freely permuted components

An invariant functional vanishes on invariant vectors when the identity is a
sum of freely permuted component operators and the group order is zero in the
coefficient ring. No group-algebra projectivity criterion is required.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {G T K M N : Type*} [Group G] [Fintype G] [Fintype T]
  [MulAction G T] [CommRing K]

/-- A free orbit is explicitly in bijection with the acting group. -/
def freeOrbitEquiv (hfree : ∀ t : T, Function.Injective (fun g : G => g • t)) (t : T) :
    G ≃ MulAction.orbit G t :=
  Equiv.ofBijective (fun g => ⟨g • t, MulAction.mem_orbit t g⟩)
    ⟨fun g h he => hfree t (congrArg Subtype.val he), by
      rintro ⟨s, hs⟩
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hs
      exact ⟨g, Subtype.ext hg⟩⟩

theorem sum_eq_zero_of_free_action
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : K) = 0) (f : T → K)
    (hf : ∀ (g : G) (t : T), f (g • t) = f t) : ∑ t, f t = 0 := by
  let Q := MulAction.orbitRel.Quotient G T
  letI : Fintype Q := Fintype.ofFinite _
  letI (q : Q) : Fintype (MulAction.orbit G q.out) := Fintype.ofFinite _
  calc
    (∑ t, f t) = ∑ q : (Σ q : Q, MulAction.orbit G q.out), f q.2.val :=
      Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits G T) _ _ (fun _ => rfl)
    _ = ∑ q : Q, ∑ t : MulAction.orbit G q.out, f t.val := Fintype.sum_sigma _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have he := Fintype.sum_equiv (freeOrbitEquiv hfree q.out)
        (fun g : G => f (g • q.out))
        (fun t : MulAction.orbit G q.out => f t.val) (fun _ => rfl)
      rw [← he]
      simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, horder, zero_mul]

variable [AddCommGroup M] [Module K M]

/-- A partition of the identity into component operators is enough for the
obstruction; orthogonality and idempotence need not be assumed here. -/
theorem invariantFunctional_eq_zero_of_free_components
    (ρ : G →* Module.End K M) (component : T → Module.End K M)
    (hidentity : ∀ x, ∑ t, component t x = x)
    (hcovariant : ∀ g t x, component (g • t) (ρ g x) = ρ g (component t x))
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : K) = 0)
    (ℓ : M →ₗ[K] K) (hℓ : ∀ g x, ℓ (ρ g x) = ℓ x)
    (v : M) (hv : ∀ g, ρ g v = v) : ℓ v = 0 := by
  have hf : ∀ (g : G) (t : T), ℓ (component (g • t) v) = ℓ (component t v) := by
    intro g t
    calc
      ℓ (component (g • t) v) = ℓ (component (g • t) (ρ g v)) := by rw [hv]
      _ = ℓ (ρ g (component t v)) := congrArg ℓ (hcovariant g t v)
      _ = ℓ (component t v) := hℓ g (component t v)
  calc
    ℓ v = ℓ (∑ t, component t v) := congrArg ℓ (hidentity v).symm
    _ = ∑ t, ℓ (component t v) := map_sum ℓ _ _
    _ = 0 := sum_eq_zero_of_free_action hfree horder _ hf

variable [AddCommGroup N] [Module K N] [Nontrivial K]

/-- An equivariant augmentation split by an invariant vector cannot be
transported to such a freely decomposed module in modular characteristic. -/
theorem no_equivariant_equiv_of_free_components
    (ρM : G →* Module.End K M) (ρN : G →* Module.End K N)
    (component : T → Module.End K N)
    (hidentity : ∀ x, ∑ t, component t x = x)
    (hcovariant : ∀ g t x, component (g • t) (ρN g x) = ρN g (component t x))
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : K) = 0)
    (ℓ : M →ₗ[K] K) (hℓ : ∀ g x, ℓ (ρM g x) = ℓ x)
    (v : M) (hv : ∀ g, ρM g v = v) (hvalue : ℓ v = 1)
    (e : M ≃ₗ[K] N) (he : ∀ g x, e (ρM g x) = ρN g (e x)) : False := by
  have hinv : ∀ g, ρN g (e v) = e v := by
    intro g
    rw [← he, hv]
  have heInv : ∀ g x, e.symm (ρN g x) = ρM g (e.symm x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  have hfunctional : ∀ g x, (ℓ.comp e.symm.toLinearMap) (ρN g x) =
      (ℓ.comp e.symm.toLinearMap) x := by
    intro g x
    change ℓ (e.symm (ρN g x)) = ℓ (e.symm x)
    rw [heInv, hℓ]
  have hzero := invariantFunctional_eq_zero_of_free_components ρN component
    hidentity hcovariant hfree horder (ℓ.comp e.symm.toLinearMap) hfunctional (e v) hinv
  have hone : (1 : K) = 0 := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      hvalue] using hzero
  exact one_ne_zero hone

end FourPapers.Universal
end
end
end

/- BEGIN FourPapers/Universal/CyclicRankReduction.lean -/
section


section

/-! # Only prime top rank needs modular lifting

If `(d - 1)!` is invertible, ordinary averaging is available in every smaller
rank.  It is also available in rank `d` unless `d` itself is prime.  The only
remaining local construction is therefore the regular action of a cyclic
group of prime order on a simplex of that same rank.
-/

namespace FourPapers.Universal

variable {K : Type*} [CommRing K]

theorem lower_rank_factorial_isUnit {d r : ℕ} (hrd : r < d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    IsUnit ((r.factorial : ℕ) : K) := by
  apply isUnit_of_dvd_unit _ hD
  exact map_dvd (Nat.castRingHom K)
    (Nat.factorial_dvd_factorial (by omega : r ≤ d - 1))

theorem composite_rank_isUnit {d : ℕ} (hd : 1 ≤ d) (hp : ¬d.Prime)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) : IsUnit (d : K) := by
  by_cases hdone : d = 1
  · subst d
    simp
  have hd2 : 2 ≤ d := by omega
  obtain ⟨a, b, had, hbd, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hd2).mp hp
  have ha : 0 < a := by
    by_contra hn
    have hzero : a = 0 := by omega
    simp [hzero] at hab
    omega
  have hb : 0 < b := by
    by_contra hn
    have hzero : b = 0 := by omega
    simp [hzero] at hab
    omega
  have hau : IsUnit (a : K) := isUnit_of_dvd_unit
    (map_dvd (Nat.castRingHom K) (Nat.dvd_factorial ha (by omega : a ≤ d - 1))) hD
  have hbu : IsUnit (b : K) := isUnit_of_dvd_unit
    (map_dvd (Nat.castRingHom K) (Nat.dvd_factorial hb (by omega : b ≤ d - 1))) hD
  simpa only [← Nat.cast_mul, hab] using hau.mul hbu

theorem full_factorial_isUnit_or_prime {d : ℕ} (hd : 1 ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    IsUnit ((d.factorial : ℕ) : K) ∨ d.Prime := by
  by_cases hp : d.Prime
  · exact Or.inr hp
  · left
    have hu := (composite_rank_isUnit hd hp hD).mul hD
    simpa only [← Nat.cast_mul, Nat.mul_factorial_pred (by omega : d ≠ 0)] using hu

/-- The exact exceptional branch needed for the positive implication of
Theorem 1.3. -/
theorem factorial_rank_exception {d r : ℕ} (hd : 1 ≤ d) (hrd : r ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    IsUnit ((r.factorial : ℕ) : K) ∨ (r = d ∧ d.Prime) := by
  rcases lt_or_eq_of_le hrd with hlt | rfl
  · exact Or.inl (lower_rank_factorial_isUnit hlt hD)
  · rcases full_factorial_isUnit_or_prime hd hD with hu | hp
    · exact Or.inl hu
    · exact Or.inr ⟨rfl, hp⟩

end FourPapers.Universal

end
end

/- BEGIN FourPapers/Universal/CyclicRelativeInjectivity.lean -/
section


section

/-! # Relative injectivity of regular permutation modules

The extension in this file is the elementary coinduction argument used in
Section 8 of the paper.  The inclusion is required only to split over the
coefficient ring; its chosen splitting need not be equivariant.
-/

noncomputable section

namespace FourPapers.Universal

/-- A linear group representation, definitionally the standard Mathlib `Representation`. -/
abbrev CyclicRepresentation (K G M : Type*) [CommRing K] [Group G]
    [AddCommGroup M] [Module K M] := G →* (M →ₗ[K] M)

variable {K G M N C T : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup C] [Module K C] [AddCommGroup T] [Module K T]

/-- Left translation on functions, in the usual contragredient convention. -/
def coinducedRepresentation : CyclicRepresentation K G (G → C) where
  toFun g :=
    { toFun := fun f h => f (g⁻¹ * h)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f h; simp
  map_mul' g h := by
    ext f x
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    simp [mul_assoc]

@[simp] theorem coinducedRepresentation_apply (g : G) (f : G → C) (h : G) :
    coinducedRepresentation (K := K) (C := C) g f h = f (g⁻¹ * h) := rfl

/-- Equivariance of a coefficient-linear map between two representations. -/
def RepresentationIntertwines (ρ : CyclicRepresentation K G M)
    (τ : CyclicRepresentation K G N) (f : M →ₗ[K] N) : Prop :=
  ∀ g x, f (ρ g x) = τ g (f x)

/-- Coinduction extends a map using just the identity coordinate. -/
def coinducedExtension (ρ : CyclicRepresentation K G N)
    (s : N →ₗ[K] M) (f : M →ₗ[K] (G → C)) : N →ₗ[K] (G → C) where
  toFun n h := f (s (ρ h⁻¹ n)) 1
  map_add' x y := by ext h; simp
  map_smul' a x := by ext h; simp

theorem coinducedExtension_equivariant (ρ : CyclicRepresentation K G N)
    (s : N →ₗ[K] M) (f : M →ₗ[K] (G → C)) :
    RepresentationIntertwines ρ coinducedRepresentation (coinducedExtension ρ s f) := by
  intro g n
  ext h
  change f (s (ρ h⁻¹ (ρ g n))) 1 = f (s (ρ (g⁻¹ * h)⁻¹ n)) 1
  rw [mul_inv_rev, inv_inv, ρ.map_mul]
  rfl

theorem coinducedExtension_restrict
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] (G → C))
    (hf : RepresentationIntertwines ρ coinducedRepresentation f) :
    (coinducedExtension τ s f).comp i = f := by
  ext m h
  change f (s (τ h⁻¹ (i m))) 1 = f m h
  rw [← hi]
  have hsi : s (i (ρ h⁻¹ m)) = ρ h⁻¹ m :=
    congrArg (fun q : M →ₗ[K] M => q (ρ h⁻¹ m)) hs
  rw [hsi]
  have hh := congrFun (hf h⁻¹ m) 1
  simpa only [coinducedRepresentation_apply, inv_inv, mul_one] using hh

/-- Every map into a coinduced module extends along an equivariant inclusion
that splits over the coefficient ring. -/
theorem exists_equivariantExtension_coinduced
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] (G → C))
    (hf : RepresentationIntertwines ρ coinducedRepresentation f) :
    ∃ F : N →ₗ[K] (G → C),
      RepresentationIntertwines τ coinducedRepresentation F ∧ F.comp i = f :=
  ⟨coinducedExtension τ s f, coinducedExtension_equivariant τ s f,
    coinducedExtension_restrict ρ τ i s hi hs f hf⟩

/-- Relative injectivity is transported across an actual equivariant linear
equivalence; in applications its coordinates are the free orbits of a
permutation basis. -/
theorem exists_equivariantExtension_of_coinduced
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G T) (e : T ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines υ coinducedRepresentation e.toLinearMap)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] T) (hf : RepresentationIntertwines ρ υ f) :
    ∃ F : N →ₗ[K] T, RepresentationIntertwines τ υ F ∧ F.comp i = f := by
  have hf' : RepresentationIntertwines ρ coinducedRepresentation
      (e.toLinearMap.comp f) := by
    intro g m
    change e (f (ρ g m)) = coinducedRepresentation (K := K) (C := C) g (e (f m))
    have hh := he g (f m)
    change e (υ g (f m)) = coinducedRepresentation (K := K) (C := C) g (e (f m)) at hh
    exact (congrArg e (hf g m)).trans hh
  obtain ⟨F, hF, hFi⟩ := exists_equivariantExtension_coinduced ρ τ i s hi hs
    (e.toLinearMap.comp f) hf'
  refine ⟨e.symm.toLinearMap.comp F, ?_, ?_⟩
  · intro g n
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    have hh := he g (e.symm (F n))
    change e (υ g (e.symm (F n))) =
      coinducedRepresentation (K := K) (C := C) g (e (e.symm (F n))) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact (hF g n).trans hh.symm
  · ext m
    apply e.injective
    simpa using congrArg (fun q : M →ₗ[K] (G → C) => q m) hFi

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPermutationInjectivity.lean -/
section


section

/-! # Free permutation coordinates are coinduced

This file proves the free-orbit case of the relative-injectivity assertion in
Section 8.  No field assumption and no division by the group order occur.
-/

noncomputable section

namespace FourPapers.Universal

open Classical

variable {K G X : Type*} [CommRing K] [Group G] [MulAction G X]

def permutationFunctionRepresentation : CyclicRepresentation K G (X → K) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹ • x)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by
    ext f x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    simp [mul_smul]

@[simp] theorem permutationFunctionRepresentation_apply (g : G) (f : X → K) (x : X) :
    permutationFunctionRepresentation (K := K) g f x = f (g⁻¹ • x) := rfl

theorem freeOrbitCoordinate_bijective
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    Function.Bijective
      (fun a : G × MulAction.orbitRel.Quotient G X => a.1 • a.2.out) := by
  constructor
  · rintro ⟨g, q⟩ ⟨h, r⟩ heq
    have hqr : q = r := by
      have h := congrArg (fun x : X => (Quotient.mk'' x :
        MulAction.orbitRel.Quotient G X)) heq
      simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq,
        Quotient.out_eq'] using h
    subst r
    change g • q.out = h • q.out at heq
    have hhg : h⁻¹ * g = 1 := hf _ q.out (by
      rw [mul_smul, heq, inv_smul_smul])
    have hgh : g = h := by
      calc
        g = h * (h⁻¹ * g) := by simp
        _ = h := by rw [hhg, mul_one]
    subst h
    rfl
  · intro x
    let q : MulAction.orbitRel.Quotient G X := Quotient.mk'' x
    have hx : q.out ∈ MulAction.orbit G x :=
      Quotient.exact (Quotient.out_eq' q)
    obtain ⟨g, hg⟩ := hx
    refine ⟨(g⁻¹, q), ?_⟩
    change g⁻¹ • q.out = x
    rw [← hg, inv_smul_smul]

def freeOrbitCoordinateEquiv
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    (G × MulAction.orbitRel.Quotient G X) ≃ X :=
  Equiv.ofBijective _ (freeOrbitCoordinate_bijective hf)

@[simp] theorem freeOrbitCoordinateEquiv_apply
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1)
    (g : G) (q : MulAction.orbitRel.Quotient G X) :
    freeOrbitCoordinateEquiv hf (g, q) = g • q.out := rfl

/-- A free permutation representation is a product of regular function
representations, with one coordinate for each orbit. -/
def freePermutationCoinducedEquiv
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    (X → K) ≃ₗ[K] (G → MulAction.orbitRel.Quotient G X → K) where
  toFun f g q := f (g • q.out)
  invFun f x :=
    let a := (freeOrbitCoordinateEquiv hf).symm x
    f a.1 a.2
  left_inv f := by
    funext x
    change f (freeOrbitCoordinateEquiv hf
      ((freeOrbitCoordinateEquiv hf).symm x)) = f x
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    funext g q
    change f (((freeOrbitCoordinateEquiv hf).symm
      (freeOrbitCoordinateEquiv hf (g, q))).1)
      (((freeOrbitCoordinateEquiv hf).symm
      (freeOrbitCoordinateEquiv hf (g, q))).2) = f g q
    rw [Equiv.symm_apply_apply]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem freePermutationCoinducedEquiv_equivariant
    (hf : ∀ (g : G) (x : X), g • x = x → g = 1) :
    RepresentationIntertwines permutationFunctionRepresentation coinducedRepresentation
      (freePermutationCoinducedEquiv (K := K) hf).toLinearMap := by
  intro g f
  ext h q
  change f (g⁻¹ • (h • q.out)) = f ((g⁻¹ * h) • q.out)
  rw [mul_smul]

variable {M N : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- The free permutation case of Section 8's relative injectivity statement,
proved by explicit regular-orbit coordinates. -/
theorem exists_equivariantExtension_freePermutation
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (i : M →ₗ[K] N) (s : N →ₗ[K] M)
    (hi : RepresentationIntertwines ρ τ i)
    (hs : s.comp i = LinearMap.id)
    (f : M →ₗ[K] (X → K))
    (hf : RepresentationIntertwines ρ permutationFunctionRepresentation f) :
    ∃ F : N →ₗ[K] (X → K),
      RepresentationIntertwines τ permutationFunctionRepresentation F ∧ F.comp i = f :=
  exists_equivariantExtension_of_coinduced ρ τ permutationFunctionRepresentation
    (freePermutationCoinducedEquiv hfree)
    (freePermutationCoinducedEquiv_equivariant hfree) i s hi hs f hf

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicEquivariantChoice.lean -/
section


section

/-! # Equivariant choices from stabilizer-fixed local choices

Choices are made once on each orbit and transported.  The stabilizer
condition is proved sufficient for independence of the transporting group
element.  In the free-action case this condition is automatic.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

def orbitChoiceRepresentative (x : X) : X :=
  (Quotient.mk'' x : MulAction.orbitRel.Quotient G X).out

theorem exists_orbitChoiceTransport (x : X) :
    ∃ g : G, g • orbitChoiceRepresentative (G := G) x = x := by
  let q : MulAction.orbitRel.Quotient G X := Quotient.mk'' x
  have hx : q.out ∈ MulAction.orbit G x := Quotient.exact (Quotient.out_eq' q)
  obtain ⟨g, hg⟩ := hx
  refine ⟨g⁻¹, ?_⟩
  change g⁻¹ • q.out = x
  rw [← hg, inv_smul_smul]

def orbitChoiceTransport (x : X) : G := (exists_orbitChoiceTransport (G := G) x).choose

theorem orbitChoiceTransport_spec (x : X) :
    orbitChoiceTransport (G := G) x • orbitChoiceRepresentative (G := G) x = x :=
  (exists_orbitChoiceTransport (G := G) x).choose_spec

theorem orbitChoiceRepresentative_smul (g : G) (x : X) :
    orbitChoiceRepresentative (G := G) (g • x) = orbitChoiceRepresentative (G := G) x := by
  unfold orbitChoiceRepresentative
  apply congrArg (fun q : MulAction.orbitRel.Quotient G X => q.out)
  apply Quotient.sound
  exact ⟨g, rfl⟩

theorem exists_equivariant_choice (R : X → Y → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hfixed : ∀ x : X, ∃ y : Y, R x y ∧ ∀ g : G, g • x = x → g • y = y) :
    ∃ f : X → Y, (∀ x, R x (f x)) ∧ ∀ (g : G) x, f (g • x) = g • f x := by
  choose y hyR hyfix using hfixed
  let f : X → Y := fun x => orbitChoiceTransport (G := G) x • y (orbitChoiceRepresentative (G := G) x)
  refine ⟨f, ?_, ?_⟩
  · intro x
    have hh := hR (orbitChoiceTransport (G := G) x)
      (orbitChoiceRepresentative (G := G) x) (y (orbitChoiceRepresentative (G := G) x))
      (hyR (orbitChoiceRepresentative (G := G) x))
    rw [orbitChoiceTransport_spec] at hh
    exact hh
  · intro h x
    let r := orbitChoiceRepresentative (G := G) x
    let a := orbitChoiceTransport (G := G) x
    let b := orbitChoiceTransport (G := G) (h • x)
    have ha : a • r = x := orbitChoiceTransport_spec (G := G) x
    have hb : b • r = h • x := by
      simpa only [orbitChoiceRepresentative_smul] using (orbitChoiceTransport_spec (G := G) (h • x))
    have hk : (b⁻¹ * h * a) • r = r := by
      rw [mul_smul, mul_smul, ha, ← hb, inv_smul_smul]
    have hy : (b⁻¹ * h * a) • y r = y r := hyfix r _ hk
    have hh := congrArg (fun z : Y => b • z) hy
    simp only [mul_smul, smul_inv_smul] at hh
    change b • y (orbitChoiceRepresentative (G := G) (h • x)) = h • (a • y r)
    rw [orbitChoiceRepresentative_smul]
    exact hh.symm

theorem exists_equivariant_choice_of_free (R : X → Y → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (hne : ∀ x : X, ∃ y : Y, R x y) :
    ∃ f : X → Y, (∀ x, R x (f x)) ∧ ∀ (g : G) x, f (g • x) = g • f x := by
  apply exists_equivariant_choice R hR
  intro x
  obtain ⟨y, hy⟩ := hne x
  refine ⟨y, hy, ?_⟩
  intro g hg
  rw [hfree g x hg, one_smul]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicEquivariantInduction.lean -/
section


section

/-! # Equivariant extension along a finite rank filtration

At each rank the boundary is already fixed equivariantly.  Stabilizer-fixed
extensions on orbit representatives give a simultaneous equivariant extension
on that rank.  Strict rank growth ensures that no new compatibility equation
relates two distinct faces introduced at the same stage.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {G P Y : Type*} [Group G] [PartialOrder P] [Fintype P]
  [MulAction G P] [MulAction G Y]

def equivariantRankCut (rank : P → ℕ) (n : ℕ) : Set P := {p | rank p < n}

def equivariantRankCutMulAction (rank : P → ℕ) (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (n : ℕ) : MulAction G (equivariantRankCut rank n) where
  smul g p := ⟨g • p.val, by simpa only [equivariantRankCut, Set.mem_setOf_eq, hrank] using p.property⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

def rankLevelMulAction (rank : P → ℕ) (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (n : ℕ) : MulAction G {p : P // rank p = n} where
  smul g p := ⟨g • p.val, (hrank g p.val).trans p.property⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

structure EquivariantRankStage (rank : P → ℕ)
    (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (Good : P → Y → Prop) (Compatible : P → P → Y → Y → Prop) (n : ℕ) where
  value : equivariantRankCut rank n → Y
  good : ∀ p, Good p.val (value p)
  compatible : ∀ p q, q.val < p.val → Compatible p.val q.val (value p) (value q)
  equivariant : ∀ (g : G) p,
    value ⟨g • p.val, by simpa only [equivariantRankCut, Set.mem_setOf_eq, hrank] using p.property⟩ = g • value p

theorem exists_equivariant_rank_family
    (rank : P → ℕ) (hstrict : StrictMono rank)
    (hrank : ∀ (g : G) p, rank (g • p) = rank p)
    (hlt : ∀ (g : G) {p q : P}, p < q → g • p < g • q)
    (Good : P → Y → Prop) (Compatible : P → P → Y → Y → Prop)
    (hGood : ∀ (g : G) p y, Good p y → Good (g • p) (g • y))
    (hCompatible : ∀ (g : G) p q y z,
      Compatible p q y z → Compatible (g • p) (g • q) (g • y) (g • z))
    (hlift : ∀ n (old : EquivariantRankStage rank hrank Good Compatible n)
      (p : P), rank p = n → ∃ y : Y,
        Good p y ∧
        (∀ q : equivariantRankCut rank n, q.val < p → Compatible p q.val y (old.value q)) ∧
        ∀ g : G, g • p = p → g • y = y) :
    ∃ f : P → Y, (∀ p, Good p (f p)) ∧
      (∀ p q, q < p → Compatible p q (f p) (f q)) ∧
      ∀ (g : G) p, f (g • p) = g • f p := by
  have stages : ∀ n, Nonempty (EquivariantRankStage rank hrank Good Compatible n) := by
    intro n
    induction n with
    | zero =>
      exact ⟨{
        value := fun p => False.elim (Nat.not_lt_zero _ p.property)
        good := fun p => False.elim (Nat.not_lt_zero _ p.property)
        compatible := fun p => False.elim (Nat.not_lt_zero _ p.property)
        equivariant := fun g p => False.elim (Nat.not_lt_zero _ p.property) }⟩
    | succ n ih =>
      let old := Classical.choice ih
      letI := rankLevelMulAction rank hrank n
      let R : {p : P // rank p = n} → Y → Prop := fun p y =>
        Good p.val y ∧ ∀ q : equivariantRankCut rank n, q.val < p.val → Compatible p.val q.val y (old.value q)
      have hR : ∀ (g : G) p y, R p y → R (g • p) (g • y) := by
        intro g p y hy
        refine ⟨hGood g p.val y hy.1, ?_⟩
        intro q hqp
        let q' : equivariantRankCut rank n := ⟨g⁻¹ • q.val, by
          simpa only [equivariantRankCut, Set.mem_setOf_eq, hrank] using q.property⟩
        have hq'p : q'.val < p.val := by
          have hh := hlt g⁻¹ hqp
          change g⁻¹ • q.val < g⁻¹ • (g • p.val) at hh
          change g⁻¹ • q.val < p.val
          simpa only [inv_smul_smul] using hh
        have hh := hCompatible g p.val q'.val y (old.value q') (hy.2 q' hq'p)
        have hqeq : g • q'.val = q.val := smul_inv_smul g q.val
        have hv : g • old.value q' = old.value q := by
          rw [← old.equivariant g q']
          congr 1
          exact Subtype.ext hqeq
        change Compatible (g • p.val) q.val (g • y) (old.value q)
        simpa only [hqeq, hv] using hh
      have hfixed : ∀ p : {p : P // rank p = n}, ∃ y : Y,
          R p y ∧ ∀ g : G, g • p = p → g • y = y := by
        intro p
        obtain ⟨y, hy, hb, he⟩ := hlift n old p.val p.property
        exact ⟨y, ⟨hy, hb⟩, fun g hg => he g (congrArg Subtype.val hg)⟩
      obtain ⟨fresh, hfresh, hefresh⟩ := exists_equivariant_choice R hR hfixed
      let value : equivariantRankCut rank (n + 1) → Y := fun p =>
        if h : rank p.val < n then old.value ⟨p.val, h⟩
        else fresh ⟨p.val, by have hp := p.property; change rank p.val < n + 1 at hp; omega⟩
      refine ⟨{ value := value, good := ?_, compatible := ?_, equivariant := ?_ }⟩
      · intro p
        by_cases hp : rank p.val < n
        · simpa only [value, dif_pos hp] using old.good ⟨p.val, hp⟩
        · simpa only [value, dif_neg hp] using (hfresh ⟨p.val, by
            have hh := p.property; change rank p.val < n + 1 at hh; omega⟩).1
      · intro p q hqp
        have hq : rank q.val < n := by
          have hh := hstrict hqp
          have hp := p.property
          change rank p.val < n + 1 at hp
          omega
        by_cases hp : rank p.val < n
        · simpa only [value, dif_pos hp, dif_pos hq] using
            old.compatible ⟨p.val, hp⟩ ⟨q.val, hq⟩ hqp
        · simpa only [value, dif_neg hp, dif_pos hq] using
            (hfresh ⟨p.val, by
              have hh := p.property; change rank p.val < n + 1 at hh; omega⟩).2
                ⟨q.val, hq⟩ hqp
      · intro g p
        by_cases hp : rank p.val < n
        · have hgp : rank (g • p.val) < n := by rwa [hrank]
          simpa only [value, dif_pos hp, dif_pos hgp] using old.equivariant g ⟨p.val, hp⟩
        · have hgp : ¬ rank (g • p.val) < n := by rwa [hrank]
          have hp' : rank p.val = n := by
            have hh := p.property; change rank p.val < n + 1 at hh; omega
          have hh := hefresh g ⟨p.val, hp'⟩
          change fresh ⟨g • p.val, (hrank g p.val).trans hp'⟩ = g • fresh ⟨p.val, hp'⟩ at hh
          simpa only [value, dif_neg hp, dif_neg hgp] using hh
  let n := (Finset.univ.sup rank) + 1
  let final := Classical.choice (stages n)
  have hn (p : P) : rank p < n :=
    Nat.lt_succ_of_le (Finset.le_sup (f := rank) (Finset.mem_univ p))
  refine ⟨fun p => final.value ⟨p, hn p⟩, fun p => final.good ⟨p, hn p⟩,
    fun p q h => final.compatible ⟨p, hn p⟩ ⟨q, hn q⟩ h, ?_⟩
  intro g p
  exact final.equivariant g ⟨p, hn p⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCosetTrace.lean -/
section

section
/-! # Integral trace from subgroup invariants

An element fixed by a subgroup has a well-defined orbit value on the left
coset space.  Summing these values gives a group-fixed element, without any
division.  Every equivariant boundary whose value was already group-fixed
is multiplied by the subgroup index.  All assertions apply to an actual
submodule of coherent parameter maps as well as to an ordinary module.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable {K G M N : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

def subgroupFixedSubmodule (ρ : CyclicRepresentation K G M) (H : Subgroup G) : Submodule K M where
  carrier := {x | ∀ h : H, ρ h.val x = x}
  zero_mem' := by intro h; exact map_zero _
  add_mem' := by intro x y hx hy h; rw [map_add, hx h, hy h]
  smul_mem' := by intro c x hx h; rw [map_smul, hx h]

def cosetLeftPermutation (H : Subgroup G) (g : G) : Equiv.Perm (G ⧸ H) where
  toFun := Quotient.map' (fun a => g * a) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hab)
  invFun := Quotient.map' (fun a => g⁻¹ * a) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hab)
  left_inv q := by
    induction q using QuotientGroup.induction_on with
    | H a => change (QuotientGroup.mk (g⁻¹ * (g * a)) : G ⧸ H) = QuotientGroup.mk a; simp
  right_inv q := by
    induction q using QuotientGroup.induction_on with
    | H a => change (QuotientGroup.mk (g * (g⁻¹ * a)) : G ⧸ H) = QuotientGroup.mk a; simp

@[simp] theorem cosetLeftPermutation_mk (H : Subgroup G) (g a : G) :
    cosetLeftPermutation H g (QuotientGroup.mk a) = QuotientGroup.mk (g * a) := rfl

def cosetOrbitValue (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) : G ⧸ H → M :=
  Quotient.lift (fun g => ρ g x) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hfixed := hx ⟨a⁻¹ * b, hmem⟩
    calc
      ρ a x = ρ a (ρ (a⁻¹ * b) x) := by rw [hfixed]
      _ = ρ (a * (a⁻¹ * b)) x := by rw [ρ.map_mul a (a⁻¹ * b)]; rfl
      _ = ρ b x := by rw [mul_inv_cancel_left])

@[simp] theorem cosetOrbitValue_mk (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (g : G) :
    cosetOrbitValue ρ H x hx (QuotientGroup.mk g) = ρ g x := rfl

theorem cosetOrbitValue_out (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (q : G ⧸ H) :
    cosetOrbitValue ρ H x hx q = ρ q.out x := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

theorem cosetOrbitValue_translate (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (g : G) (q : G ⧸ H) :
    cosetOrbitValue ρ H x hx (cosetLeftPermutation H g q) =
      ρ g (cosetOrbitValue ρ H x hx q) := by
  induction q using QuotientGroup.induction_on with
  | H a =>
      change ρ (g * a) x = ρ g (ρ a x)
      rw [ρ.map_mul]
      rfl

variable [Fintype G]

def cosetTrace (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) : M :=
  ∑ q : G ⧸ H, cosetOrbitValue ρ H x hx q

theorem cosetTrace_fixed (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (g : G) :
    ρ g (cosetTrace ρ H x hx) = cosetTrace ρ H x hx := by
  rw [cosetTrace, map_sum]
  calc
    ∑ q : G ⧸ H, ρ g (cosetOrbitValue ρ H x hx q) =
        ∑ q : G ⧸ H, cosetOrbitValue ρ H x hx (cosetLeftPermutation H g q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (cosetOrbitValue_translate ρ H x hx g q).symm
    _ = ∑ q : G ⧸ H, cosetOrbitValue ρ H x hx q :=
      Equiv.sum_comp (cosetLeftPermutation H g) (cosetOrbitValue ρ H x hx)

/-- This scalar is the subgroup index, and requires no invertibility. -/
theorem cosetTrace_map_const (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (q : M →+ N) (y : N)
    (hq : ∀ g, q (ρ g x) = y) :
    q (cosetTrace ρ H x hx) = H.index • y := by
  simp only [cosetTrace, map_sum, cosetOrbitValue_out, hq,
    Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]

theorem cosetTrace_map_equivariant (ρ : CyclicRepresentation K G M)
    (τ : CyclicRepresentation K G N) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x)
    (q : M →ₗ[K] N) (hq : RepresentationIntertwines ρ τ q)
    (hfixed : ∀ g, τ g (q x) = q x) :
    q (cosetTrace ρ H x hx) = H.index • q x :=
  cosetTrace_map_const ρ H x hx q.toAddMonoidHom (q x) (fun g => (hq g x).trans (hfixed g))

theorem cosetTrace_mem (ρ : CyclicRepresentation K G M) (H : Subgroup G)
    (x : M) (hx : ∀ h : H, ρ h.val x = x) (U : Submodule K M)
    (hU : ∀ g z, z ∈ U → ρ g z ∈ U) (hxU : x ∈ U) :
    cosetTrace ρ H x hx ∈ U := by
  apply U.sum_mem
  intro q hq
  rw [cosetOrbitValue_out]
  exact hU q.out x hxU

def cosetTraceLinear (ρ : CyclicRepresentation K G M) (H : Subgroup G) :
    subgroupFixedSubmodule ρ H →ₗ[K] M where
  toFun x := cosetTrace ρ H x.val x.property
  map_add' x y := by
    simp only [cosetTrace, cosetOrbitValue_out, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [cosetTrace, cosetOrbitValue_out, Submodule.coe_smul, map_smul,
      Finset.smul_sum, RingHom.id_apply]

/-- The index of any embedded group of order `n` in a permutation group on
`n` letters is `(n-1)!`.  The cyclic prime subgroup is the application. -/
theorem permutationEmbedding_index_factorial {V T : Type*} [Fintype V]
    [Group T] (f : T →* Equiv.Perm V) (hf : Function.Injective f)
    (n : ℕ) (hn : 0 < n) (hT : Nat.card T = n) (hV : Fintype.card V = n) :
    f.range.index = (n - 1).factorial := by
  have hrange : Nat.card f.range = n := by
    calc
      Nat.card f.range = Nat.card T := (Nat.card_congr (Equiv.ofInjective f hf)).symm
      _ = n := hT
  have hmul := f.range.card_mul_index
  rw [hrange, Nat.card_eq_fintype_card, Fintype.card_perm, hV] at hmul
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * f.range.index = n.factorial := hmul
    _ = n * (n - 1).factorial := by
      have he : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
      conv_lhs => rw [← he, Nat.factorial_succ]
      rw [he]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralAveraging.lean -/
section


section

/-! # Integral affine averaging without division

This is the argument of Lemma A.8.  The group order is never inverted: the
errors of a point fixed modulo the group order are first divided inside the
given lattice, and their sum is the correction to an integral fixed point.
-/

noncomputable section

namespace FourPapers.Universal

open scoped BigOperators

variable {K G M N : Type*} [CommRing K] [Group G] [Fintype G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem representation_sum_fixed (ρ : CyclicRepresentation K G M) (h : G) (x : M) :
    ρ h (∑ g : G, ρ g x) = ∑ g : G, ρ g x := by
  rw [map_sum]
  calc
    ∑ g : G, ρ h (ρ g x) = ∑ g : G, ρ (h * g) x := by
      apply Finset.sum_congr rfl
      intro g hg
      exact (congrArg (fun f : M →ₗ[K] M => f x) (ρ.map_mul h g)).symm
    _ = ∑ g : G, ρ g x :=
      Fintype.sum_equiv (Equiv.mulLeft h) (fun g => ρ (h * g) x)
        (fun g => ρ g x) (fun _ => rfl)

/-- The explicit correction has norm equal to the ordinary group norm. -/
theorem affineCorrection_norm (ρ : CyclicRepresentation K G M) (x : M) (v : G → M)
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g) :
    Fintype.card G • (x + ∑ g : G, v g) = ∑ g : G, ρ g x := by
  rw [nsmul_add, Finset.smul_sum]
  simp only [hv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]

/-- Lemma A.8 in linear ambient coordinates.  Injectivity of multiplication by
the group order is exactly the torsion-free fact used from the integral
lattice. -/
theorem affineCorrection_fixed (ρ : CyclicRepresentation K G M) (x : M) (v : G → M)
    (hregular : Function.Injective (fun y : M => Fintype.card G • y))
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g) :
    ∀ h, ρ h (x + ∑ g : G, v g) = x + ∑ g : G, v g := by
  intro h
  apply hregular
  change Fintype.card G • (ρ h (x + ∑ g : G, v g)) = Fintype.card G • (x + ∑ g : G, v g)
  rw [← map_nsmul, affineCorrection_norm ρ x v hv, representation_sum_fixed]

/-- The integral correction stays in the same affine fiber whenever each
divided error lies in the restriction kernel. -/
theorem exists_fixedPoint_sameFiber (ρ : CyclicRepresentation K G M)
    (q : M →ₗ[K] N) (x : M) (v : G → M)
    (hregular : Function.Injective (fun y : M => Fintype.card G • y))
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g)
    (hqv : ∀ g, q (v g) = 0) :
    ∃ y : M, (∀ g, ρ g y = y) ∧ q y = q x := by
  refine ⟨x + ∑ g : G, v g, affineCorrection_fixed ρ x v hregular hv, ?_⟩
  simp [hqv]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeRetraction.lean -/
section


section

/-! # The prime-rank orbit retraction in characteristic `p`

The map first identifies all vertex variables with one variable, retains
only exponents divisible by `p`, and divides those exponents by `p`.  Its
target variable has internal degree `p`.  These are actual polynomial maps,
and parameter compatibility is proved from the binomial coefficients.
-/

noncomputable section

namespace FourPapers.Universal

open Classical
open scoped BigOperators Polynomial

variable {K V : Type*} [CommRing K]

def coefficientCompression (p : ℕ) : K[X] →ₗ[K] K[X] :=
  Polynomial.lsum fun n => if p ∣ n then Polynomial.monomial (n / p) else 0

@[simp] theorem coefficientCompression_monomial (p n : ℕ) (a : K) :
    coefficientCompression p (Polynomial.monomial n a) =
      if p ∣ n then Polynomial.monomial (n / p) a else 0 := by
  by_cases h : p ∣ n <;> simp [coefficientCompression, Polynomial.lsum_apply, h]

@[simp] theorem coefficientCompression_one (p : ℕ) :
    coefficientCompression (K := K) p 1 = 1 := by
  simpa using coefficientCompression_monomial p 0 (1 : K)

theorem coefficientCompression_X_pow_mul (p : ℕ) (hp : 0 < p) (f : K[X]) :
    coefficientCompression p (Polynomial.X ^ p * f) =
      Polynomial.X * coefficientCompression p f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [mul_add, hf, hg]
  | monomial n a =>
      have hdiv : p ∣ n + p ↔ p ∣ n := by
        simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_self,
          add_zero, Nat.mod_mod]
      rw [Polynomial.X_pow_mul_monomial, coefficientCompression_monomial,
        coefficientCompression_monomial]
      by_cases hn : p ∣ n
      · rw [if_pos (hdiv.mpr hn), if_pos hn, Nat.add_div_right n hp]
        simpa using (Polynomial.X_pow_mul_monomial 1 (n / p) a).symm
      · rw [if_neg (fun h => hn (hdiv.mp h)), if_neg hn, mul_zero]

/-- Diagonal evaluation is invariant under every relabeling of the vertices. -/
def diagonalEvaluation : MvPolynomial V K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun _ => Polynomial.X

@[simp] theorem diagonalEvaluation_rename (e : V → V) (f : MvPolynomial V K) :
    diagonalEvaluation (MvPolynomial.rename e f) = diagonalEvaluation f := by
  unfold diagonalEvaluation
  rw [MvPolynomial.aeval_rename]
  rfl

theorem diagonalEvaluation_monomial (a : V →₀ ℕ) (c : K) :
    diagonalEvaluation (MvPolynomial.monomial a c) =
      Polynomial.monomial (a.sum fun _ n => n) c := by
  rw [diagonalEvaluation, MvPolynomial.aeval_monomial]
  change Polynomial.C c * (∏ v ∈ a.support, Polynomial.X ^ a v) = _
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.C_mul_X_pow_eq_monomial]
  rfl

variable [Fintype V]

theorem diagonalEvaluation_esymm (i : ℕ) :
    diagonalEvaluation (MvPolynomial.esymm V K i) =
      (Fintype.card V).choose i • (Polynomial.X : K[X]) ^ i := by
  unfold diagonalEvaluation MvPolynomial.esymm
  rw [map_sum]
  calc
    ∑ t ∈ Finset.univ.powersetCard i,
        (MvPolynomial.aeval (fun _ : V => (Polynomial.X : K[X])))
          (∏ v ∈ t, MvPolynomial.X v) =
        ∑ _t ∈ Finset.univ.powersetCard i, (Polynomial.X : K[X]) ^ i := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcard : t.card = i := (Finset.mem_powersetCard.mp ht).2
      simp only [map_prod, MvPolynomial.aeval_X, Finset.prod_const, hcard]
    _ = _ := by simp

def primeOrbitRetraction (p : ℕ) : MvPolynomial V K →ₗ[K] K[X] :=
  (coefficientCompression p).comp diagonalEvaluation.toLinearMap

@[simp] theorem primeOrbitRetraction_monomial (p : ℕ) (a : V →₀ ℕ) (c : K) :
    primeOrbitRetraction p (MvPolynomial.monomial a c) =
      if p ∣ a.sum (fun _ n => n) then
        Polynomial.monomial ((a.sum fun _ n => n) / p) c else 0 := by
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    diagonalEvaluation_monomial, coefficientCompression_monomial]

@[simp] theorem primeOrbitRetraction_one (p : ℕ) :
    primeOrbitRetraction (V := V) (K := K) p 1 = 1 := by
  simp [primeOrbitRetraction]

@[simp] theorem primeOrbitRetraction_rename (p : ℕ) (e : V → V)
    (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.rename e f) = primeOrbitRetraction p f := by
  simp [primeOrbitRetraction]

variable (p : ℕ) [CharP K p]

private theorem prime_dvd_interior_binomial (hp : p.Prime) {i : ℕ}
    (hi : 0 < i) (hip : i < p) : p ∣ p.choose i := by
  have hmul := Nat.add_one_mul_choose_eq (p - 1) (i - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p),
    Nat.sub_add_cancel (by omega : 1 ≤ i)] at hmul
  have hdiv : p ∣ p.choose i * i := by
    rw [← hmul]
    exact dvd_mul_right _ _
  exact (hp.dvd_mul.mp hdiv).resolve_right (Nat.not_dvd_of_pos_of_lt hi hip)

theorem primeOrbitRetraction_lower_parameter (hp : p.Prime)
    (hcard : Fintype.card V = p) {i : ℕ} (hi : 0 < i) (hip : i < p)
    (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.esymm V K i * f) = 0 := by
  have hc : (p.choose i : K[X]) = 0 :=
    (CharP.cast_eq_zero_iff (K[X]) p _).mpr (prime_dvd_interior_binomial p hp hi hip)
  have he : diagonalEvaluation (MvPolynomial.esymm V K i) = 0 := by
    rw [diagonalEvaluation_esymm, hcard, nsmul_eq_mul, hc, zero_mul]
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, he, zero_mul, map_zero]

theorem primeOrbitRetraction_top_parameter (hp : 0 < p)
    (hcard : Fintype.card V = p) (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.esymm V K p * f) =
      Polynomial.X * primeOrbitRetraction p f := by
  have he : diagonalEvaluation (MvPolynomial.esymm V K p) =
      (Polynomial.X : K[X]) ^ p := by
    rw [diagonalEvaluation_esymm, hcard, Nat.choose_self, one_smul]
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, he, coefficientCompression_X_pow_mul p hp]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOneDegreeLift.lean -/
section


section

/-! # The equivariant correction in one homogeneous degree

This is the exact extension step in Lemma 8.1.  It keeps both the prescribed
quotient map and the already constructed map on a split subspace.
-/

noncomputable section

namespace FourPapers.Universal

variable {K G M N Q C : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

/-- Restriction of a representation to an invariant submodule. -/
def invariantSubmoduleRepresentation (ρ : CyclicRepresentation K G M)
    (U : Submodule K M) (hU : ∀ g x, x ∈ U → ρ g x ∈ U) :
    CyclicRepresentation K G U where
  toFun g :=
    { toFun := fun x => ⟨ρ g x.val, hU g x.val x.property⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    exact congrArg (fun f : M →ₗ[K] M => f x.val) (ρ.map_mul g h)

@[simp] theorem invariantSubmoduleRepresentation_apply
    (ρ : CyclicRepresentation K G M) (U : Submodule K M)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (g : G) (x : U) :
    (invariantSubmoduleRepresentation ρ U hU g x).val = ρ g x.val := rfl

theorem kernel_invariant_of_intertwines
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (f : M →ₗ[K] N) (hf : RepresentationIntertwines ρ τ f) :
    ∀ g x, x ∈ LinearMap.ker f → ρ g x ∈ LinearMap.ker f := by
  intro g x hx
  change f (ρ g x) = 0
  rw [hf, LinearMap.mem_ker.mp hx, map_zero]

/-- Correct an equivariant preliminary lift by a map into its kernel.  The
kernel's regular-orbit coordinates supply the relative-injectivity step. -/
theorem equivariant_lift_extend_subspace
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (U : Submodule K M) (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (s : M →ₗ[K] U) (hs : s.comp U.subtype = LinearMap.id)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (β : M →ₗ[K] N)
    (hβ : RepresentationIntertwines ρ τ β) (hqβ : q.comp β = a)
    (f : U →ₗ[K] N)
    (hf : RepresentationIntertwines (invariantSubmoduleRepresentation ρ U hU) τ f)
    (hqf : q.comp f = a.comp U.subtype)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ L : M →ₗ[K] N,
      RepresentationIntertwines ρ τ L ∧ L.comp U.subtype = f ∧ q.comp L = a := by
  let δ : U →ₗ[K] LinearMap.ker q :=
    LinearMap.codRestrict (LinearMap.ker q) (f - β.comp U.subtype) (by
      intro x
      change q (f x - β x.val) = 0
      rw [map_sub]
      have h1 := congrArg (fun z : U →ₗ[K] Q => z x) hqf
      have h2 := congrArg (fun z : M →ₗ[K] Q => z x.val) hqβ
      exact sub_eq_zero.mpr (h1.trans h2.symm))
  have hδ : RepresentationIntertwines (invariantSubmoduleRepresentation ρ U hU)
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) δ := by
    intro g x
    apply Subtype.ext
    change f (invariantSubmoduleRepresentation ρ U hU g x) - β (ρ g x.val) =
      τ g (f x - β x.val)
    rw [hf, hβ, map_sub]
  have hi : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρ U hU) ρ U.subtype := by
    intro g x
    rfl
  obtain ⟨D, hD, hDi⟩ := exists_equivariantExtension_of_coinduced
    (invariantSubmoduleRepresentation ρ U hU) ρ
    (invariantSubmoduleRepresentation τ (LinearMap.ker q)
      (kernel_invariant_of_intertwines τ υ q hq)) e he U.subtype s hi hs δ hδ
  refine ⟨β + (LinearMap.ker q).subtype.comp D, ?_, ?_, ?_⟩
  · intro g x
    change β (ρ g x) + (D (ρ g x)).val = τ g (β x + (D x).val)
    rw [hβ, hD, map_add]
    rfl
  · ext x
    have hd := congrArg (fun z : U →ₗ[K] LinearMap.ker q => (z x).val) hDi
    change β x.val + (D x.val).val = f x
    change (D x.val).val = f x - β x.val at hd
    rw [hd, ← add_sub_assoc, add_comm (β x.val) (f x)]
    exact add_sub_cancel_right (f x) (β x.val)
  · ext x
    have hx := (D x).property
    change q (D x).val = 0 at hx
    change q (β x + (D x).val) = a x
    rw [map_add, hx, add_zero]
    exact congrArg (fun z : M →ₗ[K] Q => z x) hqβ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSplitKernelLift.lean -/
section


section

/-! # An ordinary lift can be made equivariant

An equivariant kernel with regular-orbit coordinates is relatively injective.
Over a field its inclusion splits as an ordinary linear map, hence also
equivariantly.  Consequently an ordinary lift of an equivariant quotient map
can be corrected to an equivariant lift.  This removes any assumption of an
already equivariant preliminary section from the graded construction.
-/

noncomputable section

namespace FourPapers.Universal

variable {K G M N Q C : Type*} [Field K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

theorem exists_equivariantLift_of_coinduced_kernel
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (ha : RepresentationIntertwines ρ υ a)
    (β : M →ₗ[K] N) (hqβ : q.comp β = a)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ F : M →ₗ[K] N, RepresentationIntertwines ρ τ F ∧ q.comp F = a := by
  let H := LinearMap.ker q
  let ρH := invariantSubmoduleRepresentation τ H
    (kernel_invariant_of_intertwines τ υ q hq)
  obtain ⟨s, hs⟩ := H.subtype.exists_leftInverse_of_injective H.ker_subtype
  have hi : RepresentationIntertwines ρH τ H.subtype := by
    intro g x
    rfl
  have hid : RepresentationIntertwines ρH ρH (LinearMap.id : H →ₗ[K] H) := by
    intro g x
    rfl
  obtain ⟨r, hre, hri⟩ := exists_equivariantExtension_of_coinduced
    ρH τ ρH e he H.subtype s hi hs LinearMap.id hid
  let P : N →ₗ[K] N := LinearMap.id - H.subtype.comp r
  have hP : RepresentationIntertwines τ τ P := by
    intro g x
    change τ g x - (r (τ g x)).val = τ g (x - (r x).val)
    rw [hre, map_sub]
    rfl
  have hPH (x : H) : P x.val = 0 := by
    have hrx := congrArg (fun F : H →ₗ[K] H => (F x).val) hri
    change x.val - (r x.val).val = 0
    change (r x.val).val = x.val at hrx
    rw [hrx, sub_self]
  have hqP (x : N) : q (P x) = q x := by
    change q (x - (r x).val) = q x
    rw [map_sub, show q (r x).val = 0 from (r x).property, sub_zero]
  refine ⟨P.comp β, ?_, ?_⟩
  · intro g x
    have hx : β (ρ g x) - τ g (β x) ∈ H := by
      change q (β (ρ g x) - τ g (β x)) = 0
      rw [map_sub, hq]
      have hb1 := congrArg (fun F : M →ₗ[K] Q => F (ρ g x)) hqβ
      have hb2 := congrArg (fun F : M →ₗ[K] Q => F x) hqβ
      change q (β (ρ g x)) = a (ρ g x) at hb1
      change q (β x) = a x at hb2
      rw [hb1, hb2, ha, sub_self]
    have hz := hPH ⟨β (ρ g x) - τ g (β x), hx⟩
    rw [map_sub] at hz
    change P (β (ρ g x)) = τ g (P (β x))
    exact (sub_eq_zero.mp hz).trans (hP g (β x))
  · ext x
    change q (P (β x)) = a x
    rw [hqP]
    exact congrArg (fun F : M →ₗ[K] Q => F x) hqβ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedBasis.lean -/
section


section

/-! # Homogeneous free bases for equivariant lifting

The two bases below are the parameter basis and the coefficient basis of a
graded free module.  In the application they are `booleanColorBasis` and
`booleanParameterBasis`.  The degree properties express positivity of the
parameters, and are proved from their actual color multidegrees.
-/

noncomputable section

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable (K A M I J : Type*) [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

structure ScalarGradedBasis where
  parameterBasis : Module.Basis I A M
  coefficientBasis : Module.Basis J K M
  generatorDegree : I → ℕ
  degree : J → ℕ
  parent : J → I
  multiplier : J → A
  coefficient_eq : ∀ j, coefficientBasis j = multiplier j • parameterBasis (parent j)
  parent_degree_le : ∀ j, generatorDegree (parent j) ≤ degree j
  equal_degree_eq : ∀ j, degree j = generatorDegree (parent j) →
    coefficientBasis j = parameterBasis (parent j)
  generator_homogeneous : ∀ i j, degree j ≠ generatorDegree i →
    coefficientBasis.repr (parameterBasis i) j = 0

namespace ScalarGradedBasis

variable {K A M I J}
variable (s : ScalarGradedBasis K A M I J)

def piece (n : ℕ) : Submodule K M :=
  basisOrdinaryDegreePiece s.coefficientBasis s.degree n

def cut (n : ℕ) : Submodule A M :=
  Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n})

theorem generator_mem_piece (i : I) :
    s.parameterBasis i ∈ s.piece (s.generatorDegree i) :=
  s.generator_homogeneous i

theorem coefficient_mem_piece (j : J) : s.coefficientBasis j ∈ s.piece (s.degree j) := by
  intro k hk
  rw [Module.Basis.repr_self]
  have hne : j ≠ k := by
    intro h
    subst k
    exact hk rfl
  simp [Finsupp.single_apply, hne]

theorem generator_mem_cut {n : ℕ} (i : I) (hi : s.generatorDegree i < n) :
    s.parameterBasis i ∈ s.cut n :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem coefficient_mem_cut {n : ℕ} (j : J)
    (hj : s.generatorDegree (s.parent j) < n) :
    s.coefficientBasis j ∈ s.cut n := by
  rw [s.coefficient_eq]
  exact (s.cut n).smul_mem _ (s.generator_mem_cut _ hj)

def projection (n : ℕ) : M →ₗ[K] s.piece n :=
  LinearMap.codRestrict (s.piece n)
    (basisDegreeProjection s.coefficientBasis s.degree n) (by
      intro x j hj
      simp only [basisDegreeProjection_repr, if_neg hj])

@[simp] theorem projection_coefficient (n : ℕ) (j : J) (hj : s.degree j = n) :
    s.projection n (s.coefficientBasis j) =
      ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ := by
  apply Subtype.ext
  exact (basisDegreeProjection_basis s.coefficientBasis s.degree n j).trans (if_pos hj)

@[simp] theorem projection_coefficient_of_ne (n : ℕ) (j : J) (hj : s.degree j ≠ n) :
    s.projection n (s.coefficientBasis j) = 0 := by
  apply Subtype.ext
  exact (basisDegreeProjection_basis s.coefficientBasis s.degree n j).trans (if_neg hj)

@[simp] theorem projection_subtype (n : ℕ) (x : s.piece n) :
    s.projection n x.val = x := by
  apply Subtype.ext
  apply s.coefficientBasis.repr.injective
  ext j
  change s.coefficientBasis.repr
    (basisDegreeProjection s.coefficientBasis s.degree n x.val) j = _
  rw [basisDegreeProjection_repr]
  by_cases hj : s.degree j = n
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact (x.property j hj).symm

variable {N : Type*} [AddCommGroup N] [Module K N]

theorem maps_eq_on_piece (n : ℕ) (f : M →ₗ[K] N) (g : s.piece n →ₗ[K] N)
    (h : ∀ j (hj : s.degree j = n),
      f (s.coefficientBasis j) = g ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩)
    (x : s.piece n) : f x.val = g x := by
  have he : f.comp ((s.piece n).subtype.comp (s.projection n)) =
      g.comp (s.projection n) := by
    apply s.coefficientBasis.ext
    intro j
    by_cases hj : s.degree j = n
    · simp only [LinearMap.comp_apply, s.projection_coefficient n j hj,
        Submodule.subtype_apply]
      exact h j hj
    · simp only [LinearMap.comp_apply, s.projection_coefficient_of_ne n j hj,
        map_zero]
  have hx := congrArg (fun z : M →ₗ[K] N => z x.val) he
  simpa using hx

theorem homogeneous_mem_cut {m n : ℕ} (hmn : m < n) (x : M)
    (hx : x ∈ s.piece m) : x ∈ s.cut n := by
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply ((s.cut n).restrictScalars K).sum_mem
  intro j hj
  apply ((s.cut n).restrictScalars K).smul_mem
  have hdeg : s.degree j = m := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj (hx j hn)
  apply s.coefficient_mem_cut j
  calc
    s.generatorDegree (s.parent j) ≤ s.degree j := s.parent_degree_le j
    _ = m := hdeg
    _ < n := hmn

variable [Module A N] [IsScalarTower K A N]

theorem maps_eq_on_cut (n : ℕ) (f g : M →ₗ[A] N)
    (h : ∀ i, s.generatorDegree i < n → f (s.parameterBasis i) = g (s.parameterBasis i))
    (x : M) (hx : x ∈ s.cut n) : f x = g x := by
  change x ∈ Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact h i hi
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul a x hx ih => simp [ih]

theorem graded_of_generators (T : ℕ → Submodule K N)
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (f : M →ₗ[A] N) (hf : ∀ i, f (s.parameterBasis i) ∈ T (s.generatorDegree i))
    (n : ℕ) (x : M) (hx : x ∈ s.piece n) : f x ∈ T n := by
  let fk : M →ₗ[K] N := f.restrictScalars K
  change fk x ∈ T n
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  have hdeg : s.degree j = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj (hx j hn)
  change f (s.coefficientBasis j) ∈ T n
  rw [s.coefficient_eq, map_smul]
  exact hdeg ▸ hmult j _ (hf (s.parent j))

variable {G : Type*} [Group G]

def restrictRepresentation (ρ : CyclicRepresentation A G M) : CyclicRepresentation K G M where
  toFun g := (ρ g).restrictScalars K
  map_one' := by ext x; exact congrArg (fun f : M →ₗ[A] M => f x) ρ.map_one
  map_mul' g h := by ext x; exact congrArg (fun f : M →ₗ[A] M => f x) (ρ.map_mul g h)

theorem cut_invariant (ρ : CyclicRepresentation A G M)
    (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
    (n : ℕ) (g : G) (x : M) (hx : x ∈ s.cut n) : ρ g x ∈ s.cut n := by
  change x ∈ Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact s.homogeneous_mem_cut hi _ (hρ g _ _ (s.generator_mem_piece i))
  | zero => simpa using (s.cut n).zero_mem
  | add x y hx hy ihx ihy => simpa using (s.cut n).add_mem ihx ihy
  | smul a x hx ih => simpa using (s.cut n).smul_mem a ih

end ScalarGradedBasis

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedLift.lean -/
section


section

/-! # The finite degree induction for equivariant lifting

This file separates the finite induction from the one-degree kernel calculation.
No map on the generators is assumed to intertwine the group action.  The lower
generator span is stable because the action preserves degree, and agreement on
its intersection with the next degree is imposed explicitly.
-/

noncomputable section

namespace FourPapers.Universal
namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)

/-- The induction invariant is stated on all parameter-basis generators of
degree below `n`.  A-linearity extends the last two conditions to `cut n`. -/
def LiftStage (n : ℕ) (f : M →ₗ[A] N) : Prop :=
  (∀ i, f (s.parameterBasis i) ∈ T (s.generatorDegree i)) ∧
  (∀ i, s.generatorDegree i < n → q (f (s.parameterBasis i)) = a (s.parameterBasis i)) ∧
  (∀ g i, s.generatorDegree i < n →
    f (ρ g (s.parameterBasis i)) = τ g (f (s.parameterBasis i)))

theorem LiftStage.quotient_on_cut {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f) (x : M) (hx : x ∈ s.cut n) :
    q (f x) = a x :=
  s.maps_eq_on_cut n (q.comp f) a hf.2.1 x hx

theorem LiftStage.equivariant_on_cut {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f) (g : G) (x : M) (hx : x ∈ s.cut n) :
    f (ρ g x) = τ g (f x) :=
  s.maps_eq_on_cut n (f.comp (ρ g)) ((τ g).comp f) (hf.2.2 g) x hx

variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)

/-- A one-degree lift, with the previously fixed lower-generator values. -/
def DegreeLift (n : ℕ) (f : M →ₗ[A] N) (L : s.piece n →ₗ[K] N) : Prop :=
  (∀ x, L x ∈ T n) ∧
  (∀ g x, L ⟨ρ g x.val, hρ g n x.val x.property⟩ = τ g (L x)) ∧
  (∀ x, q (L x) = a x.val) ∧
  (∀ x, x.val ∈ s.cut n → L x = f x.val)

/-- The induction step.  Its only input beyond the preceding stage is a lift on
the actual homogeneous component, compatible on the actual intersection. -/
theorem liftStage_succ {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f)
    (L : s.piece n →ₗ[K] N) (hL : s.DegreeLift ρ τ T q a hρ n f L) :
    ∃ F : M →ₗ[A] N, s.LiftStage ρ τ T q a (n + 1) F := by
  let v : I → N := fun i =>
    if hi : s.generatorDegree i = n then
      L ⟨s.parameterBasis i, hi ▸ s.generator_mem_piece i⟩
    else f (s.parameterBasis i)
  let F : M →ₗ[A] N := s.parameterBasis.constr A v
  have hF (i : I) : F (s.parameterBasis i) = v i :=
    s.parameterBasis.constr_basis A v i
  have hFcut (x : M) (hx : x ∈ s.cut n) : F x = f x := by
    apply s.maps_eq_on_cut n F f _ x hx
    intro i hi
    rw [hF]
    exact dif_neg (Nat.ne_of_lt hi)
  have hFpiece (x : s.piece n) : F x.val = L x := by
    apply s.maps_eq_on_piece n (F.restrictScalars K) L _ x
    intro j hj
    have hp : s.generatorDegree (s.parent j) ≤ n := by
      simpa only [hj] using s.parent_degree_le j
    by_cases he : s.generatorDegree (s.parent j) = n
    · have hc : s.coefficientBasis j = s.parameterBasis (s.parent j) :=
        s.equal_degree_eq j (hj.trans he.symm)
      change F (s.coefficientBasis j) = _
      calc
        F (s.coefficientBasis j) = F (s.parameterBasis (s.parent j)) := congrArg F hc
        _ = L ⟨s.parameterBasis (s.parent j), he ▸ s.generator_mem_piece (s.parent j)⟩ := by
          rw [hF]
          exact dif_pos he
        _ = L ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ :=
          congrArg L (Subtype.ext hc.symm)
    · have hlt : s.generatorDegree (s.parent j) < n := lt_of_le_of_ne hp he
      have hcut := s.coefficient_mem_cut j hlt
      change F (s.coefficientBasis j) = _
      rw [hFcut _ hcut]
      exact (hL.2.2.2 ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ hcut).symm
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    rw [hF]
    dsimp only [v]
    split_ifs with hi
    · simpa only [hi] using hL.1
        ⟨s.parameterBasis i, hi ▸ s.generator_mem_piece i⟩
    · exact hf.1 i
  · intro i hi
    by_cases hlt : s.generatorDegree i < n
    · rw [hFcut _ (s.generator_mem_cut i hlt)]
      exact hf.2.1 i hlt
    · have he : s.generatorDegree i = n := by omega
      let x : s.piece n := ⟨s.parameterBasis i, he ▸ s.generator_mem_piece i⟩
      rw [hFpiece x]
      exact hL.2.2.1 x
  · intro g i hi
    by_cases hlt : s.generatorDegree i < n
    · have hbi : s.parameterBasis i ∈ s.cut n := s.generator_mem_cut i hlt
      rw [hFcut _ (s.cut_invariant ρ hρ n g _ hbi), hFcut _ hbi]
      exact hf.2.2 g i hlt
    · have he : s.generatorDegree i = n := by omega
      let x : s.piece n := ⟨s.parameterBasis i, he ▸ s.generator_mem_piece i⟩
      let gx : s.piece n := ⟨ρ g x.val, hρ g n x.val x.property⟩
      change F gx.val = τ g (F x.val)
      rw [hFpiece gx, hFpiece x]
      exact hL.2.1 g x

/-- The full finite induction.  The one-degree extension premise is discharged
by the relative-injectivity theorem in the next construction, not postulated as
a property of the paper's face rings. -/
theorem exists_equivariantGradedLift_of_degreeExtensions [Fintype I]
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (hstep : ∀ n f, s.LiftStage ρ τ T q a n f →
      ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have stages : ∀ n, ∃ f : M →ₗ[A] N, s.LiftStage ρ τ T q a n f := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, ?_, ?_, ?_⟩
        · intro i
          exact (T (s.generatorDegree i)).zero_mem
        · intro i hi
          exact False.elim (Nat.not_lt_zero _ hi)
        · intro g i hi
          exact False.elim (Nat.not_lt_zero _ hi)
    | succ n ih =>
        obtain ⟨f, hf⟩ := ih
        obtain ⟨L, hL⟩ := hstep n f hf
        exact s.liftStage_succ ρ τ T q a hρ hf L hL
  let n : ℕ := Finset.univ.sup s.generatorDegree + 1
  obtain ⟨f, hf⟩ := stages n
  have hbound (i : I) : s.generatorDegree i < n :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  refine ⟨f, s.graded_of_generators T hmult f hf.1, ?_, ?_⟩
  · apply s.parameterBasis.ext
    intro i
    exact hf.2.1 i (hbound i)
  · intro g x
    have he : f.comp (ρ g) = (τ g).comp f := by
      apply s.parameterBasis.ext
      intro i
      exact hf.2.2 g i (hbound i)
    exact congrArg (fun F : M →ₗ[A] N => F x) he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedKernelLift.lean -/
section


section

/-! # Graded equivariant lifting from regular-orbit kernels

The hypotheses here are explicit linear maps and explicit equivariant coordinate
equivalences for homogeneous kernels.  They are the objects supplied by the
prime-cyclic polynomial calculation.  The finite induction of
`CyclicGradedLift` then produces one parameter-linear lift in every degree.
-/

noncomputable section

namespace FourPapers.Universal
namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (υ : CyclicRepresentation A G Q)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)
variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
variable (hτ : ∀ g n x, x ∈ T n → τ g x ∈ T n)
variable (hq : RepresentationIntertwines τ υ q)

def sourceDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (s.piece n) :=
  invariantSubmoduleRepresentation (restrictRepresentation ρ) (s.piece n)
    (fun g x hx => hρ g n x hx)

def targetDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (T n) :=
  invariantSubmoduleRepresentation (restrictRepresentation τ) (T n)
    (fun g x hx => hτ g n x hx)

def degreeQuotient (n : ℕ) : T n →ₗ[K] Q :=
  (q.restrictScalars K).comp (T n).subtype

def degreeTarget (n : ℕ) : s.piece n →ₗ[K] Q :=
  (a.restrictScalars K).comp (s.piece n).subtype

include hq in
theorem degreeQuotient_intertwines (n : ℕ) :
    RepresentationIntertwines (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n) := by
  intro g x
  exact hq g x.val

def kernelDegreeRepresentation (n : ℕ) :
    CyclicRepresentation K G (LinearMap.ker (degreeQuotient T q n)) :=
  invariantSubmoduleRepresentation (targetDegreeRepresentation τ T hτ n)
    (LinearMap.ker (degreeQuotient T q n))
    (kernel_invariant_of_intertwines (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n)
      (degreeQuotient_intertwines τ υ T q hτ hq n))

variable
  (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
    s.multiplier j • y ∈ T (s.degree j))

include hρ hmult

/-- The full one-degree step, including construction of the lower subspace and
its ordinary linear retraction.  The field assumption is used only to split
that subspace; it is not used to average the group action. -/
theorem degreeLift_of_coinduced_kernel
    {n : ℕ} {f : M →ₗ[A] N} (hf : s.LiftStage ρ τ T q a n f)
    (β : s.piece n →ₗ[K] T n)
    (hβ : RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
      (targetDegreeRepresentation τ T hτ n) β)
    (hqβ : (degreeQuotient T q n).comp β = s.degreeTarget a n)
    {C : Type*} [AddCommGroup C] [Module K C]
    (e : LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation e.toLinearMap) :
    ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L := by
  let ρn := s.sourceDegreeRepresentation ρ hρ n
  let τn := targetDegreeRepresentation τ T hτ n
  let υK := restrictRepresentation (K := K) υ
  let qn := degreeQuotient T q n
  let an := s.degreeTarget a n
  let U : Submodule K (s.piece n) :=
    ((s.cut n).restrictScalars K).comap (s.piece n).subtype
  have hU : ∀ g x, x ∈ U → ρn g x ∈ U := by
    intro g x hx
    change ρ g x.val ∈ s.cut n
    exact s.cut_invariant ρ hρ n g x.val hx
  obtain ⟨r, hr⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  let fU : U →ₗ[K] T n :=
    LinearMap.codRestrict (T n)
      ((f.restrictScalars K).comp ((s.piece n).subtype.comp U.subtype)) (by
        intro x
        exact s.graded_of_generators T hmult f hf.1 n x.val.val x.val.property)
  have hfU : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρn U hU) τn fU := by
    intro g x
    apply Subtype.ext
    exact LiftStage.equivariant_on_cut s ρ τ T q a hf g x.val.val x.property
  have hqfU : qn.comp fU = an.comp U.subtype := by
    ext x
    exact LiftStage.quotient_on_cut s ρ τ T q a hf x.val.val x.property
  have hqn : RepresentationIntertwines τn υK qn :=
    degreeQuotient_intertwines τ υ T q hτ hq n
  obtain ⟨L, hLeq, hLU, hqL⟩ := equivariant_lift_extend_subspace
    ρn τn υK U hU r hr qn hqn an β hβ hqβ fU hfU hqfU e he
  refine ⟨(T n).subtype.comp L, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (L x).property
  · intro g x
    exact congrArg Subtype.val (hLeq g x)
  · intro x
    exact congrArg (fun F : s.piece n →ₗ[K] Q => F x) hqL
  · intro x hx
    let ux : U := ⟨x, hx⟩
    exact congrArg (fun F : U →ₗ[K] T n => (F ux).val) hLU

/-- Graded parameter-linear equivariant lifting, with every one-degree
extension proved from regular-orbit coordinates for its actual kernel. -/
theorem exists_equivariantGradedLift_of_coinduced_kernels [Fintype I]
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hβ : ∀ n, RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
      (targetDegreeRepresentation τ T hτ n) (β n))
    (hqβ : ∀ n, (degreeQuotient T q n).comp (β n) = s.degreeTarget a n)
    (e : ∀ n, LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  apply s.exists_equivariantGradedLift_of_degreeExtensions ρ τ T q a hρ hmult
  intro n f hf
  exact s.degreeLift_of_coinduced_kernel ρ τ υ T q a hρ hτ hq hmult hf
    (β n) (hβ n) (hqβ n) (e n) (he n)

/-- The form used for the actual face rings: the preliminary lift is required
only to preserve degree and the prescribed quotient map.  All equivariance is
constructed from the explicit regular-orbit kernels. -/
theorem exists_equivariantGradedLift_of_ordinary_lifts [Fintype I]
    (ha : RepresentationIntertwines ρ υ a)
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hqβ : ∀ n, (degreeQuotient T q n).comp (β n) = s.degreeTarget a n)
    (e : ∀ n, LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have hβeq : ∀ n, ∃ F : s.piece n →ₗ[K] T n,
      RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
        (targetDegreeRepresentation τ T hτ n) F ∧
      (degreeQuotient T q n).comp F = s.degreeTarget a n := by
    intro n
    apply exists_equivariantLift_of_coinduced_kernel
      (s.sourceDegreeRepresentation ρ hρ n) (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n)
      (degreeQuotient_intertwines τ υ T q hτ hq n) (s.degreeTarget a n)
      (fun g x => ha g x.val) (β n) (hqβ n) (e n) (he n)
  choose F hF hqF using hβeq
  exact s.exists_equivariantGradedLift_of_coinduced_kernels
    ρ τ υ T q a hρ hτ hq hmult C F hF hqF e he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBooleanGrading.lean -/
section


section

/-! # The actual Boolean descent basis satisfies the lifting hypotheses

The scalar basis and parameter basis are the already proved bases of the
actual barycentric face ring.  Its homogeneous pieces agree with ordinary
rank-weighted polynomial degree, not a grading chosen to make lifting easier.
-/

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem colorOrdinaryDegree_eq_zero_iff (m : ColorExponent V) :
    colorOrdinaryDegree m = 0 ↔ m = 0 := by
  constructor
  · intro hm
    apply Finsupp.ext
    intro c
    have hc : m c ≤ colorOrdinaryDegree m := by
      rw [colorOrdinaryDegree_fintype]
      calc
        m c = m c * 1 := (Nat.mul_one _).symm
        _ ≤ m c * (c.val + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos _)
        _ ≤ ∑ i : Fin (Fintype.card V), m i * (i.val + 1) :=
          Finset.single_le_sum (f := fun i : Fin (Fintype.card V) => m i * (i.val + 1))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    change m c = 0
    omega
  · rintro rfl
    simp [colorOrdinaryDegree]

@[simp] theorem booleanParameterBasis_zero_parameter
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanParameterBasis (K := K) (σ, 0) = booleanColorBasis (K := K) σ := by
  simp [parameterDescentVector, colorPower]

/-- The exact positive graded free-basis structure of the Boolean barycentric
ring used in the prime-rank lift. -/
def booleanScalarGradedBasis :
    ScalarGradedBasis K (MvPolynomial (Fin (Fintype.card V)) K)
      (BooleanBarycentricRing V K)
      (VertexOrdering (Fintype.card V) V)
      (VertexOrdering (Fintype.card V) V × ColorExponent V) where
  parameterBasis := booleanColorBasis
  coefficientBasis := booleanParameterBasis
  generatorDegree σ := colorOrdinaryDegree (descentColorExponent σ)
  degree p := colorOrdinaryDegree p.2 + colorOrdinaryDegree (descentColorExponent p.1)
  parent := Prod.fst
  multiplier p := MvPolynomial.monomial p.2 1
  coefficient_eq p := by
    rw [booleanParameterBasis_apply, booleanColorBasis_apply]
    exact parameterDescentVector_eq_monomial_smul p
  parent_degree_le p := Nat.le_add_left _ _
  equal_degree_eq p hp := by
    obtain ⟨σ, m⟩ := p
    change colorOrdinaryDegree m + colorOrdinaryDegree (descentColorExponent σ) =
      colorOrdinaryDegree (descentColorExponent σ) at hp
    have hm : colorOrdinaryDegree m = 0 := by omega
    have hm0 := (colorOrdinaryDegree_eq_zero_iff m).mp hm
    subst m
    exact booleanParameterBasis_zero_parameter σ
  generator_homogeneous σ p hp := by
    rw [← booleanParameterBasis_zero_parameter, Module.Basis.repr_self]
    have hne : (σ, (0 : ColorExponent V)) ≠ p := by
      intro he
      subst p
      exact hp (by simp [colorOrdinaryDegree])
    simp [Finsupp.single_apply, hne]

theorem basisDegreeProjection_eq_self_iff_mem
    {I M : Type*} [AddCommGroup M] [Module K M]
    (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) (x : M) :
    basisDegreeProjection b degree n x = x ↔
      x ∈ basisOrdinaryDegreePiece b degree n := by
  constructor
  · intro hx i hi
    have h := congrArg (fun y => b.repr y i) hx
    rw [basisDegreeProjection_repr, if_neg hi] at h
    exact h.symm
  · intro hx
    apply b.repr.injective
    ext i
    rw [basisDegreeProjection_repr]
    by_cases hi : degree i = n
    · rw [if_pos hi]
    · rw [if_neg hi, hx i hi]

theorem booleanParameterDegreeProjection_eq (n : ℕ) :
    basisDegreeProjection (booleanChainBasis (V := V) (K := K))
      (fun a => chainOrdinaryDegree a.val) n =
    basisDegreeProjection (booleanParameterBasis (V := V) (K := K))
      (fun p => colorOrdinaryDegree p.2 +
        colorOrdinaryDegree (descentColorExponent p.1)) n := by
  apply basisDegreeProjection_eq_of_homogeneous
  intro a p hp
  rw [booleanParameterBasis_apply]
  apply parameterDescentVector_repr_color
  intro he
  apply hp
  rw [← colorOrdinaryDegree_chainColorDegree, he, colorOrdinaryDegree_add]

/-- Faithfulness of the homogeneous pieces in the lifting construction: they
are exactly the standard chain-monomial components of ordinary degree `n`. -/
theorem booleanScalarGradedBasis_piece_eq (n : ℕ) :
    (booleanScalarGradedBasis (V := V) (K := K)).piece n =
      basisOrdinaryDegreePiece (booleanChainBasis (V := V) (K := K))
        (fun a => chainOrdinaryDegree a.val) n := by
  ext x
  change x ∈ basisOrdinaryDegreePiece booleanParameterBasis
      (fun p => colorOrdinaryDegree p.2 +
        colorOrdinaryDegree (descentColorExponent p.1)) n ↔ _
  rw [← basisDegreeProjection_eq_self_iff_mem,
    ← basisDegreeProjection_eq_self_iff_mem,
    booleanParameterDegreeProjection_eq]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicExponentFreeness.lean -/
section

section
/-! # Homogeneous exponent vectors under a prime cyclic permutation

This is the literal exponent action induced by renaming polynomial variables.
A nonidentity stabilizer forces the exponent vector to be constant. Therefore
all nonconstant exponent vectors have free orbits, and in a degree not divisible
by p every exponent vector has a free orbit.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime]

/-- A nonzero translation is transitive on the prime cyclic set, expressed
without any finiteness or algebraic assumptions on the values of the function. -/
theorem primeShift_invariant_constant {A : Type*} (a : ZMod p → A)
    (g : ZMod p) (hg : g ≠ 0) (h : ∀ x, a (g + x) = a x) :
    ∀ x, a x = a 0 := by
  have hn : ∀ n : ℕ, ∀ x : ZMod p, a ((n : ZMod p) * g + x) = a x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        calc
          a (((n + 1 : ℕ) : ZMod p) * g + x) = a (g + ((n : ZMod p) * g + x)) := by
            congr 1
            simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            ac_rfl
          _ = a ((n : ZMod p) * g + x) := h _
          _ = a x := ih x
  intro x
  obtain ⟨n, he⟩ := ZMod.natCast_zmod_surjective (x / g)
  have hx : (n : ZMod p) * g = x := by rw [he, div_mul_cancel₀ _ hg]
  simpa only [hx, add_zero] using hn n 0

def cyclicConstantExponent (m : ℕ) : ZMod p →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => m)

@[simp] theorem cyclicConstantExponent_apply (m : ℕ) (x : ZMod p) :
    cyclicConstantExponent p m x = m := rfl

theorem cyclicConstantExponent_degree (m : ℕ) :
    (cyclicConstantExponent p m).degree = p * m := by
  rw [Finsupp.degree_eq_sum]
  simp only [cyclicConstantExponent_apply, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, Nat.cast_id]

theorem primeShift_fixed_exponent_constant (a : ZMod p →₀ ℕ)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : a.mapDomain (Equiv.addLeft g.toAdd) = a) : ∀ x, a x = a 0 := by
  have hg0 : g.toAdd ≠ 0 := by
    intro h
    exact hg (congrArg Multiplicative.ofAdd h)
  apply primeShift_invariant_constant p (fun x => a x) g.toAdd hg0
  intro x
  have hh := congrArg (fun b : ZMod p →₀ ℕ => b (g.toAdd + x)) hfix
  change (a.mapDomain (Equiv.addLeft g.toAdd)) ((Equiv.addLeft g.toAdd) x) =
    a (g.toAdd + x) at hh
  rw [Finsupp.mapDomain_apply_of_injective (Equiv.addLeft g.toAdd).injective] at hh
  exact hh.symm

theorem primeShift_fixed_exponent_degree (a : ZMod p →₀ ℕ)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : a.mapDomain (Equiv.addLeft g.toAdd) = a) : a.degree = p * a 0 := by
  have hc := primeShift_fixed_exponent_constant p a g hg hfix
  rw [Finsupp.degree_eq_sum]
  calc
    (∑ x : ZMod p, a x) = ∑ _x : ZMod p, a 0 := Finset.sum_congr rfl (fun x _ => hc x)
    _ = p * a 0 := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id]

theorem primeShift_fixed_exponent_eq (a : ZMod p →₀ ℕ)
    (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : a.mapDomain (Equiv.addLeft g.toAdd) = a) :
    a = cyclicConstantExponent p (a.degree / p) := by
  have hc := primeShift_fixed_exponent_constant p a g hg hfix
  have hd := primeShift_fixed_exponent_degree p a g hg hfix
  have hdiv : a.degree / p = a 0 := by
    rw [hd, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]
  ext x
  rw [cyclicConstantExponent_apply, hdiv]
  exact hc x

theorem primeShift_no_fixed_exponent_of_not_dvd (a : ZMod p →₀ ℕ)
    (hn : ¬ p ∣ a.degree) (g : PrimeCycleGroup p) (hg : g ≠ 1) :
    a.mapDomain (Equiv.addLeft g.toAdd) ≠ a := by
  intro hfix
  exact hn ⟨a 0, primeShift_fixed_exponent_degree p a g hg hfix⟩

theorem primeShift_constant_exponent_fixed (m : ℕ) (g : PrimeCycleGroup p) :
    (cyclicConstantExponent p m).mapDomain (Equiv.addLeft g.toAdd) =
      cyclicConstantExponent p m := by
  ext x
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

abbrev CyclicHomogeneousExponent (n : ℕ) := {a : ZMod p →₀ ℕ // a.degree = n}

noncomputable instance cyclicHomogeneousExponentFintype (n : ℕ) :
    Fintype (CyclicHomogeneousExponent p n) :=
  (Finsupp.finite_of_degree_eq n).fintype

def cyclicHomogeneousExponentAction (n : ℕ) :
    MulAction (PrimeCycleGroup p) (CyclicHomogeneousExponent p n) where
  smul g a := ⟨a.val.mapDomain (Equiv.addLeft g.toAdd), by
    rw [Finsupp.degree_mapDomain]
    exact a.property⟩
  one_smul a := by
    apply Subtype.ext
    change a.val.mapDomain (Equiv.addLeft (0 : ZMod p)) = a.val
    have he : (Equiv.addLeft (0 : ZMod p) : ZMod p → ZMod p) = id := by
      funext x
      exact zero_add x
    rw [he, Finsupp.mapDomain_id]
  mul_smul g h a := by
    apply Subtype.ext
    change a.val.mapDomain (Equiv.addLeft (g.toAdd + h.toAdd)) =
      (a.val.mapDomain (Equiv.addLeft h.toAdd)).mapDomain (Equiv.addLeft g.toAdd)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext x
    exact add_assoc g.toAdd h.toAdd x

theorem cyclicHomogeneous_nonidentity_fixed_unique (n : ℕ)
    (a : CyclicHomogeneousExponent p n) (g : PrimeCycleGroup p) (hg : g ≠ 1)
    (hfix : (cyclicHomogeneousExponentAction p n).smul g a = a) :
    a.val = cyclicConstantExponent p (n / p) := by
  have hh := primeShift_fixed_exponent_eq p a.val g hg (congrArg Subtype.val hfix)
  simpa only [a.property] using hh

theorem cyclicHomogeneous_action_free_of_not_dvd (n : ℕ) (hn : ¬ p ∣ n) :
    ∀ a : CyclicHomogeneousExponent p n,
      Function.Injective (fun g : PrimeCycleGroup p =>
        (cyclicHomogeneousExponentAction p n).smul g a) := by
  letI := cyclicHomogeneousExponentAction p n
  intro a g h heq
  change g • a = h • a at heq
  have hfix : (h⁻¹ * g) • a = a := by rw [mul_smul, heq, inv_smul_smul]
  have hunit : h⁻¹ * g = 1 := by
    by_contra hg
    exact primeShift_no_fixed_exponent_of_not_dvd p a.val
      (by simpa only [a.property] using hn) (h⁻¹ * g) hg (congrArg Subtype.val hfix)
  exact (inv_mul_eq_one.mp hunit).symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicAugmentationKernel.lean -/
section

section
/-! # An explicit basis of an augmentation kernel

For a finite permutation basis with a distinguished fixed vector δ, the
augmentation kernel has basis e_i − e_δ, i ≠ δ. The construction is valid
over every commutative coefficient ring and carries the expected permutation
action. It is used degreewise in the exceptional prime-rank lifting argument.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset

variable {I K : Type*} [Fintype I] [CommRing K]

theorem sum_eq_pivot_add_sum_complement {M : Type*} [AddCommMonoid M]
    (i₀ : I) (f : I → M) :
    (∑ i, f i) = f i₀ + ∑ i : {i : I // i ≠ i₀}, f i.val := by
  have he : (∑ i : {i : I // i ≠ i₀}, f i.val) =
      ∑ i ∈ Finset.univ.erase i₀, f i :=
    (Finset.sum_subtype (Finset.univ.erase i₀) (fun i => by simp) f).symm
  rw [he]
  calc
    (∑ i, f i) = (∑ i ∈ Finset.univ.erase i₀, f i) + f i₀ :=
      (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i₀)).symm
    _ = f i₀ + ∑ i ∈ Finset.univ.erase i₀, f i := add_comm _ _

def finiteAugmentation (K : Type*) [CommRing K] : (I → K) →ₗ[K] K where
  toFun x := ∑ i, x i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

def augmentedVector (i₀ : I) (x : {i : I // i ≠ i₀} → K) : I → K :=
  fun i => if h : i = i₀ then -(∑ j, x j) else x ⟨i, h⟩

theorem augmentedVector_sum (i₀ : I) (x : {i : I // i ≠ i₀} → K) :
    (∑ i, augmentedVector i₀ x i) = 0 := by
  rw [sum_eq_pivot_add_sum_complement i₀]
  have hrest : (∑ i : {i : I // i ≠ i₀}, augmentedVector i₀ x i.val) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [augmentedVector, dif_neg i.property]
  rw [hrest]
  simp [augmentedVector]

def augmentationKernelEquiv (K : Type*) [CommRing K] (i₀ : I) :
    ({i : I // i ≠ i₀} → K) ≃ₗ[K] LinearMap.ker (finiteAugmentation (I := I) K) where
  toFun x := ⟨augmentedVector i₀ x, augmentedVector_sum i₀ x⟩
  invFun x := fun i => x.val i.val
  left_inv x := by
    funext i
    simp only [augmentedVector, dif_neg i.property]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀
    · subst i
      simp only [augmentedVector, dif_pos rfl]
      have hx : x.val i₀ + ∑ j : {i : I // i ≠ i₀}, x.val j.val = 0 := by
        rw [← sum_eq_pivot_add_sum_complement]
        exact x.property
      exact (eq_neg_iff_add_eq_zero.mpr hx).symm
    · simp only [augmentedVector, dif_neg hi]
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀ <;>
      simp [augmentedVector, hi, Finset.sum_add_distrib, neg_add, add_comm]
  map_smul' c x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀ <;>
      simp [augmentedVector, hi, Finset.mul_sum, smul_eq_mul]

def augmentationKernelBasis (K : Type*) [CommRing K] (i₀ : I) :
    Module.Basis {i : I // i ≠ i₀} K (LinearMap.ker (finiteAugmentation (I := I) K)) :=
  (Pi.basisFun K {i : I // i ≠ i₀}).map (augmentationKernelEquiv K i₀)

/-- These really are the difference vectors in the original finite module. -/
theorem augmentationKernelBasis_apply (i₀ : I) (j : {i : I // i ≠ i₀}) (i : I) :
    (augmentationKernelBasis K i₀ j).val i =
      (if i = j.val then 1 else 0) - (if i = i₀ then 1 else 0) := by
  by_cases hi : i = i₀
  · subst i
    have hj : i₀ ≠ j.val := Ne.symm j.property
    simp [augmentationKernelBasis, Module.Basis.map_apply, augmentationKernelEquiv,
      augmentedVector, Pi.basisFun_apply, Pi.single_apply, hj]
  · simp [augmentationKernelBasis, Module.Basis.map_apply, augmentationKernelEquiv,
      augmentedVector, Pi.basisFun_apply, Pi.single_apply, hi, Subtype.ext_iff, eq_comm]

/-- A permutation fixing the pivot permutes the difference-basis vectors.
The equation is in the original function space, so it applies immediately
after any equivariant monomial-basis identification. -/
theorem augmentationKernelBasis_covariant (i₀ : I) (e : Equiv.Perm I) (he : e i₀ = i₀)
    (j : {i : I // i ≠ i₀}) :
    (fun i => (augmentationKernelBasis K i₀ j).val (e.symm i)) =
      (augmentationKernelBasis K i₀
        ⟨e j.val, by
          intro h
          apply j.property
          exact e.injective (h.trans he.symm)⟩).val := by
  funext i
  rw [augmentationKernelBasis_apply, augmentationKernelBasis_apply]
  have h₁ : e.symm i = j.val ↔ i = e j.val := by
    constructor
    · intro h
      simpa using congrArg e h
    · intro h
      rw [h, Equiv.symm_apply_apply]
  have h₀ : e.symm i = i₀ ↔ i = i₀ := by
    constructor
    · intro h
      have hh := congrArg e h
      simpa only [Equiv.apply_symm_apply, he] using hh
    · intro h
      subst i
      exact e.symm_apply_eq.mpr he.symm
  simp only [h₁, h₀]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousCoordinates.lean -/
section

section
/-! # Actual homogeneous polynomial coordinates for cyclic lifting

The homogeneous component is the existing `polynomialDegreePiece` submodule
of the ordinary multivariate polynomial ring. Evaluation at all variables
equal to one becomes the finite coefficient sum in its monomial coordinates.
Consequently its actual kernel has the difference-monomial basis used by the
prime-cyclic lifting construction.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

abbrev CyclicPolynomialPiece (n : ℕ) :=
  polynomialDegreePiece (V := ZMod p) (K := K) n

theorem cyclicPolynomialPiece_mem_iff_supported (n : ℕ) (f : MvPolynomial (ZMod p) K) :
    f ∈ CyclicPolynomialPiece p K n ↔
      f.coeff ∈ Finsupp.supported K K {a : ZMod p →₀ ℕ | a.degree = n} := by
  rw [Finsupp.mem_supported']
  change (∀ a : ZMod p →₀ ℕ, vertexDegree (fun x => a x) ≠ n → f.coeff a = 0) ↔ _
  simp only [vertexDegree, ← Finsupp.degree_eq_sum, Set.mem_setOf_eq]

def cyclicPolynomialSupportedEquiv (n : ℕ) :
    CyclicPolynomialPiece p K n ≃ₗ[K]
      Finsupp.supported K K {a : ZMod p →₀ ℕ | a.degree = n} where
  toFun f := ⟨f.val.coeff,
    (cyclicPolynomialPiece_mem_iff_supported p K n f.val).mp f.property⟩
  invFun f := ⟨(MvPolynomial.basisMonomials (ZMod p) K).repr.symm f.val, by
    apply (cyclicPolynomialPiece_mem_iff_supported p K n _).mpr
    change (MvPolynomial.basisMonomials (ZMod p) K).repr
      ((MvPolynomial.basisMonomials (ZMod p) K).repr.symm f.val) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.apply_symm_apply f.val
  map_add' f g := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.map_smul c f.val

def cyclicPolynomialCoordinates (n : ℕ) :
    CyclicPolynomialPiece p K n ≃ₗ[K] (CyclicHomogeneousExponent p n → K) :=
  (cyclicPolynomialSupportedEquiv p K n).trans
    ((Finsupp.supportedEquivFinsupp {a : ZMod p →₀ ℕ | a.degree = n}).trans
      (Finsupp.linearEquivFunOnFinite K K (CyclicHomogeneousExponent p n)))

@[simp] theorem cyclicPolynomialCoordinates_apply (n : ℕ)
    (f : CyclicPolynomialPiece p K n) (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n f a = f.val.coeff a.val := rfl

def cyclicHomogeneousMonomial (n : ℕ) (a : CyclicHomogeneousExponent p n) :
    CyclicPolynomialPiece p K n :=
  ⟨MvPolynomial.monomial a.val 1, by
    have hd : vertexDegree (fun x => a.val x) = n := by
      rw [vertexDegree, ← Finsupp.degree_eq_sum]
      exact a.property
    intro b hb
    have hne : a.val ≠ b := by
      intro he
      subst b
      exact hb hd
    simp only [MvPolynomial.coeff_monomial, if_neg hne]⟩

@[simp] theorem cyclicPolynomialCoordinates_monomial (n : ℕ)
    (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n (cyclicHomogeneousMonomial p K n a) = Pi.single a 1 := by
  funext b
  rw [cyclicPolynomialCoordinates_apply]
  simp [cyclicHomogeneousMonomial, MvPolynomial.coeff_monomial,
    Pi.single_apply, Subtype.ext_iff, eq_comm]

def cyclicHomogeneousMonomialBasis (n : ℕ) :
    Module.Basis (CyclicHomogeneousExponent p n) K (CyclicPolynomialPiece p K n) :=
  (Pi.basisFun K (CyclicHomogeneousExponent p n)).map (cyclicPolynomialCoordinates p K n).symm

theorem cyclicHomogeneousMonomialBasis_apply (n : ℕ) (a : CyclicHomogeneousExponent p n) :
    cyclicHomogeneousMonomialBasis p K n a = cyclicHomogeneousMonomial p K n a := by
  apply (cyclicPolynomialCoordinates p K n).injective
  simp only [cyclicHomogeneousMonomialBasis, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Pi.basisFun_apply, cyclicPolynomialCoordinates_monomial]

theorem rename_equiv_coefficient (e : Equiv.Perm (ZMod p))
    (f : MvPolynomial (ZMod p) K) (a : ZMod p →₀ ℕ) :
    (MvPolynomial.rename e f).coeff a = f.coeff (a.mapDomain e.symm) := by
  have he : (a.mapDomain e.symm).mapDomain e = a := by
    rw [← Finsupp.mapDomain_comp]
    have hh : (e : ZMod p → ZMod p) ∘ e.symm = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hh, Finsupp.mapDomain_id]
  simpa only [he] using
    MvPolynomial.coeff_rename_mapDomain e e.injective f (a.mapDomain e.symm)

def cyclicHomogeneousRename (n : ℕ) (e : Equiv.Perm (ZMod p)) :
    Module.End K (CyclicPolynomialPiece p K n) where
  toFun f := ⟨MvPolynomial.rename e f.val, by
    intro a ha
    rw [rename_equiv_coefficient]
    apply f.property
    have hd : vertexDegree (fun x => (a.mapDomain e.symm) x) = vertexDegree (fun x => a x) := by
      simp only [vertexDegree, ← Finsupp.degree_eq_sum, Finsupp.degree_mapDomain]
    rwa [hd]⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

theorem cyclicPolynomialCoordinates_rename (n : ℕ) (e : Equiv.Perm (ZMod p))
    (f : CyclicPolynomialPiece p K n) (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n (cyclicHomogeneousRename p K n e f) a =
      cyclicPolynomialCoordinates p K n f
        ⟨a.val.mapDomain e.symm, by rw [Finsupp.degree_mapDomain]; exact a.property⟩ := by
  exact rename_equiv_coefficient p K e f.val a.val

/-- Literal evaluation at the all-one root assignment, restricted to the
actual homogeneous polynomial component. -/
def cyclicHomogeneousAugmentation (n : ℕ) : CyclicPolynomialPiece p K n →ₗ[K] K :=
  (MvPolynomial.aeval (fun _ : ZMod p => (1 : K))).toLinearMap.comp
    (CyclicPolynomialPiece p K n).subtype

theorem cyclicHomogeneousAugmentation_eq_sum (n : ℕ) :
    cyclicHomogeneousAugmentation p K n =
      (finiteAugmentation (I := CyclicHomogeneousExponent p n) K).comp
        (cyclicPolynomialCoordinates p K n).toLinearMap := by
  apply (cyclicHomogeneousMonomialBasis p K n).ext
  intro a
  rw [cyclicHomogeneousMonomialBasis_apply]
  change MvPolynomial.aeval (fun _ : ZMod p => (1 : K))
      (MvPolynomial.monomial a.val 1) =
    ∑ i, cyclicPolynomialCoordinates p K n (cyclicHomogeneousMonomial p K n a) i
  rw [cyclicPolynomialCoordinates_monomial]
  simp [MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod]

def cyclicHomogeneousAugmentationKernelEquiv (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousAugmentation p K n) ≃ₗ[K]
      LinearMap.ker (finiteAugmentation (I := CyclicHomogeneousExponent p n) K) where
  toFun f := ⟨cyclicPolynomialCoordinates p K n f.val, by
    change finiteAugmentation K (cyclicPolynomialCoordinates p K n f.val) = 0
    have hh : cyclicHomogeneousAugmentation p K n f.val = 0 := f.property
    simp only [cyclicHomogeneousAugmentation_eq_sum, LinearMap.comp_apply,
      LinearEquiv.coe_coe] at hh
    exact hh⟩
  invFun f := ⟨(cyclicPolynomialCoordinates p K n).symm f.val, by
    change cyclicHomogeneousAugmentation p K n
      ((cyclicPolynomialCoordinates p K n).symm f.val) = 0
    rw [cyclicHomogeneousAugmentation_eq_sum, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ f.val
  right_inv f := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ f.val
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

def cyclicHomogeneousPivot (n : ℕ) (hn : p ∣ n) : CyclicHomogeneousExponent p n :=
  ⟨cyclicConstantExponent p (n / p), by
    rw [cyclicConstantExponent_degree, Nat.mul_comm, Nat.div_mul_cancel hn]⟩

def cyclicHomogeneousDifferenceBasis (n : ℕ) (hn : p ∣ n) :
    Module.Basis {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn} K
      (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) :=
  (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn)).map
    (cyclicHomogeneousAugmentationKernelEquiv p K n).symm

/-- The actual kernel vectors are differences of the original monomials;
the pivot is the unique invariant exponent vector in degree n. -/
theorem cyclicHomogeneousDifferenceBasis_apply (n : ℕ) (hn : p ∣ n)
    (a : {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}) :
    (cyclicHomogeneousDifferenceBasis p K n hn a).val =
      cyclicHomogeneousMonomial p K n a.val -
        cyclicHomogeneousMonomial p K n (cyclicHomogeneousPivot p n hn) := by
  apply (cyclicPolynomialCoordinates p K n).injective
  have hleft : cyclicPolynomialCoordinates p K n
      (cyclicHomogeneousDifferenceBasis p K n hn a).val =
        (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn) a).val := by
    change cyclicPolynomialCoordinates p K n
      ((cyclicPolynomialCoordinates p K n).symm
        (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn) a).val) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [hleft, map_sub, cyclicPolynomialCoordinates_monomial,
    cyclicPolynomialCoordinates_monomial]
  funext b
  rw [augmentationKernelBasis_apply]
  simp only [Pi.single_apply, Pi.sub_apply, eq_comm]
  split_ifs <;> rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousAction.lean -/
section

section
/-! # Actual cyclic polynomial actions and free kernel coordinates -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

theorem primeTranslation_symm (g : PrimeCycleGroup p) :
    (Equiv.addLeft g.toAdd).symm = Equiv.addLeft (g⁻¹).toAdd := by
  apply Equiv.ext
  intro x
  apply (Equiv.addLeft g.toAdd).injective
  rw [Equiv.apply_symm_apply]
  change x = g.toAdd + (-g.toAdd + x)
  abel

def cyclicPolynomialRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p) (CyclicPolynomialPiece p K n) where
  toFun g := cyclicHomogeneousRename p K n (Equiv.addLeft g.toAdd)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.rename (Equiv.addLeft (0 : ZMod p)) f.val = f.val
    have he : (Equiv.addLeft (0 : ZMod p) : ZMod p → ZMod p) = id := by
      funext x
      exact zero_add x
    rw [he, MvPolynomial.rename_id_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.rename (Equiv.addLeft (g.toAdd + h.toAdd)) f.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (MvPolynomial.rename (Equiv.addLeft h.toAdd) f.val)
    rw [MvPolynomial.rename_rename]
    have he : (Equiv.addLeft (g.toAdd + h.toAdd) : ZMod p → ZMod p) =
        (Equiv.addLeft g.toAdd) ∘ (Equiv.addLeft h.toAdd) := by
      funext x
      exact add_assoc g.toAdd h.toAdd x
    rw [he]

theorem cyclicPolynomialCoordinates_equivariant (n : ℕ) :
    letI := cyclicHomogeneousExponentAction p n
    RepresentationIntertwines (cyclicPolynomialRepresentation p K n)
      permutationFunctionRepresentation (cyclicPolynomialCoordinates p K n).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  funext a
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val).coeff a.val =
    f.val.coeff (a.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val a.val

theorem cyclicHomogeneousAugmentation_invariant (n : ℕ) (g : PrimeCycleGroup p)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousAugmentation p K n (cyclicPolynomialRepresentation p K n g f) =
      cyclicHomogeneousAugmentation p K n f := by
  letI := cyclicHomogeneousExponentAction p n
  rw [cyclicHomogeneousAugmentation_eq_sum]
  change (∑ a, cyclicPolynomialCoordinates p K n (cyclicPolynomialRepresentation p K n g f) a) =
    ∑ a, cyclicPolynomialCoordinates p K n f a
  calc
    _ = ∑ a, cyclicPolynomialCoordinates p K n f (g⁻¹ • a) :=
      congrArg (fun z : CyclicHomogeneousExponent p n → K => ∑ a, z a)
        (cyclicPolynomialCoordinates_equivariant p K n g f)
    _ = _ := Fintype.sum_equiv (MulAction.toPerm (g⁻¹)) _ _ (fun _ => rfl)

def cyclicAugmentationKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) (by
      intro g f hf
      change cyclicHomogeneousAugmentation p K n (cyclicPolynomialRepresentation p K n g f) = 0
      rw [cyclicHomogeneousAugmentation_invariant]
      exact hf)

theorem cyclicHomogeneousPivot_fixed (n : ℕ) (hn : p ∣ n) (g : PrimeCycleGroup p) :
    (cyclicHomogeneousExponentAction p n).smul g (cyclicHomogeneousPivot p n hn) =
      cyclicHomogeneousPivot p n hn := by
  apply Subtype.ext
  exact primeShift_constant_exponent_fixed p (n / p) g

abbrev CyclicNonpivotExponent (n : ℕ) (hn : p ∣ n) :=
  {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}

def cyclicNonpivotExponentAction (n : ℕ) (hn : p ∣ n) :
    MulAction (PrimeCycleGroup p) (CyclicNonpivotExponent p n hn) := by
  letI := cyclicHomogeneousExponentAction p n
  exact {
    smul := fun g a => ⟨g • a.val, by
      intro h
      have hh := congrArg (fun b => g⁻¹ • b) h
      have hpivot : g⁻¹ • cyclicHomogeneousPivot p n hn =
          cyclicHomogeneousPivot p n hn := cyclicHomogeneousPivot_fixed p n hn g⁻¹
      rw [inv_smul_smul, hpivot] at hh
      exact a.property hh⟩
    one_smul := fun a => Subtype.ext (one_smul (PrimeCycleGroup p) a.val)
    mul_smul := fun g h a => Subtype.ext (mul_smul g h a.val) }

/-- Excluding the unique invariant exponent vector leaves a free action. -/
theorem cyclicNonpivotExponent_no_fixed (n : ℕ) (hn : p ∣ n)
    (g : PrimeCycleGroup p) (a : CyclicNonpivotExponent p n hn)
    (hfix : (cyclicNonpivotExponentAction p n hn).smul g a = a) : g = 1 := by
  by_contra hg
  apply a.property
  apply Subtype.ext
  exact cyclicHomogeneous_nonidentity_fixed_unique p n a.val g hg
    (congrArg Subtype.val hfix)

def cyclicAugmentationComplementCoordinates (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousAugmentation p K n) ≃ₗ[K]
      (CyclicNonpivotExponent p n hn → K) :=
  (cyclicHomogeneousAugmentationKernelEquiv p K n).trans
    (augmentationKernelEquiv K (cyclicHomogeneousPivot p n hn)).symm

@[simp] theorem cyclicAugmentationComplementCoordinates_apply (n : ℕ) (hn : p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousAugmentation p K n))
    (a : CyclicNonpivotExponent p n hn) :
    cyclicAugmentationComplementCoordinates p K n hn f a = f.val.val.coeff a.val.val := rfl

/-- In the actual homogeneous kernel, the difference-monomial coordinates
carry the free permutation representation on nonpivot exponents. -/
theorem cyclicAugmentationComplementCoordinates_equivariant (n : ℕ) (hn : p ∣ n) :
    letI := cyclicNonpivotExponentAction p n hn
    RepresentationIntertwines (cyclicAugmentationKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicAugmentationComplementCoordinates p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  funext a
  change cyclicAugmentationComplementCoordinates p K n hn
      (cyclicAugmentationKernelRepresentation p K n g f) a =
    cyclicAugmentationComplementCoordinates p K n hn f (g⁻¹ • a)
  rw [cyclicAugmentationComplementCoordinates_apply,
    cyclicAugmentationComplementCoordinates_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val.val =
    f.val.val.coeff (a.val.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val.val

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicRetractionKernel.lean -/
section


section

/-! # The actual homogeneous kernel of the prime orbit retraction

In degree `n`, the orbit retraction is zero if `p` does not divide `n`.
Otherwise it is the coefficient sum, followed by the monomial embedding in
degree `n / p`.  This identifies its actual kernel with the free cyclic
permutation modules used by the equivariant lifting argument.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

def cyclicHomogeneousOrbitRetraction (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K] K[X] :=
  (primeOrbitRetraction p).comp (CyclicPolynomialPiece p K n).subtype

@[simp] theorem cyclicHomogeneousAugmentation_monomial (n : ℕ)
    (a : CyclicHomogeneousExponent p n) :
    cyclicHomogeneousAugmentation p K n (cyclicHomogeneousMonomial p K n a) = 1 := by
  change MvPolynomial.eval (fun _ => (1 : K)) (MvPolynomial.monomial a.val (1 : K)) = 1
  simp [MvPolynomial.eval_monomial]

theorem cyclicHomogeneousOrbitRetraction_eq (n : ℕ) :
    cyclicHomogeneousOrbitRetraction p K n =
      if p ∣ n then
        (Polynomial.monomial (n / p)).comp (cyclicHomogeneousAugmentation p K n)
      else 0 := by
  apply (cyclicHomogeneousMonomialBasis p K n).ext
  intro a
  rw [cyclicHomogeneousMonomialBasis_apply]
  have ha : a.val.sum (fun _ i => i) = n := a.property
  have he : cyclicHomogeneousOrbitRetraction p K n
      (cyclicHomogeneousMonomial p K n a) =
      if p ∣ n then Polynomial.monomial (n / p) 1 else 0 := by
    change primeOrbitRetraction p (MvPolynomial.monomial a.val (1 : K)) = _
    rw [primeOrbitRetraction_monomial, ha]
  rw [he]
  by_cases hn : p ∣ n
  · simp only [if_pos hn, LinearMap.comp_apply, cyclicHomogeneousAugmentation_monomial]
  · simp only [if_neg hn, LinearMap.zero_apply]

theorem cyclicHomogeneousOrbitRetraction_apply (n : ℕ)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousOrbitRetraction p K n f =
      if p ∣ n then Polynomial.monomial (n / p)
        (cyclicHomogeneousAugmentation p K n f) else 0 := by
  rw [cyclicHomogeneousOrbitRetraction_eq]
  split_ifs <;> rfl

theorem cyclicHomogeneousOrbitKernel_eq_top (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) = ⊤ := by
  rw [cyclicHomogeneousOrbitRetraction_eq, if_neg hn, LinearMap.ker_zero]

theorem cyclicHomogeneousOrbitKernel_eq_augmentationKernel (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) =
      LinearMap.ker (cyclicHomogeneousAugmentation p K n) := by
  ext f
  change cyclicHomogeneousOrbitRetraction p K n f = 0 ↔
    cyclicHomogeneousAugmentation p K n f = 0
  rw [cyclicHomogeneousOrbitRetraction_apply, if_pos hn]
  exact Polynomial.monomial_eq_zero_iff _ _

def cyclicOrbitKernelCoordinatesOfNotDvd (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (CyclicHomogeneousExponent p n → K) :=
  ((LinearEquiv.ofEq _ _ (cyclicHomogeneousOrbitKernel_eq_top p K n hn)).trans
    Submodule.topEquiv).trans (cyclicPolynomialCoordinates p K n)

@[simp] theorem cyclicOrbitKernelCoordinatesOfNotDvd_apply (n : ℕ) (hn : ¬p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (a : CyclicHomogeneousExponent p n) :
    cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f a = f.val.val.coeff a.val := by
  change cyclicPolynomialCoordinates p K n f.val a = f.val.val.coeff a.val
  exact cyclicPolynomialCoordinates_apply p K n f.val a

def cyclicOrbitKernelCoordinatesOfDvd (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      ({a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn} → K) :=
  ((LinearEquiv.ofEq _ _
    (cyclicHomogeneousOrbitKernel_eq_augmentationKernel p K n hn)).trans
      (cyclicHomogeneousAugmentationKernelEquiv p K n)).trans
    (augmentationKernelEquiv K (cyclicHomogeneousPivot p n hn)).symm

@[simp] theorem cyclicOrbitKernelCoordinatesOfDvd_apply (n : ℕ) (hn : p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (a : {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}) :
    cyclicOrbitKernelCoordinatesOfDvd p K n hn f a = f.val.val.coeff a.val.val := by
  change cyclicPolynomialCoordinates p K n f.val a.val = f.val.val.coeff a.val.val
  exact cyclicPolynomialCoordinates_apply p K n f.val a.val

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitKernelCoinduced.lean -/
section


section

/-! # Coinduced coordinates for the actual orbit-retraction kernel

The representation here is the literal variable-renaming action restricted to
the kernel of the homogeneous orbit retraction.  The coordinate equivalences
are built from actual monomial coefficients.  Their free-orbit decomposition
provides the coinduced target required by the equivariant lifting step.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

theorem cyclicHomogeneousOrbitRetraction_invariant (n : ℕ) (g : PrimeCycleGroup p)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousOrbitRetraction p K n (cyclicPolynomialRepresentation p K n g f) =
      cyclicHomogeneousOrbitRetraction p K n f := by
  simp only [cyclicHomogeneousOrbitRetraction_apply,
    cyclicHomogeneousAugmentation_invariant]

theorem cyclicOrbitKernel_invariant (n : ℕ) :
    ∀ (g : PrimeCycleGroup p) (f : CyclicPolynomialPiece p K n),
      f ∈ LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) →
        cyclicPolynomialRepresentation p K n g f ∈
          LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) := by
  intro g f hf
  change cyclicHomogeneousOrbitRetraction p K n
    (cyclicPolynomialRepresentation p K n g f) = 0
  rw [cyclicHomogeneousOrbitRetraction_invariant]
  exact hf

def cyclicOrbitKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (cyclicOrbitKernel_invariant p K n)

theorem cyclicOrbitKernelCoordinatesOfNotDvd_equivariant (n : ℕ) (hn : ¬p ∣ n) :
    letI := cyclicHomogeneousExponentAction p n
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  funext a
  change cyclicOrbitKernelCoordinatesOfNotDvd p K n hn
      (cyclicOrbitKernelRepresentation p K n g f) a =
    cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f (g⁻¹ • a)
  rw [cyclicOrbitKernelCoordinatesOfNotDvd_apply, cyclicOrbitKernelCoordinatesOfNotDvd_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val =
    f.val.val.coeff (a.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val

theorem cyclicOrbitKernelCoordinatesOfDvd_equivariant (n : ℕ) (hn : p ∣ n) :
    letI := cyclicNonpivotExponentAction p n hn
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  funext a
  change cyclicOrbitKernelCoordinatesOfDvd p K n hn
      (cyclicOrbitKernelRepresentation p K n g f) a =
    cyclicOrbitKernelCoordinatesOfDvd p K n hn f (g⁻¹ • a)
  rw [cyclicOrbitKernelCoordinatesOfDvd_apply, cyclicOrbitKernelCoordinatesOfDvd_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val.val =
    f.val.val.coeff (a.val.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val.val

abbrev CyclicOrbitIndexOfNotDvd (n : ℕ) : Type :=
  letI := cyclicHomogeneousExponentAction p n
  MulAction.orbitRel.Quotient (PrimeCycleGroup p) (CyclicHomogeneousExponent p n)

abbrev CyclicOrbitIndexOfDvd (n : ℕ) (hn : p ∣ n) : Type :=
  letI := cyclicNonpivotExponentAction p n hn
  MulAction.orbitRel.Quotient (PrimeCycleGroup p) (CyclicNonpivotExponent p n hn)

theorem cyclicHomogeneous_no_fixed_of_not_dvd (n : ℕ) (hn : ¬p ∣ n) :
    ∀ (g : PrimeCycleGroup p) (a : CyclicHomogeneousExponent p n),
      (cyclicHomogeneousExponentAction p n).smul g a = a → g = 1 := by
  letI := cyclicHomogeneousExponentAction p n
  intro g a hfix
  apply cyclicHomogeneous_action_free_of_not_dvd p n hn a
  exact hfix.trans (one_smul (PrimeCycleGroup p) a).symm

def cyclicOrbitKernelCoinducedOfNotDvd (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → CyclicOrbitIndexOfNotDvd p n → K) := by
  letI := cyclicHomogeneousExponentAction p n
  exact (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn).trans
    (freePermutationCoinducedEquiv (cyclicHomogeneous_no_fixed_of_not_dvd p n hn))

theorem cyclicOrbitKernelCoinducedOfNotDvd_equivariant (n : ℕ) (hn : ¬p ∣ n) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      coinducedRepresentation (cyclicOrbitKernelCoinducedOfNotDvd p K n hn).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  change freePermutationCoinducedEquiv
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn)
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn
        (cyclicOrbitKernelRepresentation p K n g f)) =
    coinducedRepresentation (K := K) (C := CyclicOrbitIndexOfNotDvd p n → K) g
      (freePermutationCoinducedEquiv
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn)
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f))
  exact (congrArg
    (freePermutationCoinducedEquiv (cyclicHomogeneous_no_fixed_of_not_dvd p n hn))
    (cyclicOrbitKernelCoordinatesOfNotDvd_equivariant p K n hn g f)).trans
    (freePermutationCoinducedEquiv_equivariant
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn) g
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f))

def cyclicOrbitKernelCoinducedOfDvd (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → CyclicOrbitIndexOfDvd p n hn → K) := by
  letI := cyclicNonpivotExponentAction p n hn
  exact (cyclicOrbitKernelCoordinatesOfDvd p K n hn).trans
    (freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn))

theorem cyclicOrbitKernelCoinducedOfDvd_equivariant (n : ℕ) (hn : p ∣ n) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      coinducedRepresentation (cyclicOrbitKernelCoinducedOfDvd p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  change freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn)
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn
        (cyclicOrbitKernelRepresentation p K n g f)) =
    coinducedRepresentation (K := K) (C := CyclicOrbitIndexOfDvd p n hn → K) g
      (freePermutationCoinducedEquiv
      (cyclicNonpivotExponent_no_fixed p n hn)
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn f))
  exact (congrArg
    (freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn))
    (cyclicOrbitKernelCoordinatesOfDvd_equivariant p K n hn g f)).trans
    (freePermutationCoinducedEquiv_equivariant
      (cyclicNonpivotExponent_no_fixed p n hn) g
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn f))

/-- Every degree of the actual orbit-retraction kernel is coinduced, with
no hypothesis on the characteristic or invertibility of the group order. -/
theorem cyclicOrbitKernel_isCoinduced (n : ℕ) :
    ∃ (J : Type) (e : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K)),
      RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  by_cases hn : p ∣ n
  · exact ⟨CyclicOrbitIndexOfDvd p n hn, cyclicOrbitKernelCoinducedOfDvd p K n hn,
      cyclicOrbitKernelCoinducedOfDvd_equivariant p K n hn⟩
  · exact ⟨CyclicOrbitIndexOfNotDvd p n, cyclicOrbitKernelCoinducedOfNotDvd p K n hn,
      cyclicOrbitKernelCoinducedOfNotDvd_equivariant p K n hn⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBoundaryKernel.lean -/
section


section

/-! # The combined boundary and orbit kernel

The quotient map records the genuine top-face boundary and the orbit
retraction simultaneously.  Its homogeneous kernel is top multiplication
times the corresponding orbit kernel one rank lower in degree.  Degrees
below the top rank are handled explicitly; both kernels are then zero.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

local instance : LinearOrder (ZMod p) := LinearOrder.lift' ZMod.val (ZMod.val_injective p)

def cyclicPolynomialTop : MvPolynomial (ZMod p) K :=
  ∏ v : ZMod p, MvPolynomial.X v

omit [CharP K p] in
theorem cyclicPolynomialTop_eq_esymm :
    cyclicPolynomialTop p K = MvPolynomial.esymm (ZMod p) K p := by
  unfold cyclicPolynomialTop MvPolynomial.esymm
  have hc : (Finset.univ : Finset (ZMod p)).card = p := by simp
  have he : (Finset.univ : Finset (ZMod p)).powersetCard p = {Finset.univ} :=
    (congrArg (fun n => (Finset.univ : Finset (ZMod p)).powersetCard n) hc.symm).trans
      (Finset.powersetCard_self _)
  rw [he]
  simp

omit [CharP K p] in
theorem cyclicPolynomialTop_degree :
    cyclicPolynomialTop p K ∈ CyclicPolynomialPiece p K p := by
  have hd : vertexDegree (fun v : ZMod p => fullExponent (ZMod p) v) = p := by
    simp [vertexDegree, ZMod.card]
  have hh := monomial_mem_polynomialDegreePiece (fullExponent (ZMod p)) (1 : K)
  rw [hd, full_monomial_eq_prod] at hh
  exact hh

omit [CharP K p] in
theorem cyclicPolynomialTop_mul_injective :
    Function.Injective (fun f : MvPolynomial (ZMod p) K => cyclicPolynomialTop p K * f) :=
  (MvPolynomial.isRegular_prod_X (R := K) (Finset.univ : Finset (ZMod p))).left

theorem cyclicPolynomialTop_orbitRetraction (f : MvPolynomial (ZMod p) K) :
    primeOrbitRetraction p (cyclicPolynomialTop p K * f) =
      Polynomial.X * primeOrbitRetraction p f := by
  rw [cyclicPolynomialTop_eq_esymm]
  exact primeOrbitRetraction_top_parameter p (Fact.out : p.Prime).pos (ZMod.card p) f

def cyclicBoundaryOrbitMap :
    MvPolynomial (ZMod p) K →ₗ[K]
      PolynomialBoundaryRing (ZMod p) K × K[X] :=
  polynomialBooleanBoundaryMap.toLinearMap.prod (primeOrbitRetraction p)

def cyclicBoundaryOrbitDegreeMap (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K]
      PolynomialBoundaryRing (ZMod p) K × K[X] :=
  (cyclicBoundaryOrbitMap p K).comp (CyclicPolynomialPiece p K n).subtype

theorem cyclicBoundaryOrbitDegree_mem_kernel (n : ℕ) (f : CyclicPolynomialPiece p K n) :
    f ∈ LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) ↔
      polynomialBooleanBoundaryMap f.val = 0 ∧ primeOrbitRetraction p f.val = 0 := by
  change (polynomialBooleanBoundaryMap f.val, primeOrbitRetraction p f.val) = (0, 0) ↔ _
  exact Prod.mk_inj

omit [CharP K p] in
theorem cyclicPolynomialTop_predecessor_degree (m : ℕ) (f : MvPolynomial (ZMod p) K)
    (hf : cyclicPolynomialTop p K * f ∈ CyclicPolynomialPiece p K (m + p)) :
    f ∈ CyclicPolynomialPiece p K m := by
  intro a ha
  have hdeg : vertexDegree (fun v => (fullExponent (ZMod p) + a) v) =
      p + vertexDegree (fun v => a v) := by
    change vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v)) = _
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hn : vertexDegree (fun v => (fullExponent (ZMod p) + a) v) ≠ m + p := by
    rw [hdeg]
    omega
  have hh := hf (fullExponent (ZMod p) + a) hn
  rw [cyclicPolynomialTop, ← full_monomial_eq_prod,
    MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem cyclicBoundaryOrbitKernel_zero_below (n : ℕ) (hn : n < p)
    (f : LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) : f = 0 := by
  obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f.val).mp f.property
  obtain ⟨g, hg⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val.val).mp hb
  have hg0 : g = 0 := by
    ext a
    have hdeg : p ≤ vertexDegree (fun v => (fullExponent (ZMod p) + a) v) := by
      change p ≤ vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v))
      rw [vertexDegree_add]
      simp [vertexDegree]
    have hh := f.val.property (fullExponent (ZMod p) + a) (by omega)
    rw [← hg, ← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
    exact hh
  apply Subtype.ext
  apply Subtype.ext
  change f.val.val = 0
  rw [← hg, hg0, mul_zero]

theorem cyclicOrbitKernel_zero_degree
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K 0)) : f = 0 := by
  have hcoeff : ∀ a : ZMod p →₀ ℕ, f.val.val.coeff a = 0 := by
    intro a
    by_cases ha : a = 0
    · subst a
      have hE := f.property
      change cyclicHomogeneousOrbitRetraction p K 0 f.val = 0 at hE
      rw [cyclicHomogeneousOrbitRetraction_apply, if_pos (dvd_zero p)] at hE
      have haug : cyclicHomogeneousAugmentation p K 0 f.val = 0 :=
        (Polynomial.monomial_eq_zero_iff _ _).mp hE
      rw [cyclicHomogeneousAugmentation_eq_sum] at haug
      change (∑ a : CyclicHomogeneousExponent p 0,
        cyclicPolynomialCoordinates p K 0 f.val a) = 0 at haug
      have hzero : ∀ a : CyclicHomogeneousExponent p 0, a.val = 0 := by
        intro a
        exact (Finsupp.degree_eq_zero_iff a.val).mp a.property
      letI : Unique (CyclicHomogeneousExponent p 0) := {
        default := ⟨0, by simp⟩
        uniq := fun a => Subtype.ext (hzero a) }
      rw [Finset.univ_unique, Finset.sum_singleton, cyclicPolynomialCoordinates_apply] at haug
      simpa only [hzero default] using haug
    · apply f.val.property
      change vertexDegree (fun v => a v) ≠ 0
      rw [vertexDegree, ← Finsupp.degree_eq_sum]
      exact fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
  apply Subtype.ext
  apply Subtype.ext
  exact MvPolynomial.ext _ _ hcoeff

def cyclicBoundaryOrbitTopMap (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) →ₗ[K]
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) := by
  by_cases hn : p ≤ n
  · refine {
      toFun := fun f => ⟨⟨cyclicPolynomialTop p K * f.val.val, ?_⟩, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
    · have hh := polynomialDegreePiece_mul p (n - p) (cyclicPolynomialTop p K) f.val.val
        (cyclicPolynomialTop_degree p K) f.val.property
      simpa only [Nat.add_sub_of_le hn] using hh
    · apply (cyclicBoundaryOrbitDegree_mem_kernel p K n _).mpr
      constructor
      · apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
        exact ⟨f.val.val, rfl⟩
      · rw [cyclicPolynomialTop_orbitRetraction]
        change Polynomial.X * cyclicHomogeneousOrbitRetraction p K (n - p) f.val = 0
        rw [show cyclicHomogeneousOrbitRetraction p K (n - p) f.val = 0 from f.property,
          mul_zero]
    · intro f g
      apply Subtype.ext
      apply Subtype.ext
      exact mul_add _ _ _
    · intro c f
      apply Subtype.ext
      apply Subtype.ext
      exact mul_smul_comm _ _ _
  · exact 0

theorem cyclicBoundaryOrbitTopMap_apply (n : ℕ) (hn : p ≤ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p))) :
    (cyclicBoundaryOrbitTopMap p K n f).val.val = cyclicPolynomialTop p K * f.val.val := by
  simp only [cyclicBoundaryOrbitTopMap, dif_pos hn]
  rfl

theorem cyclicBoundaryOrbitTopMap_bijective (n : ℕ) :
    Function.Bijective (cyclicBoundaryOrbitTopMap p K n) := by
  by_cases hn : p ≤ n
  · constructor
    · intro f g hfg
      apply Subtype.ext
      apply Subtype.ext
      apply cyclicPolynomialTop_mul_injective p K
      exact (cyclicBoundaryOrbitTopMap_apply p K n hn f).symm.trans
        ((congrArg (fun x => x.val.val) hfg).trans
          (cyclicBoundaryOrbitTopMap_apply p K n hn g))
    · intro f
      obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f.val).mp f.property
      obtain ⟨g, hg⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val.val).mp hb
      have hgdeg : g ∈ CyclicPolynomialPiece p K (n - p) := by
        apply cyclicPolynomialTop_predecessor_degree p K (n - p) g
        rw [Nat.sub_add_cancel hn]
        simpa only [cyclicPolynomialTop, hg] using f.val.property
      have hgE : primeOrbitRetraction p g = 0 := by
        apply (Polynomial.isRegular_X (R := K)).left
        change Polynomial.X * primeOrbitRetraction p g = Polynomial.X * (0 : K[X])
        rw [mul_zero, ← cyclicPolynomialTop_orbitRetraction,
          show cyclicPolynomialTop p K * g = f.val.val from hg]
        exact hE
      let g' : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) :=
        ⟨⟨g, hgdeg⟩, hgE⟩
      refine ⟨g', ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (cyclicBoundaryOrbitTopMap_apply p K n hn g').trans hg
  · have hlt : n < p := Nat.lt_of_not_ge hn
    have hz : n - p = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    have hsource : ∀ f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)), f = 0 := by
      rw [hz]
      exact cyclicOrbitKernel_zero_degree p K
    constructor
    · intro f g _
      exact (hsource f).trans (hsource g).symm
    · intro f
      exact ⟨0, (map_zero _).trans (cyclicBoundaryOrbitKernel_zero_below p K n hlt f).symm⟩

def cyclicBoundaryOrbitKernelEquiv (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) ≃ₗ[K]
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) :=
  LinearEquiv.ofBijective (cyclicBoundaryOrbitTopMap p K n)
    (cyclicBoundaryOrbitTopMap_bijective p K n)

omit [CharP K p] in
theorem cyclicPolynomialTop_rename (e : Equiv.Perm (ZMod p)) :
    MvPolynomial.rename e (cyclicPolynomialTop p K) = cyclicPolynomialTop p K := by
  simp only [cyclicPolynomialTop, map_prod, MvPolynomial.rename_X]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

def cyclicBoundaryOrbitKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) (by
      intro g f hf
      obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f).mp hf
      apply (cyclicBoundaryOrbitDegree_mem_kernel p K n _).mpr
      constructor
      · obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val).mp hb
        change cyclicPolynomialTop p K * x = f.val at hx
        apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
        refine ⟨MvPolynomial.rename (Equiv.addLeft g.toAdd) x, ?_⟩
        change cyclicPolynomialTop p K * MvPolynomial.rename (Equiv.addLeft g.toAdd) x =
          MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val
        rw [← hx, map_mul, cyclicPolynomialTop_rename]
      · change primeOrbitRetraction p
          (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val) = 0
        rw [primeOrbitRetraction_rename]
        exact hE)

theorem cyclicBoundaryOrbitKernelEquiv_equivariant (n : ℕ) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K (n - p))
      (cyclicBoundaryOrbitKernelRepresentation p K n)
      (cyclicBoundaryOrbitKernelEquiv p K n).toLinearMap := by
  intro g f
  apply Subtype.ext
  apply Subtype.ext
  by_cases hn : p ≤ n
  · change (cyclicBoundaryOrbitTopMap p K n
        (cyclicOrbitKernelRepresentation p K (n - p) g f)).val.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (cyclicBoundaryOrbitTopMap p K n f).val.val
    rw [cyclicBoundaryOrbitTopMap_apply p K n hn,
      cyclicBoundaryOrbitTopMap_apply p K n hn, map_mul, cyclicPolynomialTop_rename]
    rfl
  · change (cyclicBoundaryOrbitTopMap p K n
        (cyclicOrbitKernelRepresentation p K (n - p) g f)).val.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (cyclicBoundaryOrbitTopMap p K n f).val.val
    simp [cyclicBoundaryOrbitTopMap, hn]

/-- Every actual homogeneous combined kernel has regular-orbit coordinates.
This supplies the kernel hypothesis in the graded equivariant lifting theorem. -/
theorem cyclicBoundaryOrbitKernel_isCoinduced (n : ℕ) :
    ∃ J : Type, ∃ e : LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K),
      RepresentationIntertwines (cyclicBoundaryOrbitKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  obtain ⟨J, e, he⟩ := cyclicOrbitKernel_isCoinduced p K (n - p)
  let t := cyclicBoundaryOrbitKernelEquiv p K n
  refine ⟨J, t.symm.trans e, ?_⟩
  intro g x
  have ht : t.symm (cyclicBoundaryOrbitKernelRepresentation p K n g x) =
      cyclicOrbitKernelRepresentation p K (n - p) g (t.symm x) := by
    apply t.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := cyclicBoundaryOrbitKernelEquiv_equivariant p K n g (t.symm x)
    change t (cyclicOrbitKernelRepresentation p K (n - p) g (t.symm x)) =
      cyclicBoundaryOrbitKernelRepresentation p K n g (t (t.symm x)) at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  change e (t.symm (cyclicBoundaryOrbitKernelRepresentation p K n g x)) = _
  rw [ht]
  exact he g (t.symm x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicTopCoordinate.lean -/
section


section

/-! # The genuine fixed top-face quotient and its polynomial section

On the barycentric ring the quotient kills every proper face variable and
retains the top face.  On the polynomial side the section substitutes the
product of all vertex variables.  The orbit retraction is a left inverse of
this section, and its parameter action matches the source quotient exactly.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped Polynomial

section Boolean

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

def booleanTopPolynomialEvaluation : MvPolynomial (BooleanFace V) K →ₐ[K] K[X] :=
  MvPolynomial.aeval (fun F => if F = booleanTopFace then Polynomial.X else 0)

theorem booleanTopPolynomialEvaluation_forbidden
    (a : BooleanFace V →₀ ℕ) (ha : ¬IsChainExponent a) :
    booleanTopPolynomialEvaluation (K := K) (MvPolynomial.monomial a 1) = 0 := by
  have hx : ∃ F ∈ a.support, F ≠ booleanTopFace := by
    by_contra hn
    apply ha
    intro F hF G hG
    have hFt : F = booleanTopFace := by
      by_contra h
      exact hn ⟨F, hF, h⟩
    have hGt : G = booleanTopFace := by
      by_contra h
      exact hn ⟨G, hG, h⟩
    exact Or.inl (by rw [hFt, hGt])
  obtain ⟨F, hF, hFt⟩ := hx
  rw [booleanTopPolynomialEvaluation, MvPolynomial.aeval_monomial, map_one, one_mul]
  apply Finset.prod_eq_zero hF
  change (if F = booleanTopFace then Polynomial.X else (0 : K[X])) ^ a F = 0
  rw [if_neg hFt, zero_pow (Finsupp.mem_support_iff.mp hF)]

def booleanTopEvaluation : BooleanBarycentricRing V K →ₐ[K] K[X] :=
  Ideal.Quotient.liftₐ (forbiddenIdeal IsChainExponent) booleanTopPolynomialEvaluation (by
    have hi : forbiddenIdeal (K := K) (IsChainExponent (V := V)) ≤
        RingHom.ker booleanTopPolynomialEvaluation.toRingHom := by
      rw [forbiddenIdeal]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact booleanTopPolynomialEvaluation_forbidden a ha
    exact fun f hf => hi hf)

@[simp] theorem booleanTopEvaluation_face (F : BooleanFace V) :
    booleanTopEvaluation (K := K) (faceVariable F) =
      if F = booleanTopFace then Polynomial.X else 0 := by
  change booleanTopPolynomialEvaluation (MvPolynomial.X F) = _
  exact MvPolynomial.aeval_X _ _

@[simp] theorem booleanTopEvaluation_top :
    booleanTopEvaluation (V := V) (K := K) booleanTop = Polynomial.X := by
  simp [booleanTop]

theorem booleanTopEvaluation_rankParameter (r : ℕ) :
    booleanTopEvaluation (V := V) (K := K) (booleanRankParameter r) =
      if r = Fintype.card V then Polynomial.X else 0 := by
  rw [booleanRankParameter, map_sum]
  rw [Finset.sum_eq_single (booleanTopFace (V := V))]
  · by_cases h : r = Fintype.card V <;> simp [h, eq_comm]
  · intro F hF hFt
    by_cases hcard : F.val.card = r <;> simp [hcard, hFt]
  · intro h
    exact (h (Finset.mem_univ _)).elim

def topParameterMap : MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] K[X] :=
  MvPolynomial.aeval (fun c => if c.val + 1 = Fintype.card V then Polynomial.X else 0)

theorem booleanTopEvaluation_colorMap :
    (booleanTopEvaluation (V := V) (K := K)).comp booleanColorMap = topParameterMap := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [AlgHom.comp_apply, booleanColorMap, topParameterMap, MvPolynomial.aeval_X]
  rw [← booleanRankParameter_color, booleanTopEvaluation_rankParameter]

theorem booleanTopEvaluation_parameter_mul
    (a : MvPolynomial (Fin (Fintype.card V)) K) (x : BooleanBarycentricRing V K) :
    booleanTopEvaluation (booleanColorMap a * x) =
      topParameterMap a * booleanTopEvaluation x := by
  rw [map_mul]
  exact congrArg (fun y : K[X] => y * booleanTopEvaluation x)
    (DFunLike.congr_fun booleanTopEvaluation_colorMap a)

theorem orderingDescentFace_ne_top
    (σ : VertexOrdering (Fintype.card V) V) (c : Fin (Fintype.card V))
    (hc : c ∈ orderingDescents σ) : orderingFace σ c ≠ booleanTopFace := by
  intro he
  have hh := congrArg (fun F : BooleanFace V => F.val.card) he
  change (orderingPrefix σ c).card = (Finset.univ : Finset V).card at hh
  rw [card_orderingPrefix, Finset.card_univ] at hh
  obtain ⟨hlt, _⟩ := (mem_orderingDescents σ c).mp hc
  omega

theorem booleanTopEvaluation_descentVector
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanTopEvaluation (K := K) (descentVector σ) =
      if orderingDescents σ = ∅ then 1 else 0 := by
  by_cases hσ : orderingDescents σ = ∅
  · simp [descentVector, hσ]
  · rw [if_neg hσ, descentVector, map_prod]
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hσ
    apply Finset.prod_eq_zero hc
    rw [booleanTopEvaluation_face, if_neg (orderingDescentFace_ne_top σ c hc)]

end Boolean

section Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

def cyclicTopEmbedding : K[X] →ₐ[K] MvPolynomial (ZMod p) K :=
  Polynomial.aeval (cyclicPolynomialTop p K)

theorem primeOrbitRetraction_top_pow (n : ℕ) :
    primeOrbitRetraction p (cyclicPolynomialTop p K ^ n) = (Polynomial.X : K[X]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', cyclicPolynomialTop_orbitRetraction, ih, pow_succ']

theorem primeOrbitRetraction_topEmbedding (f : K[X]) :
    primeOrbitRetraction p (cyclicTopEmbedding p K f) = f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n c =>
      rw [cyclicTopEmbedding, Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul,
        primeOrbitRetraction_top_pow, Algebra.smul_def]
      exact Polynomial.C_mul_X_pow_eq_monomial

theorem cyclicTopEmbedding_boundary (f : K[X]) :
    polynomialBooleanBoundaryMap (cyclicTopEmbedding p K f) =
      algebraMap K (PolynomialBoundaryRing (ZMod p) K) (f.coeff 0) := by
  have ht : polynomialBooleanBoundaryMap (cyclicPolynomialTop p K) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    exact ⟨1, mul_one _⟩
  have he : (polynomialBooleanBoundaryMap (V := ZMod p) (K := K)).comp
      (cyclicTopEmbedding p K) = Polynomial.aeval 0 := by
    apply Polynomial.algHom_ext
    simpa [cyclicTopEmbedding] using ht
  have hh := DFunLike.congr_fun he f
  exact hh.trans (Polynomial.coeff_zero_eq_aeval_zero' f).symm

theorem primeOrbitRetraction_parameterLinear :
    IsParameterLinear (polynomialColorMap (V := ZMod p) (K := K))
      (topParameterMap (V := ZMod p) (K := K)) (primeOrbitRetraction p) := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro c f
  simp only [polynomialColorMap, topParameterMap, MvPolynomial.aeval_X, ZMod.card]
  by_cases hc : c.val + 1 = p
  · rw [if_pos hc, hc]
    exact primeOrbitRetraction_top_parameter p (Fact.out : p.Prime).pos (ZMod.card p) f
  · rw [if_neg hc, zero_mul]
    apply primeOrbitRetraction_lower_parameter p (Fact.out : p.Prime) (ZMod.card p)
    · omega
    · have hb : c.val < p := c.isLt.trans_eq (ZMod.card p)
      omega

end Polynomial
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBooleanAction.lean -/
section


section

/-! # Actual Boolean vertex-permutation actions

The action is the existing restriction functor along the inverse vertex
permutation.  The generator formula identifies it with literal relabeling of
faces.  Parameter linearity, ordinary grading, and the fixed top quotient are
proved for this action.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

section General

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def booleanPermutationAlgEquiv (e : Equiv.Perm V) :
    BooleanBarycentricRing V K ≃ₐ[K] BooleanBarycentricRing V K :=
  { booleanRestriction (K := K) e.symm.toEmbedding with
    invFun := booleanRestriction e.toEmbedding
    left_inv := by
      intro x
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.toEmbedding e.symm.toEmbedding) x
      have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      rw [he, booleanRestriction_refl] at hh
      exact hh
    right_inv := by
      intro x
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.symm.toEmbedding e.toEmbedding) x
      have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.apply_symm_apply v
      rw [he, booleanRestriction_refl] at hh
      exact hh }

@[simp] theorem booleanPermutationAlgEquiv_face (e : Equiv.Perm V) (F : BooleanFace V) :
    booleanPermutationAlgEquiv (K := K) e (faceVariable F) =
      faceVariable (booleanFaceEmbedding e.toEmbedding F) := by
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
    ext v
    exact e.symm_apply_apply v
  have hh := booleanRestriction_face_included (K := K) e.symm.toEmbedding
    (booleanFaceEmbedding e.toEmbedding F)
  rw [booleanFaceEmbedding_trans, he, booleanFaceEmbedding_refl] at hh
  exact hh

@[simp] theorem booleanPermutationAlgEquiv_one (x : BooleanBarycentricRing V K) :
    booleanPermutationAlgEquiv (1 : Equiv.Perm V) x = x := by
  change booleanRestriction (Function.Embedding.refl V) x = x
  rw [booleanRestriction_refl]
  rfl

theorem booleanPermutationAlgEquiv_mul (e f : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanPermutationAlgEquiv (e * f) x =
      booleanPermutationAlgEquiv e (booleanPermutationAlgEquiv f x) := by
  have he : (e * f).symm.toEmbedding = e.symm.toEmbedding.trans f.symm.toEmbedding := by
    ext v
    rfl
  change booleanRestriction (e * f).symm.toEmbedding x =
    booleanRestriction e.symm.toEmbedding (booleanRestriction f.symm.toEmbedding x)
  rw [he]
  exact (DFunLike.congr_fun (booleanRestriction_comp (K := K)
    e.symm.toEmbedding f.symm.toEmbedding) x).symm

theorem booleanPermutationAlgEquiv_parameter (e : Equiv.Perm V) (r : ℕ) :
    booleanPermutationAlgEquiv (K := K) e (booleanRankParameter r) = booleanRankParameter r :=
  booleanRestriction_rankParameter e.symm.toEmbedding r

theorem booleanPermutationAlgEquiv_colorMap (e : Equiv.Perm V)
    (a : MvPolynomial (Fin (Fintype.card V)) K) :
    booleanPermutationAlgEquiv e (booleanColorMap a) = booleanColorMap a := by
  have he : (booleanPermutationAlgEquiv (K := K) e).toAlgHom.comp booleanColorMap =
      booleanColorMap := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, booleanColorMap, MvPolynomial.aeval_X]
    rw [← booleanRankParameter_color]
    exact booleanPermutationAlgEquiv_parameter e (c.val + 1)
  exact DFunLike.congr_fun he a

/-- The genuine permutation action is linear over the prescribed rank-sum
parameter algebra, not merely over the coefficient field. -/
def booleanParameterPermutationRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card V)) K)
      (Equiv.Perm V) (BooleanBarycentricRing V K) where
  toFun e := {
    toFun := booleanPermutationAlgEquiv e
    map_add' := (booleanPermutationAlgEquiv e).map_add
    map_smul' := by
      intro a x
      change booleanPermutationAlgEquiv e (booleanColorMap a * x) =
        booleanColorMap a * booleanPermutationAlgEquiv e x
      rw [map_mul, booleanPermutationAlgEquiv_colorMap] }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact booleanPermutationAlgEquiv_one x
  map_mul' e f := by
    apply LinearMap.ext
    intro x
    exact booleanPermutationAlgEquiv_mul e f x

theorem chainOrdinaryDegree_map_faceEmbedding (e : V ↪ V)
    (a : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a.mapDomain (booleanFaceEmbedding e)) = chainOrdinaryDegree a := by
  unfold chainOrdinaryDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ i j => by simp only [add_mul])]
  simp only [booleanFaceEmbedding_card]

theorem booleanPermutationAlgEquiv_degree (e : Equiv.Perm V) (n : ℕ)
    (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) :
    booleanPermutationAlgEquiv e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n := by
  intro a ha
  change booleanChainBasis.repr (booleanRestriction e.symm.toEmbedding x) a = 0
  rw [booleanRestriction_coefficient]
  apply hx
  change chainOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e.symm.toEmbedding)) ≠ n
  rw [chainOrdinaryDegree_map_faceEmbedding]
  exact ha

theorem booleanAlgHom_ext {S : Type*} [CommRing S] [Algebra K S]
    (f g : BooleanBarycentricRing V K →ₐ[K] S)
    (h : ∀ F, f (faceVariable F) = g (faceVariable F)) : f = g := by
  have he : f.comp (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) =
      g.comp (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) := by
    apply MvPolynomial.algHom_ext
    exact h
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun he a

variable [Nonempty V]

theorem booleanFaceEmbedding_equiv_top (e : Equiv.Perm V) :
    booleanFaceEmbedding e.toEmbedding (booleanTopFace (V := V)) = booleanTopFace := by
  apply Subtype.ext
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  exact Finset.mem_map.mpr ⟨e.symm v, Finset.mem_univ _, e.apply_symm_apply v⟩

theorem booleanTopEvaluation_permutation (e : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanTopEvaluation (booleanPermutationAlgEquiv e x) = booleanTopEvaluation x := by
  have he : (booleanTopEvaluation (V := V) (K := K)).comp
      (booleanPermutationAlgEquiv e).toAlgHom = booleanTopEvaluation := by
    apply booleanAlgHom_ext
    intro F
    change booleanTopEvaluation (booleanPermutationAlgEquiv e (faceVariable F)) =
      booleanTopEvaluation (faceVariable F)
    rw [booleanPermutationAlgEquiv_face, booleanTopEvaluation_face, booleanTopEvaluation_face]
    have ht : booleanFaceEmbedding e.toEmbedding F = booleanTopFace ↔ F = booleanTopFace := by
      constructor
      · intro h
        exact (booleanFaceEmbedding e.toEmbedding).injective
          (h.trans (booleanFaceEmbedding_equiv_top e).symm)
      · rintro rfl
        exact booleanFaceEmbedding_equiv_top e
    simp only [ht]
  exact DFunLike.congr_fun he x

end General

section Graded

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem booleanParameterPermutationRepresentation_graded (e : Equiv.Perm V)
    (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n) :
    booleanParameterPermutationRepresentation e x ∈
      (booleanScalarGradedBasis (V := V) (K := K)).piece n := by
  rw [booleanScalarGradedBasis_piece_eq] at hx ⊢
  exact booleanPermutationAlgEquiv_degree e n x hx

end Graded
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrdinaryLift.lean -/
section


section

/-! # A normalized ordinary lift to both prescribed quotients

Starting with any graded, normalized parameter-linear boundary lift, correct
the images of the actual descent basis by the top-coordinate section.  The
correction has zero boundary and gives exact compatibility with the fixed
top-face quotient.  No equivariance is assumed at this stage.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped Polynomial

section DegreeFacts

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem descentOrdinaryDegree_eq_zero_iff
    (σ : VertexOrdering (Fintype.card V) V) :
    colorOrdinaryDegree (descentColorExponent σ) = 0 ↔ orderingDescents σ = ∅ := by
  rw [colorOrdinaryDegree_eq_zero_iff]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hh := congrArg (fun a : ColorExponent V => a c) h
    simp only [descentColorExponent_apply, if_pos hc, Finsupp.zero_apply] at hh
    exact Nat.one_ne_zero hh
  · intro h
    simp [descentColorExponent, h]

theorem weightOrdering_zero_no_descents :
    orderingDescents (weightOrdering (fun _ : V => 0)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, hh⟩ := weightOrdering_descent_lt (fun _ : V => 0)
    ((mem_orderingDescents _ _).mp hc)
  exact (Nat.lt_irrefl 0) hh

theorem parameterLinear_ordinary_degree
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) : f x ∈ polynomialDegreePiece n := by
  rw [← booleanChainBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul]
  apply Submodule.smul_mem
  have hdeg : chainOrdinaryDegree a.val = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (hx a hn)
  rw [← hdeg]
  exact parameterLinear_chain_degree f hf hd a

end DegreeFacts

section Cyclic

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicTopEmbedding_monomial_degree (m : ℕ) (c : K) :
    cyclicTopEmbedding p K (Polynomial.monomial m c) ∈
      CyclicPolynomialPiece p K (m * p) := by
  rw [cyclicTopEmbedding, Polynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  exact polynomialDegreePiece_pow p (cyclicPolynomialTop p K)
    (cyclicPolynomialTop_degree p K) m

theorem cyclicTopEmbedding_orbitRetraction_degree (n : ℕ)
    (f : CyclicPolynomialPiece p K n) :
    cyclicTopEmbedding p K (primeOrbitRetraction p f.val) ∈ CyclicPolynomialPiece p K n := by
  change cyclicTopEmbedding p K (cyclicHomogeneousOrbitRetraction p K n f) ∈ _
  rw [cyclicHomogeneousOrbitRetraction_apply]
  by_cases hn : p ∣ n
  · rw [if_pos hn]
    have hh := cyclicTopEmbedding_monomial_degree p K (n / p)
      (cyclicHomogeneousAugmentation p K n f)
    simpa only [Nat.div_mul_cancel hn] using hh
  · rw [if_neg hn, map_zero]
    exact Submodule.zero_mem _

theorem cyclicHomogeneousOrbitRetraction_constant_zero (n : ℕ) (hn : 0 < n)
    (f : CyclicPolynomialPiece p K n) :
    (primeOrbitRetraction p f.val).coeff 0 = 0 := by
  change (cyclicHomogeneousOrbitRetraction p K n f).coeff 0 = 0
  rw [cyclicHomogeneousOrbitRetraction_apply]
  by_cases hd : p ∣ n
  · rw [if_pos hd, Polynomial.coeff_monomial]
    have hq : n / p ≠ 0 := by
      intro hzero
      have hh := Nat.div_mul_cancel hd
      rw [hzero, zero_mul] at hh
      omega
    rw [if_neg hq]
  · rw [if_neg hd]
    rfl

def cyclicOrdinaryCorrectedLift
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K) :
    BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  exact ((booleanColorBasis (V := ZMod p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
    (fun σ => f (descentVector σ) + cyclicTopEmbedding p K
      (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))))).restrictScalars K

@[simp] theorem cyclicOrdinaryCorrectedLift_descent
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicOrdinaryCorrectedLift p K f (descentVector σ) =
      f (descentVector σ) + cyclicTopEmbedding p K
        (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))) := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  simpa only [cyclicOrdinaryCorrectedLift, LinearMap.restrictScalars_apply,
    booleanColorBasis_apply] using
    (booleanColorBasis (V := ZMod p) (K := K)).constr_basis
      (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (fun τ => f (descentVector τ) + cyclicTopEmbedding p K
        (booleanTopEvaluation (descentVector τ) - primeOrbitRetraction p (f (descentVector τ)))) σ

theorem cyclicOrdinaryCorrectedLift_parameterLinear
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K) :
    IsParameterLinear booleanColorMap polynomialColorMap (cyclicOrdinaryCorrectedLift p K f) := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  intro a x
  exact (((booleanColorBasis (V := ZMod p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
    (fun σ => f (descentVector σ) + cyclicTopEmbedding p K
      (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))))).map_smul a x)

theorem cyclicOrdinaryCorrectedLift_orbitRetraction
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (x : BooleanBarycentricRing (ZMod p) K) :
    primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f x) = booleanTopEvaluation x := by
  have he : (primeOrbitRetraction p).comp (cyclicOrdinaryCorrectedLift p K f) =
      (booleanTopEvaluation (V := ZMod p) (K := K)).toLinearMap := by
    apply parameterLinear_ext_descent (topParameterMap (V := ZMod p) (K := K))
    · intro a y
      change primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f (booleanColorMap a * y)) = _
      rw [cyclicOrdinaryCorrectedLift_parameterLinear,
        primeOrbitRetraction_parameterLinear]
      rfl
    · exact booleanTopEvaluation_parameter_mul
    · intro σ
      change primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f (descentVector σ)) = _
      rw [cyclicOrdinaryCorrectedLift_descent, map_add, primeOrbitRetraction_topEmbedding]
      rw [← add_sub_assoc,
        add_comm (primeOrbitRetraction p (f (descentVector σ)))
          (booleanTopEvaluation (descentVector σ)), add_sub_cancel_right]
      rfl
  exact DFunLike.congr_fun he x

theorem cyclicOrdinaryCorrectedLift_one
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (h1 : f 1 = 1) : cyclicOrdinaryCorrectedLift p K f 1 = 1 := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hd : descentVector (K := K) σ = 1 := by
    simp [descentVector, σ, weightOrdering_zero_no_descents]
  rw [← hd, cyclicOrdinaryCorrectedLift_descent, hd, h1,
    map_one, primeOrbitRetraction_one, sub_self, map_zero, add_zero]

theorem cyclicOrdinaryCorrectedLift_boundary
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (h1 : f 1 = 1)
    (hd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (x : BooleanBarycentricRing (ZMod p) K) :
    polynomialBooleanBoundaryMap (cyclicOrdinaryCorrectedLift p K f x) =
      polynomialBooleanBoundaryMap (f x) := by
  have he : polynomialBooleanBoundaryMap.toLinearMap.comp (cyclicOrdinaryCorrectedLift p K f) =
      polynomialBooleanBoundaryMap.toLinearMap.comp f := by
    apply parameterLinear_ext_descent (polynomialBoundaryColorMap (V := ZMod p) (K := K))
    · intro a y
      change polynomialBooleanBoundaryMap
        (cyclicOrdinaryCorrectedLift p K f (booleanColorMap a * y)) = _
      rw [cyclicOrdinaryCorrectedLift_parameterLinear, polynomialBooleanBoundaryMap_parameter_mul]
      rfl
    · intro a y
      change polynomialBooleanBoundaryMap (f (booleanColorMap a * y)) = _
      rw [hf, polynomialBooleanBoundaryMap_parameter_mul]
      rfl
    · intro σ
      change polynomialBooleanBoundaryMap (cyclicOrdinaryCorrectedLift p K f (descentVector σ)) = _
      rw [cyclicOrdinaryCorrectedLift_descent, map_add, cyclicTopEmbedding_boundary]
      have hc : (booleanTopEvaluation (descentVector σ) -
          primeOrbitRetraction p (f (descentVector σ))).coeff 0 = 0 := by
        by_cases hσ : orderingDescents σ = ∅
        · have hh : descentVector (K := K) σ = 1 := by simp [descentVector, hσ]
          rw [hh, h1, map_one, primeOrbitRetraction_one, sub_self]
          rfl
        · rw [Polynomial.coeff_sub, booleanTopEvaluation_descentVector, if_neg hσ]
          have hn : 0 < colorOrdinaryDegree (descentColorExponent σ) :=
            Nat.pos_of_ne_zero (fun h => hσ ((descentOrdinaryDegree_eq_zero_iff σ).mp h))
          rw [cyclicHomogeneousOrbitRetraction_constant_zero p K _ hn
            ⟨f (descentVector σ), hd σ⟩]
          simp
      rw [hc, map_zero, add_zero]
      rfl
  exact DFunLike.congr_fun he x

theorem cyclicOrdinaryCorrectedLift_descent_degree
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicOrdinaryCorrectedLift p K f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [cyclicOrdinaryCorrectedLift_descent, map_sub]
  apply Submodule.add_mem _ (hd σ)
  apply Submodule.sub_mem
  · rw [booleanTopEvaluation_descentVector]
    by_cases hσ : orderingDescents σ = ∅
    · rw [if_pos hσ, map_one, (descentOrdinaryDegree_eq_zero_iff σ).mpr hσ]
      exact polynomialDegreePiece_one
    · rw [if_neg hσ, map_zero]
      exact Submodule.zero_mem _
  · exact cyclicTopEmbedding_orbitRetraction_degree p K _ ⟨f (descentVector σ), hd σ⟩

end Cyclic
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicParameterModules.lean -/
section


section

/-! # Parameter modules and the actual controlled quotient

The scoped polynomial module structure is evaluation at elementary symmetric
polynomials.  The controlled submodule is the intersection of the genuine
boundary kernel and the orbit-retraction kernel.  The quotient and all group
actions are induced from these actual maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial

namespace CyclicParameterAction

scoped instance (priority := 2000) polynomialAlgebra {V K : Type*} [Fintype V] [CommRing K] :
    Algebra (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  (polynomialColorMap (V := V) (K := K)).toRingHom.toAlgebra

scoped instance (priority := 2000) polynomialSMul {V K : Type*} [Fintype V] [CommRing K] :
    SMul (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  @Algebra.toSMul _ _ _ _ (polynomialAlgebra (V := V) (K := K))

scoped instance (priority := 2000) polynomialModule {V K : Type*} [Fintype V] [CommRing K] :
    Module (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  @Algebra.toModule _ _ _ _ (polynomialAlgebra (V := V) (K := K))

scoped instance polynomialTower {V K : Type*} [Fintype V] [CommRing K] :
    IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  IsScalarTower.of_algHom (polynomialColorMap (V := V) (K := K))

end CyclicParameterAction

open scoped CyclicParameterAction

section General

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem polynomialColorMap_rename (e : Equiv.Perm V)
    (a : MvPolynomial (Fin (Fintype.card V)) K) :
    MvPolynomial.rename e (polynomialColorMap a) = polynomialColorMap a := by
  have he : (MvPolynomial.rename e).comp (polynomialColorMap (V := V) (K := K)) =
      polynomialColorMap := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, polynomialColorMap, MvPolynomial.aeval_X,
      MvPolynomial.rename_esymm]
  exact DFunLike.congr_fun he a

def polynomialParameterPermutationRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card V)) K)
      (Equiv.Perm V) (MvPolynomial V K) where
  toFun e := {
    toFun := MvPolynomial.rename e
    map_add' := (MvPolynomial.rename e).map_add
    map_smul' := by
      intro a x
      change MvPolynomial.rename e (polynomialColorMap a * x) =
        polynomialColorMap a * MvPolynomial.rename e x
      rw [map_mul, polynomialColorMap_rename] }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact MvPolynomial.rename_id_apply x
  map_mul' e f := by
    apply LinearMap.ext
    intro x
    change MvPolynomial.rename (e * f) x = MvPolynomial.rename e (MvPolynomial.rename f x)
    rw [MvPolynomial.rename_rename]
    rfl

def parameterLinearMap
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f) :
    BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      MvPolynomial V K where
  toFun := f
  map_add' := f.map_add
  map_smul' := hf

end General

section QuotientAction

variable {A G N : Type*} [CommRing A] [Group G] [AddCommGroup N] [Module A N]

def invariantQuotientRepresentation (ρ : CyclicRepresentation A G N)
    (H : Submodule A N) (hH : ∀ g x, x ∈ H → ρ g x ∈ H) :
    CyclicRepresentation A G (N ⧸ H) where
  toFun g := H.mapQ H (ρ g) (fun x hx => hH g x hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := H.mkQ_surjective x
    change H.mkQ (ρ 1 y) = H.mkQ y
    rw [ρ.map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := H.mkQ_surjective x
    change H.mkQ (ρ (g * h) y) = H.mkQ (ρ g (ρ h y))
    rw [ρ.map_mul]
    rfl

@[simp] theorem invariantQuotientRepresentation_mk
    (ρ : CyclicRepresentation A G N) (H : Submodule A N)
    (hH : ∀ g x, x ∈ H → ρ g x ∈ H) (g : G) (x : N) :
    invariantQuotientRepresentation ρ H hH g (H.mkQ x) = H.mkQ (ρ g x) := rfl

theorem invariantQuotientRepresentation_mk_intertwines
    (ρ : CyclicRepresentation A G N) (H : Submodule A N)
    (hH : ∀ g x, x ∈ H → ρ g x ∈ H) :
    RepresentationIntertwines ρ (invariantQuotientRepresentation ρ H hH) H.mkQ := by
  intro g x
  rfl

end QuotientAction

section Cyclic

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

def cyclicVertexPermutation : PrimeCycleGroup p →* Equiv.Perm (ZMod p) where
  toFun g := Equiv.addLeft g.toAdd
  map_one' := by ext v; exact zero_add v
  map_mul' g h := by ext v; exact add_assoc g.toAdd h.toAdd v

def cyclicPolynomialParameterRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (MvPolynomial (ZMod p) K) :=
  polynomialParameterPermutationRepresentation.comp (cyclicVertexPermutation p)

def cyclicBooleanParameterRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (BooleanBarycentricRing (ZMod p) K) :=
  booleanParameterPermutationRepresentation.comp (cyclicVertexPermutation p)

@[simp] theorem cyclicPolynomialParameterRepresentation_apply
    (g : PrimeCycleGroup p) (f : MvPolynomial (ZMod p) K) :
    cyclicPolynomialParameterRepresentation p K g f =
      MvPolynomial.rename (Equiv.addLeft g.toAdd) f := rfl

@[simp] theorem cyclicBooleanParameterRepresentation_apply
    (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) K) :
    cyclicBooleanParameterRepresentation p K g x =
      booleanPermutationAlgEquiv (Equiv.addLeft g.toAdd) x := rfl

def cyclicControlledKernel :
    Submodule (MvPolynomial (Fin (Fintype.card (ZMod p))) K) (MvPolynomial (ZMod p) K) where
  carrier := {f | polynomialBooleanBoundaryMap f = 0 ∧ primeOrbitRetraction p f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · rw [map_add, hf.1, hg.1, add_zero]
    · rw [map_add, hf.2, hg.2, add_zero]
  smul_mem' := by
    intro a f hf
    change polynomialBooleanBoundaryMap (polynomialColorMap a * f) = 0 ∧
      primeOrbitRetraction p (polynomialColorMap a * f) = 0
    constructor
    · rw [polynomialBooleanBoundaryMap_parameter_mul, hf.1, mul_zero]
    · rw [primeOrbitRetraction_parameterLinear, hf.2, mul_zero]

theorem cyclicControlledKernel_invariant :
    ∀ (g : PrimeCycleGroup p) (f : MvPolynomial (ZMod p) K),
      f ∈ cyclicControlledKernel p K →
        cyclicPolynomialParameterRepresentation p K g f ∈ cyclicControlledKernel p K := by
  intro g f hf
  constructor
  · obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f).mp hf.1
    change cyclicPolynomialTop p K * x = f at hx
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename (Equiv.addLeft g.toAdd) x, ?_⟩
    change cyclicPolynomialTop p K * MvPolynomial.rename (Equiv.addLeft g.toAdd) x =
      MvPolynomial.rename (Equiv.addLeft g.toAdd) f
    rw [← hx, map_mul, cyclicPolynomialTop_rename]
  · rw [cyclicPolynomialParameterRepresentation_apply, primeOrbitRetraction_rename]
    exact hf.2

abbrev CyclicControlledQuotient :=
  MvPolynomial (ZMod p) K ⧸ cyclicControlledKernel p K

def cyclicControlledQuotientRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (CyclicControlledQuotient p K) :=
  invariantQuotientRepresentation (cyclicPolynomialParameterRepresentation p K)
    (cyclicControlledKernel p K) (cyclicControlledKernel_invariant p K)

end Cyclic
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicModularLift.lean -/
section


section

/-! # The prime-cyclic controlled lift for actual face rings

This is the exceptional modular construction in the positive direction of
Theorem 1.3.  Every source, action, quotient, and kernel is the one already
defined on the actual Boolean barycentric and polynomial rings.  The sole
input is an ordinary graded normalized boundary lift whose boundary values
are equivariant; equivariance of the full lift is constructed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicPolynomialParameterRepresentation_graded :
    ∀ (g : PrimeCycleGroup p) (n : ℕ) (f : MvPolynomial (ZMod p) K),
      f ∈ CyclicPolynomialPiece p K n →
        cyclicPolynomialParameterRepresentation p K g f ∈ CyclicPolynomialPiece p K n := by
  intro g n f hf
  exact (cyclicPolynomialRepresentation p K n g ⟨f, hf⟩).property

theorem cyclicBooleanParameterRepresentation_graded :
    ∀ (g : PrimeCycleGroup p) (n : ℕ) (x : BooleanBarycentricRing (ZMod p) K),
      x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n →
        cyclicBooleanParameterRepresentation p K g x ∈
          (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n := by
  intro g n x hx
  exact booleanParameterPermutationRepresentation_graded (Equiv.addLeft g.toAdd) n x hx

theorem cyclicControlledQuotient_intertwines :
    RepresentationIntertwines (cyclicPolynomialParameterRepresentation p K)
      (cyclicControlledQuotientRepresentation p K) (cyclicControlledKernel p K).mkQ := by
  intro g x
  rfl

def cyclicControlledDegreeMap (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K] CyclicControlledQuotient p K :=
  ((cyclicControlledKernel p K).mkQ.restrictScalars K).comp
    (CyclicPolynomialPiece p K n).subtype

theorem cyclicControlledDegreeKernel_eq (n : ℕ) :
    LinearMap.ker (cyclicControlledDegreeMap p K n) =
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) := by
  ext f
  change (cyclicControlledKernel p K).mkQ f.val = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (cyclicBoundaryOrbitDegree_mem_kernel p K n f).symm

def cyclicControlledDegreeKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicControlledDegreeMap p K n)) :=
  ScalarGradedBasis.kernelDegreeRepresentation
    (cyclicPolynomialParameterRepresentation p K) (cyclicControlledQuotientRepresentation p K)
    (CyclicPolynomialPiece p K) (cyclicControlledKernel p K).mkQ
    (cyclicPolynomialParameterRepresentation_graded p K) (cyclicControlledQuotient_intertwines p K) n

theorem cyclicControlledDegreeKernel_isCoinduced (n : ℕ) :
    ∃ J : Type, ∃ e : LinearMap.ker (cyclicControlledDegreeMap p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K),
      RepresentationIntertwines (cyclicControlledDegreeKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  obtain ⟨J, e, he⟩ := cyclicBoundaryOrbitKernel_isCoinduced p K n
  let t := LinearEquiv.ofEq _ _ (cyclicControlledDegreeKernel_eq p K n)
  have ht : RepresentationIntertwines (cyclicControlledDegreeKernelRepresentation p K n)
      (cyclicBoundaryOrbitKernelRepresentation p K n) t.toLinearMap := by
    intro g x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  refine ⟨J, t.trans e, ?_⟩
  intro g x
  change e (t (cyclicControlledDegreeKernelRepresentation p K n g x)) =
    coinducedRepresentation (K := K) (C := J → K) g (e (t x))
  exact (congrArg e (ht g x)).trans (he g (t x))

theorem cyclicBoundary_rename_congr (e : Equiv.Perm (ZMod p))
    (f g : MvPolynomial (ZMod p) K)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p K * x = f - g at hx
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e x, ?_⟩
    change cyclicPolynomialTop p K * MvPolynomial.rename e x = MvPolynomial.rename e (f - g)
    rw [← hx, map_mul, cyclicPolynomialTop_rename]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem booleanScalarGradedBasis_one :
    (1 : BooleanBarycentricRing (ZMod p) K) ∈
      (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece 0 := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hd : orderingDescents σ = ∅ := weightOrdering_zero_no_descents
  have hdegree : colorOrdinaryDegree (descentColorExponent σ) = 0 :=
    (descentOrdinaryDegree_eq_zero_iff σ).mpr hd
  have h := (booleanScalarGradedBasis (V := ZMod p) (K := K)).generator_mem_piece σ
  simpa only [booleanScalarGradedBasis, booleanColorBasis_apply, descentVector, hd,
    Finset.prod_empty, hdegree] using h

/-- A full parameter-linear prime-cyclic lift with the prescribed actual
boundary, fixed quotient, ordinary grading, and normalization. -/
theorem exists_primeCyclic_boundary_lift
    (f₀ : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hf₀ : IsParameterLinear booleanColorMap polynomialColorMap f₀)
    (h₁ : f₀ 1 = 1)
    (hd₀ : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f₀ (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hb₀ : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) K),
      polynomialBooleanBoundaryMap (f₀ (cyclicBooleanParameterRepresentation p K g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p K g (f₀ x))) :
    ∃ F : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K,
      IsParameterLinear booleanColorMap polynomialColorMap F ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := K)).piece n →
        F x ∈ CyclicPolynomialPiece p K n) ∧
      F 1 = 1 ∧
      (∀ x, polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f₀ x)) ∧
      (∀ x, primeOrbitRetraction p (F x) = booleanTopEvaluation x) ∧
      (∀ g x, F (cyclicBooleanParameterRepresentation p K g x) =
        cyclicPolynomialParameterRepresentation p K g (F x)) := by
  let s := booleanScalarGradedBasis (V := ZMod p) (K := K)
  let ρ := cyclicBooleanParameterRepresentation p K
  let τ := cyclicPolynomialParameterRepresentation p K
  let υ := cyclicControlledQuotientRepresentation p K
  let H := cyclicControlledKernel p K
  let T := CyclicPolynomialPiece p K
  let f := cyclicOrdinaryCorrectedLift p K f₀
  have hf : IsParameterLinear booleanColorMap polynomialColorMap f :=
    cyclicOrdinaryCorrectedLift_parameterLinear p K f₀
  have hfone : f 1 = 1 := cyclicOrdinaryCorrectedLift_one p K f₀ h₁
  have hfboundary (x) : polynomialBooleanBoundaryMap (f x) = polynomialBooleanBoundaryMap (f₀ x) :=
    cyclicOrdinaryCorrectedLift_boundary p K f₀ hf₀ h₁ hd₀ x
  have hfE (x) : primeOrbitRetraction p (f x) = booleanTopEvaluation x :=
    cyclicOrdinaryCorrectedLift_orbitRetraction p K f₀ x
  have hfgrade : ∀ n x, x ∈ s.piece n → f x ∈ T n := by
    intro n x hx
    rw [booleanScalarGradedBasis_piece_eq] at hx
    exact parameterLinear_ordinary_degree f hf
      (cyclicOrdinaryCorrectedLift_descent_degree p K f₀ hd₀) n x hx
  let fA := parameterLinearMap f hf
  let a := H.mkQ.comp fA
  have ha : RepresentationIntertwines ρ υ a := by
    intro g x
    change H.mkQ (f (ρ g x)) = H.mkQ (τ g (f x))
    apply (Submodule.Quotient.eq H).mpr
    constructor
    · change polynomialBooleanBoundaryMap (f (ρ g x) - τ g (f x)) = 0
      rw [map_sub, hfboundary, hb₀]
      apply sub_eq_zero.mpr
      exact (cyclicBoundary_rename_congr p K (Equiv.addLeft g.toAdd) (f x) (f₀ x)
        (hfboundary x)).symm
    · change primeOrbitRetraction p (f (ρ g x) - τ g (f x)) = 0
      rw [map_sub, hfE, cyclicPolynomialParameterRepresentation_apply,
        primeOrbitRetraction_rename, hfE]
      change booleanTopEvaluation (booleanPermutationAlgEquiv (Equiv.addLeft g.toAdd) x) -
        booleanTopEvaluation x = 0
      rw [booleanTopEvaluation_permutation, sub_self]
  let β : ∀ n, s.piece n →ₗ[K] T n := fun n =>
    LinearMap.codRestrict (T n) (f.comp (s.piece n).subtype)
      (fun x => hfgrade n x.val x.property)
  have hqβ : ∀ n, (ScalarGradedBasis.degreeQuotient T H.mkQ n).comp (β n) =
      s.degreeTarget a n := by intro n; rfl
  choose J e he using cyclicControlledDegreeKernel_isCoinduced p K
  let C : ℕ → Type _ := fun n => J n → K
  letI : ∀ n, AddCommGroup (C n) := fun _ => inferInstance
  letI : ∀ n, Module K (C n) := fun _ => inferInstance
  have hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j) := by
    intro j y hy
    change polynomialColorMap (MvPolynomial.monomial j.2 1) * y ∈
      polynomialDegreePiece (colorOrdinaryDegree j.2 + colorOrdinaryDegree (descentColorExponent j.1))
    exact polynomialDegreePiece_mul _ _ _ _ (polynomialColorMap_monomial_degree j.2) hy
  obtain ⟨F, hFgrade, hFq, hFeq⟩ := s.exists_equivariantGradedLift_of_ordinary_lifts
    ρ τ υ T H.mkQ a (cyclicBooleanParameterRepresentation_graded p K)
    (cyclicPolynomialParameterRepresentation_graded p K) (cyclicControlledQuotient_intertwines p K)
    hmult ha C β hqβ e he
  have hdiff (x : BooleanBarycentricRing (ZMod p) K) : F x - f x ∈ H := by
    apply (Submodule.Quotient.eq H).mp
    exact congrArg (fun L : BooleanBarycentricRing (ZMod p) K →ₗ[
      MvPolynomial (Fin (Fintype.card (ZMod p))) K] CyclicControlledQuotient p K => L x) hFq
  have hFboundary (x) : polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f₀ x) := by
    have hh := (hdiff x).1
    change polynomialBooleanBoundaryMap (F x - f x) = 0 at hh
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).trans (hfboundary x)
  have hFE (x) : primeOrbitRetraction p (F x) = booleanTopEvaluation x := by
    have hh := (hdiff x).2
    change primeOrbitRetraction p (F x - f x) = 0 at hh
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).trans (hfE x)
  have hFone : F 1 = 1 := by
    have hd : F 1 - 1 ∈ T 0 := (T 0).sub_mem
      (hFgrade 0 1 (booleanScalarGradedBasis_one p K)) polynomialDegreePiece_one
    have hk : (⟨F 1 - 1, hd⟩ : CyclicPolynomialPiece p K 0) ∈
        LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K 0) := by
      apply (cyclicBoundaryOrbitDegree_mem_kernel p K 0 _).mpr
      have hh := hdiff 1
      change polynomialBooleanBoundaryMap (F 1 - f 1) = 0 ∧
        primeOrbitRetraction p (F 1 - f 1) = 0 at hh
      simpa only [hfone] using hh
    have hz := cyclicBoundaryOrbitKernel_zero_below p K 0 (Fact.out : p.Prime).pos ⟨⟨F 1 - 1, hd⟩, hk⟩
    exact sub_eq_zero.mp (congrArg (fun z => z.val.val) hz)
  refine ⟨F.restrictScalars K, ?_, hFgrade, hFone, hFboundary, hFE, hFeq⟩
  intro b x
  exact F.map_smul b x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedIsomorphism.lean -/
section


section

/-! # A graded boundary lift is an isomorphism

The proof uses a finite triangular argument on the actual parameter basis.
A homogeneous element divisible by the positive-degree top parameter belongs
to the span of strictly lower-degree parameter generators.  Thus two graded
parameter lifts with the same boundary differ by a strictly triangular map
after conjugating by either known lift.  The coefficient ring is arbitrary.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Abstract

variable {K A M I J : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

theorem ScalarGradedBasis.bijective_of_lower_cut_errors
    (s : ScalarGradedBasis K A M I J) (f : M →ₗ[A] M)
    (hf : ∀ i, f (s.parameterBasis i) - s.parameterBasis i ∈ s.cut (s.generatorDegree i)) :
    Function.Bijective f := by
  have hcoeff (i j : I) (hij : s.generatorDegree i ≤ s.generatorDegree j) :
      s.parameterBasis.repr (f (s.parameterBasis i) - s.parameterBasis i) j = 0 := by
    by_contra hn
    have hs := (s.parameterBasis.mem_span_image).mp (hf i)
    have hj := hs (Finsupp.mem_support_iff.mpr hn)
    exact (Nat.not_lt_of_ge hij) hj
  apply canonicalLeading_bijective s.parameterBasis s.parameterBasis s.generatorDegree f
  constructor
  · intro i
    have hh := hcoeff i i le_rfl
    simpa only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, sub_eq_zero] using hh
  · intro i j hne hij
    have hh := hcoeff i j hij
    simpa [Finsupp.single_apply, hne, Ne.symm hne] using hh

end Abstract

section Boolean

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

theorem chainOrdinaryDegree_add (a b : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a + b) = chainOrdinaryDegree a + chainOrdinaryDegree b :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])

theorem chainOrdinaryDegree_add_top (a : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      chainOrdinaryDegree a + Fintype.card V := by
  rw [chainOrdinaryDegree_add]
  simp [chainOrdinaryDegree, booleanTopFace]

theorem booleanTop_mul_shift_coefficient (x : BooleanBarycentricRing V K)
    (a : BooleanChainExponent V) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem booleanTop_predecessor_degree (m : ℕ) (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) (m + Fintype.card V)) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => chainOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : chainOrdinaryDegree b.val ≠ m + Fintype.card V := by
    change chainOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [chainOrdinaryDegree_add_top]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  rwa [booleanTop_mul_shift_coefficient] at hh

theorem booleanTop_homogeneous_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : chainOrdinaryDegree b.val ≠ n := by
    change chainOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [chainOrdinaryDegree_add_top]
    omega
  have hh := hx b hb
  rw [booleanTop_mul_shift_coefficient] at hh
  exact hh

theorem booleanTop_mul_mem_cut (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n) :
    booleanTop * x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n := by
  have hr : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  let c : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hc : c.val + 1 = Fintype.card V := by dsimp [c]; omega
  have ht : booleanTop * x = (MvPolynomial.X c : MvPolynomial (Fin (Fintype.card V)) K) • x := by
    change booleanTop * x = booleanColorMap (MvPolynomial.X c) * x
    rw [booleanColorMap, MvPolynomial.aeval_X, ← booleanRankParameter_color, hc,
      booleanRankParameter_top]
  rw [ht]
  exact ((booleanScalarGradedBasis (V := V) (K := K)).cut n).smul_mem _ hx

/-- A genuine top-boundary kernel element of degree `n` uses only parameter
generators of degree strictly below `n`. -/
theorem booleanBoundary_homogeneous_mem_cut (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hb : booleanBoundaryMap x = 0) :
    x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n := by
  obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff x).mp hb
  rw [booleanScalarGradedBasis_piece_eq] at hx
  have htop : booleanTop * y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n := by simpa only [hy] using hx
  by_cases hn : Fintype.card V ≤ n
  · have hydeg : y ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece
        (n - Fintype.card V) := by
      rw [booleanScalarGradedBasis_piece_eq]
      apply booleanTop_predecessor_degree
      simpa only [Nat.sub_add_cancel hn] using htop
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
    have hlt : n - Fintype.card V < n := by omega
    rw [← hy]
    exact booleanTop_mul_mem_cut n y
      ((booleanScalarGradedBasis (V := V) (K := K)).homogeneous_mem_cut hlt y hydeg)
  · have hyzero := booleanTop_homogeneous_zero_below n (Nat.lt_of_not_ge hn) y htop
    rw [← hy, hyzero, mul_zero]
    exact Submodule.zero_mem _

theorem booleanParameterEnd_bijective_of_graded_boundary_identity
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K)
    (hd : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hb : ∀ x, booleanBoundaryMap (f x) = booleanBoundaryMap x) :
    Function.Bijective f := by
  let s := booleanScalarGradedBasis (V := V) (K := K)
  apply s.bijective_of_lower_cut_errors f
  intro i
  apply booleanBoundary_homogeneous_mem_cut
  · exact (s.piece (s.generatorDegree i)).sub_mem
      (hd _ _ (s.generator_mem_piece i)) (s.generator_mem_piece i)
  · rw [map_sub, hb, sub_self]

/-- Any graded parameter-linear lift of the same actual boundary is an
isomorphism once one graded parameter comparison is known. -/
theorem parameterLift_bijective_of_same_boundary
    (e : ParameterEquiv (booleanColorMap (V := V) (K := K)) polynomialColorMap)
    (b : LocalBoundaryComparison (V := V) (K := K))
    (he : ∀ x, polynomialBooleanBoundaryMap (e.toLinearEquiv x) =
      b.toLinearEquiv (booleanBoundaryMap x))
    (hed : ∀ n y, y ∈ polynomialDegreePiece n → e.toLinearEquiv.symm y ∈
      (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hfd : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ polynomialDegreePiece n)
    (hfb : ∀ x, polynomialBooleanBoundaryMap (f x) =
      polynomialBooleanBoundaryMap (e.toLinearEquiv x)) : Function.Bijective f := by
  let T : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K :=
    e.overParameters.symm.toLinearMap.comp (parameterLinearMap f hf)
  have hT : Function.Bijective T := by
    apply booleanParameterEnd_bijective_of_graded_boundary_identity T
    · intro n x hx
      exact hed n (f x) (hfd n x hx)
    · intro x
      apply b.toLinearEquiv.injective
      rw [← he, ← he]
      change polynomialBooleanBoundaryMap (e.toLinearEquiv (e.toLinearEquiv.symm (f x))) = _
      rw [LinearEquiv.apply_symm_apply]
      exact hfb x
  have hcomp : (fun x => e.toLinearEquiv (T x)) = f := by
    funext x
    exact e.toLinearEquiv.apply_symm_apply (f x)
  rw [← hcomp]
  exact e.toLinearEquiv.bijective.comp hT

end Boolean
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBoundaryIsomorphism.lean -/
section

section
/-! # Positive-degree boundary lifting without a previously known isomorphism

This is the graded lifting argument of Lemma 2.1.  The boundary comparison
is an actual isomorphism of the two top-parameter quotients.  Strong induction
on ordinary degree proves injectivity and surjectivity of any graded lift
commuting with the top parameters.  It neither compares the lift with an
already invertible map nor assumes a prescribed leading coefficient matrix.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

section GradedLinearAlgebra

variable {K M N I J : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem ordinaryBasis_mem_piece (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  by_cases h : i = j
  · subst j
    exact (hj rfl).elim
  · simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg h]

theorem ordinaryProjection_mem_piece (b : Module.Basis I K M) (w : I → ℕ)
    (n : ℕ) (x : M) :
    basisDegreeProjection b w n x ∈ basisOrdinaryDegreePiece b w n := by
  intro i hi
  rw [basisDegreeProjection_repr, if_neg hi]

theorem ordinaryProjection_natural (b : Module.Basis I K M) (c : Module.Basis J K N)
    (w : I → ℕ) (v : J → ℕ) (f : M →ₗ[K] N)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n →
      f x ∈ basisOrdinaryDegreePiece c v n) (n : ℕ) (x : M) :
    basisDegreeProjection c v n (f x) = f (basisDegreeProjection b w n x) := by
  have he : (basisDegreeProjection c v n).comp f = f.comp (basisDegreeProjection b w n) := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, basisDegreeProjection_basis]
    by_cases hi : w i = n
    · rw [if_pos hi]
      exact (basisDegreeProjection_eq_self_iff_mem c v n (f (b i))).mpr
        (hf n (b i) (hi ▸ ordinaryBasis_mem_piece b w i))
    · rw [if_neg hi, map_zero]
      apply c.repr.injective
      ext j
      rw [basisDegreeProjection_repr, map_zero, Finsupp.zero_apply]
      by_cases hj : v j = n
      · rw [if_pos hj]
        exact hf (w i) (b i) (ordinaryBasis_mem_piece b w i) j
          (fun h => hi (h.symm.trans hj))
      · rw [if_neg hj]
  exact LinearMap.congr_fun he x

variable {Q R : Type*} [AddCommGroup Q] [Module K Q]
  [AddCommGroup R] [Module K R]

/-- A degree-preserving top-parameter lift of an actual boundary isomorphism
is bijective.  All kernel and predecessor hypotheses refer to the given maps
and the given basis degrees; they do not assert any isomorphism of the lifts. -/
theorem gradedBoundaryLift_bijective
    (b : Module.Basis I K M) (c : Module.Basis J K N) (w : I → ℕ) (v : J → ℕ)
    (qM : M →ₗ[K] Q) (qN : N →ₗ[K] R) (boundary : Q ≃ₗ[K] R)
    (σ : M →ₗ[K] M) (τ : N →ₗ[K] N) (r : ℕ) (hr : 0 < r)
    (hτ : Function.Injective τ)
    (hkerM : ∀ x, qM x = 0 → ∃ a, σ a = x)
    (hkerN : ∀ y, qN y = 0 → ∃ a, τ a = y)
    (hσpred : ∀ n a, r ≤ n → σ a ∈ basisOrdinaryDegreePiece b w n →
      a ∈ basisOrdinaryDegreePiece b w (n - r))
    (hτpred : ∀ n a, r ≤ n → τ a ∈ basisOrdinaryDegreePiece c v n →
      a ∈ basisOrdinaryDegreePiece c v (n - r))
    (hσbelow : ∀ n a, n < r → σ a ∈ basisOrdinaryDegreePiece b w n → a = 0)
    (hτbelow : ∀ n a, n < r → τ a ∈ basisOrdinaryDegreePiece c v n → a = 0)
    (hboundary : ∀ n y, y ∈ basisOrdinaryDegreePiece c v n →
      ∃ x, x ∈ basisOrdinaryDegreePiece b w n ∧ qN y = boundary (qM x))
    (f : M →ₗ[K] N)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n →
      f x ∈ basisOrdinaryDegreePiece c v n)
    (htop : ∀ x, f (σ x) = τ (f x))
    (hquot : ∀ x, qN (f x) = boundary (qM x)) : Function.Bijective f := by
  have hinj : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n → f x = 0 → x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx hfx
        have hqx : qM x = 0 := by
          apply boundary.injective
          rw [← hquot, hfx, map_zero, map_zero]
        obtain ⟨a, ha⟩ := hkerM x hqx
        have hσa : σ a ∈ basisOrdinaryDegreePiece b w n := ha.symm ▸ hx
        by_cases hrn : r ≤ n
        · have hfa : f a = 0 := by
            apply hτ
            rw [← htop, ha, hfx, map_zero]
          have ha0 := ih (n - r) (by omega) a (hσpred n a hrn hσa) hfa
          rw [← ha, ha0, map_zero]
        · have ha0 := hσbelow n a (Nat.lt_of_not_ge hrn) hσa
          rw [← ha, ha0, map_zero]
  have hsurj : ∀ n y, y ∈ basisOrdinaryDegreePiece c v n → ∃ x, f x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hy
        obtain ⟨x, hx, hbx⟩ := hboundary n y hy
        have hqdiff : qN (y - f x) = 0 := by rw [map_sub, hquot, hbx, sub_self]
        obtain ⟨a, ha⟩ := hkerN (y - f x) hqdiff
        have hτa : τ a ∈ basisOrdinaryDegreePiece c v n :=
          ha.symm ▸ (basisOrdinaryDegreePiece c v n).sub_mem hy (hgrade n x hx)
        by_cases hrn : r ≤ n
        · obtain ⟨z, hz⟩ := ih (n - r) (by omega) a (hτpred n a hrn hτa)
          refine ⟨x + σ z, ?_⟩
          rw [map_add, htop, hz, ha]
          abel
        · have ha0 := hτbelow n a (Nat.lt_of_not_ge hrn) hτa
          refine ⟨x, ?_⟩
          have hh : y - f x = 0 := by rw [← ha, ha0, map_zero]
          exact (sub_eq_zero.mp hh).symm
  have hzero : ∀ x, f x = 0 → x = 0 := by
    intro x hfx
    apply b.repr.injective
    ext i
    have hh : basisDegreeProjection b w (w i) x = 0 := by
      apply hinj (w i) _ (ordinaryProjection_mem_piece b w (w i) x)
      rw [← ordinaryProjection_natural b c w v f hgrade, hfx, map_zero]
    have hc := congrArg (fun z => b.repr z i) hh
    simpa only [basisDegreeProjection_repr, if_true, map_zero, Finsupp.zero_apply] using hc
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro y
    choose a ha using fun j : J => hsurj (v j) (c j) (ordinaryBasis_mem_piece c v j)
    refine ⟨∑ j ∈ (c.repr y).support, c.repr y j • a j, ?_⟩
    simp only [map_sum, map_smul, ha]
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using c.linearCombination_repr y

end GradedLinearAlgebra

section BooleanBoundary

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

/-- The actual degree piece in the Boolean top-parameter quotient. -/
def booleanBoundaryOrdinaryPiece (n : ℕ) : Submodule K (BooleanBoundaryRing V K) :=
  (basisOrdinaryDegreePiece booleanChainBasis (fun a => chainOrdinaryDegree a.val) n).map
    booleanBoundaryMap.toLinearMap

/-- The actual degree piece in the polynomial top-monomial quotient. -/
def polynomialBoundaryOrdinaryPiece (n : ℕ) : Submodule K (PolynomialBoundaryRing V K) :=
  (polynomialDegreePiece n).map polynomialBooleanBoundaryMap.toLinearMap

theorem polynomialOrdinaryPiece_eq_basis (n : ℕ) :
    polynomialDegreePiece (V := V) (K := K) n =
      basisOrdinaryDegreePiece (MvPolynomial.basisMonomials V K)
        (fun a => vertexDegree (fun v => a v)) n := by
  ext x
  rfl

theorem fullPolynomialTop_predecessor_degree (m : ℕ) (f : MvPolynomial V K)
    (hf : (∏ v : V, X v) * f ∈ polynomialDegreePiece (m + Fintype.card V)) :
    f ∈ polynomialDegreePiece m := by
  intro a ha
  have hdeg : vertexDegree (fun v => (fullExponent V + a) v) =
      Fintype.card V + vertexDegree (fun v => a v) := by
    change vertexDegree ((fun v => fullExponent V v) + (fun v => a v)) = _
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hf (fullExponent V + a) (by rw [hdeg]; omega)
  rw [← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem fullPolynomialTop_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (f : MvPolynomial V K) (hf : (∏ v : V, X v) * f ∈ polynomialDegreePiece n) : f = 0 := by
  ext a
  have hdeg : Fintype.card V ≤ vertexDegree (fun v => (fullExponent V + a) v) := by
    change Fintype.card V ≤ vertexDegree ((fun v => fullExponent V v) + (fun v => a v))
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hf (fullExponent V + a) (by omega)
  rw [← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem parameterLinear_top
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (x : BooleanBarycentricRing V K) :
    f (booleanTop * x) = (∏ v : V, X v) * f x := by
  have hr : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hc : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have h := parameterLinear_intertwinesAllRanks f hf (Fintype.card V - 1) x
  have htop : MvPolynomial.esymm V K (Fintype.card V) = ∏ v : V, X v := by
    unfold MvPolynomial.esymm
    rw [← Finset.card_univ, Finset.powersetCard_self]
    simp
  simpa only [hc, booleanRankParameter_top, htop] using h

/-- Lemma 2.1 on the actual simplex rings.  The inverse boundary map is
assumed graded in the genuine quotient grading, as it is for any graded
boundary isomorphism.  No isomorphism of the full rings is assumed. -/
theorem booleanPolynomialLift_bijective_of_graded_boundary
    (boundary : LocalBoundaryComparison (V := V) (K := K))
    (hbgrade : ∀ n y, y ∈ polynomialBoundaryOrdinaryPiece (V := V) (K := K) n →
      boundary.toLinearEquiv.symm y ∈ booleanBoundaryOrdinaryPiece (V := V) (K := K) n)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hquot : ∀ x, polynomialBooleanBoundaryMap (f x) =
      boundary.toLinearEquiv (booleanBoundaryMap x)) : Function.Bijective f := by
  apply gradedBoundaryLift_bijective booleanChainBasis (MvPolynomial.basisMonomials V K)
    (fun a => chainOrdinaryDegree a.val) (fun a => vertexDegree (fun v => a v))
    booleanBoundaryMap.toLinearMap polynomialBooleanBoundaryMap.toLinearMap boundary.toLinearEquiv
    (LinearMap.mulLeft K booleanTop) (LinearMap.mulLeft K (∏ v : V, X v)) (Fintype.card V)
    (Fintype.card_pos_iff.mpr inferInstance)
    (MvPolynomial.isRegular_prod_X (R := K) (Finset.univ : Finset V)).left
    (fun x hx => (booleanBoundaryMap_eq_zero_iff x).mp hx)
    (fun y hy => (polynomialBooleanBoundaryMap_eq_zero_iff y).mp hy)
    (fun n a hn ha => booleanTop_predecessor_degree (n - Fintype.card V) a
      (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => by
      rw [← polynomialOrdinaryPiece_eq_basis] at ha ⊢
      exact fullPolynomialTop_predecessor_degree (n - Fintype.card V) a
        (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => booleanTop_homogeneous_zero_below n hn a ha)
    (fun n a hn ha => fullPolynomialTop_zero_below n hn a
      (by rwa [← polynomialOrdinaryPiece_eq_basis] at ha))
    ?_ f ?_ (parameterLinear_top f hf) hquot
  · intro n y hy
    have hy' : y ∈ polynomialDegreePiece n := by rwa [← polynomialOrdinaryPiece_eq_basis] at hy
    have hb := hbgrade n (polynomialBooleanBoundaryMap y) ⟨y, hy', rfl⟩
    obtain ⟨x, hx, he⟩ := hb
    refine ⟨x, hx, ?_⟩
    change polynomialBooleanBoundaryMap y =
      boundary.toLinearEquiv (booleanBoundaryMap x)
    have hh := congrArg boundary.toLinearEquiv he
    simpa only [LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] using hh.symm
  · intro n x hx
    rw [← polynomialOrdinaryPiece_eq_basis]
    exact hgrade n x hx

end BooleanBoundary
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralHom.lean -/
section


section

/-! # Integral affine correction on parameter-linear maps

Conjugation gives an honest representation on the module of parameter-linear
maps.  The integral correction is therefore applied to the actual maps, not
to independently averaged values on a chosen basis.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable {A G M N : Type*} [CommRing A] [Group G]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def parameterHomRepresentation (ρ : CyclicRepresentation A G M)
    (τ : CyclicRepresentation A G N) : CyclicRepresentation ℤ G (M →ₗ[A] N) where
  toFun g := {
    toFun f := (τ g).comp (f.comp (ρ g⁻¹))
    map_add' := by intro f h; ext x; simp
    map_smul' := by intro c f; ext x; simp }
  map_one' := by ext f x; simp
  map_mul' g h := by
    ext f x
    change τ (g * h) (f (ρ (g * h)⁻¹ x)) =
      τ g (τ h (f (ρ h⁻¹ (ρ g⁻¹ x))))
    rw [mul_inv_rev, ρ.map_mul, τ.map_mul]
    rfl

@[simp] theorem parameterHomRepresentation_apply
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (g : G) (f : M →ₗ[A] N) (x : M) :
    parameterHomRepresentation ρ τ g f x = τ g (f (ρ g⁻¹ x)) := rfl

theorem parameterHomRepresentation_fixed_iff
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (f : M →ₗ[A] N) :
    (∀ g, parameterHomRepresentation ρ τ g f = f) ↔ RepresentationIntertwines ρ τ f := by
  constructor
  · intro h g x
    have hh := congrArg (fun F : M →ₗ[A] N => F (ρ g x)) (h g)
    have hinv : ρ g⁻¹ (ρ g x) = x := by
      change (ρ g⁻¹ * ρ g) x = x
      rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
      rfl
    change τ g (f (ρ g⁻¹ (ρ g x))) = f (ρ g x) at hh
    rw [hinv] at hh
    exact hh.symm
  · intro h g
    ext x
    change τ g (f (ρ g⁻¹ x)) = f x
    rw [h]
    change (τ g * τ g⁻¹) (f x) = f x
    rw [← τ.map_mul, mul_inv_cancel, τ.map_one]
    rfl

variable [Fintype G]

theorem parameterHom_nsmul_injective
    (hN : Function.Injective (fun y : N => Fintype.card G • y)) :
    Function.Injective (fun f : M →ₗ[A] N => Fintype.card G • f) := by
  intro f h he
  ext x
  apply hN
  exact congrArg (fun F : M →ₗ[A] N => F x) he

/-- Lemma A.8 applied to actual parameter-linear maps, with exact preservation
of a boundary map and any separately specified homogeneous submodules. -/
theorem exists_integralEquivariant_map_correction
    {Q : Type*} [AddCommGroup Q] (q : N →ₗ[ℤ] Q)
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (f : M →ₗ[A] N) (v : G → M →ₗ[A] N)
    (hN : Function.Injective (fun y : N => Fintype.card G • y))
    (hv : ∀ g, parameterHomRepresentation ρ τ g f = f + Fintype.card G • v g)
    (hqv : ∀ g x, q (v g x) = 0)
    (S : ℕ → Submodule ℤ M) (T : ℕ → Submodule ℤ N)
    (hfgrade : ∀ n x, x ∈ S n → f x ∈ T n)
    (hvgrade : ∀ g n x, x ∈ S n → v g x ∈ T n)
    (x₀ : M) (hv₀ : ∀ g, v g x₀ = 0) :
    ∃ F : M →ₗ[A] N,
      RepresentationIntertwines ρ τ F ∧
      (∀ x, q (F x) = q (f x)) ∧
      (∀ n x, x ∈ S n → F x ∈ T n) ∧ F x₀ = f x₀ := by
  let F : M →ₗ[A] N := f + ∑ g, v g
  have hfixed : ∀ g, parameterHomRepresentation ρ τ g F = F :=
    affineCorrection_fixed (parameterHomRepresentation ρ τ) f v
      (parameterHom_nsmul_injective hN) hv
  refine ⟨F, (parameterHomRepresentation_fixed_iff ρ τ F).mp hfixed, ?_, ?_, ?_⟩
  · intro x
    change q (f x + (∑ g, v g) x) = q (f x)
    simp [hqv]
  · intro n x hx
    change f x + (∑ g, v g) x ∈ T n
    apply (T n).add_mem (hfgrade n x hx)
    rw [LinearMap.sum_apply]
    exact (T n).sum_mem (fun g _ => hvgrade g n x hx)
  · change f x₀ + (∑ g, v g) x₀ = f x₀
    simp [hv₀]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegerCoefficients.lean -/
section


section

/-! # Exact integer coefficient lifting and division

The integer-to-modular steps are coefficientwise identities in the actual
multivariate polynomial rings.  Homogeneous lifts retain the original
exponent vectors; division is used only after divisibility has been proved.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial

variable {V : Type*}

def liftZModPolynomial (p : ℕ) (f : MvPolynomial V (ZMod p)) : MvPolynomial V ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : ZMod p => (c.val : ℤ)) (by simp) f.coeff)

@[simp] theorem liftZModPolynomial_coeff (p : ℕ) (f : MvPolynomial V (ZMod p))
    (a : V →₀ ℕ) :
    (liftZModPolynomial p f).coeff a = ((f.coeff a).val : ℤ) := rfl

theorem liftZModPolynomial_map (p : ℕ) [NeZero p] (f : MvPolynomial V (ZMod p)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (liftZModPolynomial p f) = f := by
  ext a
  rw [MvPolynomial.coeff_map, liftZModPolynomial_coeff]
  change (((f.coeff a).val : ℤ) : ZMod p) = f.coeff a
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

def divideIntegerPolynomial (p : ℕ) (f : MvPolynomial V ℤ) : MvPolynomial V ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : ℤ => c / (p : ℤ)) (by simp) f.coeff)

@[simp] theorem divideIntegerPolynomial_coeff (p : ℕ) (f : MvPolynomial V ℤ)
    (a : V →₀ ℕ) :
    (divideIntegerPolynomial p f).coeff a = f.coeff a / (p : ℤ) := rfl

theorem nsmul_divideIntegerPolynomial (p : ℕ) (f : MvPolynomial V ℤ)
    (hf : MvPolynomial.map (Int.castRingHom (ZMod p)) f = 0) :
    p • divideIntegerPolynomial p f = f := by
  ext a
  have hc := congrArg (fun h : MvPolynomial V (ZMod p) => h.coeff a) hf
  rw [MvPolynomial.coeff_map] at hc
  change (f.coeff a : ZMod p) = 0 at hc
  have hd : (p : ℤ) ∣ f.coeff a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc
  rw [MvPolynomial.coeff_smul, divideIntegerPolynomial_coeff, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_of_dvd hd

theorem integerPolynomial_nsmul_injective {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun f : MvPolynomial V ℤ => p • f) := by
  intro f g hfg
  ext a
  have h := congrArg (fun h : MvPolynomial V ℤ => h.coeff a) hfg
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, nsmul_eq_mul, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (by exact_mod_cast hp) h

variable [Fintype V] [LinearOrder V]

theorem liftZModPolynomial_degree (p n : ℕ) (f : MvPolynomial V (ZMod p))
    (hf : f ∈ polynomialDegreePiece n) :
    liftZModPolynomial p f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [liftZModPolynomial_coeff, hf a ha]
  simp

theorem divideIntegerPolynomial_degree (p n : ℕ) (f : MvPolynomial V ℤ)
    (hf : f ∈ polynomialDegreePiece n) :
    divideIntegerPolynomial p f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [divideIntegerPolynomial_coeff, hf a ha]
  simp

theorem integerPolynomial_degree_of_nsmul {p n : ℕ} (hp : p ≠ 0)
    (f : MvPolynomial V ℤ) (hf : p • f ∈ polynomialDegreePiece n) :
    f ∈ polynomialDegreePiece n := by
  intro a ha
  have hh := hf a ha
  rw [MvPolynomial.coeff_smul, nsmul_eq_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hp)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicParameterBaseChange.lean -/
section


section

/-! # Coefficient change of actual parameter-linear maps

Extension is defined by the images of the already verified descent basis.
The comparison with coefficient change is proved on the complete scalar
parameter basis, including every parameter monomial.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V K L : Type*} [Fintype V] [LinearOrder V] [CommRing K] [CommRing L]

theorem booleanCoefficientChange_descent (h : K →+* L)
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanCoefficientChange h (descentVector (K := K) σ) = descentVector (K := L) σ := by
  change monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h
    (descentVector (K := K) σ) = _
  rw [descentVector, descentVector, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  exact booleanCoefficientChange_face h (orderingFace σ c)

theorem booleanCoefficientChange_color (h : K →+* L) (c : Fin (Fintype.card V)) :
    booleanCoefficientChange h (colorSum (K := K) c) = colorSum (K := L) c := by
  rw [← booleanRankParameter_color, booleanCoefficientChange_parameter, booleanRankParameter_color]

theorem booleanCoefficientChange_colorPower (h : K →+* L) (m : ColorExponent V) :
    booleanCoefficientChange h (colorPower (K := K) m) = colorPower (K := L) m := by
  change monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed h
    (colorPower (K := K) m) = _
  rw [colorPower, colorPower, map_prod]
  apply Finset.prod_congr rfl
  intro c hc
  rw [map_pow]
  congr 1
  exact booleanCoefficientChange_color h c

theorem booleanCoefficientChange_parameterBasis (h : K →+* L)
    (i : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    booleanCoefficientChange h (booleanParameterBasis (K := K) i) =
      booleanParameterBasis (K := L) i := by
  rw [booleanParameterBasis_apply, booleanParameterBasis_apply, parameterDescentVector,
    parameterDescentVector, booleanCoefficientChange_mul,
    booleanCoefficientChange_colorPower, booleanCoefficientChange_descent]

theorem polynomialCoefficientChange_parameterMonomial (h : K →+* L) (m : ColorExponent V) :
    polynomialCoefficientChange h (polynomialColorMap (K := K) (MvPolynomial.monomial m 1)) =
      polynomialColorMap (K := L) (MvPolynomial.monomial m 1) := by
  change MvPolynomial.map h (polynomialColorMap (K := K) (MvPolynomial.monomial m 1)) = _
  simp only [polynomialColorMap, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod, map_prod, map_pow, MvPolynomial.map_esymm]

theorem polynomialCoefficientChange_degree (h : K →+* L) (n : ℕ)
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece n) :
    polynomialCoefficientChange h f ∈ polynomialDegreePiece n := by
  intro a ha
  change (MvPolynomial.map h f).coeff a = 0
  rw [MvPolynomial.coeff_map, hf a ha, map_zero]

theorem parameterLinearMap_parameterDescent
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K] MvPolynomial V K)
    (i : VertexOrdering (Fintype.card V) V × ColorExponent V) :
    f (parameterDescentVector i) =
      polynomialColorMap (MvPolynomial.monomial i.2 1) * f (descentVector i.1) := by
  rw [parameterDescentVector_eq_monomial_smul, map_smul]
  rfl

def extendIntegralParameterMap (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ) :
    BooleanBarycentricRing V L →ₗ[MvPolynomial (Fin (Fintype.card V)) L] MvPolynomial V L :=
  (booleanColorBasis (V := V) (K := L)).constr (MvPolynomial (Fin (Fintype.card V)) L)
    (fun σ => polynomialCoefficientChange (Int.castRingHom L) (f (descentVector σ)))

@[simp] theorem extendIntegralParameterMap_descent (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (σ : VertexOrdering (Fintype.card V) V) :
    extendIntegralParameterMap L f (descentVector σ) =
      polynomialCoefficientChange (Int.castRingHom L) (f (descentVector σ)) := by
  simpa only [extendIntegralParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := V) (K := L)).constr_basis (MvPolynomial (Fin (Fintype.card V)) L)
      (fun τ => polynomialCoefficientChange (Int.castRingHom L) (f (descentVector τ))) σ

theorem extendIntegralParameterMap_commutes (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (x : BooleanBarycentricRing V ℤ) :
    extendIntegralParameterMap L f (booleanCoefficientChange (Int.castRingHom L) x) =
      polynomialCoefficientChange (Int.castRingHom L) (f x) := by
  have he : ((extendIntegralParameterMap L f).restrictScalars L).comp
      (booleanCoefficientChange (Int.castRingHom L)) =
      (polynomialCoefficientChange (Int.castRingHom L)).comp (f.restrictScalars ℤ) := by
    apply (booleanParameterBasis (V := V) (K := ℤ)).ext
    intro i
    change extendIntegralParameterMap L f
        (booleanCoefficientChange (Int.castRingHom L) (booleanParameterBasis i)) =
      polynomialCoefficientChange (Int.castRingHom L) (f (booleanParameterBasis i))
    rw [booleanCoefficientChange_parameterBasis, booleanParameterBasis_apply,
      booleanParameterBasis_apply, parameterLinearMap_parameterDescent,
      parameterLinearMap_parameterDescent, extendIntegralParameterMap_descent]
    change _ = MvPolynomial.map (Int.castRingHom L)
      (polynomialColorMap (MvPolynomial.monomial i.2 1) * f (descentVector i.1))
    rw [map_mul]
    rw [← polynomialCoefficientChange_eq, polynomialCoefficientChange_parameterMonomial]
    rfl
  exact DFunLike.congr_fun he x

theorem extendIntegralParameterMap_degree (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card V) V) :
    extendIntegralParameterMap L f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [extendIntegralParameterMap_descent]
  exact polynomialCoefficientChange_degree _ _ _ (hf σ)

theorem extendIntegralParameterMap_one (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (m : ℤ) (hf : f 1 = MvPolynomial.C m) :
    extendIntegralParameterMap L f 1 = MvPolynomial.C (m : L) := by
  have h := extendIntegralParameterMap_commutes L f 1
  have h₁ : booleanCoefficientChange (V := V) (Int.castRingHom L) 1 = 1 :=
    (monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed (Int.castRingHom L)).map_one
  rw [h₁, hf] at h
  simpa [polynomialCoefficientChange_eq] using h

theorem extendIntegralParameterMap_permutation (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (e : Equiv.Perm V)
    (hf : ∀ x, f (booleanPermutationAlgEquiv e x) = MvPolynomial.rename e (f x)) :
    ∀ x, extendIntegralParameterMap L f (booleanPermutationAlgEquiv e x) =
      MvPolynomial.rename e (extendIntegralParameterMap L f x) := by
  have he : ((extendIntegralParameterMap L f).restrictScalars L).comp
      (booleanPermutationAlgEquiv (K := L) e).toLinearMap =
      (MvPolynomial.rename e).toLinearMap.comp ((extendIntegralParameterMap L f).restrictScalars L) := by
    apply (booleanParameterBasis (V := V) (K := L)).ext
    intro i
    have hBi := booleanCoefficientChange_parameterBasis (Int.castRingHom L) i
    change extendIntegralParameterMap L f (booleanPermutationAlgEquiv e (booleanParameterBasis i)) =
      MvPolynomial.rename e (extendIntegralParameterMap L f (booleanParameterBasis i))
    rw [← hBi]
    have hn := booleanCoefficientChange_restriction (Int.castRingHom L) e.symm.toEmbedding
      (booleanParameterBasis (K := ℤ) i)
    change booleanCoefficientChange (Int.castRingHom L)
        (booleanPermutationAlgEquiv e (booleanParameterBasis (K := ℤ) i)) =
      booleanPermutationAlgEquiv e
        (booleanCoefficientChange (Int.castRingHom L) (booleanParameterBasis (K := ℤ) i)) at hn
    rw [← hn, extendIntegralParameterMap_commutes, extendIntegralParameterMap_commutes, hf]
    exact MvPolynomial.map_rename (Int.castRingHom L) e _
  intro x
  exact DFunLike.congr_fun he x

theorem extendIntegralParameterMap_conjugation (L : Type*) [CommRing L]
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (e : Equiv.Perm V) (x : BooleanBarycentricRing V ℤ) :
    polynomialCoefficientChange (Int.castRingHom L)
        (MvPolynomial.rename e (f (booleanPermutationAlgEquiv e.symm x))) =
      MvPolynomial.rename e (extendIntegralParameterMap L f
        (booleanPermutationAlgEquiv e.symm (booleanCoefficientChange (Int.castRingHom L) x))) := by
  rw [polynomialCoefficientChange_eq, MvPolynomial.map_rename]
  rw [← polynomialCoefficientChange_eq, ← extendIntegralParameterMap_commutes]
  exact congrArg (fun y => MvPolynomial.rename e (extendIntegralParameterMap L f y))
    (booleanCoefficientChange_restriction (Int.castRingHom L) e.toEmbedding x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralDivision.lean -/
section


section

/-! # Dividing integral parameter maps after modular vanishing

Division is performed on the genuine descent-basis images.  The resulting
map is parameter-linear by construction, and the multiplication identity is
checked on that full parameter basis.  Boundary and grading conditions then
descend using torsion freeness of the actual coefficient bases.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Basis

variable {I M : Type*} [AddCommGroup M] [Module ℤ M]

theorem integerBasis_nsmul_injective (b : Module.Basis I ℤ M) {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun x : M => p • x) := by
  intro x y hxy
  apply b.repr.injective
  ext i
  have hh := congrArg (fun z => b.repr z i) hxy
  simp only [map_nsmul, Finsupp.nsmul_apply, nsmul_eq_mul] at hh
  exact mul_left_cancel₀ (by exact_mod_cast hp) hh

end Basis

variable {V : Type*} [Fintype V] [LinearOrder V]

def divideIntegralParameterMap (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ) :
    BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ :=
  (booleanColorBasis (V := V) (K := ℤ)).constr (MvPolynomial (Fin (Fintype.card V)) ℤ)
    (fun σ => divideIntegerPolynomial p (f (descentVector σ)))

@[simp] theorem divideIntegralParameterMap_descent (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (σ : VertexOrdering (Fintype.card V) V) :
    divideIntegralParameterMap p f (descentVector σ) = divideIntegerPolynomial p (f (descentVector σ)) := by
  simpa only [divideIntegralParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := V) (K := ℤ)).constr_basis (MvPolynomial (Fin (Fintype.card V)) ℤ)
      (fun τ => divideIntegerPolynomial p (f (descentVector τ))) σ

theorem nsmul_divideIntegralParameterMap (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0) :
    p • divideIntegralParameterMap p f = f := by
  apply (booleanColorBasis (V := V) (K := ℤ)).ext
  intro σ
  simp only [booleanColorBasis_apply, LinearMap.smul_apply, divideIntegralParameterMap_descent]
  exact nsmul_divideIntegerPolynomial p _ (hf σ)

theorem divideIntegralParameterMap_degree (p : ℕ)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card V) V) :
    divideIntegralParameterMap p f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [divideIntegralParameterMap_descent]
  exact divideIntegerPolynomial_degree p _ _ (hf σ)

theorem divideIntegralParameterMap_boundary (p : ℕ) (hp : p ≠ 0)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0)
    (hb : ∀ x, polynomialBooleanBoundaryMap (f x) = 0)
    (x : BooleanBarycentricRing V ℤ) :
    polynomialBooleanBoundaryMap (divideIntegralParameterMap p f x) = 0 := by
  apply integerBasis_nsmul_injective
    (standardMonomialBasis (K := ℤ) (OmitsVertex V) (omitsVertex_divisorClosed V)) hp
  change p • polynomialBooleanBoundaryMap (divideIntegralParameterMap p f x) =
    p • (0 : PolynomialBoundaryRing V ℤ)
  rw [smul_zero, ← map_nsmul]
  have hh := congrArg (fun F : BooleanBarycentricRing V ℤ →ₗ[
    MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ => F x)
      (nsmul_divideIntegralParameterMap p f hf)
  change p • divideIntegralParameterMap p f x = f x at hh
  rw [hh, hb]

theorem divideIntegralParameterMap_zero_at (p : ℕ) (hp : p ≠ 0)
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ)) = 0)
    (x : BooleanBarycentricRing V ℤ) (hx : f x = 0) :
    divideIntegralParameterMap p f x = 0 := by
  apply integerPolynomial_nsmul_injective hp
  change p • divideIntegralParameterMap p f x = p • (0 : MvPolynomial V ℤ)
  rw [smul_zero]
  have hh := congrArg (fun F : BooleanBarycentricRing V ℤ →ₗ[
    MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ => F x)
      (nsmul_divideIntegralParameterMap p f hf)
  exact hh.trans hx

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralCorrection.lean -/
section


section

/-! # Integral correction of an actual prime-cyclic comparison

The input map already has the prescribed integral boundary.  Its failure of
equivariance vanishes after reduction modulo the prime.  We divide this
failure on the actual descent basis and apply the integral affine correction;
the resulting map retains the boundary, ordinary degree, and normalization.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem integralParameterMap_graded
    (f : BooleanBarycentricRing V ℤ →ₗ[MvPolynomial (Fin (Fintype.card V)) ℤ] MvPolynomial V ℤ)
    (hf : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (n : ℕ) (x : BooleanBarycentricRing V ℤ)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := ℤ)).piece n) :
    f x ∈ polynomialDegreePiece n := by
  rw [booleanScalarGradedBasis_piece_eq] at hx
  exact parameterLinear_ordinary_degree (f.restrictScalars ℤ)
    (fun a y => f.map_smul a y) hf n x hx

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem primeCycle_card : Fintype.card (PrimeCycleGroup p) = p := by
  simp [PrimeCycleGroup, ZMod.card]

theorem exists_integralPrimeCyclic_correction
    (f : BooleanBarycentricRing (ZMod p) ℤ →ₗ[
      MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ] MvPolynomial (ZMod p) ℤ)
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hfmod : ∀ (g : PrimeCycleGroup p) (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)),
      MvPolynomial.map (Int.castRingHom (ZMod p))
        ((parameterHomRepresentation (cyclicBooleanParameterRepresentation p ℤ)
          (cyclicPolynomialParameterRepresentation p ℤ) g f - f) (descentVector σ)) = 0)
    (m : ℤ) (hf₁ : f 1 = MvPolynomial.C m) :
    ∃ F : BooleanBarycentricRing (ZMod p) ℤ →ₗ[
        MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ] MvPolynomial (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) F ∧
      (∀ x, polynomialBooleanBoundaryMap (F x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        F x ∈ polynomialDegreePiece n) ∧ F 1 = MvPolynomial.C m := by
  let ρ := cyclicBooleanParameterRepresentation p ℤ
  let τ := cyclicPolynomialParameterRepresentation p ℤ
  let s := booleanScalarGradedBasis (V := ZMod p) (K := ℤ)
  let δ := fun g : PrimeCycleGroup p => parameterHomRepresentation ρ τ g f - f
  let v := fun g : PrimeCycleGroup p => divideIntegralParameterMap p (δ g)
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfg : ∀ n x, x ∈ s.piece n → f x ∈ polynomialDegreePiece n :=
    integralParameterMap_graded f hfgrade
  have hρg : ∀ (g : PrimeCycleGroup p) n x,
      x ∈ s.piece n → ρ g x ∈ s.piece n := by
    intro g n x hx
    exact booleanParameterPermutationRepresentation_graded (Equiv.addLeft g.toAdd) n x hx
  have hτg : ∀ (g : PrimeCycleGroup p) n y,
      y ∈ polynomialDegreePiece n → τ g y ∈ polynomialDegreePiece n := by
    intro g n y hy
    exact (cyclicPolynomialRepresentation p ℤ n g ⟨y, hy⟩).property
  have hδg : ∀ (g : PrimeCycleGroup p) n x,
      x ∈ s.piece n → δ g x ∈ polynomialDegreePiece n := by
    intro g n x hx
    exact (polynomialDegreePiece n).sub_mem (hτg g n _ (hfg n _ (hρg g⁻¹ n x hx)))
      (hfg n x hx)
  have hδb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (δ g x) = 0 := by
    intro g x
    change polynomialBooleanBoundaryMap (τ g (f (ρ g⁻¹ x)) - f x) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hh := hfboundary g (ρ g⁻¹ x)
    have hi : ρ g (ρ g⁻¹ x) = x := by
      change (ρ g * ρ g⁻¹) x = x
      rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
      rfl
    rw [hi] at hh
    exact hh.symm
  have hδ₁ : ∀ g : PrimeCycleGroup p, δ g 1 = 0 := by
    intro g
    change MvPolynomial.rename (Equiv.addLeft g.toAdd)
      (f (booleanPermutationAlgEquiv (Equiv.addLeft (g⁻¹).toAdd) 1)) - f 1 = 0
    rw [map_one, hf₁, MvPolynomial.rename_C, sub_self]
  have hv : ∀ g, parameterHomRepresentation ρ τ g f = f + Fintype.card (PrimeCycleGroup p) • v g := by
    intro g
    rw [primeCycle_card]
    have hdiv := nsmul_divideIntegralParameterMap p (δ g) (hfmod g)
    change parameterHomRepresentation ρ τ g f = f + p • divideIntegralParameterMap p (δ g)
    rw [hdiv]
    change parameterHomRepresentation ρ τ g f = f + (parameterHomRepresentation ρ τ g f - f)
    rw [← add_sub_assoc, add_comm f (parameterHomRepresentation ρ τ g f), add_sub_cancel_right]
  have hvb : ∀ g x, polynomialBooleanBoundaryMap (v g x) = 0 := by
    intro g x
    exact divideIntegralParameterMap_boundary p hp (δ g) (hfmod g) (hδb g) x
  have hvg : ∀ g n x, x ∈ s.piece n → v g x ∈ polynomialDegreePiece n := by
    intro g
    apply integralParameterMap_graded
    intro σ
    exact divideIntegralParameterMap_degree p (δ g)
      (fun σ => hδg g _ _ (by
        simpa only [s, booleanScalarGradedBasis, booleanColorBasis_apply] using
          s.generator_mem_piece σ)) σ
  have hv₁ : ∀ g, v g 1 = 0 := by
    intro g
    exact divideIntegralParameterMap_zero_at p hp (δ g) (hfmod g) 1 (hδ₁ g)
  obtain ⟨F, hFeq, hFb, hFg, hF₁⟩ := exists_integralEquivariant_map_correction
    polynomialBooleanBoundaryMap.toLinearMap ρ τ f v
    (by simpa only [primeCycle_card] using (integerPolynomial_nsmul_injective (V := ZMod p) hp))
    hv hvb s.piece polynomialDegreePiece hfg hvg 1 hv₁
  exact ⟨F, hFeq, hFb, hFg, hF₁.trans hf₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralLift.lean -/
section


section

/-! # Lifting a modular comparison with its exact integral boundary

A modular difference with zero boundary is a multiple of the actual top
monomial.  Lift its quotient coefficient by coefficient, then multiply by
the integral top monomial.  This keeps the prescribed integral boundary
exact, rather than merely congruent modulo the prime.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

abbrev BooleanParameterMap (V K : Type*) [Fintype V] [LinearOrder V] [CommRing K] :=
  BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K] MvPolynomial V K

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicPolynomialTop_map {K L : Type*} [CommRing K] [CommRing L]
    (h : K →+* L) :
    MvPolynomial.map h (cyclicPolynomialTop p K) = cyclicPolynomialTop p L := by
  simp only [cyclicPolynomialTop, map_prod, MvPolynomial.map_X]

theorem cyclicPolynomialTop_factor_zero_below {K : Type*} [CommRing K]
    (n : ℕ) (hn : n < p) (y : MvPolynomial (ZMod p) K)
    (hy : cyclicPolynomialTop p K * y ∈ polynomialDegreePiece n) : y = 0 := by
  ext a
  have hdeg : p ≤ vertexDegree (fun v => (fullExponent (ZMod p) + a) v) := by
    change p ≤ vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v))
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hy (fullExponent (ZMod p) + a) (by omega)
  rw [cyclicPolynomialTop, ← full_monomial_eq_prod,
    MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

def modularBoundaryDifference (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) : MvPolynomial (ZMod p) (ZMod p) :=
  F (descentVector σ) - MvPolynomial.map (Int.castRingHom (ZMod p)) (f (descentVector σ))

theorem modularBoundaryDifference_boundary (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    polynomialBooleanBoundaryMap (modularBoundaryDifference p f F σ) = 0 := by
  unfold modularBoundaryDifference
  rw [map_sub, hb, extendIntegralParameterMap_descent, polynomialCoefficientChange_eq, sub_self]

def modularBoundaryCofactor (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) : MvPolynomial (ZMod p) (ZMod p) :=
  Classical.choose ((polynomialBooleanBoundaryMap_eq_zero_iff _).mp
    (modularBoundaryDifference_boundary p f F hb σ))

theorem modularBoundaryCofactor_spec (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicPolynomialTop p (ZMod p) * modularBoundaryCofactor p f F hb σ =
      modularBoundaryDifference p f F σ :=
  Classical.choose_spec ((polynomialBooleanBoundaryMap_eq_zero_iff _).mp
    (modularBoundaryDifference_boundary p f F hb σ))

def liftModularParameterMap (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x)) :
    BooleanParameterMap (ZMod p) ℤ :=
  (booleanColorBasis (V := ZMod p) (K := ℤ)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ)
    (fun σ => f (descentVector σ) + cyclicPolynomialTop p ℤ *
      liftZModPolynomial p (modularBoundaryCofactor p f F hb σ))

@[simp] theorem liftModularParameterMap_descent (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    liftModularParameterMap p f F hb (descentVector σ) =
      f (descentVector σ) + cyclicPolynomialTop p ℤ *
        liftZModPolynomial p (modularBoundaryCofactor p f F hb σ) := by
  simpa only [liftModularParameterMap, booleanColorBasis_apply] using
    (booleanColorBasis (V := ZMod p) (K := ℤ)).constr_basis
      (MvPolynomial (Fin (Fintype.card (ZMod p))) ℤ) _ σ

theorem liftModularParameterMap_reduction (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x)) :
    extendIntegralParameterMap (ZMod p) (liftModularParameterMap p f F hb) = F := by
  apply (booleanColorBasis (V := ZMod p) (K := ZMod p)).ext
  intro σ
  rw [booleanColorBasis_apply, extendIntegralParameterMap_descent,
    polynomialCoefficientChange_eq, liftModularParameterMap_descent,
    map_add, map_mul, cyclicPolynomialTop_map, liftZModPolynomial_map,
    modularBoundaryCofactor_spec, modularBoundaryDifference]
  rw [← add_sub_assoc, add_comm _ (F (descentVector σ)), add_sub_cancel_right]

theorem liftModularParameterMap_boundary (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (x : BooleanBarycentricRing (ZMod p) ℤ) :
    polynomialBooleanBoundaryMap (liftModularParameterMap p f F hb x) =
      polynomialBooleanBoundaryMap (f x) := by
  let L := liftModularParameterMap p f F hb
  have he := parameterLinear_ext_descent polynomialBoundaryColorMap
    (polynomialBooleanBoundaryMap.toLinearMap.comp (L.restrictScalars ℤ))
    (polynomialBooleanBoundaryMap.toLinearMap.comp (f.restrictScalars ℤ))
    (fun a y => by
      change polynomialBooleanBoundaryMap (L (a • y)) = _
      rw [L.map_smul]
      exact polynomialBooleanBoundaryMap_parameter_mul a (L y))
    (fun a y => by
      change polynomialBooleanBoundaryMap (f (a • y)) = _
      rw [f.map_smul]
      exact polynomialBooleanBoundaryMap_parameter_mul a (f y))
    (fun σ => by
      change polynomialBooleanBoundaryMap (liftModularParameterMap p f F hb (descentVector σ)) = _
      rw [liftModularParameterMap_descent, map_add]
      have hz : polynomialBooleanBoundaryMap (cyclicPolynomialTop p ℤ *
          liftZModPolynomial p (modularBoundaryCofactor p f F hb σ)) = 0 :=
        (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr ⟨_, rfl⟩
      rw [hz, add_zero]
      rfl)
  exact DFunLike.congr_fun he x

theorem liftModularParameterMap_degree (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (hf : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hF : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      F (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    liftModularParameterMap p f F hb (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  let n := colorOrdinaryDegree (descentColorExponent σ)
  let y := modularBoundaryCofactor p f F hb σ
  have hy : cyclicPolynomialTop p (ZMod p) * y ∈ polynomialDegreePiece n := by
    rw [modularBoundaryCofactor_spec]
    exact (polynomialDegreePiece n).sub_mem (hF σ)
      (polynomialCoefficientChange_degree (Int.castRingHom (ZMod p)) n _ (hf σ))
  rw [liftModularParameterMap_descent]
  apply (polynomialDegreePiece n).add_mem (hf σ)
  by_cases hn : p ≤ n
  · have hygrade : y ∈ polynomialDegreePiece (n - p) := by
      apply cyclicPolynomialTop_predecessor_degree p (ZMod p) (n - p) y
      simpa only [Nat.sub_add_cancel hn] using hy
    have hh := polynomialDegreePiece_mul p (n - p) (cyclicPolynomialTop p ℤ)
      (liftZModPolynomial p y) (cyclicPolynomialTop_degree p ℤ)
      (liftZModPolynomial_degree p (n - p) y hygrade)
    simpa only [Nat.add_sub_of_le hn] using hh
  · have hyzero : y = 0 := cyclicPolynomialTop_factor_zero_below p n (by omega) y hy
    have hlift : liftZModPolynomial p y = 0 := by
      ext a
      rw [liftZModPolynomial_coeff, hyzero]
      simp
    change cyclicPolynomialTop p ℤ * liftZModPolynomial p y ∈ polynomialDegreePiece n
    rw [hlift, mul_zero]
    exact (polynomialDegreePiece n).zero_mem

theorem liftModularParameterMap_one (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (m : ℤ) (hf : f 1 = MvPolynomial.C m) (hF : F 1 = MvPolynomial.C (m : ZMod p)) :
    liftModularParameterMap p f F hb 1 = MvPolynomial.C m := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hσ : descentVector (K := ℤ) σ = 1 := by
    rw [descentVector, weightOrdering_zero_no_descents, Finset.prod_empty]
  have hσ' : descentVector (K := ZMod p) σ = 1 := by
    rw [descentVector, weightOrdering_zero_no_descents, Finset.prod_empty]
  have hδ : modularBoundaryDifference p f F σ = 0 := by
    rw [modularBoundaryDifference, hσ, hσ', hf, hF, MvPolynomial.map_C]
    exact sub_self _
  have hy : modularBoundaryCofactor p f F hb σ = 0 := by
    apply cyclicPolynomialTop_mul_injective p (ZMod p)
    change cyclicPolynomialTop p (ZMod p) * modularBoundaryCofactor p f F hb σ =
      cyclicPolynomialTop p (ZMod p) * 0
    rw [mul_zero, modularBoundaryCofactor_spec, hδ]
  rw [← hσ, liftModularParameterMap_descent, hσ, hf]
  have hlift : liftZModPolynomial p (modularBoundaryCofactor p f F hb σ) = 0 := by
    ext a
    rw [liftZModPolynomial_coeff, hy]
    simp
  rw [hlift, mul_zero, add_zero]

theorem integralCyclic_conjugation_vanishes_modular
    (f : BooleanParameterMap (ZMod p) ℤ)
    (hf : RepresentationIntertwines (cyclicBooleanParameterRepresentation p (ZMod p))
      (cyclicPolynomialParameterRepresentation p (ZMod p)) (extendIntegralParameterMap (ZMod p) f))
    (g : PrimeCycleGroup p) (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
      ((parameterHomRepresentation (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) g f - f) (descentVector σ)) = 0 := by
  let ρ := cyclicBooleanParameterRepresentation p (ZMod p)
  let τ := cyclicPolynomialParameterRepresentation p (ZMod p)
  let F := extendIntegralParameterMap (ZMod p) f
  let x := booleanCoefficientChange (Int.castRingHom (ZMod p)) (descentVector (K := ℤ) σ)
  have he : (cyclicVertexPermutation p g).symm = cyclicVertexPermutation p g⁻¹ := by
    exact ((cyclicVertexPermutation p).map_inv g).symm
  change MvPolynomial.map (Int.castRingHom (ZMod p))
    (MvPolynomial.rename (cyclicVertexPermutation p g)
      (f (booleanPermutationAlgEquiv (cyclicVertexPermutation p g⁻¹) (descentVector σ))) -
      f (descentVector σ)) = 0
  rw [map_sub, ← he, ← polynomialCoefficientChange_eq,
    extendIntegralParameterMap_conjugation]
  rw [← polynomialCoefficientChange_eq, ← extendIntegralParameterMap_commutes]
  rw [he]
  change τ g (F (ρ g⁻¹ x)) - F x = 0
  rw [hf]
  have hi : τ g (τ g⁻¹ (F x)) = F x := by
    change (τ g * τ g⁻¹) (F x) = F x
    rw [← τ.map_mul, mul_inv_cancel, τ.map_one]
    rfl
  rw [hi, sub_self]

theorem integralCyclic_boundary_rename_congr (e : Equiv.Perm (ZMod p))
    (f g : MvPolynomial (ZMod p) ℤ)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p ℤ * y = f - g at hy
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e y, ?_⟩
    change cyclicPolynomialTop p ℤ * MvPolynomial.rename e y = MvPolynomial.rename e (f - g)
    rw [← hy, map_mul, cyclicPolynomialTop_rename]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem exists_integralPrimeCyclic_lift_of_modular
    (f : BooleanParameterMap (ZMod p) ℤ)
    (F : BooleanParameterMap (ZMod p) (ZMod p))
    (hb : ∀ x, polynomialBooleanBoundaryMap (F x) =
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f x))
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hFgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      F (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hFequiv : RepresentationIntertwines (cyclicBooleanParameterRepresentation p (ZMod p))
      (cyclicPolynomialParameterRepresentation p (ZMod p)) F)
    (m : ℤ) (hf₁ : f 1 = MvPolynomial.C m) (hF₁ : F 1 = MvPolynomial.C (m : ZMod p)) :
    ∃ L : BooleanParameterMap (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) L ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        L x ∈ polynomialDegreePiece n) ∧ L 1 = MvPolynomial.C m := by
  let l := liftModularParameterMap p f F hb
  have hlred : extendIntegralParameterMap (ZMod p) l = F :=
    liftModularParameterMap_reduction p f F hb
  have hlb : ∀ x, polynomialBooleanBoundaryMap (l x) = polynomialBooleanBoundaryMap (f x) :=
    liftModularParameterMap_boundary p f F hb
  have hle : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (l (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (l x)) := by
    intro g x
    rw [hlb, hfboundary]
    exact (integralCyclic_boundary_rename_congr p (Equiv.addLeft g.toAdd) (l x) (f x) (hlb x)).symm
  obtain ⟨L, hLe, hLb, hLg, hL₁⟩ := exists_integralPrimeCyclic_correction p l
    (liftModularParameterMap_degree p f F hb hfgrade hFgrade) hle
    (integralCyclic_conjugation_vanishes_modular p l (by rwa [hlred]))
    m (liftModularParameterMap_one p f F hb m hf₁ hF₁)
  exact ⟨L, hLe, fun x => (hLb x).trans (hlb x), hLg, hL₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralPrimeLift.lean -/
section


section

/-! # Integral prime-cyclic boundary lifting

This combines the actual modular controlled lift, exact integral lifting of
its top-monomial corrections, and integral affine averaging.  The conclusion
has no modular lifting, kernel splitting, or torsion-freeness hypotheses:
only an ordinary normalized graded lift of an equivariant boundary is input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicBoundary_coefficient_congr {K L : Type*} [CommRing K] [CommRing L]
    (h : K →+* L) (f g : MvPolynomial (ZMod p) K)
    (he : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.map h f) =
      polynomialBooleanBoundaryMap (MvPolynomial.map h g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff (f - g)).mp hz
  change cyclicPolynomialTop p K * y = f - g at hy
  have hr : polynomialBooleanBoundaryMap (MvPolynomial.map h (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.map h y, ?_⟩
    change cyclicPolynomialTop p L * MvPolynomial.map h y = MvPolynomial.map h (f - g)
    rw [← hy, map_mul, cyclicPolynomialTop_map]
  rw [map_sub, map_sub] at hr
  exact sub_eq_zero.mp hr

theorem extendIntegralParameterMap_cyclicBoundary (f : BooleanParameterMap (ZMod p) ℤ)
    (hf : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x))) :
    ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) (ZMod p)),
      polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f
        (cyclicBooleanParameterRepresentation p (ZMod p) g x)) =
      polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p (ZMod p) g
        (extendIntegralParameterMap (ZMod p) f x)) := by
  intro g
  let F := extendIntegralParameterMap (ZMod p) f
  let ρ := cyclicBooleanParameterRepresentation p (ZMod p)
  let τ := cyclicPolynomialParameterRepresentation p (ZMod p)
  let q : MvPolynomial (ZMod p) (ZMod p) →ₗ[ZMod p] PolynomialBoundaryRing (ZMod p) (ZMod p) :=
    polynomialBooleanBoundaryMap.toLinearMap
  have he : q.comp ((F.restrictScalars (ZMod p)).comp ((ρ g).restrictScalars (ZMod p))) =
      q.comp (((τ g).restrictScalars (ZMod p)).comp (F.restrictScalars (ZMod p))) := by
    apply (booleanParameterBasis (V := ZMod p) (K := ZMod p)).ext
    intro i
    change polynomialBooleanBoundaryMap (F (ρ g (booleanParameterBasis i))) =
      polynomialBooleanBoundaryMap (τ g (F (booleanParameterBasis i)))
    rw [← booleanCoefficientChange_parameterBasis (Int.castRingHom (ZMod p)) i]
    have hact := booleanCoefficientChange_restriction (Int.castRingHom (ZMod p))
      (cyclicVertexPermutation p g).symm.toEmbedding (booleanParameterBasis (K := ℤ) i)
    change booleanCoefficientChange (Int.castRingHom (ZMod p))
        (cyclicBooleanParameterRepresentation p ℤ g (booleanParameterBasis (K := ℤ) i)) =
      ρ g (booleanCoefficientChange (Int.castRingHom (ZMod p))
        (booleanParameterBasis (K := ℤ) i)) at hact
    rw [← hact]
    change polynomialBooleanBoundaryMap (extendIntegralParameterMap (ZMod p) f
      (booleanCoefficientChange (Int.castRingHom (ZMod p))
        (cyclicBooleanParameterRepresentation p ℤ g (booleanParameterBasis (K := ℤ) i)))) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename (cyclicVertexPermutation p g)
        (extendIntegralParameterMap (ZMod p) f
          (booleanCoefficientChange (Int.castRingHom (ZMod p)) (booleanParameterBasis (K := ℤ) i))))
    rw [extendIntegralParameterMap_commutes, extendIntegralParameterMap_commutes,
      polynomialCoefficientChange_eq, polynomialCoefficientChange_eq,
      ← MvPolynomial.map_rename]
    exact cyclicBoundary_coefficient_congr p (Int.castRingHom (ZMod p)) _ _
      (hf g (booleanParameterBasis i))
  intro x
  exact DFunLike.congr_fun he x

theorem exists_integralPrimeCyclic_boundary_lift
    (f : BooleanParameterMap (ZMod p) ℤ)
    (hfgrade : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (hfboundary : ∀ (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) ℤ),
      polynomialBooleanBoundaryMap (f (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (f x)))
    (hf₁ : f 1 = 1) :
    ∃ L : BooleanParameterMap (ZMod p) ℤ,
      RepresentationIntertwines (cyclicBooleanParameterRepresentation p ℤ)
        (cyclicPolynomialParameterRepresentation p ℤ) L ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      (∀ n x, x ∈ (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).piece n →
        L x ∈ polynomialDegreePiece n) ∧ L 1 = 1 := by
  let fbar := extendIntegralParameterMap (ZMod p) f
  have hfb : IsParameterLinear booleanColorMap polynomialColorMap
      (fbar.restrictScalars (ZMod p)) := fun a x => fbar.map_smul a x
  have hfbar₁ : fbar 1 = 1 := by
    simpa only [Int.cast_one, map_one] using
      (extendIntegralParameterMap_one (ZMod p) f 1 (by simpa only [map_one] using hf₁))
  obtain ⟨F, hFp, hFg, hF₁, hFb, hFE, hFe⟩ := exists_primeCyclic_boundary_lift p (ZMod p)
    (fbar.restrictScalars (ZMod p)) hfb hfbar₁
    (extendIntegralParameterMap_degree (ZMod p) f hfgrade)
    (extendIntegralParameterMap_cyclicBoundary p f hfboundary)
  let FA := parameterLinearMap F hFp
  have hFgen : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      FA (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
    intro σ
    change F (descentVector σ) ∈ polynomialDegreePiece _
    apply hFg
    simpa only [booleanScalarGradedBasis, booleanColorBasis_apply] using
      (booleanScalarGradedBasis (V := ZMod p) (K := ZMod p)).generator_mem_piece σ
  obtain ⟨L, hLe, hLb, hLg, hL₁⟩ := exists_integralPrimeCyclic_lift_of_modular p f FA hFb
    hfgrade hFgen hfboundary hFe 1
    (by simpa only [map_one] using hf₁)
    (by change F 1 = MvPolynomial.C ((1 : ℤ) : ZMod p);
        simpa only [Int.cast_one, MvPolynomial.C_1] using hF₁)
  exact ⟨L, hLe, hLb, hLg, by simpa only [map_one] using hL₁⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/StalkAutomorphisms.lean -/
section

section
/-! # Actual relabeling of face stalks

An order automorphism sends an actual vertex below `p` to an actual vertex
below its image.  The two stalk maps are variable renaming in the polynomial
ring and restriction along the inverse vertex bijection in the Boolean
face ring.  Their compatibility with restriction, rank parameters, and
ordinary degree is proved for these maps.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section VertexRelabeling
variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]

def booleanVertexRelabelEquiv (e : V ≃ W) :
    BooleanBarycentricRing V K ≃ₐ[K] BooleanBarycentricRing W K :=
  { booleanRestriction (K := K) e.symm.toEmbedding with
    invFun := booleanRestriction e.toEmbedding
    left_inv := by
      intro x
      have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.toEmbedding e.symm.toEmbedding) x
      rw [he, booleanRestriction_refl] at hh
      exact hh
    right_inv := by
      intro x
      have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl W := by
        ext v
        exact e.apply_symm_apply v
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.symm.toEmbedding e.toEmbedding) x
      rw [he, booleanRestriction_refl] at hh
      exact hh }

@[simp] theorem booleanVertexRelabelEquiv_refl (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv (Equiv.refl V) x = x := by
  change booleanRestriction (Function.Embedding.refl V) x = x
  rw [booleanRestriction_refl]
  rfl

theorem booleanVertexRelabelEquiv_trans (e : V ≃ W) (f : W ≃ U)
    (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv (e.trans f) x =
      booleanVertexRelabelEquiv f (booleanVertexRelabelEquiv e x) := by
  have he : (e.trans f).symm.toEmbedding = f.symm.toEmbedding.trans e.symm.toEmbedding := by
    ext v
    rfl
  change booleanRestriction (e.trans f).symm.toEmbedding x =
    booleanRestriction f.symm.toEmbedding (booleanRestriction e.symm.toEmbedding x)
  rw [he]
  exact (DFunLike.congr_fun (booleanRestriction_comp (K := K)
    f.symm.toEmbedding e.symm.toEmbedding) x).symm

@[simp] theorem booleanVertexRelabelEquiv_parameter (e : V ≃ W) (r : ℕ) :
    booleanVertexRelabelEquiv (K := K) e (booleanRankParameter r) = booleanRankParameter r :=
  booleanRestriction_rankParameter e.symm.toEmbedding r

@[simp] theorem booleanVertexRelabelEquiv_face (e : V ≃ W) (F : BooleanFace V) :
    booleanVertexRelabelEquiv (K := K) e (faceVariable F) =
      faceVariable (booleanFaceEmbedding e.toEmbedding F) := by
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
    ext v
    exact e.symm_apply_apply v
  have hh := booleanRestriction_face_included (K := K) e.symm.toEmbedding
    (booleanFaceEmbedding e.toEmbedding F)
  rw [booleanFaceEmbedding_trans, he, booleanFaceEmbedding_refl] at hh
  exact hh

theorem vertexDegree_finsupp_sum (a : V →₀ ℕ) :
    vertexDegree (fun v => a v) = a.sum (fun _ n => n) :=
  (Finsupp.sum_fintype a (fun _ n => n) (fun _ => rfl)).symm

theorem vertexDegree_mapDomain (f : V → W) (a : V →₀ ℕ) :
    vertexDegree (fun w => a.mapDomain f w) = vertexDegree (fun v => a v) := by
  rw [vertexDegree_finsupp_sum, vertexDegree_finsupp_sum,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

theorem polynomialRename_degree (f : V → W) (n : ℕ)
    (x : MvPolynomial V K) (hx : x ∈ polynomialDegreePiece n) :
    MvPolynomial.rename f x ∈ polynomialDegreePiece n := by
  intro a ha
  apply MvPolynomial.coeff_rename_eq_zero f x a
  intro b hb
  apply hx b
  intro hd
  apply ha
  rw [← hb, vertexDegree_mapDomain, hd]

/-- The same rank-weighted ordinary degree as `chainOrdinaryDegree`, with no
auxiliary ordering of the vertex type required in its interface. -/
def booleanOrdinaryDegree [DecidableEq V] (a : BooleanFace V →₀ ℕ) : ℕ :=
  a.sum (fun F n => n * F.val.card)

theorem booleanOrdinaryDegree_eq_chainOrdinaryDegree [LinearOrder V]
    (a : BooleanFace V →₀ ℕ) : booleanOrdinaryDegree a = chainOrdinaryDegree a := rfl

theorem chainOrdinaryDegree_map_vertexEmbedding [DecidableEq V] [DecidableEq W] (e : V ↪ W)
    (a : BooleanFace V →₀ ℕ) :
    booleanOrdinaryDegree (a.mapDomain (booleanFaceEmbedding e)) = booleanOrdinaryDegree a := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ i j => by simp only [add_mul])]
  simp only [booleanFaceEmbedding_card]

theorem booleanRestriction_degree (e : V ↪ W) (n : ℕ)
    (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanRestriction e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  rw [booleanRestriction_coefficient]
  apply hx
  change booleanOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e)) ≠ n
  rwa [chainOrdinaryDegree_map_vertexEmbedding]

theorem booleanVertexRelabelEquiv_degree (e : V ≃ W) (n : ℕ)
    (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanVertexRelabelEquiv e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  booleanRestriction_degree e.symm.toEmbedding n x hx

end VertexRelabeling

section Stalks
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

def faceVertexOrderEquiv (e : P ≃o P) (p : P) : FaceVertex p ≃ FaceVertex (e p) where
  toFun a := ⟨e a.val, (e.isAtom_iff a.val).mpr a.property.1, e.monotone a.property.2⟩
  invFun a := ⟨e.symm a.val, (e.symm.isAtom_iff a.val).mpr a.property.1,
    by simpa only [e.symm_apply_apply] using e.symm.monotone a.property.2⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)

@[simp] theorem faceVertexOrderEquiv_apply (e : P ≃o P) (p : P) (a : FaceVertex p) :
    (faceVertexOrderEquiv e p a).val = e a.val := rfl

@[simp] theorem faceVertexOrderEquiv_symm_apply (e : P ≃o P) (p : P)
    (a : FaceVertex (e p)) : ((faceVertexOrderEquiv e p).symm a).val = e.symm a.val := rfl

@[simp] theorem faceVertexOrderEquiv_refl (p : P) :
    faceVertexOrderEquiv (OrderIso.refl P) p = Equiv.refl _ := by
  ext a
  rfl

theorem faceVertexOrderEquiv_trans (e f : P ≃o P) (p : P) :
    faceVertexOrderEquiv (e.trans f) p =
      (faceVertexOrderEquiv e p).trans (faceVertexOrderEquiv f (e p)) := by
  ext a
  rfl

theorem faceVertexOrderEquiv_inclusion (e : P ≃o P) {p q : P} (h : q ≤ p) :
    (faceVertexInclusion h).trans (faceVertexOrderEquiv e p).toEmbedding =
      (faceVertexOrderEquiv e q).toEmbedding.trans (faceVertexInclusion (e.monotone h)) := by
  ext a
  rfl

theorem faceVertexOrderEquiv_card (e : P ≃o P) (p : P) :
    Fintype.card (FaceVertex p) = Fintype.card (FaceVertex (e p)) :=
  Fintype.card_congr (faceVertexOrderEquiv e p)

variable (K : Type*) [CommRing K]

def polynomialStalkOrderEquiv (e : P ≃o P) (p : P) :
    PolynomialStalk K p ≃ₐ[K] PolynomialStalk K (e p) :=
  MvPolynomial.renameEquiv K (faceVertexOrderEquiv e p)

def barycentricStalkOrderEquiv (e : P ≃o P) (p : P) :
    BarycentricStalk K p ≃ₐ[K] BarycentricStalk K (e p) :=
  booleanVertexRelabelEquiv (faceVertexOrderEquiv e p)

@[simp] theorem polynomialStalkOrderEquiv_X (e : P ≃o P) (p : P) (a : FaceVertex p) :
    polynomialStalkOrderEquiv K e p (X a) = X (faceVertexOrderEquiv e p a) :=
  MvPolynomial.rename_X _ _

@[simp] theorem polynomialStalkOrderEquiv_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    polynomialStalkOrderEquiv K e p (polynomialParameter K p r) =
      polynomialParameter K (e p) r :=
  MvPolynomial.rename_esymm (σ := FaceVertex p) (R := K) r (faceVertexOrderEquiv e p)

@[simp] theorem barycentricStalkOrderEquiv_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    barycentricStalkOrderEquiv K e p (booleanRankParameter r) = booleanRankParameter r :=
  booleanVertexRelabelEquiv_parameter (faceVertexOrderEquiv e p) r

@[simp] theorem polynomialStalkOrderEquiv_refl (p : P) (x : PolynomialStalk K p) :
    polynomialStalkOrderEquiv K (OrderIso.refl P) p x = x := by
  simp only [polynomialStalkOrderEquiv, faceVertexOrderEquiv_refl, MvPolynomial.renameEquiv_refl,
    AlgEquiv.refl]
  rfl

@[simp] theorem barycentricStalkOrderEquiv_refl (p : P) (x : BarycentricStalk K p) :
    barycentricStalkOrderEquiv K (OrderIso.refl P) p x = x := by
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv (OrderIso.refl P) p) x = x
  have he : faceVertexOrderEquiv (OrderIso.refl P) p = Equiv.refl (FaceVertex p) :=
    faceVertexOrderEquiv_refl p
  exact he.symm ▸ booleanVertexRelabelEquiv_refl x

theorem polynomialStalkOrderEquiv_trans (e f : P ≃o P) (p : P) (x : PolynomialStalk K p) :
    polynomialStalkOrderEquiv K (e.trans f) p x =
      polynomialStalkOrderEquiv K f (e p) (polynomialStalkOrderEquiv K e p x) := by
  rw [polynomialStalkOrderEquiv, faceVertexOrderEquiv_trans, ← MvPolynomial.renameEquiv_trans]
  rfl

theorem barycentricStalkOrderEquiv_trans (e f : P ≃o P) (p : P) (x : BarycentricStalk K p) :
    barycentricStalkOrderEquiv K (e.trans f) p x =
      barycentricStalkOrderEquiv K f (e p) (barycentricStalkOrderEquiv K e p x) := by
  change booleanVertexRelabelEquiv (faceVertexOrderEquiv (e.trans f) p) x =
    booleanVertexRelabelEquiv (faceVertexOrderEquiv f (e p))
      (booleanVertexRelabelEquiv (faceVertexOrderEquiv e p) x)
  exact (faceVertexOrderEquiv_trans e f p).symm ▸
    booleanVertexRelabelEquiv_trans (faceVertexOrderEquiv e p) (faceVertexOrderEquiv f (e p)) x

theorem polynomialStalkOrderEquiv_restriction (e : P ≃o P) {p q : P} (h : q ≤ p)
    (x : PolynomialStalk K p) :
    polynomialRestriction K (e.monotone h) (polynomialStalkOrderEquiv K e p x) =
      polynomialStalkOrderEquiv K e q (polynomialRestriction K h x) := by
  have he : (polynomialRestriction K (e.monotone h)).comp
      (polynomialStalkOrderEquiv K e p).toAlgHom =
      (polynomialStalkOrderEquiv K e q).toAlgHom.comp (polynomialRestriction K h) := by
    apply MvPolynomial.algHom_ext
    intro a
    by_cases hq : a.val ≤ q
    · have haq : e a.val ≤ e q := e.monotone hq
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
        polynomialStalkOrderEquiv_X, polynomialRestriction_X, faceVertexOrderEquiv_apply,
        dif_pos hq, dif_pos haq]
      rfl
    · have haq : ¬ e a.val ≤ e q := fun h' => hq (e.le_iff_le.mp h')
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
        polynomialStalkOrderEquiv_X, polynomialRestriction_X, faceVertexOrderEquiv_apply,
        dif_neg hq, dif_neg haq, map_zero]
  exact DFunLike.congr_fun he x

theorem barycentricStalkOrderEquiv_restriction (e : P ≃o P) {p q : P} (h : q ≤ p)
    (x : BarycentricStalk K p) :
    booleanRestriction (faceVertexInclusion (e.monotone h)) (barycentricStalkOrderEquiv K e p x) =
      barycentricStalkOrderEquiv K e q (booleanRestriction (faceVertexInclusion h) x) := by
  have he : (faceVertexInclusion (e.monotone h)).trans (faceVertexOrderEquiv e p).symm.toEmbedding =
      (faceVertexOrderEquiv e q).symm.toEmbedding.trans (faceVertexInclusion h) := by
    ext a
    rfl
  change booleanRestriction (faceVertexInclusion (e.monotone h))
      (booleanRestriction (faceVertexOrderEquiv e p).symm.toEmbedding x) =
    booleanRestriction (faceVertexOrderEquiv e q).symm.toEmbedding
      (booleanRestriction (faceVertexInclusion h) x)
  calc
    _ = booleanRestriction ((faceVertexInclusion (e.monotone h)).trans
        (faceVertexOrderEquiv e p).symm.toEmbedding) x :=
      DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x
    _ = booleanRestriction ((faceVertexOrderEquiv e q).symm.toEmbedding.trans
        (faceVertexInclusion h)) x := by rw [he]
    _ = _ := (DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x).symm

theorem polynomialStalkOrderEquiv_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : PolynomialStalk K p) (hx : x ∈ polynomialDegreePiece n) :
    polynomialStalkOrderEquiv K e p x ∈ polynomialDegreePiece n :=
  polynomialRename_degree (faceVertexOrderEquiv e p) n x hx

theorem barycentricStalkOrderEquiv_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : BarycentricStalk K p)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    barycentricStalkOrderEquiv K e p x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  booleanVertexRelabelEquiv_degree (faceVertexOrderEquiv e p) n x hx

end Stalks
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/StalkGradingBridge.lean -/
section

section
/-! # Ordinary grading and the existing stalk standard coordinates -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

/-- Retain a specified equality procedure when choosing an auxiliary order.
Only the comparison proof changes; the equality field is literally `d`. -/
def linearOrderWithDecidableEq {α : Type*} (o : LinearOrder α) (d : DecidableEq α) :
    LinearOrder α :=
  { o with
    toDecidableEq := d
    compare_eq_compareOfLessAndEq := by
      intro a b
      have hd : d = o.toDecidableEq := Subsingleton.elim _ _
      cases hd
      exact o.compare_eq_compareOfLessAndEq a b }

section Basis
variable {I K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
theorem scalarOrdinaryBasis_mem_piece (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  by_cases h : i = j
  · subst j
    exact (hj rfl).elim
  · simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg h]

end Basis
section Stalk
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (hs : IsSimplicialPoset P)
/-- Standard-coordinate homogeneity is ordinary homogeneity in the literal
polynomial and chain-monomial bases. -/
theorem ordinaryDegree_of_hasStandardDegree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : HasStandardDegree K hs p f) :
    ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n := by
  letI : LinearOrder (FaceVertex p) :=
    linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
        (Fintype.equivFin (FaceVertex p)).injective) inferInstance
  have hb (u : BooleanChainExponent (FaceVertex p)) :
      f (booleanChainBasis u) ∈ polynomialDegreePiece (chainOrdinaryDegree u.val) := by
    intro a ha
    let v : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm a
    have hv : chainVertexMap v.val = a := chainVertexEquiv.apply_symm_apply a
    have hd : standardOrdinaryDegree ((standardInsideEquiv hs p) v).val ≠
        standardOrdinaryDegree ((standardInsideEquiv hs p) u).val := by
      rw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside,
        ← vertexDegree_eq_chainOrdinaryDegree, hv]
      exact ha
    have h := hf ((standardInsideEquiv hs p) u) ((standardInsideEquiv hs p) v).val hd
    rw [barycentricStalkStandardBasis_local,
      polynomialStandardCoordinates_chain, hv] at h
    exact h
  intro n x hx
  rw [← (booleanChainBasis (V := FaceVertex p) (K := K)).linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply (polynomialDegreePiece n).sum_mem
  intro u hu
  rw [map_smul]
  apply (polynomialDegreePiece n).smul_mem
  have hd : booleanOrdinaryDegree u.val = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hu (hx u hn)
  change chainOrdinaryDegree u.val = n at hd
  exact hd ▸ hb u

end Stalk
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkFamilies.lean -/
section


section

/-! # Linear families on the actual face stalks

All family operations act on genuine Boolean and polynomial stalk maps.
Relabeling uses the inverse order automorphism at the target face, avoiding
arbitrary identifications of vertex sets.  Coherence is an actual restriction
square, and the parameter and degree conditions are the original ones.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

abbrev StalkLinearFamily := ∀ p : P, BarycentricStalk K p →ₗ[K] PolynomialStalk K p

structure CoherentLinearMap (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p →ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)

def CoherentLinearMap.sectionMap {D E : ModuleDiagram K P} (f : CoherentLinearMap K D E) :
    D.sections →ₗ[K] E.sections where
  toFun x := ⟨fun p => f.component p (x.val p), by
    intro p q h
    rw [f.naturality, x.property p q h]⟩
  map_add' x y := by apply Subtype.ext; funext p; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; funext p; exact map_smul _ _ _

def stalkFamilyRelabel (e : P ≃o P) :
    StalkLinearFamily (P := P) K →ₗ[K] StalkLinearFamily (P := P) K where
  toFun F p := (polynomialStalkOrderEquiv K e.symm p).symm.toLinearMap.comp
    ((F (e.symm p)).comp (barycentricStalkOrderEquiv K e.symm p).toLinearMap)
  map_add' F H := by funext p; apply LinearMap.ext; intro x; simp
  map_smul' c F := by funext p; apply LinearMap.ext; intro x; simp

@[simp] theorem stalkFamilyRelabel_apply (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (p : P) (x : BarycentricStalk K p) :
    stalkFamilyRelabel K e F p x = (polynomialStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)) := rfl

theorem polynomialStalkOrderEquiv_trans_symm (e f : P ≃o P) (p : P)
    (x : PolynomialStalk K ((e.trans f) p)) :
    (polynomialStalkOrderEquiv K (e.trans f) p).symm x =
      (polynomialStalkOrderEquiv K e p).symm
        ((polynomialStalkOrderEquiv K f (e p)).symm x) := by
  apply (polynomialStalkOrderEquiv K (e.trans f) p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_trans,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

@[simp] theorem stalkFamilyRelabel_refl (F : StalkLinearFamily (P := P) K) :
    stalkFamilyRelabel K (OrderIso.refl P) F = F := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K (OrderIso.refl P) p).symm
    (F p (barycentricStalkOrderEquiv K (OrderIso.refl P) p x)) = F p x
  apply (polynomialStalkOrderEquiv K (OrderIso.refl P) p).injective
  rw [AlgEquiv.apply_symm_apply, barycentricStalkOrderEquiv_refl,
    polynomialStalkOrderEquiv_refl]

theorem stalkFamilyRelabel_trans (e f : P ≃o P) (F : StalkLinearFamily (P := P) K) :
    stalkFamilyRelabel K (e.trans f) F = stalkFamilyRelabel K f (stalkFamilyRelabel K e F) := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K (f.symm.trans e.symm) p).symm
      (F (e.symm (f.symm p)) (barycentricStalkOrderEquiv K (f.symm.trans e.symm) p x)) = _
  rw [polynomialStalkOrderEquiv_trans_symm, barycentricStalkOrderEquiv_trans]
  rfl

def coherentStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p q (h : q ≤ p) x,
    polynomialRestriction K h (F p x) = F q (booleanRestriction (faceVertexInclusion h) x)}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p q h x
    change polynomialRestriction K h (F p x + H p x) = _
    rw [map_add, hF, hH]
    rfl
  smul_mem' := by
    intro c F hF p q h x
    change polynomialRestriction K h (c • F p x) = _
    rw [map_smul, hF]
    rfl

def parameterStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p r x, F p (booleanRankParameter (r + 1) * x) = polynomialParameter K p (r + 1) * F p x}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p r x
    change F p (booleanRankParameter (r + 1) * x) + H p (booleanRankParameter (r + 1) * x) =
      polynomialParameter K p (r + 1) * (F p x + H p x)
    rw [hF, hH, mul_add]
  smul_mem' := by
    intro c F hF p r x
    change c • F p _ = polynomialParameter K p (r + 1) * (c • F p x)
    rw [hF, mul_smul_comm]

def gradedStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
    (fun a => booleanOrdinaryDegree a.val) n → F p x ∈ polynomialDegreePiece n}
  zero_mem' := by intro p n x hx; exact (polynomialDegreePiece n).zero_mem
  add_mem' := by intro F H hF hH p n x hx; exact (polynomialDegreePiece n).add_mem (hF p n x hx) (hH p n x hx)
  smul_mem' := by intro c F hF p n x hx; exact (polynomialDegreePiece n).smul_mem c (hF p n x hx)

def coherentGradedParameterStalkFamilies : Submodule K (StalkLinearFamily (P := P) K) :=
  coherentStalkFamilySubmodule K ⊓ (parameterStalkFamilySubmodule K ⊓ gradedStalkFamilySubmodule K)

theorem polynomialStalkOrderEquiv_symm_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    (polynomialStalkOrderEquiv K e p).symm (polynomialParameter K (e p) r) =
      polynomialParameter K p r := by
  apply (polynomialStalkOrderEquiv K e p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_parameter]

theorem polynomialStalkOrderEquiv_symm_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : PolynomialStalk K (e p)) (hx : x ∈ polynomialDegreePiece n) :
    (polynomialStalkOrderEquiv K e p).symm x ∈ polynomialDegreePiece n :=
  polynomialRename_degree (faceVertexOrderEquiv e p).symm n x hx

theorem stalkFamilyRelabel_parameter (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ parameterStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ parameterStalkFamilySubmodule K := by
  intro p r x
  rw [stalkFamilyRelabel_apply, map_mul, barycentricStalkOrderEquiv_parameter,
    hF, map_mul, polynomialStalkOrderEquiv_symm_parameter]
  rfl

theorem stalkFamilyRelabel_graded (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ gradedStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  exact polynomialStalkOrderEquiv_symm_degree K e.symm p n _
    (hF (e.symm p) n _ (barycentricStalkOrderEquiv_degree K e.symm p n x hx))

theorem stalkFamilyRelabel_coherent (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  apply (polynomialStalkOrderEquiv K e.symm q).injective
  have hn := polynomialStalkOrderEquiv_restriction K e.symm h
    ((polynomialStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)))
  change polynomialStalkOrderEquiv K e.symm q
      (polynomialRestriction K h ((polynomialStalkOrderEquiv K e.symm p).symm
        (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)))) =
    polynomialStalkOrderEquiv K e.symm q
      ((polynomialStalkOrderEquiv K e.symm q).symm
        (F (e.symm q) (barycentricStalkOrderEquiv K e.symm q
          (booleanRestriction (faceVertexInclusion h) x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hF,
    barycentricStalkOrderEquiv_restriction]

theorem stalkFamilyRelabel_normalized (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (c : K) (hF : ∀ p, F p 1 = MvPolynomial.C c) :
    ∀ p, stalkFamilyRelabel K e F p 1 = MvPolynomial.C c := by
  intro p
  rw [stalkFamilyRelabel_apply, map_one, hF]
  exact (polynomialStalkOrderEquiv K e.symm p).symm.commutes c

section Action
variable {G : Type*} [Group G]
variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def stalkFamilyRepresentation : CyclicRepresentation K G (StalkLinearFamily (P := P) K) where
  toFun g := stalkFamilyRelabel K (act g)
  map_one' := by
    apply LinearMap.ext
    intro F
    rw [h₁, stalkFamilyRelabel_refl]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    rw [hmul, stalkFamilyRelabel_trans]
    rfl

def representationMulAction {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : CyclicRepresentation A G M) : MulAction G M where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [ρ.map_one]; rfl
  mul_smul g h x := by change ρ (g * h) x = ρ g (ρ h x); rw [ρ.map_mul]; rfl

end Action
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkInduction.lean -/
section


section

/-! # Orbitwise induction for actual coherent stalk maps

The generic orbit choice is applied to families supported at one face.  A
rank stage therefore stores actual maps on exactly the previously constructed
stalks.  Its boundary map is obtained by reading those components, and the
compatibility predicate is the genuine restriction equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def stalkFamilySingle (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    StalkLinearFamily (P := P) K := Pi.single p f

@[simp] theorem stalkFamilySingle_same (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    stalkFamilySingle K p f p = f := by simp [stalkFamilySingle]

@[simp] theorem stalkFamilySingle_ne (p q : P) (h : q ≠ p)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) :
    stalkFamilySingle K p f q = 0 := by simp [stalkFamilySingle, h]

theorem stalkFamilySingle_eq_of_supported (p : P) (F : StalkLinearFamily (P := P) K)
    (hF : ∀ q, q ≠ p → F q = 0) : stalkFamilySingle K p (F p) = F := by
  funext q
  by_cases hq : q = p
  · subst q
    exact stalkFamilySingle_same K p (F p)
  · rw [stalkFamilySingle_ne K p q hq, hF q hq]

def StalkLocalGood (p : P) (F : StalkLinearFamily (P := P) K) : Prop :=
  (∀ q, q ≠ p → F q = 0) ∧ F ∈ parameterStalkFamilySubmodule K ∧
    F ∈ gradedStalkFamilySubmodule K ∧ F p 1 = 1

def StalkLocalCompatible (p q : P) (F H : StalkLinearFamily (P := P) K) : Prop :=
  ∀ (h : q ≤ p) x, polynomialRestriction K h (F p x) =
    H q (booleanRestriction (faceVertexInclusion h) x)

theorem stalkFamilySingle_good (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hp : ∀ r x, f (booleanRankParameter (r + 1) * x) = polynomialParameter K p (r + 1) * f x)
    (hd : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (h₁ : f 1 = 1) : StalkLocalGood K p (stalkFamilySingle K p f) := by
  refine ⟨fun q hq => stalkFamilySingle_ne K p q hq f, ?_, ?_, ?_⟩
  · intro q r x
    by_cases hq : q = p
    · subst q; simpa only [stalkFamilySingle_same] using hp r x
    · rw [stalkFamilySingle_ne K p q hq f]
      simp
  · intro q n x hx
    by_cases hq : q = p
    · subst q; simpa only [stalkFamilySingle_same] using hd n x hx
    · rw [stalkFamilySingle_ne K p q hq f]
      exact (polynomialDegreePiece n).zero_mem
  · simpa only [stalkFamilySingle_same] using h₁

theorem stalkFamilyRelabel_good (e : P ≃o P) (p : P) (F : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K p F) :
    StalkLocalGood K (e p) (stalkFamilyRelabel K e F) := by
  refine ⟨?_, stalkFamilyRelabel_parameter K e F hF.2.1,
    stalkFamilyRelabel_graded K e F hF.2.2.1, ?_⟩
  · intro q hq
    have hn : e.symm q ≠ p := by
      intro he
      exact hq ((e.apply_symm_apply q).symm.trans (congrArg e he))
    apply LinearMap.ext
    intro x
    rw [stalkFamilyRelabel_apply, hF.1 _ hn]
    simp
  · rw [stalkFamilyRelabel_apply, map_one]
    have hhq (q : P) (hq : q = p) : F q 1 = 1 := by
      subst q
      exact hF.2.2.2
    have hh : F (e.symm (e p)) 1 = 1 := hhq _ (e.symm_apply_apply p)
    rw [hh, map_one]

theorem stalkFamilyRelabel_compatible (e : P ≃o P) (p q : P)
    (F H : StalkLinearFamily (P := P) K) (hFH : StalkLocalCompatible K p q F H) :
    StalkLocalCompatible K (e p) (e q) (stalkFamilyRelabel K e F) (stalkFamilyRelabel K e H) := by
  intro h x
  apply (polynomialStalkOrderEquiv K e.symm (e q)).injective
  have hn := polynomialStalkOrderEquiv_restriction K e.symm h
    ((polynomialStalkOrderEquiv K e.symm (e p)).symm
      (F (e.symm (e p)) (barycentricStalkOrderEquiv K e.symm (e p) x)))
  change polynomialStalkOrderEquiv K e.symm (e q)
      (polynomialRestriction K h ((polynomialStalkOrderEquiv K e.symm (e p)).symm
        (F (e.symm (e p)) (barycentricStalkOrderEquiv K e.symm (e p) x)))) =
    polynomialStalkOrderEquiv K e.symm (e q)
      ((polynomialStalkOrderEquiv K e.symm (e q)).symm
        (H (e.symm (e q)) (barycentricStalkOrderEquiv K e.symm (e q)
          (booleanRestriction (faceVertexInclusion h) x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [← barycentricStalkOrderEquiv_restriction]
  have hh : StalkLocalCompatible K (e.symm (e p)) (e.symm (e q)) F H := by
    simpa only [e.symm_apply_apply] using hFH
  exact hh (e.symm.monotone h) _

section Stage

variable {G : Type*} [Group G] [MulAction G P] [MulAction G (StalkLinearFamily (P := P) K)]
variable (hs : IsSimplicialPoset P)
variable (hrank : ∀ (g : G) (p : P), faceRank (g • p) = faceRank p)

def EquivariantRankStage.stalkBoundary {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) :
    CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)) where
  component q := old.value ⟨q.val, by
    change faceRank q.val < n
    rw [← hp]
    exact faceRank_strictMono hs q.property⟩ q.val
  naturality q r h x := by
    by_cases he : r = q
    · subst r
      simp only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.toLinearMap_apply, AlgHom.id_apply]
    · have hlt : r.val < q.val := lt_of_le_of_ne h (fun h' => he (Subtype.ext h'))
      exact old.compatible
        ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩
        ⟨r.val, by change faceRank r.val < n; rw [← hp]; exact faceRank_strictMono hs r.property⟩
        hlt h x

theorem EquivariantRankStage.stalkBoundary_parameter {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) (r : ℕ) (x : BarycentricStalk K q.val) :
    (old.stalkBoundary K hs hrank p hp).component q (booleanRankParameter (r + 1) * x) =
      polynomialParameter K q.val (r + 1) * (old.stalkBoundary K hs hrank p hp).component q x :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.1 q.val r x

theorem EquivariantRankStage.stalkBoundary_degree {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) (m : ℕ) (x : BarycentricStalk K q.val)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m) :
    (old.stalkBoundary K hs hrank p hp).component q x ∈ polynomialDegreePiece m :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.2.1 q.val m x hx

theorem EquivariantRankStage.stalkBoundary_one {n : ℕ}
    (old : EquivariantRankStage faceRank hrank (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (q : Set.Iio p) :
    (old.stalkBoundary K hs hrank p hp).component q 1 = 1 :=
  (old.good ⟨q.val, by change faceRank q.val < n; rw [← hp]; exact faceRank_strictMono hs q.property⟩).2.2.2

end Stage

section ActualAction

variable {G : Type*} [Group G]
variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def orderActionMulAction : MulAction G P where
  smul g p := act g p
  one_smul p := by change act 1 p = p; rw [h₁]; rfl
  mul_smul g h p := by change act (g * h) p = act g (act h p); rw [hmul]; rfl

theorem exists_equivariant_coherent_stalk_family (hs : IsSimplicialPoset P)
    (hlift :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      ∀ n (old : EquivariantRankStage faceRank
          (fun g p => faceRank_eq_of_orderIso (act g) p)
          (StalkLocalGood K) (StalkLocalCompatible K) n)
        (p : P), faceRank p = n → ∃ y : StalkLinearFamily (P := P) K,
          StalkLocalGood K p y ∧
          (∀ q : rankCut faceRank n, q.val < p →
            StalkLocalCompatible K p q.val y (old.value q)) ∧
          ∀ g : G, act g p = p → stalkFamilyRelabel K (act g) y = y) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧
      F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧
      (∀ p, F p 1 = 1) ∧ ∀ g : G, stalkFamilyRelabel K (act g) F = F := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  obtain ⟨f, hfg, hfc, hfe⟩ := exists_equivariant_rank_family faceRank
    (faceRank_strictMono hs) (fun g p => faceRank_eq_of_orderIso (act g) p)
    (fun g _ _ h => (act g).strictMono h)
    (StalkLocalGood K) (StalkLocalCompatible K)
    (fun g p y hy => stalkFamilyRelabel_good K (act g) p y hy)
    (fun g p q y z hy => stalkFamilyRelabel_compatible K (act g) p q y z hy)
    hlift
  let F : StalkLinearFamily (P := P) K := fun p => f p p
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h x
    by_cases he : q = p
    · subst q
      simpa only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.id_apply, AlgHom.toLinearMap_apply]
    · exact hfc p q (lt_of_le_of_ne h he) h x
  · intro p r x
    exact (hfg p).2.1 p r x
  · intro p n x hx
    exact (hfg p).2.2.1 p n x hx
  · intro p
    exact (hfg p).2.2.2
  · intro g
    funext p
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun z : StalkLinearFamily (P := P) K => z p x)
      (hfe g ((act g).symm p))
    change f (act g ((act g).symm p)) p x =
      stalkFamilyRelabel K (act g) (f ((act g).symm p)) p x at hh
    rw [(act g).apply_symm_apply] at hh
    exact hh.symm

end ActualAction
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicConstantStalk.lean -/
section


section

/-! # The normalized constant stalk

The empty face has no vertices, so its actual Boolean stalk is generated by
the constant element over the coefficient ring.  A normalized linear map is
therefore unique; equivariance at the constant stalk requires no averaging.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical Finset MvPolynomial

section Empty
variable {V K : Type*} [Fintype V] [CommRing K] [IsEmpty V]

theorem boolean_empty_exists_smul_one (x : BooleanBarycentricRing V K) :
    ∃ c : K, c • (1 : BooleanBarycentricRing V K) = x := by
  letI : IsEmpty (BooleanFace V) := ⟨fun F => by
    obtain ⟨v, hv⟩ := F.property
    exact isEmptyElim v⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (BooleanFace V) a
  refine ⟨c, ?_⟩
  let q := Ideal.Quotient.mkₐ K (forbiddenIdeal (K := K) (IsChainExponent (V := V)))
  calc
    c • (1 : BooleanBarycentricRing V K) = c • q 1 := by rw [map_one]
    _ = q (c • (1 : MvPolynomial (BooleanFace V) K)) := (map_smul q c 1).symm
    _ = q (MvPolynomial.C c) := by rw [Algebra.smul_def, mul_one]; rfl
    _ = _ := rfl

theorem boolean_empty_linear_ext_one {N : Type*} [AddCommGroup N] [Module K N]
    (f g : BooleanBarycentricRing V K →ₗ[K] N) (h : f 1 = g 1) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := boolean_empty_exists_smul_one x
  rw [map_smul, map_smul, h]

end Empty

section Canonical
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem canonicalBooleanPolynomial_one : canonicalBooleanPolynomial (V := V) (K := K) 1 = 1 := by
  have hzero : booleanChainBasis (K := K) (⟨0, isChainExponent_zero⟩ : BooleanChainExponent V) = 1 := by
    rw [booleanChainBasis, standardMonomialBasis_apply]
    simp
  rw [← hzero, canonicalBooleanPolynomial_basis]
  have hchain : chainVertexMap (0 : BooleanFace V →₀ ℕ) = 0 := by
    ext v
    simp [chainVertexMap, chainVertexMapUnordered]
  rw [hchain]
  simp

theorem canonicalBooleanPolynomial_degree (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n) :
    canonicalBooleanPolynomial x ∈ polynomialDegreePiece n := by
  intro a ha
  let c : BooleanChainExponent V := chainVertexEquiv.symm a
  have hc : chainVertexMap c.val = a := chainVertexEquiv.apply_symm_apply a
  rw [← hc, canonicalBooleanPolynomial_coefficient]
  apply hx c
  change chainOrdinaryDegree c.val ≠ n
  rw [← vertexDegree_eq_chainOrdinaryDegree, hc]
  exact ha

end Canonical

section Stalk
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def emptyFaceVertex : IsEmpty (FaceVertex (⊥ : P)) := ⟨fun v =>
  v.property.1.ne_bot (le_bot_iff.mp v.property.2)⟩

theorem stalkLocalGood_bot_unique (F H : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K ⊥ F) (hH : StalkLocalGood K ⊥ H) : F = H := by
  letI := emptyFaceVertex (P := P)
  funext p
  by_cases hp : p = ⊥
  · subst p
    exact boolean_empty_linear_ext_one _ _ (hF.2.2.2.trans hH.2.2.2.symm)
  · rw [hF.1 p hp, hH.1 p hp]

theorem stalkLocalGood_bot_fixed (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : StalkLocalGood K ⊥ F) : stalkFamilyRelabel K e F = F := by
  apply stalkLocalGood_bot_unique K _ F _ hF
  have hh := stalkFamilyRelabel_good K e ⊥ F hF
  simpa only [e.map_bot] using hh

theorem exists_stalkLocalGood_bot : ∃ F : StalkLinearFamily (P := P) K, StalkLocalGood K ⊥ F := by
  letI := emptyFaceVertex (P := P)
  letI : LinearOrder (FaceVertex (⊥ : P)) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex (⊥ : P)))
      (Fintype.equivFin (FaceVertex (⊥ : P))).injective
  let f : BarycentricStalk K (⊥ : P) →ₗ[K] PolynomialStalk K ⊥ :=
    canonicalBooleanPolynomial.toLinearMap
  refine ⟨stalkFamilySingle K ⊥ f, stalkFamilySingle_good K ⊥ f ?_
    (canonicalBooleanPolynomial_degree) canonicalBooleanPolynomial_one⟩
  intro r x
  have hr : Fintype.card (FaceVertex (⊥ : P)) < r + 1 := by simp
  rw [booleanRankParameter_above _ hr, zero_mul, map_zero,
    polynomialParameter, esymm_above_card _ hr, zero_mul]

end Stalk
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCoherentBoundaryLift.lean -/
section

section
/-! # Ordinary graded extensions of coherent boundary maps

The input is a coherent family of actual linear maps, without any assumption
of invertibility.  The correction uses the established section of the genuine
proper-face restriction map.  Extending its values on the actual descent
basis gives a parameter-linear map with the prescribed restrictions.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def linearCoherentBoundaryCorrection (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p :=
  (polynomialCarrierBoundaryExtension K hs p).comp
    ((e.sectionMap K).comp (stalkBoundaryRestriction (barycentricDiagram K) p))

theorem linearCoherentBoundaryCorrection_restrict (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p
      (linearCoherentBoundaryCorrection K hs p e x) =
      e.sectionMap K (stalkBoundaryRestriction (barycentricDiagram K) p x) :=
  polynomialCarrierBoundaryExtension_restrict K hs p _

theorem linearCoherentBoundaryCorrection_coefficient (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p)
    (b : StandardFaceIndex P) :
    (polynomialStandardCoordinates K hs p (linearCoherentBoundaryCorrection K hs p e x)).val b =
      if hb : standardCarrier b < p then
        (polynomialStandardCoordinates K hs (standardCarrier b)
          (e.component ⟨standardCarrier b, hb⟩
            (booleanRestriction (faceVertexInclusion hb.le) x))).val b else 0 := by
  unfold linearCoherentBoundaryCorrection polynomialCarrierBoundaryExtension
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coefficientBoundaryExtension_apply]
  rfl

theorem linearCoherentBoundaryCorrection_standard_degree (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q)) :
    HasStandardDegree K hs p (linearCoherentBoundaryCorrection K hs p e) := by
  intro a b hab
  rw [linearCoherentBoundaryCorrection_coefficient]
  by_cases hb : standardCarrier b < p
  · rw [dif_pos hb]
    have hres := barycentricStandardCoordinates_naturality K hs hb.le
      (barycentricStalkStandardBasis K hs p a)
    rw [barycentricStandardCoordinates_basis, coefficientRestriction_unit] at hres
    by_cases ha : standardCarrier a.val ≤ standardCarrier b
    · rw [dif_pos ha] at hres
      have hval : booleanRestriction (K := K) (faceVertexInclusion hb.le)
          (barycentricStalkStandardBasis K hs p a) =
            barycentricStalkStandardBasis K hs (standardCarrier b) ⟨a.val, ha⟩ := by
        apply (barycentricStandardCoordinates K hs (standardCarrier b)).injective
        rw [← hres, barycentricStandardCoordinates_basis]
      rw [hval]
      exact he ⟨standardCarrier b, hb⟩ ⟨a.val, ha⟩ b hab
    · rw [dif_neg ha] at hres
      have hval : booleanRestriction (K := K) (faceVertexInclusion hb.le)
          (barycentricStalkStandardBasis K hs p a) = 0 := by
        apply (barycentricStandardCoordinates K hs (standardCarrier b)).injective
        rw [← hres, map_zero]
      rw [hval, map_zero, map_zero]
      rfl
  · rw [dif_neg hb]

variable (p : P) [LinearOrder (FaceVertex p)]

def linearCoherentLocalExtension
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  exact ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun σ => linearCoherentBoundaryCorrection K hs p e (descentVector σ))).restrictScalars K

@[simp] theorem linearCoherentLocalExtension_basis
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    linearCoherentLocalExtension K hs p e (descentVector σ) =
      linearCoherentBoundaryCorrection K hs p e (descentVector σ) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  change ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun τ => linearCoherentBoundaryCorrection K hs p e (descentVector τ))) (descentVector σ) = _
  simpa only [booleanColorBasis_apply] using
    (Module.Basis.constr_basis (booleanColorBasis (V := FaceVertex p) (K := K))
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun τ => linearCoherentBoundaryCorrection K hs p e (descentVector τ)) σ)

theorem linearCoherentLocalExtension_parameter_mul
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IsParameterLinear booleanColorMap polynomialColorMap (linearCoherentLocalExtension K hs p e) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  let f :=
    (booleanColorBasis (V := FaceVertex p) (K := K)).constr
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun σ => linearCoherentBoundaryCorrection K hs p e (descentVector σ))
  intro a x
  change f (booleanColorMap a * x) = polynomialColorMap a * f x
  exact f.map_smul a x

theorem linearCoherentLocalExtension_intertwinesAllRanks
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IntertwinesAllRanks (linearCoherentLocalExtension K hs p e) :=
  parameterLinear_intertwinesAllRanks _ (linearCoherentLocalExtension_parameter_mul K hs p e)

set_option backward.isDefEq.respectTransparency false in
theorem linearCoherentLocalExtension_naturality
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q ((booleanRankParameter (V := FaceVertex q.val) (K := K) (i + 1)) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (q : Set.Iio p) (x : BarycentricStalk K p) :
    polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x) := by
  let F : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (polynomialRestriction K q.property.le).toLinearMap.comp (linearCoherentLocalExtension K hs p e)
  let G : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (e.component q).comp
      (booleanRestriction (K := K) (faceVertexInclusion q.property.le)).toLinearMap
  have hF : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change polynomialRestriction K q.property.le
      (linearCoherentLocalExtension K hs p e (booleanColorMap (X c) * z)) = _
    erw [linearCoherentLocalExtension_parameter_mul K hs p e, map_mul]
    rw [polynomialColorMap, MvPolynomial.aeval_X,
      polynomialParameterMap, MvPolynomial.aeval_X]
    change polynomialRestriction K q.property.le
      (esymm (FaceVertex p) K (c.val + 1)) *
      polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e z) =
      esymm (FaceVertex q.val) K (c.val + 1) *
      polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e z)
    congr 1
    exact polynomialRestriction_parameter K q.property.le (c.val + 1)
  have hG : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) G := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change e.component q (booleanRestriction (faceVertexInclusion q.property.le)
      (booleanColorMap (X c) * z)) = _
    erw [map_mul]
    have hb : booleanRestriction (K := K) (faceVertexInclusion q.property.le)
        (booleanColorMap (X c)) = booleanRankParameter (c.val + 1) := by
      have hc : booleanColorMap (K := K) (X c) = colorSum c := by
        rw [booleanColorMap, MvPolynomial.aeval_X]
        rfl
      have hcol := hc.trans (booleanRankParameter_color (K := K) c).symm
      exact (congrArg (booleanRestriction (K := K) (faceVertexInclusion q.property.le)) hcol).trans
        (booleanRestriction_rankParameter (K := K) (faceVertexInclusion q.property.le) (c.val + 1))
    erw [hb]
    rw [polynomialParameterMap, MvPolynomial.aeval_X]
    change e.component q (booleanRankParameter (c.val + 1) *
      booleanRestriction (faceVertexInclusion q.property.le) z) =
      polynomialParameter K q.val (c.val + 1) *
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) z)
    exact he q c.val (booleanRestriction (faceVertexInclusion q.property.le) z)
  have hfg : F = G := parameterLinear_ext_descent
    (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F G hF hG (by
      intro σ
      change polynomialRestriction K q.property.le
        (linearCoherentLocalExtension K hs p e (descentVector σ)) = _
      rw [linearCoherentLocalExtension_basis]
      have h := congrArg (fun y : ((polynomialDiagram K).restrict (Set.Iio p)).sections => y.val q)
        (linearCoherentBoundaryCorrection_restrict K hs p e (descentVector σ))
      exact h)
  exact DFunLike.congr_fun hfg x

variable {p}

theorem linearCoherentLocalExtension_descent_degree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    linearCoherentLocalExtension K hs p e (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  intro b hb
  let a := descentChainIndex σ
  let c : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm b
  have hcb : chainVertexMap c.val = b := chainVertexEquiv.apply_symm_apply b
  have hne : standardOrdinaryDegree ((standardInsideEquiv hs p) c).val ≠
      standardOrdinaryDegree ((standardInsideEquiv hs p) a).val := by
    erw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside, descentChainIndex_degree,
      ← vertexDegree_eq_chainOrdinaryDegree, hcb]
    exact hb
  have h := linearCoherentBoundaryCorrection_standard_degree K hs p e he
    ((standardInsideEquiv hs p) a) ((standardInsideEquiv hs p) c).val hne
  erw [barycentricStalkStandardBasis_local, ← descentVector_eq_chainBasis,
    polynomialStandardCoordinates_chain, hcb] at h
  change (linearCoherentLocalExtension K hs p e (descentVector σ)).coeff b = 0
  rw [linearCoherentLocalExtension_basis]
  exact h

theorem linearCoherentLocalExtension_hasStandardDegree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q)) :
    HasStandardDegree K hs p (linearCoherentLocalExtension K hs p e) := by
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := parameterLinear_chain_degree (linearCoherentLocalExtension K hs p e)
      (linearCoherentLocalExtension_parameter_mul K hs p e)
      (linearCoherentLocalExtension_descent_degree K hs p e he) u (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p
      (linearCoherentLocalExtension K hs p e (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p
        (linearCoherentLocalExtension K hs p e (barycentricStalkStandardBasis K hs p a))).property b hb

theorem linearCoherentLocalExtension_graded (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (n : ℕ) (x : BarycentricStalk K p)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    linearCoherentLocalExtension K hs p e x ∈ polynomialDegreePiece n :=
  parameterLinear_ordinary_degree _ (linearCoherentLocalExtension_parameter_mul K hs p e)
    (linearCoherentLocalExtension_descent_degree K hs p e he) n x hx

theorem hasStandardDegree_of_ordinary_degree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n) :
    HasStandardDegree K hs p f := by
  letI : LinearOrder (FaceVertex p) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := hf (chainOrdinaryDegree u.val) (booleanChainBasis u)
      (ordinaryBasis_mem_piece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) u)
      (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p (f (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).property b hb

theorem polynomialDegreePiece_zero_eq_C {V : Type*} [Fintype V]
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece 0) : f = MvPolynomial.C (f.coeff 0) := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp
  · rw [MvPolynomial.coeff_C_of_ne_zero ha]
    apply hf a
    intro hd
    apply ha
    ext v
    have hv : a v ≤ vertexDegree (fun w => a w) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    change a v = 0
    omega

/-- The ordinary extension has the same constant normalization as all its
proper-face components.  Positive rank supplies the proper bottom face. -/
theorem linearCoherentLocalExtension_normalized (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    linearCoherentLocalExtension K hs p e 1 = 1 := by
  let σ := weightOrdering (fun _ : FaceVertex p => 0)
  have hdes : descentVector (K := K) σ = 1 := by
    simp [descentVector, σ, weightOrdering_zero_no_descents]
  have hdeg : colorOrdinaryDegree (descentColorExponent σ) = 0 := by
    rw [descentOrdinaryDegree_eq_zero_iff]
    exact weightOrdering_zero_no_descents
  have hdegree := linearCoherentLocalExtension_descent_degree K hs p e hegrade σ
  rw [hdes, hdeg] at hdegree
  have hC := polynomialDegreePiece_zero_eq_C K _ hdegree
  have hp : (⊥ : P) < p := by
    have hr : 0 < faceRank p := by
      rw [← card_faceVertex p]
      exact Fintype.card_pos
    apply bot_lt_iff_ne_bot.mpr
    intro he
    rw [he, faceRank_bot] at hr
    exact (Nat.lt_irrefl 0) hr
  let q : Set.Iio p := ⟨⊥, hp⟩
  have hn := linearCoherentLocalExtension_naturality K hs p e heparam q 1
  rw [hC] at hn
  simp only [polynomialRestriction_C, map_one, heone] at hn
  have hc' : (linearCoherentLocalExtension K hs p e 1).coeff 0 = 1 := by
    apply MvPolynomial.C_injective (FaceVertex (⊥ : P)) K
    exact hn.trans (MvPolynomial.C_1).symm
  rw [hC, hc', MvPolynomial.C_1]

include hs in
/-- A normalized graded parameter-linear extension of an arbitrary coherent
normalized graded boundary family.  This is the actual local choice needed
for the orbit induction; no boundary invertibility is assumed. -/
theorem exists_linearCoherentLocalExtension (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ (q : Set.Iio p) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e.component q x ∈ polynomialDegreePiece n)
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    ∃ f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p,
      IsParameterLinear booleanColorMap polynomialColorMap f ∧
      (∀ (q : Set.Iio p) x, polynomialRestriction K q.property.le (f x) =
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) x)) ∧
      (∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n) ∧ f 1 = 1 := by
  have hd : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q) :=
    fun q => hasStandardDegree_of_ordinary_degree K hs q.val (e.component q) (hegrade q)
  exact ⟨linearCoherentLocalExtension K hs p e,
    linearCoherentLocalExtension_parameter_mul K hs p e,
    linearCoherentLocalExtension_naturality K hs p e heparam,
    linearCoherentLocalExtension_graded K hs p e hd,
    linearCoherentLocalExtension_normalized K hs p e heparam hd heone⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/SimplexTransportGeometry.lean -/
section

section
/-! # Literal finite-simplex vertex geometry

Shared exact declarations for finite-subset order isomorphisms, simplex
vertices, and finite embeddings. No cyclic lifting theorem is imported.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset
section Simplex
variable {V W U : Type*} [Fintype V] [Fintype W] [Fintype U]

def finsetOrderCongr (e : V ≃ W) : Finset V ≃o Finset W :=
  { e.finsetCongr with map_rel_iff' := by intro s t; exact Finset.map_subset_map }

@[simp] theorem finsetOrderCongr_apply (e : V ≃ W) (s : Finset V) :
    finsetOrderCongr e s = s.map e.toEmbedding := rfl

@[simp] theorem finsetOrderCongr_refl : finsetOrderCongr (Equiv.refl V) = OrderIso.refl _ := by
  ext s
  simp

theorem finsetOrderCongr_trans (e : V ≃ W) (f : W ≃ U) :
    finsetOrderCongr (e.trans f) = (finsetOrderCongr e).trans (finsetOrderCongr f) := by
  apply OrderIso.ext
  funext s
  exact congrArg (fun t : Finset V ≃ Finset U => t s) (Equiv.finsetCongr_trans e f).symm

def simplexIntervalOrderEquiv (s : Finset V) : Set.Iic s ≃o Finset s where
  toFun t := t.val.subtype (fun v => v ∈ s)
  invFun t := ⟨t.map (Function.Embedding.subtype _), by
    intro v hv
    exact Finset.property_of_mem_map_subtype t hv⟩
  left_inv t := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (fun v hv => t.property hv)
  right_inv t := by
    ext v
    simp
  map_rel_iff' := by
    intro t u
    constructor
    · intro h v hv
      have hv' : (⟨v, t.property hv⟩ : s) ∈ t.val.subtype (fun v => v ∈ s) :=
        Finset.mem_subtype.mpr hv
      exact Finset.mem_subtype.mp (h hv')
    · intro h v hv
      exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp hv))

theorem simplex_isSimplicialPoset : IsSimplicialPoset (Finset V) := by
  intro s
  exact ⟨Fintype.card s, ⟨(simplexIntervalOrderEquiv s).trans
    (finsetOrderCongr (Fintype.equivFin s))⟩⟩

def simplexAtomMap (s : Finset V) (v : s) : FaceVertex s :=
  ⟨{v.val}, Finset.isAtom_singleton v.val, Finset.singleton_subset_iff.mpr v.property⟩

theorem simplexAtomMap_bijective (s : Finset V) : Function.Bijective (simplexAtomMap s) := by
  constructor
  · intro v w h
    apply Subtype.ext
    have hh := congrArg (fun a : FaceVertex s => a.val) h
    exact Finset.singleton_injective hh
  · intro a
    obtain ⟨v, hv⟩ := Finset.isAtom_iff.mp a.property.1
    have hvs : v ∈ s := by
      apply a.property.2
      rw [hv]
      exact Finset.mem_singleton_self v
    refine ⟨⟨v, hvs⟩, ?_⟩
    apply Subtype.ext
    exact hv.symm

def simplexVertexEquiv (s : Finset V) : FaceVertex s ≃ s :=
  (Equiv.ofBijective (simplexAtomMap s) (simplexAtomMap_bijective s)).symm

@[simp] theorem simplexVertexEquiv_symm (s : Finset V) (v : s) :
    (simplexVertexEquiv s).symm v = simplexAtomMap s v := rfl

theorem simplex_faceRank (s : Finset V) : faceRank s = s.card := by
  rw [← card_faceVertex]
  exact (Fintype.card_congr (simplexVertexEquiv s)).trans (Fintype.card_coe s)

def simplexTopVertexEquiv : FaceVertex (Finset.univ : Finset V) ≃ V :=
  (simplexVertexEquiv Finset.univ).trans {
    toFun := Subtype.val
    invFun := fun v => ⟨v, Finset.mem_univ v⟩
    left_inv := fun v => Subtype.ext rfl
    right_inv := fun v => rfl }

theorem simplexOrderAction_one : finsetOrderCongr (1 : Equiv.Perm V) = OrderIso.refl _ :=
  finsetOrderCongr_refl

theorem simplexOrderAction_mul (e f : Equiv.Perm V) :
    finsetOrderCongr (e * f) = (finsetOrderCongr f).trans (finsetOrderCongr e) :=
  finsetOrderCongr_trans f e

@[simp] theorem finsetOrderCongr_univ (e : Equiv.Perm V) :
    finsetOrderCongr e (Finset.univ : Finset V) = Finset.univ := by
  change Finset.univ.map e.toEmbedding = Finset.univ
  exact Finset.map_univ_equiv e

@[simp] theorem finsetOrderCongr_empty (e : Equiv.Perm V) :
    finsetOrderCongr e (∅ : Finset V) = ∅ := Finset.map_empty _

end Simplex

section Placements
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

def embeddingPlacementFace (i : A ↪ V) : Finset V := Finset.univ.map i

def embeddingPlacementEquiv (i : A ↪ V) : A ≃ embeddingPlacementFace i :=
  Equiv.ofBijective (fun a => ⟨i a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩)
    ⟨fun a b h => i.injective (congrArg Subtype.val h), by
      intro a
      obtain ⟨b, _, hb⟩ := Finset.mem_map.mp a.property
      exact ⟨b, Subtype.ext hb⟩⟩

def embeddingPlacementVertex (i : A ↪ V) : A ≃ FaceVertex (embeddingPlacementFace i) :=
  (embeddingPlacementEquiv i).trans (simplexVertexEquiv (embeddingPlacementFace i)).symm

@[simp] theorem embeddingPlacementVertex_val (i : A ↪ V) (a : A) :
    (embeddingPlacementVertex i a).val = {i a} := rfl

theorem finsetOrderCongr_symm (e : V ≃ V) :
    finsetOrderCongr e.symm = (finsetOrderCongr e).symm := rfl

end Placements
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSimplexGeometry.lean -/
section


section

/-! # The actual Boolean simplex and its prime-cycle action

Faces are literal finite subsets.  Their atoms are literal singleton subsets,
and the resulting simplicial-poset stalk vertices are identified with the
vertices of the subset.  Nonempty proper faces have trivial stabilizer under
a prime cycle.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable (p : ℕ) [Fact p.Prime]

def cyclicSimplexOrderAction (g : PrimeCycleGroup p) : Finset (ZMod p) ≃o Finset (ZMod p) :=
  finsetOrderCongr (cyclicVertexPermutation p g)

theorem cyclicSimplexOrderAction_one : cyclicSimplexOrderAction p 1 = OrderIso.refl _ := by
  rw [cyclicSimplexOrderAction, (cyclicVertexPermutation p).map_one]
  exact simplexOrderAction_one

theorem cyclicSimplexOrderAction_mul (g h : PrimeCycleGroup p) :
    cyclicSimplexOrderAction p (g * h) =
      (cyclicSimplexOrderAction p h).trans (cyclicSimplexOrderAction p g) := by
  rw [cyclicSimplexOrderAction, (cyclicVertexPermutation p).map_mul]
  exact simplexOrderAction_mul _ _

theorem cyclicSimplex_proper_face_free (s : Finset (ZMod p)) (hs : s.Nonempty)
    (ht : s ≠ Finset.univ) (g : PrimeCycleGroup p)
    (hfix : cyclicSimplexOrderAction p g s = s) : g = 1 := by
  by_contra hg
  have hg0 : g.toAdd ≠ 0 := by intro h; exact hg (congrArg Multiplicative.ofAdd h)
  have hmem : ∀ x : ZMod p, (g.toAdd + x ∈ s) = (x ∈ s) := by
    intro x
    have hh : s.map (Equiv.addLeft g.toAdd).toEmbedding = s := hfix
    have hm := congrArg (fun t : Finset (ZMod p) => (Equiv.addLeft g.toAdd) x ∈ t) hh
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hm
    exact hm.symm
  have hc := primeShift_invariant_constant p (fun x => x ∈ s) g.toAdd hg0 hmem
  obtain ⟨a, ha⟩ := hs
  apply ht
  apply Finset.eq_univ_iff_forall.mpr
  intro b
  rw [hc b, ← hc a]
  exact ha

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFreeFaceAssembly.lean -/
section


section

/-! # Integral coherent extension on free face orbits

Every nonempty proper face of a prime simplex has trivial stabilizer.  An
ordinary boundary extension on one representative therefore suffices on its
whole orbit.  This file packages that argument on the actual face diagrams;
only the stabilizer-fixed extension at the top face remains a separate input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P G : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [Group G]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

/-- Read a rank-stage value with its specified actions installed explicitly. -/
def actualRankStageValue (n : ℕ)
    (old :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
        (StalkLocalGood K) (StalkLocalCompatible K) n) :
    equivariantRankCut (fun p : P => faceRank p) n → StalkLinearFamily (P := P) K := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  exact old.value

include hs in
theorem exists_ordinary_rank_stalk_extension
    (n : ℕ)
    (old :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
        (StalkLocalGood K) (StalkLocalCompatible K) n)
    (p : P) (hp : faceRank p = n) (hp₀ : p ≠ ⊥) :
    ∃ y : StalkLinearFamily (P := P) K, StalkLocalGood K p y ∧
      ∀ q : rankCut faceRank n, q.val < p → StalkLocalCompatible K p q.val y (actualRankStageValue K act h₁ hmul n old q) := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  letI : LinearOrder (FaceVertex p) :=
    linearOrderWithDecidableEq (LinearOrder.lift' (Fintype.equivFin (FaceVertex p))
        (Fintype.equivFin (FaceVertex p)).injective) inferInstance
  have hcard : 0 < Fintype.card (FaceVertex p) := by
    rw [card_faceVertex]
    exact Finset.card_pos.mpr (faceVertices_nonempty hs hp₀)
  letI : Nonempty (FaceVertex p) := Fintype.card_pos_iff.mp hcard
  let e := old.stalkBoundary K hs (fun g q => faceRank_eq_of_orderIso (act g) q) p hp
  obtain ⟨f, hfp, hfn, hfg, hf₁⟩ := exists_linearCoherentLocalExtension K hs p e
    (old.stalkBoundary_parameter K hs _ p hp)
    (old.stalkBoundary_degree K hs _ p hp)
    (old.stalkBoundary_one K hs _ p hp)
  refine ⟨stalkFamilySingle K p f,
    stalkFamilySingle_good K p f (parameterLinear_intertwinesAllRanks f hfp) hfg hf₁, ?_⟩
  intro q hqp h x
  rw [stalkFamilySingle_same]
  exact hfn ⟨q.val, hqp⟩ x

variable [OrderTop P]

include hs in
theorem exists_coherent_family_of_prime_top_extension
    (hfree : ∀ (p : P), p ≠ ⊥ → p ≠ ⊤ → ∀ g : G, act g p = p → g = 1)
    (htop :
      letI := orderActionMulAction act h₁ hmul
      letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
      ∀ n (old : EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
          (StalkLocalGood K) (StalkLocalCompatible K) n), faceRank (⊤ : P) = n →
        ∃ y : StalkLinearFamily (P := P) K,
          StalkLocalGood K ⊤ y ∧
          (∀ q : rankCut faceRank n, q.val < ⊤ → StalkLocalCompatible K ⊤ q.val y (old.value q)) ∧
          ∀ g : G, stalkFamilyRelabel K (act g) y = y) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧
      F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧
      (∀ p, F p 1 = 1) ∧ ∀ g : G, stalkFamilyRelabel K (act g) F = F := by
  apply exists_equivariant_coherent_stalk_family K act h₁ hmul hs
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  intro n old p hp
  by_cases hp₀ : p = ⊥
  · subst p
    obtain ⟨y, hy⟩ := exists_stalkLocalGood_bot (P := P) K
    exact ⟨y, hy, fun q hq => False.elim (not_lt_bot hq),
      fun g _ => stalkLocalGood_bot_fixed K (act g) y hy⟩
  · by_cases hp₁ : p = ⊤
    · subst p
      obtain ⟨y, hy, hb, he⟩ := htop n old hp
      exact ⟨y, hy, hb, fun g _ => he g⟩
    · obtain ⟨y, hy, hb⟩ := exists_ordinary_rank_stalk_extension K hs act h₁ hmul n old p hp hp₀
      refine ⟨y, hy, hb, ?_⟩
      intro g hg
      rw [hfree p hp₀ hp₁ g hg, h₁, stalkFamilyRelabel_refl]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicVertexTransport.lean -/
section


section

/-! # Transport of actual local parameter maps along vertex bijections -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical Finset MvPolynomial
open scoped CyclicParameterAction

variable {V W U K : Type*} [Fintype V] [Fintype W] [Fintype U] [CommRing K]

def vertexMapTransport (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) :
    BooleanBarycentricRing W K →ₗ[K] MvPolynomial W K :=
  (MvPolynomial.rename e).toLinearMap.comp
    (f.comp (booleanVertexRelabelEquiv (K := K) e.symm).toLinearMap)

@[simp] theorem vertexMapTransport_apply (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (x : BooleanBarycentricRing W K) :
    vertexMapTransport e f x = MvPolynomial.rename e (f (booleanVertexRelabelEquiv e.symm x)) := rfl

theorem intertwinesAllRanks_parameterLinear [LinearOrder V]
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (hf : IntertwinesAllRanks f) :
    IsParameterLinear booleanColorMap polynomialColorMap f := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro c x
  rw [booleanColorMap, MvPolynomial.aeval_X, polynomialColorMap, MvPolynomial.aeval_X,
    ← booleanRankParameter_color]
  exact hf c.val x

theorem vertexMapTransport_parameters [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IntertwinesAllRanks f) : IntertwinesAllRanks (vertexMapTransport e f) := by
  intro r x
  erw [vertexMapTransport_apply, map_mul, booleanVertexRelabelEquiv_parameter,
    hf, map_mul, MvPolynomial.rename_esymm]
  rfl

theorem vertexMapTransport_degree (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (n : ℕ) (x : BooleanBarycentricRing W K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    vertexMapTransport e f x ∈ polynomialDegreePiece n :=
  polynomialRename_degree e n _ (hf n _ (booleanVertexRelabelEquiv_degree e.symm n x hx))

theorem vertexMapTransport_one (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) (hf : f 1 = 1) :
    vertexMapTransport e f 1 = 1 := by rw [vertexMapTransport_apply, map_one, hf, map_one]

theorem booleanVertexRelabelEquiv_symm_apply (e : V ≃ W) (x : BooleanBarycentricRing V K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv e x) = x :=
  (booleanVertexRelabelEquiv (K := K) e).symm_apply_apply x

theorem vertexMapTransport_symm (e : V ≃ W)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K) :
    vertexMapTransport e.symm (vertexMapTransport e f) = f := by
  apply LinearMap.ext
  intro x
  rw [vertexMapTransport_apply, vertexMapTransport_apply, Equiv.symm_symm,
    booleanVertexRelabelEquiv_symm_apply, MvPolynomial.rename_rename]
  have he : (e.symm : W → V) ∘ (e : V → W) = id := by
    funext v
    exact e.symm_apply_apply v
  rw [he, MvPolynomial.rename_id_apply]

theorem rename_fullPolynomialTop (e : V ≃ W) :
    MvPolynomial.rename e (∏ v : V, MvPolynomial.X v : MvPolynomial V K) =
      ∏ w : W, MvPolynomial.X w := by
  rw [map_prod]
  simp only [MvPolynomial.rename_X]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem polynomialBoundary_rename_equiv_congr (e : V ≃ W)
    (f g : MvPolynomial V K) (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialBooleanBoundaryMap (MvPolynomial.rename e f) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename e g) := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff _).mp hz
  have hz' : polynomialBooleanBoundaryMap (MvPolynomial.rename e (f - g)) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename e y, ?_⟩
    rw [← hy, map_mul, rename_fullPolynomialTop]
  rw [map_sub, map_sub] at hz'
  exact sub_eq_zero.mp hz'

theorem vertexMapTransport_boundary_congr (e : V ≃ W)
    (f g : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : ∀ x, polynomialBooleanBoundaryMap (f x) = polynomialBooleanBoundaryMap (g x)) :
    ∀ x, polynomialBooleanBoundaryMap (vertexMapTransport e f x) =
      polynomialBooleanBoundaryMap (vertexMapTransport e g x) := by
  intro x
  exact polynomialBoundary_rename_equiv_congr e _ _ (h _)

theorem booleanVertexRelabelEquiv_permutation (e : V ≃ W) (h : Equiv.Perm W)
    (x : BooleanBarycentricRing W K) :
    booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv h x) =
      booleanVertexRelabelEquiv (e.symm.permCongr h) (booleanVertexRelabelEquiv e.symm x) := by
  rw [← booleanVertexRelabelEquiv_trans, ← booleanVertexRelabelEquiv_trans]
  have he : h.trans e.symm = e.symm.trans (e.symm.permCongr h) := by
    apply Equiv.ext
    intro v
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact congrArg (fun q : W ≃ V => booleanVertexRelabelEquiv (K := K) q x) he

theorem polynomialRename_permutation (e : V ≃ W) (h : Equiv.Perm W) (f : MvPolynomial V K) :
    MvPolynomial.rename e (MvPolynomial.rename (e.symm.permCongr h) f) =
      MvPolynomial.rename h (MvPolynomial.rename e f) := by
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  apply congrArg (fun q : V → W => MvPolynomial.rename q f)
  funext v
  exact e.apply_symm_apply (h (e v))

theorem vertexMapTransport_boundary_permutation [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : Equiv.Perm W)
    (hf : ∀ x, polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv (e.symm.permCongr h) x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename (e.symm.permCongr h) (f x))) :
    ∀ x, polynomialBooleanBoundaryMap (vertexMapTransport e f (booleanPermutationAlgEquiv h x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename h (vertexMapTransport e f x)) := by
  intro x
  change polynomialBooleanBoundaryMap (MvPolynomial.rename e
      (f (booleanVertexRelabelEquiv e.symm (booleanVertexRelabelEquiv h x)))) = _
  rw [booleanVertexRelabelEquiv_permutation]
  have hh := polynomialBoundary_rename_equiv_congr e _ _ (hf (booleanVertexRelabelEquiv e.symm x))
  rw [polynomialRename_permutation] at hh
  exact hh

theorem vertexMapTransport_equivariant [LinearOrder V] [LinearOrder W]
    (e : V ≃ W) (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (h : Equiv.Perm W)
    (hf : ∀ x, f (booleanPermutationAlgEquiv (e.symm.permCongr h) x) =
      MvPolynomial.rename (e.symm.permCongr h) (f x)) :
    ∀ x, vertexMapTransport e f (booleanPermutationAlgEquiv h x) =
      MvPolynomial.rename h (vertexMapTransport e f x) := by
  intro x
  change MvPolynomial.rename e (f (booleanVertexRelabelEquiv e.symm
    (booleanVertexRelabelEquiv h x))) = _
  change ∀ x, f (booleanVertexRelabelEquiv (e.symm.permCongr h) x) =
    MvPolynomial.rename (e.symm.permCongr h) (f x) at hf
  rw [booleanVertexRelabelEquiv_permutation, hf, polynomialRename_permutation]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeVertexLift.lean -/
section


section

/-! # The integral prime lift on an arbitrary prime-sized vertex set -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem exists_integralPrime_vertex_lift (e : V ≃ ZMod p)
    (f : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ)
    (hfp : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hfd : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hf₁ : f 1 = 1)
    (hfb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv
        (e.symm.permCongr (Equiv.addLeft g.toAdd)) x)) =
      polynomialBooleanBoundaryMap (MvPolynomial.rename
        (e.symm.permCongr (Equiv.addLeft g.toAdd)) (f x))) :
    ∃ L : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ,
      IsParameterLinear booleanColorMap polynomialColorMap L ∧
      (∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => chainOrdinaryDegree a.val) n → L x ∈ polynomialDegreePiece n) ∧
      L 1 = 1 ∧
      (∀ x, polynomialBooleanBoundaryMap (L x) = polynomialBooleanBoundaryMap (f x)) ∧
      ∀ (g : PrimeCycleGroup p) x,
        L (booleanPermutationAlgEquiv (e.symm.permCongr (Equiv.addLeft g.toAdd)) x) =
          MvPolynomial.rename (e.symm.permCongr (Equiv.addLeft g.toAdd)) (L x) := by
  let fQ := vertexMapTransport e f
  have hQp : IsParameterLinear booleanColorMap polynomialColorMap fQ :=
    intertwinesAllRanks_parameterLinear fQ
      (vertexMapTransport_parameters e f (parameterLinear_intertwinesAllRanks f hfp))
  let fQA := parameterLinearMap fQ hQp
  have hQd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      fQA (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
    intro σ
    apply vertexMapTransport_degree e f hfd
    change descentVector σ ∈ basisOrdinaryDegreePiece
      (booleanChainBasis (V := ZMod p) (K := ℤ))
      (fun a => chainOrdinaryDegree a.val) (colorOrdinaryDegree (descentColorExponent σ))
    have hh := (booleanScalarGradedBasis (V := ZMod p) (K := ℤ)).generator_mem_piece σ
    rw [booleanScalarGradedBasis_piece_eq] at hh
    simpa only [booleanScalarGradedBasis, booleanColorBasis_apply,
      booleanOrdinaryDegree_eq_chainOrdinaryDegree] using hh
  have hQb : ∀ (g : PrimeCycleGroup p) x,
      polynomialBooleanBoundaryMap (fQA (cyclicBooleanParameterRepresentation p ℤ g x)) =
        polynomialBooleanBoundaryMap (cyclicPolynomialParameterRepresentation p ℤ g (fQA x)) := by
    intro g x
    exact vertexMapTransport_boundary_permutation e f (Equiv.addLeft g.toAdd) (hfb g) x
  obtain ⟨LQ, hLQe, hLQb, hLQd, hLQ₁⟩ := exists_integralPrimeCyclic_boundary_lift p fQA
    hQd hQb (vertexMapTransport_one e f hf₁)
  let L := vertexMapTransport e.symm (LQ.restrictScalars ℤ)
  have hLQp : IsParameterLinear booleanColorMap polynomialColorMap (LQ.restrictScalars ℤ) :=
    fun a x => LQ.map_smul a x
  refine ⟨L, ?_, ?_, vertexMapTransport_one e.symm (LQ.restrictScalars ℤ) hLQ₁, ?_, ?_⟩
  · exact intertwinesAllRanks_parameterLinear L
      (vertexMapTransport_parameters e.symm (LQ.restrictScalars ℤ)
        (parameterLinear_intertwinesAllRanks _ hLQp))
  · intro n x hx
    apply vertexMapTransport_degree e.symm (LQ.restrictScalars ℤ) _ n x hx
    intro m y hy
    apply hLQd m y
    rwa [booleanScalarGradedBasis_piece_eq]
  · intro x
    have hh := vertexMapTransport_boundary_congr e.symm (LQ.restrictScalars ℤ) fQ hLQb x
    rw [vertexMapTransport_symm] at hh
    exact hh
  · intro g x
    let h : Equiv.Perm (ZMod p) := Equiv.addLeft g.toAdd
    have he : e.permCongr (e.symm.permCongr h) = h := e.permCongr.apply_symm_apply h
    apply vertexMapTransport_equivariant e.symm (LQ.restrictScalars ℤ)
      (e.symm.permCongr h) _ x
    intro y
    rw [Equiv.symm_symm, he]
    exact hLQe g y

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedStalk.lean -/
section


section

/-! # Fixed-face actions and the literal prime-cycle action at the top stalk

Equality transports of face indices are made explicit and proved to act by
the corresponding vertex bijection.  This connects the action on whole
families with the polynomial and Boolean permutation actions in the local
prime lift.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial

/-- An additive map is linear for the specified integer-module structures.
The explicit conversion prevents a diamond between quotient and canonical
integer actions at an integral stalk. -/
def integralLinearMapOfAddHom {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    convert f.map_zsmul c x using 1
    · exact congrArg f (int_smul_eq_zsmul _ c x)
    · exact int_smul_eq_zsmul _ c (f x)


variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

def faceVertexCast {p q : P} (h : p = q) : FaceVertex p ≃ FaceVertex q :=
  Equiv.cast (congrArg FaceVertex h)

@[simp] theorem faceVertexCast_val {p q : P} (h : p = q) (a : FaceVertex p) :
    (faceVertexCast h a).val = a.val := by cases h; rfl

def polynomialStalkCast {p q : P} (h : p = q) : PolynomialStalk K p ≃ₐ[K] PolynomialStalk K q :=
  MvPolynomial.renameEquiv K (faceVertexCast h)

def barycentricStalkCast {p q : P} (h : p = q) : BarycentricStalk K p ≃ₐ[K] BarycentricStalk K q :=
  booleanVertexRelabelEquiv (faceVertexCast h)

@[simp] theorem polynomialStalkCast_refl (p : P) (x : PolynomialStalk K p) :
    polynomialStalkCast K (rfl : p = p) x = x := by
  change MvPolynomial.rename (id : FaceVertex p → FaceVertex p) x = x
  exact MvPolynomial.rename_id_apply x

@[simp] theorem barycentricStalkCast_refl (p : P) (x : BarycentricStalk K p) :
    barycentricStalkCast K (rfl : p = p) x = x :=
  booleanVertexRelabelEquiv_refl x

theorem stalkFamily_cast (F : StalkLinearFamily (P := P) K) {p q : P} (h : p = q)
    (x : BarycentricStalk K p) :
    polynomialStalkCast K h (F p x) = F q (barycentricStalkCast K h x) := by
  cases h
  rw [polynomialStalkCast_refl, barycentricStalkCast_refl]

def fixedFaceVertexPermutation (e : P ≃o P) (p : P) (h : e p = p) : Equiv.Perm (FaceVertex p) :=
  (faceVertexOrderEquiv e p).trans (faceVertexCast h)

@[simp] theorem fixedFaceVertexPermutation_val (e : P ≃o P) (p : P) (h : e p = p)
    (a : FaceVertex p) : (fixedFaceVertexPermutation e p h a).val = e a.val := by
  rw [fixedFaceVertexPermutation, Equiv.trans_apply, faceVertexCast_val]
  rfl

theorem fixedFaceVertexPermutation_polynomial (e : P ≃o P) (p : P) (h : e p = p)
    (x : PolynomialStalk K p) :
    MvPolynomial.rename (fixedFaceVertexPermutation e p h) x =
      polynomialStalkCast K h (polynomialStalkOrderEquiv K e p x) := by
  change MvPolynomial.rename ((faceVertexOrderEquiv e p).trans (faceVertexCast h)) x =
    MvPolynomial.rename (faceVertexCast h) (MvPolynomial.rename (faceVertexOrderEquiv e p) x)
  rw [MvPolynomial.rename_rename]
  rfl

theorem fixedFaceVertexPermutation_barycentric (e : P ≃o P) (p : P) (h : e p = p)
    (x : BarycentricStalk K p) :
    booleanVertexRelabelEquiv (fixedFaceVertexPermutation e p h) x =
      barycentricStalkCast K h (barycentricStalkOrderEquiv K e p x) :=
  booleanVertexRelabelEquiv_trans (faceVertexOrderEquiv e p) (faceVertexCast h) x

theorem stalkFamilyRelabel_fixed_conjugate (e : P ≃o P) (p : P) (h : e.symm p = p)
    (F : StalkLinearFamily (P := P) K) (x : BarycentricStalk K p) :
    MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h)
      (stalkFamilyRelabel K e F p x) =
        F p (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) := by
  rw [fixedFaceVertexPermutation_polynomial, stalkFamilyRelabel_apply,
    AlgEquiv.apply_symm_apply, stalkFamily_cast,
    ← fixedFaceVertexPermutation_barycentric]

theorem stalkFamilyRelabel_fixed_at (e : P ≃o P) (p : P) (h : e.symm p = p)
    (F : StalkLinearFamily (P := P) K)
    (hF : ∀ x, F p (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) =
      MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (F p x)) :
    ∀ x, stalkFamilyRelabel K e F p x = F p x := by
  intro x
  apply (MvPolynomial.renameEquiv K (fixedFaceVertexPermutation e.symm p h)).injective
  change MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h)
      (stalkFamilyRelabel K e F p x) =
    MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (F p x)
  rw [stalkFamilyRelabel_fixed_conjugate, hF]

theorem stalkFamilyRelabel_fixed_single (e : P ≃o P) (p : P) (h : e.symm p = p)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : ∀ x, f (booleanVertexRelabelEquiv (fixedFaceVertexPermutation e.symm p h) x) =
      MvPolynomial.rename (fixedFaceVertexPermutation e.symm p h) (f x)) :
    stalkFamilyRelabel K e (stalkFamilySingle K p f) = stalkFamilySingle K p f := by
  funext q
  apply LinearMap.ext
  intro x
  by_cases hq : q = p
  · subst q
    apply stalkFamilyRelabel_fixed_at K e p h
    intro y
    simpa only [stalkFamilySingle_same] using hf y
  · have hq' : e.symm q ≠ p := by
      intro he
      exact hq (e.symm.injective (he.trans h.symm))
    rw [stalkFamilyRelabel_apply, stalkFamilySingle_ne K p q hq,
      stalkFamilySingle_ne K p (e.symm q) hq']
    simp

section Simplex
variable {V : Type*} [Fintype V]

@[simp] theorem simplexTopVertexEquiv_symm_val (v : V) :
    ((simplexTopVertexEquiv (V := V)).symm v).val = {v} := rfl

theorem simplexTopVertexEquiv_val (a : FaceVertex (Finset.univ : Finset V)) :
    a.val = {simplexTopVertexEquiv a} := by
  have hh := congrArg Subtype.val ((simplexTopVertexEquiv (V := V)).symm_apply_apply a)
  exact hh.symm

theorem simplex_fixed_top_permutation (e : Equiv.Perm V)
    (h : finsetOrderCongr e (Finset.univ : Finset V) = Finset.univ) :
    fixedFaceVertexPermutation (finsetOrderCongr e) Finset.univ h =
      (simplexTopVertexEquiv (V := V)).symm.permCongr e := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [fixedFaceVertexPermutation_val, simplexTopVertexEquiv_val a,
    finsetOrderCongr_apply, Finset.map_singleton]
  change {e (simplexTopVertexEquiv a)} =
    ((simplexTopVertexEquiv (V := V)).symm (e (simplexTopVertexEquiv a))).val
  rw [simplexTopVertexEquiv_symm_val]

theorem simplex_top_single_fixed (e : Equiv.Perm V)
    (f : BarycentricStalk K (Finset.univ : Finset V) →ₗ[K]
      PolynomialStalk K (Finset.univ : Finset V))
    (hf : ∀ x, f (booleanVertexRelabelEquiv
      ((simplexTopVertexEquiv (V := V)).symm.permCongr e.symm) x) =
        MvPolynomial.rename ((simplexTopVertexEquiv (V := V)).symm.permCongr e.symm) (f x)) :
    stalkFamilyRelabel K (finsetOrderCongr e) (stalkFamilySingle K Finset.univ f) =
      stalkFamilySingle K Finset.univ f := by
  have hsymm : (finsetOrderCongr e).symm = finsetOrderCongr e.symm := rfl
  apply stalkFamilyRelabel_fixed_single K (finsetOrderCongr e) Finset.univ
    (by rw [hsymm, finsetOrderCongr_univ]) f
  intro x
  change f (booleanVertexRelabelEquiv
      (fixedFaceVertexPermutation (finsetOrderCongr e.symm) Finset.univ (finsetOrderCongr_univ e.symm)) x) =
    MvPolynomial.rename
      (fixedFaceVertexPermutation (finsetOrderCongr e.symm) Finset.univ (finsetOrderCongr_univ e.symm)) (f x)
  rw [simplex_fixed_top_permutation]
  exact hf x

end Simplex
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/SupportCarrier.lean -/
section

section

/-! # The unique supporting face of a polynomial monomial inside a Boolean interval -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The vertices occurring with positive exponent. -/
def exponentVertices {p : P} (a : FaceVertex p →₀ ℕ) : Finset P :=
  a.support.image Subtype.val

theorem exponentVertices_subset {p : P} (a : FaceVertex p →₀ ℕ) :
    exponentVertices a ⊆ faceVertices p := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  exact mem_faceVertices.mpr w.property

/-- The carrier is chosen inside the fixed Boolean interval; distinct global
faces with identical vertices are never identified. -/
def exponentCarrier (hs : IsSimplicialPoset P) {p : P} (a : FaceVertex p →₀ ℕ) : P :=
  ((existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose).val

theorem exponentCarrier_le (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a ≤ p :=
  ((existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose).property

@[simp] theorem exponentCarrier_vertices (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : faceVertices (exponentCarrier hs a) = exponentVertices a :=
  (existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose_spec.1

theorem exponentCarrier_le_iff (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ) :
    exponentCarrier hs a ≤ q ↔ ∀ v ∈ a.support, v.val ≤ q := by
  rw [← faceVertices_subset_iff hs (exponentCarrier_le hs a) hqp,
    exponentCarrier_vertices]
  constructor
  · intro h v hv
    exact (mem_faceVertices.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))).2
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact mem_faceVertices.mpr ⟨w.property.1, h w hw⟩

theorem exponentCarrier_eq_top_iff (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a = p ↔ a.support = univ := by
  constructor
  · intro h
    have hv : exponentVertices a = faceVertices p := by rw [← exponentCarrier_vertices hs a, h]
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    have hm : v.val ∈ exponentVertices a := hv ▸ mem_faceVertices.mpr v.property
    obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hm
    have he : w = v := Subtype.ext hEq
    exact he ▸ hw
  · intro h
    apply faceVertices_injective_below hs (exponentCarrier_le hs a) le_rfl
    rw [exponentCarrier_vertices]
    ext v
    simp only [exponentVertices, h, Finset.mem_image, mem_univ, true_and, mem_faceVertices]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩

theorem exponentCarrier_lt_iff (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a < p ↔ a.support ≠ univ := by
  rw [lt_iff_le_and_ne]
  simp only [exponentCarrier_le, true_and]
  exact not_congr (exponentCarrier_eq_top_iff hs a)

/-- Pull an exponent vector back along a genuine face inclusion. -/
def restrictExponent {p q : P} (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ) :
    FaceVertex q →₀ ℕ :=
  Finsupp.comapDomain (faceVertexInclusion hqp) a (faceVertexInclusion hqp).injective.injOn

@[simp] theorem restrictExponent_apply {p q : P} (hqp : q ≤ p)
    (a : FaceVertex p →₀ ℕ) (v : FaceVertex q) :
    restrictExponent hqp a v = a (faceVertexInclusion hqp v) := rfl

theorem extend_restrictExponent {p q : P} (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ)
    (ha : ∀ v ∈ a.support, v.val ≤ q) :
    (restrictExponent hqp a).mapDomain (faceVertexInclusion hqp) = a := by
  apply Finsupp.mapDomain_comapDomain _ (faceVertexInclusion hqp).injective a
  intro v hv
  refine ⟨⟨v.val, v.property.1, ha v hv⟩, ?_⟩
  exact Subtype.ext rfl

theorem extend_restrictExponent_carrier (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) :
    (restrictExponent (exponentCarrier_le hs a) a).mapDomain
      (faceVertexInclusion (exponentCarrier_le hs a)) = a := by
  apply extend_restrictExponent
  exact (exponentCarrier_le_iff hs (exponentCarrier_le hs a) a).mp le_rfl

theorem exponentCarrier_extend_le (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex q →₀ ℕ) :
    exponentCarrier hs (a.mapDomain (faceVertexInclusion hqp)) ≤ q := by
  apply (exponentCarrier_le_iff hs hqp _).mpr
  intro v hv
  have hsupp := Finsupp.mapDomain_support (f := faceVertexInclusion hqp) (s := a)
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hsupp hv)
  exact w.property.2

/-- Pullback after extension is compatible with nested actual face inclusions. -/
theorem restrictExponent_extend_of_le {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q)
    (a : FaceVertex q →₀ ℕ) :
    restrictExponent (hrq.trans hqp) (a.mapDomain (faceVertexInclusion hqp)) =
      restrictExponent hrq a := by
  ext v
  change (a.mapDomain (faceVertexInclusion hqp))
      (faceVertexInclusion hqp (faceVertexInclusion hrq v)) =
    a (faceVertexInclusion hrq v)
  exact Finsupp.mapDomain_apply_of_injective (faceVertexInclusion hqp).injective a _

theorem support_le_exponentCarrier_extend (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex q →₀ ℕ) :
    ∀ v ∈ a.support, v.val ≤ exponentCarrier hs (a.mapDomain (faceVertexInclusion hqp)) := by
  intro v hv
  let b := a.mapDomain (faceVertexInclusion hqp)
  have hbv : faceVertexInclusion hqp v ∈ b.support := by
    rw [Finsupp.mem_support_iff]
    simpa only [b, Finsupp.mapDomain_apply_of_injective (faceVertexInclusion hqp).injective]
      using Finsupp.mem_support_iff.mp hv
  exact (exponentCarrier_le_iff hs (exponentCarrier_le hs b) b).mp le_rfl
    (faceVertexInclusion hqp v) hbv

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkBoundary.lean -/
section

section
/-! # The actual proper-face boundary and graded lifting

These maps are restriction to the inverse limit of all proper faces.  Their
kernels are exactly multiplication by the top rank parameter.  The Boolean
boundary has an explicit graded section, obtained in the already established
standard monomial coordinates.  Thus the positive-degree lifting argument
applies directly to coherent maps of actual stalk diagrams.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

include hs in
theorem polynomialStalkBoundary_eq_zero_iff (p : P) (f : PolynomialStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p f = 0 ↔
      ∃ g : PolynomialStalk K p, polynomialTop K p * g = f := by
  constructor
  · intro hf
    have hm : f ∈ Ideal.span {∏ v : FaceVertex p, (X v : PolynomialStalk K p)} := by
      apply (mem_full_product_ideal_iff (FaceVertex p) K f).mpr
      intro a ha
      have hq : exponentCarrier hs a < p := (exponentCarrier_lt_iff hs a).mpr ha
      have hres := congrArg (fun x => x.val ⟨exponentCarrier hs a, hq⟩) hf
      change polynomialRestriction K hq.le f = 0 at hres
      have hc := congrArg (fun z : PolynomialStalk K (exponentCarrier hs a) =>
        z.coeff (restrictExponent (exponentCarrier_le hs a) a)) hres
      rw [polynomialRestriction_eq_killCompl, MvPolynomial.coeff_killCompl,
        extend_restrictExponent_carrier hs a, MvPolynomial.coeff_zero] at hc
      exact hc
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hm
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    funext q
    change polynomialRestriction K q.property.le (polynomialTop K p * g) = 0
    rw [map_mul, polynomialRestriction_top K hs q.property, zero_mul]

theorem booleanChainCarrier_lt_of_top_zero (p : P) [Nonempty (FaceVertex p)]
    (a : BooleanChainExponent (FaceVertex p)) (ha : a.val booleanTopFace = 0) :
    standardCarrier ((standardInsideEquiv hs p) a).val < p := by
  let b := ((standardInsideEquiv hs p) a).val
  have hproper : ∀ F ∈ b.val.support, faceRank F.val < faceRank p := by
    intro F hF
    change F ∈ (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).support at hF
    rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    have hGt : G.val ≠ Finset.univ := by
      intro h
      have he : G = booleanTopFace := Subtype.ext h
      subst G
      exact Finsupp.mem_support_iff.mp hG ha
    rw [faceRank_booleanFaceInclusion, ← card_faceVertex p]
    simpa only [Finset.card_univ] using
      Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hGt)
  have hr : faceRank (standardCarrier b) < faceRank p := by
    rcases standardCarrier_mem_or_bot b with h | ⟨F, hF, he⟩
    · rw [h, faceRank_bot, ← card_faceVertex p]
      exact Fintype.card_pos
    · rw [he]
      exact hproper F hF
  apply lt_of_le_of_ne ((standardInsideEquiv hs p) a).property
  intro he
  exact (ne_of_lt hr) (congrArg faceRank he)

theorem barycentricStalkBoundary_coefficient_zero (p : P) (x : BarycentricStalk K p)
    (hx : stalkBoundaryRestriction (barycentricDiagram K) p x = 0)
    (a : StandardFaceIndex P) (ha : standardCarrier a < p) :
    (barycentricStandardCoordinates K hs p x).val a = 0 := by
  have hres := congrArg (fun z => z.val ⟨standardCarrier a, ha⟩) hx
  change booleanRestriction (K := K) (faceVertexInclusion ha.le) x = 0 at hres
  have hc := congrArg (fun z => z.val a)
    (barycentricStandardCoordinates_naturality K hs ha.le x)
  rw [coefficientRestriction_apply, if_pos le_rfl, hres, map_zero] at hc
  exact hc

include hs in
theorem barycentricStalkBoundary_eq_zero_iff (p : P) [Nonempty (FaceVertex p)]
    (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (barycentricDiagram K) p x = 0 ↔
      ∃ y : BarycentricStalk K p, booleanTop * y = x := by
  constructor
  · intro hx
    apply (booleanBoundaryMap_eq_zero_iff x).mp
    apply (standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr.injective
    ext a
    rw [map_zero, Finsupp.zero_apply]
    change ((standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr (coordinateBoundaryMap IsChainExponent booleanTopFace x)) a = 0
    rw [coordinateBoundaryMap_coefficient]
    let c : BooleanChainExponent (FaceVertex p) := ⟨a.val, a.property.1⟩
    let b := (standardInsideEquiv hs p) c
    have hb : standardCarrier b.val < p :=
      booleanChainCarrier_lt_of_top_zero hs p c a.property.2
    have hz := barycentricStalkBoundary_coefficient_zero K hs p x hx b.val hb
    rw [barycentricStandardCoordinates_apply_of_inside K hs p x b.val b.property] at hz
    have hid : (standardInsideEquiv hs p).symm ⟨b.val, b.property⟩ = c :=
      (standardInsideEquiv hs p).symm_apply_apply c
    rw [hid] at hz
    simpa only [booleanChainBasis, c] using hz
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    funext q
    have hn : ¬ Function.Surjective (faceVertexInclusion q.property.le) := by
      intro hsurj
      have hc := Fintype.card_le_of_surjective _ hsurj
      rw [card_faceVertex, card_faceVertex] at hc
      exact (not_le_of_gt (faceRank_strictMono hs q.property)) hc
    change booleanRestriction (K := K) (faceVertexInclusion q.property.le)
      (booleanTop * y) = 0
    rw [map_mul, booleanRestriction_top _ hn, zero_mul]

def barycentricCarrierBoundaryExtension (p : P) :
    ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections →ₗ[K]
      BarycentricStalk K p :=
  (barycentricStandardCoordinates K hs p).symm.toLinearMap.comp
    ((coefficientBoundaryExtension standardCarrier p).comp
      (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv.toLinearMap))

theorem barycentricCarrierBoundaryExtension_restrict (p : P)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections) :
    stalkBoundaryRestriction (barycentricDiagram K) p
      (barycentricCarrierBoundaryExtension K hs p x) = x := by
  apply (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv).injective
  rw [stalkBoundaryRestriction_naturality]
  change stalkBoundaryRestriction (coefficientDiagram K standardCarrier) p
    (barycentricStandardCoordinates K hs p
      ((barycentricStandardCoordinates K hs p).symm
        (coefficientBoundaryExtension standardCarrier p
          (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv x)))) = _
  rw [LinearEquiv.apply_symm_apply, coefficientBoundaryExtension_restrict]

theorem barycentricCarrierBoundaryExtension_coefficient (p : P)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections)
    (a : StandardFaceIndex P) :
    (barycentricStandardCoordinates K hs p (barycentricCarrierBoundaryExtension K hs p x)).val a =
      if ha : standardCarrier a < p then
        (barycentricStandardCoordinates K hs (standardCarrier a)
          (x.val ⟨standardCarrier a, ha⟩)).val a else 0 := by
  unfold barycentricCarrierBoundaryExtension
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coefficientBoundaryExtension_apply]
  rfl

theorem standardOrdinaryDegree_inside_orderFree (p : P)
    (a : BooleanChainExponent (FaceVertex p)) :
    standardOrdinaryDegree ((standardInsideEquiv hs p) a).val = booleanOrdinaryDegree a.val := by
  change (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).sum
    (fun F n => n * faceRank F.val) = _
  rw [Finsupp.sum_mapDomain_index (fun F => by simp) (fun F i j => by simp only [add_mul])]
  simp only [faceRank_booleanFaceInclusion, booleanOrdinaryDegree]

theorem barycentricCarrierBoundaryExtension_graded (p : P) (n : ℕ)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections)
    (hx : ∀ q : Set.Iio p, x.val q ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    barycentricCarrierBoundaryExtension K hs p x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  let b := (standardInsideEquiv hs p) a
  have hc := barycentricStandardCoordinates_apply_of_inside K hs p
    (barycentricCarrierBoundaryExtension K hs p x) b.val b.property
  have hid : (standardInsideEquiv hs p).symm ⟨b.val, b.property⟩ = a :=
    (standardInsideEquiv hs p).symm_apply_apply a
  rw [hid] at hc
  rw [← hc, barycentricCarrierBoundaryExtension_coefficient]
  split_ifs with hb
  · rw [barycentricStandardCoordinates_apply_of_inside K hs (standardCarrier b.val)
      (x.val ⟨standardCarrier b.val, hb⟩) b.val le_rfl]
    apply hx ⟨standardCarrier b.val, hb⟩
    have he := standardOrdinaryDegree_inside_orderFree hs (standardCarrier b.val)
      ((standardInsideEquiv hs (standardCarrier b.val)).symm ⟨b.val, le_rfl⟩)
    rw [Equiv.apply_symm_apply] at he
    intro hdeg
    exact ha ((standardOrdinaryDegree_inside_orderFree hs p a).symm.trans
      (he.trans hdeg))
  · rfl

theorem polynomialRestriction_degree {p q : P} (hqp : q ≤ p) (n : ℕ)
    (f : PolynomialStalk K p) (hf : f ∈ polynomialDegreePiece n) :
    polynomialRestriction K hqp f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [polynomialRestriction_eq_killCompl, MvPolynomial.coeff_killCompl]
  apply hf
  rwa [vertexDegree_mapDomain]

theorem stalkLinearEquiv_symm_graded (p : P)
    (e : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p)
    (he : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e x ∈ polynomialDegreePiece n)
    (n : ℕ) (y : PolynomialStalk K p) (hy : y ∈ polynomialDegreePiece n) :
    e.symm y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  apply (basisDegreeProjection_eq_self_iff_mem booleanChainBasis
    (fun a => booleanOrdinaryDegree a.val) n (e.symm y)).mp
  apply e.injective
  have hg : ∀ m x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) m →
      e x ∈ basisOrdinaryDegreePiece (MvPolynomial.basisMonomials (FaceVertex p) K)
        (fun a => vertexDegree (fun v => a v)) m := by
    intro m x hx
    exact he m x hx
  have hproj := ordinaryProjection_natural booleanChainBasis
    (MvPolynomial.basisMonomials (FaceVertex p) K) (fun a => booleanOrdinaryDegree a.val)
    (fun a => vertexDegree (fun v => a v)) e.toLinearMap hg n (e.symm y)
  have hh : e (e.symm y) ∈ basisOrdinaryDegreePiece
      (MvPolynomial.basisMonomials (FaceVertex p) K)
      (fun a => vertexDegree (fun v => a v)) n := by
    intro a ha
    change (e (e.symm y)).coeff a = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hy a ha
  simpa only [LinearEquiv.coe_coe] using hproj.symm.trans
    ((basisDegreeProjection_eq_self_iff_mem _ _ _ _).mpr hh)

/-- Top multiplication in the actual stalk coordinates, with no auxiliary
vertex order in the statement or in its equality instances. -/
theorem barycentricTop_shift_coefficient (p : P) [Nonempty (FaceVertex p)]
    (x : BarycentricStalk K p) (a : BooleanChainExponent (FaceVertex p)) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem barycentricTop_degree_shift (p : P) [Nonempty (FaceVertex p)]
    (a : BooleanFace (FaceVertex p) →₀ ℕ) :
    booleanOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      booleanOrdinaryDegree a + Fintype.card (FaceVertex p) := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])]
  simp [booleanTopFace]

theorem barycentricTop_predecessor_degree (p : P) [Nonempty (FaceVertex p)]
    (m : ℕ) (x : BarycentricStalk K p)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (m + Fintype.card (FaceVertex p))) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ m + Fintype.card (FaceVertex p) := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [barycentricTop_degree_shift]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  rwa [barycentricTop_shift_coefficient] at hh

theorem barycentricTop_homogeneous_zero_below (p : P) [Nonempty (FaceVertex p)]
    (n : ℕ) (hn : n < Fintype.card (FaceVertex p)) (x : BarycentricStalk K p)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ n := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [barycentricTop_degree_shift]
    omega
  have hh := hx b hb
  rw [barycentricTop_shift_coefficient] at hh
  exact hh

include hs in
/-- The actual coherent local lifting theorem.  The boundary comparison is
the isomorphism of proper-face inverse limits induced by the already
constructed lower-face isomorphisms.  Grading of their inverses is derived
from their forward grading, and no full-stalk comparison is presupposed. -/
theorem coherentStalkLift_bijective (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e.component q x ∈ polynomialDegreePiece n)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hres : ∀ (q : Set.Iio p) x, polynomialRestriction K q.property.le (f x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x)) :
    Function.Bijective f := by
  apply gradedBoundaryLift_bijective booleanChainBasis
    (MvPolynomial.basisMonomials (FaceVertex p) K)
    (fun a => booleanOrdinaryDegree a.val) (fun a => vertexDegree (fun v => a v))
    (Q := ↥(((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections))
    (R := ↥(((polynomialDiagram (P := P) K).restrict (Set.Iio p)).sections))
    (stalkBoundaryRestriction (barycentricDiagram K) p)
    (stalkBoundaryRestriction (polynomialDiagram K) p) e.sectionEquiv
    (LinearMap.mulLeft K booleanTop) (LinearMap.mulLeft K (polynomialTop K p))
    (Fintype.card (FaceVertex p)) (Fintype.card_pos_iff.mpr inferInstance)
    (polynomialTop_mul_injective K p)
    (fun x hx => (barycentricStalkBoundary_eq_zero_iff K hs p x).mp hx)
    (fun y hy => (polynomialStalkBoundary_eq_zero_iff K hs p y).mp hy)
    (fun n a hn ha => barycentricTop_predecessor_degree K p (n - Fintype.card (FaceVertex p)) a
      (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply,
        polynomialTop] using ha))
    (fun n a hn ha => by
      rw [← polynomialOrdinaryPiece_eq_basis] at ha ⊢
      exact fullPolynomialTop_predecessor_degree (n - Fintype.card (FaceVertex p)) a
        (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply,
        polynomialTop, booleanOrdinaryDegree, chainOrdinaryDegree] using ha))
    (fun n a hn ha => barycentricTop_homogeneous_zero_below K p n hn a
      (by simpa only [LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => fullPolynomialTop_zero_below n hn a
      (by simpa only [LinearMap.mulLeft_apply, polynomialTop, ← polynomialOrdinaryPiece_eq_basis] using ha))
    ?_ f ?_ (parameterLinear_top f hf) ?_
  · intro n y hy
    have hy' : y ∈ polynomialDegreePiece n := by
      rwa [← polynomialOrdinaryPiece_eq_basis] at hy
    let z := e.sectionEquiv.symm (stalkBoundaryRestriction (polynomialDiagram K) p y)
    refine ⟨barycentricCarrierBoundaryExtension K hs p z, ?_, ?_⟩
    · apply barycentricCarrierBoundaryExtension_graded
      intro q
      exact stalkLinearEquiv_symm_graded K q.val (e.component q) (he q) n
        (polynomialRestriction K q.property.le y)
        (polynomialRestriction_degree K q.property.le n y hy')
    · rw [barycentricCarrierBoundaryExtension_restrict]
      exact (e.sectionEquiv.apply_symm_apply _).symm
  · intro n x hx
    rw [← polynomialOrdinaryPiece_eq_basis]
    exact hgrade n x hx
  · intro x
    apply Subtype.ext
    funext q
    exact hres q x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicRankSum.lean -/
section


section

/-! # Completing the equivariant proper-face family at the top

The sum of the previously chosen single-face families is equivariant by
reindexing a finite orbit sum.  Adding an ordinary top extension produces an
actual coherent family.  Its conjugation error is consequently supported at
the top and has zero genuine boundary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped BigOperators

variable {P G : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [Group G]
variable (K : Type*) [CommRing K]
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))


abbrev ActualStalkRankStage (n : ℕ) :=
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  EquivariantRankStage faceRank (fun g p => faceRank_eq_of_orderIso (act g) p)
    (StalkLocalGood K) (StalkLocalCompatible K) n

def rankStalkSum (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) :
    StalkLinearFamily (P := P) K := ∑ q, (actualRankStageValue K act h₁ hmul n old) q

theorem rankStalkSum_inside (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (p : P) (hp : faceRank p < n) : rankStalkSum K act h₁ hmul n old p = (actualRankStageValue K act h₁ hmul n old) ⟨p, hp⟩ p := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change (∑ q, (actualRankStageValue K act h₁ hmul n old) q) p = _
  rw [Finset.sum_apply]
  change (∑ q : equivariantRankCut (fun p : P => faceRank p) n, old.value q p) =
    old.value ⟨p, hp⟩ p
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_single (s := Finset.univ)
    (f := fun q : equivariantRankCut (fun p : P => faceRank p) n => old.value q p x)
    ⟨p, hp⟩ ?_ ?_
  · intro q hq hne
    rw [(old.good q).1 p (fun he => hne (Subtype.ext he.symm))]
    rfl
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem rankStalkSum_outside (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (p : P) (hp : ¬ faceRank p < n) : rankStalkSum K act h₁ hmul n old p = 0 := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change (∑ q, (actualRankStageValue K act h₁ hmul n old) q) p = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  apply (old.good q).1 p
  intro he
  apply hp
  exact he ▸ q.property

theorem rankStalkSum_fixed (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (g : G) :
    stalkFamilyRelabel K (act g) (rankStalkSum K act h₁ hmul n old) =
      rankStalkSum K act h₁ hmul n old := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  letI := equivariantRankCutMulAction faceRank (fun g p => faceRank_eq_of_orderIso (act g) p) n
  rw [rankStalkSum, map_sum]
  calc
    ∑ q, stalkFamilyRelabel K (act g) ((actualRankStageValue K act h₁ hmul n old) q) = ∑ q, (actualRankStageValue K act h₁ hmul n old) (g • q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (old.equivariant g q).symm
    _ = ∑ q, (actualRankStageValue K act h₁ hmul n old) q := Equiv.sum_comp (MulAction.toPerm g) (actualRankStageValue K act h₁ hmul n old)

variable [OrderTop P]

def completeTopFamily (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P)) : StalkLinearFamily (P := P) K :=
  rankStalkSum K act h₁ hmul n old + stalkFamilySingle K ⊤ f

theorem completeTopFamily_top (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n)
    (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P)) :
    completeTopFamily K act h₁ hmul n old f ⊤ = f := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change rankStalkSum K act h₁ hmul n old ⊤ + stalkFamilySingle K ⊤ f ⊤ = f
  rw [rankStalkSum_outside K act h₁ hmul n old ⊤ (by rw [hn]; exact Nat.lt_irrefl n),
    stalkFamilySingle_same, zero_add]

theorem completeTopFamily_below (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (q : P) (hq : q < ⊤) :
    completeTopFamily K act h₁ hmul n old f q =
      (actualRankStageValue K act h₁ hmul n old) ⟨q, by rw [← hn]; exact faceRank_strictMono hs hq⟩ q := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  change rankStalkSum K act h₁ hmul n old q + stalkFamilySingle K ⊤ f q = _
  rw [rankStalkSum_inside K act h₁ hmul n old q (by rw [← hn]; exact faceRank_strictMono hs hq),
    stalkFamilySingle_ne K ⊤ q hq.ne f, add_zero]

theorem completeTopFamily_coherent (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (hf : ∀ (q : equivariantRankCut faceRank n), q.val < ⊤ →
      StalkLocalCompatible K ⊤ q.val (stalkFamilySingle K ⊤ f) ((actualRankStageValue K act h₁ hmul n old) q)) :
    completeTopFamily K act h₁ hmul n old f ∈ coherentStalkFamilySubmodule K := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  intro p q h x
  by_cases hqp : q = p
  · subst q
    simpa only [polynomialRestriction_refl, faceVertexInclusion_refl,
        booleanRestriction_refl, AlgHom.id_apply, AlgHom.toLinearMap_apply]
  · have hqp' : q < p := lt_of_le_of_ne h hqp
    have hq : q < ⊤ := hqp'.trans_le le_top
    rw [completeTopFamily_below K act h₁ hmul hs n old hn f q hq]
    by_cases hp : p = ⊤
    · subst p
      rw [completeTopFamily_top K act h₁ hmul n old hn f]
      simpa only [stalkFamilySingle_same] using
        hf ⟨q, by rw [← hn]; exact faceRank_strictMono hs hq⟩ hq h x
    · have hp' : p < ⊤ := lt_top_iff_ne_top.mpr hp
      rw [completeTopFamily_below K act h₁ hmul hs n old hn f p hp']
      exact old.compatible
        ⟨p, by rw [← hn]; exact faceRank_strictMono hs hp'⟩
        ⟨q, by rw [← hn]; exact faceRank_strictMono hs hq⟩ hqp' h x

theorem completeTopFamily_relabel_below (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (g : G) (q : P) (hq : q < ⊤) :
    stalkFamilyRelabel K (act g) (completeTopFamily K act h₁ hmul n old f) q =
      completeTopFamily K act h₁ hmul n old f q := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  have hq' : (act g).symm q ≠ ⊤ := by
    intro he
    apply hq.ne
    have hh := congrArg (act g) he
    simpa only [(act g).apply_symm_apply, (act g).map_top] using hh
  change (stalkFamilyRelabel K (act g)
      (rankStalkSum K act h₁ hmul n old + stalkFamilySingle K ⊤ f)) q = _
  rw [map_add, rankStalkSum_fixed]
  apply LinearMap.ext
  intro x
  change rankStalkSum K act h₁ hmul n old q x +
      stalkFamilyRelabel K (act g) (stalkFamilySingle K ⊤ f) q x =
    rankStalkSum K act h₁ hmul n old q x + stalkFamilySingle K ⊤ f q x
  rw [stalkFamilyRelabel_apply, stalkFamilySingle_ne K ⊤ q hq.ne f,
    stalkFamilySingle_ne K ⊤ ((act g).symm q) hq' f]
  simp

theorem completeTopFamily_boundary_error (hs : IsSimplicialPoset P)
    (n : ℕ) (old : ActualStalkRankStage K act h₁ hmul n) (hn : faceRank (⊤ : P) = n)
    (f : BarycentricStalk K (⊤ : P) →ₗ[K] PolynomialStalk K (⊤ : P))
    (hf : ∀ (q : equivariantRankCut faceRank n), q.val < ⊤ →
      StalkLocalCompatible K ⊤ q.val (stalkFamilySingle K ⊤ f) ((actualRankStageValue K act h₁ hmul n old) q))
    (g : G) (x : BarycentricStalk K (⊤ : P)) :
    polynomialBooleanBoundaryMap
      (stalkFamilyRelabel K (act g) (completeTopFamily K act h₁ hmul n old f) ⊤ x) =
        polynomialBooleanBoundaryMap (f x) := by
  letI := orderActionMulAction act h₁ hmul
  letI := representationMulAction (stalkFamilyRepresentation K act h₁ hmul)
  let F := completeTopFamily K act h₁ hmul n old f
  have hF : F ∈ coherentStalkFamilySubmodule K :=
    completeTopFamily_coherent K act h₁ hmul hs n old hn f hf
  have hδ : stalkFamilyRelabel K (act g) F - F ∈ coherentStalkFamilySubmodule K :=
    (coherentStalkFamilySubmodule K).sub_mem (stalkFamilyRelabel_coherent K (act g) F hF) hF
  have hz : stalkBoundaryRestriction (polynomialDiagram K) (⊤ : P)
      ((stalkFamilyRelabel K (act g) F - F) ⊤ x) = 0 := by
    apply Subtype.ext
    funext q
    change polynomialRestriction K q.property.le
      ((stalkFamilyRelabel K (act g) F - F) ⊤ x) = 0
    rw [hδ]
    change (stalkFamilyRelabel K (act g) F q.val - F q.val)
      (booleanRestriction (faceVertexInclusion q.property.le) x) = 0
    rw [completeTopFamily_relabel_below K act h₁ hmul hs n old hn f g q.val q.property,
      sub_self, LinearMap.zero_apply]
  have hboundary := (polynomialStalkBoundary_eq_zero_iff K hs ⊤ _).mp hz
  have hh := (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr hboundary
  change polynomialBooleanBoundaryMap
    (stalkFamilyRelabel K (act g) F ⊤ x - F ⊤ x) = 0 at hh
  rw [map_sub] at hh
  have htop : F ⊤ = f := completeTopFamily_top K act h₁ hmul n old hn f
  rw [htop] at hh
  exact sub_eq_zero.mp hh

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeCoherent.lean -/
section


section

/-! # A normalized integral coherent family on the prime simplex

Proper nonempty faces have free cyclic orbits.  At the top the actual
integral prime-cycle lifting theorem is applied to the ordinary extension of
the already equivariant boundary.  The completed family is coherent on every
face, parameter-linear, graded, normalized, and cyclic-equivariant over ℤ.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.
open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Restrictions
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]

theorem polynomialBoundary_eq_restriction (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q < p) (f g : PolynomialStalk K p)
    (h : polynomialBooleanBoundaryMap f = polynomialBooleanBoundaryMap g) :
    polynomialRestriction K hqp.le f = polynomialRestriction K hqp.le g := by
  have hz : polynomialBooleanBoundaryMap (f - g) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨y, hy⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff _).mp hz
  have hr : polynomialRestriction K hqp.le (f - g) = 0 := by
    rw [← hy, map_mul]
    change polynomialRestriction K hqp.le (polynomialTop K p) * polynomialRestriction K hqp.le y = 0
    rw [polynomialRestriction_top K hs hqp, zero_mul]
  rw [map_sub] at hr
  exact sub_eq_zero.mp hr

end Restrictions

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicSimplexOrderAction_inv_symm (g : PrimeCycleGroup p) :
    (cyclicSimplexOrderAction p g⁻¹).symm = cyclicSimplexOrderAction p g := by
  change finsetOrderCongr ((cyclicVertexPermutation p g⁻¹)⁻¹) =
    finsetOrderCongr (cyclicVertexPermutation p g)
  rw [(cyclicVertexPermutation p).map_inv, inv_inv]

theorem exists_integral_prime_simplex_family :
    ∃ F : StalkLinearFamily (P := Finset (ZMod p)) ℤ,
      F ∈ coherentStalkFamilySubmodule ℤ ∧
      F ∈ parameterStalkFamilySubmodule ℤ ∧
      F ∈ gradedStalkFamilySubmodule ℤ ∧
      (∀ s, F s 1 = 1) ∧
      ∀ g : PrimeCycleGroup p, stalkFamilyRelabel ℤ (cyclicSimplexOrderAction p g) F = F := by
  let hs : IsSimplicialPoset (Finset (ZMod p)) := simplex_isSimplicialPoset
  apply exists_coherent_family_of_prime_top_extension ℤ hs
    (cyclicSimplexOrderAction p) (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
  · intro s hs₀ hs₁ g hg
    exact cyclicSimplex_proper_face_free p s (Finset.nonempty_iff_ne_empty.mpr hs₀) hs₁ g hg
  · letI := orderActionMulAction (cyclicSimplexOrderAction p)
      (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
    letI := representationMulAction (stalkFamilyRepresentation ℤ (cyclicSimplexOrderAction p)
      (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p))
    intro n old hn
    have hp : (Finset.univ : Finset (ZMod p)) ≠ ∅ := Finset.univ_nonempty.ne_empty
    obtain ⟨y, hy, hyb⟩ := exists_ordinary_rank_stalk_extension ℤ hs
      (cyclicSimplexOrderAction p) (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
      n old Finset.univ hn hp
    let V := FaceVertex (Finset.univ : Finset (ZMod p))
    let e : V ≃ ZMod p := simplexTopVertexEquiv
    letI : LinearOrder V := linearOrderWithDecidableEq (LinearOrder.lift' e e.injective) inferInstance
    let f : BooleanBarycentricRing V ℤ →ₗ[ℤ] MvPolynomial V ℤ := y Finset.univ
    have hsingle : stalkFamilySingle ℤ Finset.univ f = y :=
      stalkFamilySingle_eq_of_supported ℤ Finset.univ y hy.1
    have hfbound : ∀ q : equivariantRankCut faceRank n, q.val < (Finset.univ : Finset (ZMod p)) →
        StalkLocalCompatible ℤ Finset.univ q.val (stalkFamilySingle ℤ Finset.univ f) (old.value q) := by
      rw [hsingle]
      exact hyb
    have hfp : IsParameterLinear booleanColorMap polynomialColorMap f :=
      intertwinesAllRanks_parameterLinear f (hy.2.1 Finset.univ)
    have hfd : ∀ m x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) m → f x ∈ polynomialDegreePiece m :=
      hy.2.2.1 Finset.univ
    have hf₁ : f 1 = 1 := hy.2.2.2
    have hfe : ∀ (g : PrimeCycleGroup p) x,
        polynomialBooleanBoundaryMap (f (booleanPermutationAlgEquiv
          (e.symm.permCongr (Equiv.addLeft g.toAdd)) x)) =
        polynomialBooleanBoundaryMap (MvPolynomial.rename
          (e.symm.permCongr (Equiv.addLeft g.toAdd)) (f x)) := by
      intro g x
      let a := cyclicSimplexOrderAction p g⁻¹
      have ha : a.symm (Finset.univ : Finset (ZMod p)) = Finset.univ := a.symm.map_top
      let T := completeTopFamily ℤ (cyclicSimplexOrderAction p)
        (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p) n old f
      have hb := completeTopFamily_boundary_error ℤ (cyclicSimplexOrderAction p)
        (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p)
        hs n old hn f hfbound g⁻¹ x
      have hrename := polynomialBoundary_rename_equiv_congr
        (fixedFaceVertexPermutation a.symm Finset.univ ha) _ _ hb
      change polynomialBooleanBoundaryMap (MvPolynomial.rename
          (fixedFaceVertexPermutation a.symm Finset.univ ha)
          (stalkFamilyRelabel ℤ a T Finset.univ x)) =
        polynomialBooleanBoundaryMap (MvPolynomial.rename
          (fixedFaceVertexPermutation a.symm Finset.univ ha) (f x)) at hrename
      have hT : T Finset.univ = f := completeTopFamily_top ℤ (cyclicSimplexOrderAction p)
        (cyclicSimplexOrderAction_one p) (cyclicSimplexOrderAction_mul p) n old hn f
      rw [stalkFamilyRelabel_fixed_conjugate ℤ a Finset.univ ha T x, hT] at hrename
      have heq : fixedFaceVertexPermutation a.symm Finset.univ ha =
          e.symm.permCongr (Equiv.addLeft g.toAdd) := by
        have hact : a.symm = finsetOrderCongr (Equiv.addLeft g.toAdd) :=
          cyclicSimplexOrderAction_inv_symm p g
        have hh := congrArg
          (fun b : Finset (ZMod p) ≃o Finset (ZMod p) =>
            fixedFaceVertexPermutation b Finset.univ b.map_top) hact
        exact hh.trans (simplex_fixed_top_permutation (Equiv.addLeft g.toAdd)
          (finsetOrderCongr_univ (Equiv.addLeft g.toAdd)))
      rw [heq] at hrename
      exact hrename
    obtain ⟨L, hLp, hLd, hL₁, hLb, hLe⟩ := exists_integralPrime_vertex_lift p e f hfp hfd hf₁ hfe
    let LL : BarycentricStalk ℤ (Finset.univ : Finset (ZMod p)) →ₗ[ℤ]
        PolynomialStalk ℤ (Finset.univ : Finset (ZMod p)) :=
      integralLinearMapOfAddHom L.toAddMonoidHom
    refine ⟨stalkFamilySingle ℤ Finset.univ LL,
      stalkFamilySingle_good ℤ Finset.univ LL (parameterLinear_intertwinesAllRanks LL hLp) hLd hL₁,
      ?_, ?_⟩
    · intro q hq h x
      erw [stalkFamilySingle_same]
      have hb := polynomialBoundary_eq_restriction hs hq (L x) (f x) (hLb x)
      have hh := hfbound q hq h x
      erw [stalkFamilySingle_same] at hh
      erw [hb]
      exact hh
    · intro g
      apply simplex_top_single_fixed ℤ (cyclicVertexPermutation p g) LL
      intro x
      have hi : (cyclicVertexPermutation p g).symm = cyclicVertexPermutation p g⁻¹ :=
        ((cyclicVertexPermutation p).map_inv g).symm
      rw [hi]
      exact hLe g⁻¹ x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSymmetricTrace.lean -/
section


section

/-! # Symmetric coherent families from integral orbit traces

At prime rank the cyclic family is traced over exactly `(p-1)!` cosets.  At
every rank ordinary full-group averaging gives the factorial scalar.  Both
constructions act on the whole genuine coherent family, so all face
restriction squares and ordinary grading are preserved.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped BigOperators

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

theorem exists_normalized_coherent_stalk_family (K : Type*) [CommRing K]
    (hs : IsSimplicialPoset P) :
    ∃ F : StalkLinearFamily (P := P) K,
      F ∈ coherentStalkFamilySubmodule K ∧ F ∈ parameterStalkFamilySubmodule K ∧
      F ∈ gradedStalkFamilySubmodule K ∧ ∀ p, F p 1 = 1 := by
  let G := Equiv.Perm (Fin 0)
  let act : G → P ≃o P := fun _ => OrderIso.refl P
  have h₁ : act 1 = OrderIso.refl P := rfl
  have hmul : ∀ g h, act (g * h) = (act h).trans (act g) := by intros; rfl
  obtain ⟨F, hc, hp, hd, hnorm, he⟩ := exists_equivariant_coherent_stalk_family K act h₁ hmul hs (by
    intro n old p hr
    by_cases hbot : p = ⊥
    · subst p
      obtain ⟨y, hy⟩ := exists_stalkLocalGood_bot (P := P) K
      exact ⟨y, hy, fun q hq => False.elim (not_lt_bot hq), fun _ _ => stalkFamilyRelabel_refl K y⟩
    · obtain ⟨y, hy, hb⟩ := exists_ordinary_rank_stalk_extension K hs act h₁ hmul n old p hr hbot
      exact ⟨y, hy, hb, fun _ _ => stalkFamilyRelabel_refl K y⟩)
  exact ⟨F, hc, hp, hd, hnorm⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def symmetricSimplexFamilyRepresentation (K : Type*) [CommRing K] :
    CyclicRepresentation K (Equiv.Perm V) (StalkLinearFamily (P := Finset V) K) :=
  stalkFamilyRepresentation K finsetOrderCongr simplexOrderAction_one simplexOrderAction_mul

def stalkFamilyEvalOne (K : Type*) [CommRing K] (s : Finset V) :
    StalkLinearFamily (P := Finset V) K →+ PolynomialStalk K s where
  toFun F := F s 1
  map_zero' := rfl
  map_add' F H := rfl

theorem simplexCosetTrace_properties (K : Type*) [CommRing K]
    (H : Subgroup (Equiv.Perm V)) (F : StalkLinearFamily (P := Finset V) K)
    (hH : ∀ h : H, symmetricSimplexFamilyRepresentation K h.val F = F)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K)
    (h₁ : ∀ s, F s 1 = 1) :
    let T := cosetTrace (symmetricSimplexFamilyRepresentation K) H F hH
    T ∈ coherentStalkFamilySubmodule K ∧ T ∈ parameterStalkFamilySubmodule K ∧
      T ∈ gradedStalkFamilySubmodule K ∧
      (∀ s, T s 1 = H.index • (1 : PolynomialStalk K s)) ∧
      ∀ e : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr e) T = T := by
  dsimp only
  refine ⟨cosetTrace_mem _ _ _ _ _ (fun e y hy => stalkFamilyRelabel_coherent K _ y hy) hc,
    cosetTrace_mem _ _ _ _ _ (fun e y hy => stalkFamilyRelabel_parameter K _ y hy) hp,
    cosetTrace_mem _ _ _ _ _ (fun e y hy => stalkFamilyRelabel_graded K _ y hy) hd, ?_, ?_⟩
  · intro s
    apply cosetTrace_map_const (symmetricSimplexFamilyRepresentation K) H F hH
      (stalkFamilyEvalOne K s) 1
    intro e
    change stalkFamilyRelabel K (finsetOrderCongr e) F s 1 = 1
    rw [stalkFamilyRelabel_apply, map_one, h₁, map_one]
  · intro e
    exact cosetTrace_fixed (symmetricSimplexFamilyRepresentation K) H F hH e

theorem exists_integral_factorial_simplex_family :
    ∃ F : StalkLinearFamily (P := Finset V) ℤ,
      F ∈ coherentStalkFamilySubmodule ℤ ∧ F ∈ parameterStalkFamilySubmodule ℤ ∧
      F ∈ gradedStalkFamilySubmodule ℤ ∧
      (∀ s, F s 1 = (Fintype.card V).factorial • (1 : PolynomialStalk ℤ s)) ∧
      ∀ e : Equiv.Perm V, stalkFamilyRelabel ℤ (finsetOrderCongr e) F = F := by
  obtain ⟨F, hc, hp, hd, h₁⟩ := exists_normalized_coherent_stalk_family ℤ
    (simplex_isSimplicialPoset (V := V))
  have hH : ∀ h : (⊥ : Subgroup (Equiv.Perm V)), symmetricSimplexFamilyRepresentation ℤ h.val F = F := by
    intro h
    have he : h.val = 1 := h.property
    rw [he, (symmetricSimplexFamilyRepresentation ℤ).map_one]
    rfl
  refine ⟨cosetTrace (symmetricSimplexFamilyRepresentation ℤ) ⊥ F hH, ?_⟩
  have hh := simplexCosetTrace_properties ℤ ⊥ F hH hc hp hd h₁
  have hi : (⊥ : Subgroup (Equiv.Perm V)).index = (Fintype.card V).factorial := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_perm]
  simpa only [hi] using hh

variable (p : ℕ) [Fact p.Prime] [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicVertexPermutation_injective : Function.Injective (cyclicVertexPermutation p) := by
  intro g h he
  have hh := congrArg (fun e : Equiv.Perm (ZMod p) => e 0) he
  change g.toAdd + 0 = h.toAdd + 0 at hh
  rw [add_zero, add_zero] at hh
  exact congrArg Multiplicative.ofAdd hh

theorem cyclicVertexPermutation_index : (cyclicVertexPermutation p).range.index = (p - 1).factorial :=
  permutationEmbedding_index_factorial (cyclicVertexPermutation p) (cyclicVertexPermutation_injective p)
    p (Fact.out : p.Prime).pos
    (by rw [Nat.card_eq_fintype_card, primeCycle_card]) (ZMod.card p)

theorem exists_integral_prime_symmetric_simplex_family :
    ∃ F : StalkLinearFamily (P := Finset (ZMod p)) ℤ,
      F ∈ coherentStalkFamilySubmodule ℤ ∧ F ∈ parameterStalkFamilySubmodule ℤ ∧
      F ∈ gradedStalkFamilySubmodule ℤ ∧
      (∀ s, F s 1 = (p - 1).factorial • (1 : PolynomialStalk ℤ s)) ∧
      ∀ e : Equiv.Perm (ZMod p), stalkFamilyRelabel ℤ (finsetOrderCongr e) F = F := by
  obtain ⟨F, hc, hp, hd, h₁, he⟩ := exists_integral_prime_simplex_family p
  let H := (cyclicVertexPermutation p).range
  have hH : ∀ h : H, symmetricSimplexFamilyRepresentation ℤ h.val F = F := by
    intro h
    obtain ⟨g, hg⟩ := h.property
    rw [← hg]
    exact he g
  refine ⟨cosetTrace (symmetricSimplexFamilyRepresentation ℤ) H F hH, ?_⟩
  have hh := simplexCosetTrace_properties ℤ H F hH hc hp hd h₁
  simpa only [H, cyclicVertexPermutation_index] using hh

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFamilyBaseChange.lean -/
section


section

/-! # Scalar extension and normalization of coherent integral families

Each component is extended through its actual integral standard basis.
Coefficient naturality proves preservation of every restriction, parameter
operator, ordinary degree, and order-automorphism symmetry.  A unit constant
scalar is then divided out in the coefficient ring.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def integralStalkLinearExtension (p : P)
    (f : BarycentricStalk ℤ p →ₗ[ℤ] PolynomialStalk ℤ p) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p :=
  integralLinearExtension (barycentricStalkStandardBasis ℤ hs p)
    (barycentricStalkStandardBasis K hs p) (polynomialCoefficientChange (Int.castRingHom K)) f

theorem integralStalkLinearExtension_commutes (p : P)
    (f : BarycentricStalk ℤ p →ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk ℤ p) :
    integralStalkLinearExtension K hs p f (booleanCoefficientChange (Int.castRingHom K) x) =
      polynomialCoefficientChange (Int.castRingHom K) (f x) :=
  integralLinearExtension_commutes (barycentricStalkStandardBasis ℤ hs p)
    (barycentricStalkStandardBasis K hs p) (booleanCoefficientChange (Int.castRingHom K))
    (polynomialCoefficientChange (Int.castRingHom K))
    (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p) f x

@[simp] theorem integralStalkLinearExtension_basis (p : P)
    (f : BarycentricStalk ℤ p →ₗ[ℤ] PolynomialStalk ℤ p) (a : StandardInside p) :
    integralStalkLinearExtension K hs p f (barycentricStalkStandardBasis K hs p a) =
      polynomialCoefficientChange (Int.castRingHom K) (f (barycentricStalkStandardBasis ℤ hs p a)) :=
  integralLinearExtension_basis _ _ _ _ a

def integralStalkFamilyExtension (F : StalkLinearFamily (P := P) ℤ) : StalkLinearFamily (P := P) K :=
  fun p => integralStalkLinearExtension K hs p (F p)

theorem integralStalkFamilyExtension_coherent (F : StalkLinearFamily (P := P) ℤ)
    (hF : F ∈ coherentStalkFamilySubmodule ℤ) :
    integralStalkFamilyExtension K hs F ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  have he : (polynomialRestriction K h).toLinearMap.comp (integralStalkLinearExtension K hs p (F p)) =
      (integralStalkLinearExtension K hs q (F q)).comp
        (booleanRestriction (K := K) (faceVertexInclusion h)).toLinearMap := by
    apply (barycentricStalkStandardBasis K hs p).ext
    intro a
    change polynomialRestriction K h
      (integralStalkLinearExtension K hs p (F p) (barycentricStalkStandardBasis K hs p a)) = _
    rw [integralStalkLinearExtension_basis,
      ← polynomialCoefficientChange_restriction (Int.castRingHom K) h, hF,
      ← integralStalkLinearExtension_commutes K hs q (F q),
      booleanCoefficientChange_restriction, booleanCoefficientChange_standardBasis]
    rfl
  exact DFunLike.congr_fun he x

theorem integralStalkFamilyExtension_parameter (F : StalkLinearFamily (P := P) ℤ)
    (hF : F ∈ parameterStalkFamilySubmodule ℤ) :
    integralStalkFamilyExtension K hs F ∈ parameterStalkFamilySubmodule K := by
  change ∀ p r x, F p (booleanRankParameter (r + 1) * x) =
    polynomialParameter ℤ p (r + 1) * F p x at hF
  intro p r x
  have he : (integralStalkLinearExtension K hs p (F p)).comp
      (LinearMap.mulLeft K (booleanRankParameter (V := FaceVertex p) (K := K) (r + 1))) =
    (LinearMap.mulLeft K (polynomialParameter K p (r + 1))).comp
      (integralStalkLinearExtension K hs p (F p)) := by
    apply (barycentricStalkStandardBasis K hs p).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a,
      ← booleanCoefficientChange_parameter (Int.castRingHom K) (r + 1),
      ← booleanCoefficientChange_mul, integralStalkLinearExtension_commutes,
      integralStalkLinearExtension_commutes, hF]
    simp only [polynomialCoefficientChange_eq, map_mul, polynomialParameter, MvPolynomial.map_esymm]
  exact DFunLike.congr_fun he x

theorem integralStalkFamilyExtension_graded (F : StalkLinearFamily (P := P) ℤ)
    (hp : F ∈ parameterStalkFamilySubmodule ℤ)
    (hd : F ∈ gradedStalkFamilySubmodule ℤ) :
    integralStalkFamilyExtension K hs F ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  apply ordinaryDegree_of_hasStandardDegree hs p
    (integralStalkLinearExtension K hs p (F p)) ?_ n x hx
  intro a b hab
  change (polynomialStandardCoordinates K hs p
    (integralStalkLinearExtension K hs p (F p)
      (barycentricStalkStandardBasis K hs p a))).val b = 0
  rw [integralStalkLinearExtension_basis, polynomialCoefficientChange_coordinates]
  have hh := hasStandardDegree_of_ordinary_degree ℤ hs p (F p) (hd p) a b hab
  rw [hh, map_zero]

theorem integralStalkFamilyExtension_scalar (F : StalkLinearFamily (P := P) ℤ)
    (m : ℕ) (hF : ∀ p, F p 1 = m • (1 : PolynomialStalk ℤ p)) :
    ∀ p, integralStalkFamilyExtension K hs F p 1 = m • (1 : PolynomialStalk K p) := by
  intro p
  have hh := integralStalkLinearExtension_commutes K hs p (F p) 1
  have h₁ : booleanCoefficientChange (V := FaceVertex p) (Int.castRingHom K) 1 = 1 :=
    (monomialCoefficientRingHom IsChainExponent isChainExponent_divisorClosed (Int.castRingHom K)).map_one
  rw [h₁, hF, map_nsmul] at hh
  simpa only [integralStalkFamilyExtension, polynomialCoefficientChange_eq, map_one] using hh

theorem integralStalkFamilyExtension_relabel (F : StalkLinearFamily (P := P) ℤ) (e : P ≃o P) :
    integralStalkFamilyExtension K hs (stalkFamilyRelabel ℤ e F) =
      stalkFamilyRelabel K e (integralStalkFamilyExtension K hs F) := by
  funext p
  apply (barycentricStalkStandardBasis K hs p).ext
  intro a
  change integralStalkLinearExtension K hs p (stalkFamilyRelabel ℤ e F p)
    (barycentricStalkStandardBasis K hs p a) = _
  rw [integralStalkLinearExtension_basis]
  have hB := booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p a
  rw [← hB]
  change MvPolynomial.map (Int.castRingHom K)
      ((polynomialStalkOrderEquiv ℤ e.symm p).symm
        (F (e.symm p) (barycentricStalkOrderEquiv ℤ e.symm p
          (barycentricStalkStandardBasis ℤ hs p a)))) =
    (polynomialStalkOrderEquiv K e.symm p).symm
      (integralStalkLinearExtension K hs (e.symm p) (F (e.symm p))
        (barycentricStalkOrderEquiv K e.symm p
          (booleanCoefficientChange (Int.castRingHom K) (barycentricStalkStandardBasis ℤ hs p a))))
  have hn := booleanCoefficientChange_restriction (Int.castRingHom K)
    (faceVertexOrderEquiv e.symm p).symm.toEmbedding (barycentricStalkStandardBasis ℤ hs p a)
  change booleanCoefficientChange (Int.castRingHom K)
      (barycentricStalkOrderEquiv ℤ e.symm p (barycentricStalkStandardBasis ℤ hs p a)) =
    barycentricStalkOrderEquiv K e.symm p
      (booleanCoefficientChange (Int.castRingHom K) (barycentricStalkStandardBasis ℤ hs p a)) at hn
  rw [← hn, integralStalkLinearExtension_commutes]
  exact MvPolynomial.map_rename (Int.castRingHom K) (faceVertexOrderEquiv e.symm p).symm _

include hs in
theorem exists_normalized_scalar_extension (F : StalkLinearFamily (P := P) ℤ)
    (m : ℕ) (hm : IsUnit (m : K))
    (hc : F ∈ coherentStalkFamilySubmodule ℤ)
    (hp : F ∈ parameterStalkFamilySubmodule ℤ)
    (hd : F ∈ gradedStalkFamilySubmodule ℤ)
    (hscalar : ∀ p, F p 1 = m • (1 : PolynomialStalk ℤ p)) :
    ∃ L : StalkLinearFamily (P := P) K,
      L ∈ coherentStalkFamilySubmodule K ∧ L ∈ parameterStalkFamilySubmodule K ∧
      L ∈ gradedStalkFamilySubmodule K ∧ (∀ p, L p 1 = 1) ∧
      ∀ e : P ≃o P, stalkFamilyRelabel ℤ e F = F → stalkFamilyRelabel K e L = L := by
  obtain ⟨u, hu⟩ := hm
  let E := integralStalkFamilyExtension K hs F
  let L : StalkLinearFamily (P := P) K := (↑u⁻¹ : K) • E
  refine ⟨L,
    (coherentStalkFamilySubmodule K).smul_mem _ (integralStalkFamilyExtension_coherent K hs F hc),
    (parameterStalkFamilySubmodule K).smul_mem _ (integralStalkFamilyExtension_parameter K hs F hp),
    (gradedStalkFamilySubmodule K).smul_mem _ (integralStalkFamilyExtension_graded K hs F hp hd),
    ?_, ?_⟩
  · intro p
    change (↑u⁻¹ : K) • (E p 1) = 1
    rw [integralStalkFamilyExtension_scalar K hs F m hscalar]
    rw [← Nat.cast_smul_eq_nsmul K m (1 : PolynomialStalk K p), ← hu]
    exact inv_smul_smul u (1 : PolynomialStalk K p)
  · intro e he
    change stalkFamilyRelabel K e ((↑u⁻¹ : K) • E) = (↑u⁻¹ : K) • E
    rw [map_smul, ← integralStalkFamilyExtension_relabel, he]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSymmetricTransport.lean -/
section

section
/-! # Transport of a symmetric simplex family to arbitrary face posets

A full symmetric family on one finite simplex determines maps on every
finite vertex set of at most that cardinality.  The construction chooses an
embedding, and its independence is proved by extending a pair of finite
embeddings to an ambient permutation.  The resulting maps commute with
every vertex inclusion and bijection, so they apply to the actual vertices
of each face of an arbitrary simplicial poset.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section VertexTransport
variable {A B C D K : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [CommRing K]

def vertexTransportLinear
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B) :
    BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K :=
  (MvPolynomial.renameEquiv K e).symm.toLinearMap.comp
    (f.comp (booleanVertexRelabelEquiv e).toLinearMap)

@[simp] theorem vertexTransportLinear_apply
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (x : BooleanBarycentricRing A K) :
    vertexTransportLinear f e x = MvPolynomial.rename e.symm (f (booleanVertexRelabelEquiv e x)) :=
  rfl

theorem vertexTransportLinear_trans
    (f : BooleanBarycentricRing C K →ₗ[K] MvPolynomial C K) (e : A ≃ B) (g : B ≃ C) :
    vertexTransportLinear (vertexTransportLinear f g) e = vertexTransportLinear f (e.trans g) := by
  apply LinearMap.ext
  intro x
  simp only [vertexTransportLinear_apply, booleanVertexRelabelEquiv_trans,
    MvPolynomial.rename_rename]
  rfl

theorem vertexTransportLinear_of_intertwines
    (f : BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K)
    (g : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (h : ∀ x, MvPolynomial.rename e (f x) = g (booleanVertexRelabelEquiv e x)) :
    vertexTransportLinear g e = f := by
  apply LinearMap.ext
  intro x
  rw [vertexTransportLinear_apply, ← h]
  exact (MvPolynomial.renameEquiv K e).symm_apply_apply (f x)

theorem vertexTransportLinear_parameter
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (hf : ∀ r x, f (booleanRankParameter (r + 1) * x) = esymm B K (r + 1) * f x)
    (r : ℕ) (x : BooleanBarycentricRing A K) :
    vertexTransportLinear f e (booleanRankParameter (r + 1) * x) =
      esymm A K (r + 1) * vertexTransportLinear f e x := by
  rw [vertexTransportLinear_apply, map_mul, booleanVertexRelabelEquiv_parameter,
    hf, map_mul, MvPolynomial.rename_esymm]
  rfl

theorem vertexTransportLinear_graded
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (n : ℕ) (x : BooleanBarycentricRing A K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    vertexTransportLinear f e x ∈ polynomialDegreePiece n :=
  polynomialRename_degree e.symm n _ (hf n _ (booleanVertexRelabelEquiv_degree e n x hx))

theorem vertexTransportLinear_normalized
    (f : BooleanBarycentricRing B K →ₗ[K] MvPolynomial B K) (e : A ≃ B)
    (hf : f 1 = 1) : vertexTransportLinear f e 1 = 1 := by
  rw [vertexTransportLinear_apply, map_one, hf, map_one]

theorem coeff_rename_inverse (e : A ≃ B) (f : MvPolynomial B K) (a : A →₀ ℕ) :
    (MvPolynomial.rename e.symm f).coeff a = f.coeff (a.mapDomain e) := by
  have h := MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective f (a.mapDomain e)
  simpa only [← Finsupp.mapDomain_comp, e.symm_comp_self, Finsupp.mapDomain_id] using h

theorem killCompl_equiv (e : A ≃ B) (f : MvPolynomial B K) :
    MvPolynomial.killCompl e.injective f = MvPolynomial.rename e.symm f := by
  ext a
  rw [MvPolynomial.coeff_killCompl, coeff_rename_inverse]

theorem killCompl_rename_square (i : A ↪ B) (j : C ↪ D) (e : A ≃ C) (g : B ≃ D)
    (h : i.trans g.toEmbedding = e.toEmbedding.trans j) (f : MvPolynomial D K) :
    MvPolynomial.killCompl i.injective (MvPolynomial.rename g.symm f) =
      MvPolynomial.rename e.symm (MvPolynomial.killCompl j.injective f) := by
  ext a
  rw [MvPolynomial.coeff_killCompl, coeff_rename_inverse, coeff_rename_inverse,
    MvPolynomial.coeff_killCompl, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  change f.coeff (a.mapDomain (i.trans g.toEmbedding)) =
    f.coeff (a.mapDomain (e.toEmbedding.trans j))
  rw [h]

theorem booleanRestriction_relabel_square (i : A ↪ B) (j : C ↪ D)
    (e : A ≃ C) (g : B ≃ D) (h : i.trans g.toEmbedding = e.toEmbedding.trans j)
    (x : BooleanBarycentricRing B K) :
    booleanVertexRelabelEquiv e (booleanRestriction i x) =
      booleanRestriction j (booleanVertexRelabelEquiv g x) := by
  have he : e.symm.toEmbedding.trans i = j.trans g.symm.toEmbedding := by
    apply Function.Embedding.ext
    intro a
    apply g.injective
    have hh := congrArg (fun t : A ↪ D => t (e.symm a)) h
    change g (i (e.symm a)) = j (e (e.symm a)) at hh
    change g (i (e.symm a)) = g (g.symm (j a))
    simpa only [Equiv.apply_symm_apply] using hh
  change booleanRestriction e.symm.toEmbedding (booleanRestriction i x) =
    booleanRestriction j (booleanRestriction g.symm.toEmbedding x)
  calc
    _ = booleanRestriction (e.symm.toEmbedding.trans i) x :=
      DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x
    _ = booleanRestriction (j.trans g.symm.toEmbedding) x := by rw [he]
    _ = _ := (DFunLike.congr_fun (booleanRestriction_comp (K := K) _ _) x).symm

end VertexTransport

section StalkTransport
variable {P A B K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype A] [Fintype B] [CommRing K]

theorem stalkFamily_fixed_natural (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : stalkFamilyRelabel K e.symm F = F) (p : P) (x : BarycentricStalk K p) :
    polynomialStalkOrderEquiv K e p (F p x) =
      F (e p) (barycentricStalkOrderEquiv K e p x) := by
  have h := congrArg (fun H : StalkLinearFamily (P := P) K => H p x) hF
  change (polynomialStalkOrderEquiv K e p).symm
    (F (e p) (barycentricStalkOrderEquiv K e p x)) = F p x at h
  have hh := congrArg (polynomialStalkOrderEquiv K e p) h
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem vertexTransport_stalk_order (F : StalkLinearFamily (P := P) K)
    (e : P ≃o P) (hF : stalkFamilyRelabel K e.symm F = F)
    (p q : P) (a : A ≃ FaceVertex p) (b : A ≃ FaceVertex q)
    (hq : q = e p) (hb : ∀ x, (b x).val = e (a x).val) :
    vertexTransportLinear (F q) b = vertexTransportLinear (F p) a := by
  subst q
  have he : b = a.trans (faceVertexOrderEquiv e p) := by
    apply Equiv.ext
    intro x
    exact Subtype.ext (hb x)
  rw [he, ← vertexTransportLinear_trans]
  congr 1
  exact vertexTransportLinear_of_intertwines (F p) (F (e p))
    (faceVertexOrderEquiv e p) (stalkFamily_fixed_natural e F hF p)

theorem vertexTransport_stalk_restriction (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) {p q : P} (hqp : q ≤ p)
    (a : A ≃ FaceVertex q) (b : B ≃ FaceVertex p) (i : A ↪ B)
    (hi : i.trans b.toEmbedding = a.toEmbedding.trans (faceVertexInclusion hqp))
    (x : BooleanBarycentricRing B K) :
    MvPolynomial.killCompl i.injective (vertexTransportLinear (F p) b x) =
      vertexTransportLinear (F q) a (booleanRestriction i x) := by
  rw [vertexTransportLinear_apply, killCompl_rename_square i (faceVertexInclusion hqp) a b hi,
    ← polynomialRestriction_eq_killCompl]
  have hh := congrArg (MvPolynomial.rename a.symm)
    (hF p q hqp (booleanVertexRelabelEquiv b x))
  have hb := congrArg (fun z => MvPolynomial.rename a.symm (F q z))
    (booleanRestriction_relabel_square i (faceVertexInclusion hqp) a b hi x).symm
  exact hh.trans hb

end StalkTransport

section SimplexPlacements
variable {A B V K : Type*} [Fintype A] [Fintype B] [Fintype V] [CommRing K]

def embeddedSimplexMap (F : StalkLinearFamily (P := Finset V) K) (i : A ↪ V) :
    BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K :=
  vertexTransportLinear (F (embeddingPlacementFace i)) (embeddingPlacementVertex i)

theorem embeddedSimplexMap_independent (F : StalkLinearFamily (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (i j : A ↪ V) : embeddedSimplexMap F i = embeddedSimplexMap F j := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair i j i.injective j.injective
  have he : i.trans σ.toEmbedding = j := Function.Embedding.ext hσ
  have hface : embeddingPlacementFace j = finsetOrderCongr σ (embeddingPlacementFace i) := by
    simp only [finsetOrderCongr_apply, embeddingPlacementFace, Finset.map_map, he]
  have hfixed : stalkFamilyRelabel K (finsetOrderCongr σ).symm F = F := by
    rw [← finsetOrderCongr_symm]
    exact hF σ.symm
  symm
  apply vertexTransport_stalk_order F (finsetOrderCongr σ) hfixed
    (embeddingPlacementFace i) (embeddingPlacementFace j)
    (embeddingPlacementVertex i) (embeddingPlacementVertex j) hface
  intro a
  simp only [embeddingPlacementVertex_val, finsetOrderCongr_apply, Finset.map_singleton,
    Equiv.coe_toEmbedding, hσ]

theorem embeddingPlacementFace_comp_subset (i : B ↪ V) (j : A ↪ B) :
    embeddingPlacementFace (j.trans i) ⊆ embeddingPlacementFace i := by
  intro v hv
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
  exact Finset.mem_map.mpr ⟨j a, Finset.mem_univ _, rfl⟩

theorem embeddingPlacementVertex_comp (i : B ↪ V) (j : A ↪ B) :
    j.trans (embeddingPlacementVertex i).toEmbedding =
      (embeddingPlacementVertex (j.trans i)).toEmbedding.trans
        (faceVertexInclusion (embeddingPlacementFace_comp_subset i j)) := by
  apply Function.Embedding.ext
  intro a
  apply Subtype.ext
  rfl

theorem embeddedSimplexMap_restriction (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) (i : B ↪ V) (j : A ↪ B)
    (x : BooleanBarycentricRing B K) :
    MvPolynomial.killCompl j.injective (embeddedSimplexMap F i x) =
      embeddedSimplexMap F (j.trans i) (booleanRestriction j x) :=
  vertexTransport_stalk_restriction F hF (embeddingPlacementFace_comp_subset i j)
    (embeddingPlacementVertex (j.trans i)) (embeddingPlacementVertex i) j
    (embeddingPlacementVertex_comp i j) x

def finiteVertexMap (F : StalkLinearFamily (P := Finset V) K)
    (hA : Fintype.card A ≤ Fintype.card V) :
    BooleanBarycentricRing A K →ₗ[K] MvPolynomial A K :=
  embeddedSimplexMap F (Classical.choice (Function.Embedding.nonempty_of_card_le hA))

theorem finiteVertexMap_eq_placement (F : StalkLinearFamily (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (i : A ↪ V) :
    finiteVertexMap F hA = embeddedSimplexMap F i :=
  embeddedSimplexMap_independent F hF _ i

theorem finiteVertexMap_restriction (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (hB : Fintype.card B ≤ Fintype.card V)
    (i : A ↪ B) (x : BooleanBarycentricRing B K) :
    MvPolynomial.killCompl i.injective (finiteVertexMap F hB x) =
      finiteVertexMap F hA (booleanRestriction i x) := by
  let j : B ↪ V := Classical.choice (Function.Embedding.nonempty_of_card_le hB)
  rw [finiteVertexMap_eq_placement F hσ hB j,
    finiteVertexMap_eq_placement F hσ hA (i.trans j)]
  exact embeddedSimplexMap_restriction F hF j i x

theorem finiteVertexMap_relabel (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (hA : Fintype.card A ≤ Fintype.card V) (hB : Fintype.card B ≤ Fintype.card V)
    (e : A ≃ B) (x : BooleanBarycentricRing A K) :
    MvPolynomial.rename e (finiteVertexMap F hA x) =
      finiteVertexMap F hB (booleanVertexRelabelEquiv e x) := by
  have h := finiteVertexMap_restriction F hF hσ hB hA e.symm.toEmbedding x
  rw [killCompl_equiv e.symm] at h
  exact h

theorem finiteVertexMap_parameter (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ parameterStalkFamilySubmodule K)
    (hA : Fintype.card A ≤ Fintype.card V) (r : ℕ) (x : BooleanBarycentricRing A K) :
    finiteVertexMap F hA (booleanRankParameter (r + 1) * x) =
      esymm A K (r + 1) * finiteVertexMap F hA x :=
  vertexTransportLinear_parameter _ _ (fun r x => hF _ r x) r x

theorem finiteVertexMap_graded (F : StalkLinearFamily (P := Finset V) K)
    (hF : F ∈ gradedStalkFamilySubmodule K)
    (hA : Fintype.card A ≤ Fintype.card V) (n : ℕ) (x : BooleanBarycentricRing A K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) : finiteVertexMap F hA x ∈ polynomialDegreePiece n :=
  vertexTransportLinear_graded _ _ (fun n x hx => hF _ n x hx) n x hx

theorem finiteVertexMap_normalized (F : StalkLinearFamily (P := Finset V) K)
    (hF : ∀ s, F s 1 = 1) (hA : Fintype.card A ≤ Fintype.card V) :
    finiteVertexMap F hA 1 = 1 := vertexTransportLinear_normalized _ _ (hF _)

end SimplexPlacements

section PosetTransport
variable {P V K : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype V] [CommRing K]

def symmetricSimplexStalkFamily (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) : StalkLinearFamily (P := P) K :=
  fun p => finiteVertexMap F (by rw [card_faceVertex]; exact hP p)

theorem symmetricSimplexStalkFamily_coherent (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F) :
    symmetricSimplexStalkFamily F hP ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  rw [polynomialRestriction_eq_killCompl]
  exact finiteVertexMap_restriction F hF hσ _ _ (faceVertexInclusion h) x

theorem symmetricSimplexStalkFamily_parameter (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ parameterStalkFamilySubmodule K) :
    symmetricSimplexStalkFamily F hP ∈ parameterStalkFamilySubmodule K := by
  intro p r x
  exact finiteVertexMap_parameter F hF _ r x

theorem symmetricSimplexStalkFamily_graded (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ gradedStalkFamilySubmodule K) :
    symmetricSimplexStalkFamily F hP ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  exact finiteVertexMap_graded F hF _ n x hx

theorem symmetricSimplexStalkFamily_normalized (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) (hF : ∀ s, F s 1 = 1) :
    ∀ p, symmetricSimplexStalkFamily F hP p 1 = 1 := by
  intro p
  exact finiteVertexMap_normalized F hF _

theorem symmetricSimplexStalkFamily_equivariant (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F)
    (e : P ≃o P) (p : P) (x : BarycentricStalk K p) :
    polynomialStalkOrderEquiv K e p (symmetricSimplexStalkFamily F hP p x) =
      symmetricSimplexStalkFamily F hP (e p) (barycentricStalkOrderEquiv K e p x) :=
  finiteVertexMap_relabel F hF hσ _ _ (faceVertexOrderEquiv e p) x

def symmetricSimplexCoherentLinearMap (F : StalkLinearFamily (P := Finset V) K)
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V)
    (hF : F ∈ coherentStalkFamilySubmodule K)
    (hσ : ∀ σ : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr σ) F = F) :
    CoherentLinearMap K (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component := symmetricSimplexStalkFamily F hP
  naturality := symmetricSimplexStalkFamily_coherent F hP hF hσ

end PosetTransport
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCoherentIsomorphism.lean -/
section

section
/-! # From normalized coherent parameter families to actual isomorphisms

The induction is on the actual face rank.  At the bottom, a normalized
linear map is the unique map of constant stalks.  At every positive face,
the already proved lower-face isomorphisms give an actual boundary
isomorphism, and the positive-degree lifting theorem proves bijectivity.
The resulting global comparison is an isomorphism of the original quotient
presentations, linear over their stated universal parameters.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P K : Type*} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]

theorem coherentNormalizedFamily_bijective (hs : IsSimplicialPoset P)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1) :
    ∀ p, Function.Bijective (F p) := by
  have hmain : ∀ n (p : P), faceRank p = n → Function.Bijective (F p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      letI : LinearOrder (FaceVertex p) := LinearOrder.lift'
        (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
      by_cases hbot : p = ⊥
      · subst p
        letI := emptyFaceVertex (P := P)
        have he : F ⊥ = (canonicalBooleanPolynomial (V := FaceVertex (⊥ : P)) (K := K)).toLinearMap :=
          boolean_empty_linear_ext_one _ _ ((h₁ ⊥).trans canonicalBooleanPolynomial_one.symm)
        rw [he]
        exact canonicalBooleanPolynomial.bijective
      · have hpos : 0 < Fintype.card (FaceVertex p) := by
          rw [card_faceVertex]
          have hh := faceRank_strictMono hs (bot_lt_iff_ne_bot.mpr hbot)
          simpa only [faceRank_bot] using hh
        letI : Nonempty (FaceVertex p) := Fintype.card_pos_iff.mp hpos
        let e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
            ((polynomialDiagram K).restrict (Set.Iio p)) := {
          component := fun q => LinearEquiv.ofBijective (F q.val)
            (ih (faceRank q.val) (by rw [← hn]; exact faceRank_strictMono hs q.property) q.val rfl)
          naturality := fun q r h x => hc q.val r.val h x }
        exact coherentStalkLift_bijective K hs p e (fun q => hd q.val) (F p)
          (intertwinesAllRanks_parameterLinear (F p) (hp p)) (hd p)
          (fun q x => hc p q.val q.property.le x)
  intro p
  exact hmain (faceRank p) p rfl

def coherentNormalizedFamilyEquiv (hs : IsSimplicialPoset P)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component p := LinearEquiv.ofBijective (F p) (coherentNormalizedFamily_bijective hs F hc hp hd h₁ p)
  naturality := hc

@[simp] theorem coherentNormalizedFamilyEquiv_apply (hs : IsSimplicialPoset P)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1)
    (p : P) (x : BarycentricStalk K p) :
    (coherentNormalizedFamilyEquiv hs F hc hp hd h₁).component p x = F p x := rfl

def coherentNormalizedParameterComparison (hs : IsSimplicialPoset P) (d : ℕ)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) :=
  originalParameterComparison K hs d (coherentNormalizedFamilyEquiv hs F hc hp hd h₁)
    (fun p r x => hp p r x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/OriginalAutomorphisms.lean -/
section

section
/-! # The natural automorphisms of the original face-ring presentations

Every action in this file is induced by renaming the actual face variables.
The quotient ideals and the rank-sum parameters are proved invariant.
-/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def nonzeroFaceOrderEquiv (e : P ≃o P) : NonzeroFace P ≃ NonzeroFace P where
  toFun p := ⟨e p.val, fun h => p.property (e.injective (h.trans e.map_bot.symm))⟩
  invFun p := ⟨e.symm p.val, fun h => p.property (e.symm.injective (h.trans e.symm.map_bot.symm))⟩
  left_inv p := Subtype.ext (e.symm_apply_apply p.val)
  right_inv p := Subtype.ext (e.apply_symm_apply p.val)

@[simp] theorem nonzeroFaceOrderEquiv_apply (e : P ≃o P) (p : NonzeroFace P) :
    (nonzeroFaceOrderEquiv e p).val = e p.val := rfl

theorem faceSymbol_rename (e : P ≃o P) (p : P) :
    MvPolynomial.rename (nonzeroFaceOrderEquiv e) (faceSymbol K p) =
      faceSymbol K (e p) := by
  by_cases hp : p = ⊥
  · subst p
    simp [faceSymbol, e.map_bot]
  · have he : e p ≠ ⊥ := fun h => hp (e.injective (h.trans e.map_bot.symm))
    simp only [faceSymbol, dif_neg hp, dif_neg he, rename_X]
    rfl

theorem minimalCommonUppers_orderIso (e : P ≃o P) (p q : P) :
    minimalCommonUppers (e p) (e q) = (minimalCommonUppers p q).image e := by
  ext w
  simp only [mem_minimalCommonUppers, Finset.mem_image]
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    refine ⟨by simpa using e.symm.monotone hw.1,
      by simpa using e.symm.monotone hw.2.1, ?_⟩
    intro v hp hq hv
    apply e.injective
    exact (hw.2.2 (e v) (e.monotone hp) (e.monotone hq)
      (by simpa using e.monotone hv)).trans (e.apply_symm_apply w).symm
  · rintro ⟨v, hv, rfl⟩
    refine ⟨e.monotone hv.1, e.monotone hv.2.1, ?_⟩
    intro w hp hq hw
    have hh := hv.2.2 (e.symm w) (by simpa using e.symm.monotone hp)
      (by simpa using e.symm.monotone hq) (by simpa using e.symm.monotone hw)
    simpa using congrArg e hh

theorem faceMeetBelow_orderIso (e : P ≃o P) (p q w : P)
    (hp : p ≤ w) (hq : q ≤ w) :
    e (faceMeetBelow hs p q w hp hq) =
      faceMeetBelow hs (e p) (e q) (e w) (e.monotone hp) (e.monotone hq) := by
  apply le_antisymm
  · exact le_faceMeetBelow hs _ _ _ _ _
      (e.monotone (faceMeetBelow_le_left hs p q w hp hq))
      (e.monotone (faceMeetBelow_le_right hs p q w hp hq))
  · have hl := e.symm.monotone
      (faceMeetBelow_le_left hs (e p) (e q) (e w) (e.monotone hp) (e.monotone hq))
    have hr := e.symm.monotone
      (faceMeetBelow_le_right hs (e p) (e q) (e w) (e.monotone hp) (e.monotone hq))
    have hm := le_faceMeetBelow hs p q w hp hq
      (by simpa only [e.symm_apply_apply] using hl)
      (by simpa only [e.symm_apply_apply] using hr)
    simpa only [e.apply_symm_apply] using e.monotone hm

theorem faceRelations_rename (e : P ≃o P) {f : FacePolynomial (P := P) K}
    (hf : f ∈ faceRelations K hs) :
    MvPolynomial.rename (nonzeroFaceOrderEquiv e) f ∈ faceRelations K hs := by
  rcases hf with ⟨p, q, w, hp, hq, rfl⟩ | ⟨p, q, hnone, rfl⟩
  · left
    refine ⟨e p, e q, e w, e.monotone hp, e.monotone hq, ?_⟩
    rw [map_sub, map_mul, map_mul, map_sum, faceSymbol_rename, faceSymbol_rename,
      faceSymbol_rename, faceMeetBelow_orderIso, minimalCommonUppers_orderIso]
    congr 1
    congr 1
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      exact faceSymbol_rename K e a
    · exact fun _ _ _ _ h => e.injective h
  · right
    refine ⟨e p, e q, ?_, ?_⟩
    · rintro ⟨w, hp, hq⟩
      exact hnone ⟨e.symm w, by simpa using e.symm.monotone hp,
        by simpa using e.symm.monotone hq⟩
    · rw [map_mul, faceSymbol_rename, faceSymbol_rename]

def faceRingOrderMap (e : P ≃o P) : FaceRing K hs →ₐ[K] FaceRing K hs := by
  let f := (Ideal.Quotient.mkₐ K (faceIdeal K hs)).comp
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e))
  apply Ideal.Quotient.liftₐ (faceIdeal K hs) f
  have hh : faceIdeal K hs ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    change Ideal.Quotient.mk (faceIdeal K hs)
      (MvPolynomial.rename (nonzeroFaceOrderEquiv e) p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (faceRelations_rename K hs e hp))
  exact fun p hp => hh hp

@[simp] theorem faceRingOrderMap_mk (e : P ≃o P) (f : FacePolynomial (P := P) K) :
    faceRingOrderMap K hs e (Ideal.Quotient.mk (faceIdeal K hs) f) =
      Ideal.Quotient.mk (faceIdeal K hs)
        (MvPolynomial.rename (nonzeroFaceOrderEquiv e) f) := rfl

def barycentricRingOrderMap (e : P ≃o P) :
    BarycentricRing (P := P) K →ₐ[K] BarycentricRing (P := P) K := by
  let f := (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)).comp
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e))
  apply Ideal.Quotient.liftₐ (barycentricIdeal K) f
  have hh : barycentricIdeal (P := P) K ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨a, b, hab, hba, rfl⟩
    change Ideal.Quotient.mk (barycentricIdeal K)
      (MvPolynomial.rename (nonzeroFaceOrderEquiv e) (X a * X b)) = 0
    rw [map_mul, rename_X, rename_X]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨nonzeroFaceOrderEquiv e a, nonzeroFaceOrderEquiv e b,
      fun h => hab (e.le_iff_le.mp h), fun h => hba (e.le_iff_le.mp h), rfl⟩
  exact fun p hp => hh hp

@[simp] theorem barycentricRingOrderMap_mk (e : P ≃o P) (f : FacePolynomial (P := P) K) :
    barycentricRingOrderMap K e (Ideal.Quotient.mk (barycentricIdeal K) f) =
      Ideal.Quotient.mk (barycentricIdeal K)
        (MvPolynomial.rename (nonzeroFaceOrderEquiv e) f) := rfl

theorem faceRingOrderMap_inverse (e : P ≃o P) (x : FaceRing K hs) :
    faceRingOrderMap K hs e.symm (faceRingOrderMap K hs e x) = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [faceRingOrderMap_mk, faceRingOrderMap_mk, rename_rename]
  have he : (nonzeroFaceOrderEquiv e.symm) ∘ nonzeroFaceOrderEquiv e = id := by
    funext p
    exact Subtype.ext (e.symm_apply_apply p.val)
  rw [he, rename_id_apply]

theorem barycentricRingOrderMap_inverse (e : P ≃o P) (x : BarycentricRing (P := P) K) :
    barycentricRingOrderMap K e.symm (barycentricRingOrderMap K e x) = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [barycentricRingOrderMap_mk, barycentricRingOrderMap_mk, rename_rename]
  have he : (nonzeroFaceOrderEquiv e.symm) ∘ nonzeroFaceOrderEquiv e = id := by
    funext p
    exact Subtype.ext (e.symm_apply_apply p.val)
  rw [he, rename_id_apply]

def faceRingOrderAut (e : P ≃o P) : FaceRing K hs ≃ₐ[K] FaceRing K hs :=
  AlgEquiv.ofAlgHom (faceRingOrderMap K hs e) (faceRingOrderMap K hs e.symm)
    (by ext x; exact faceRingOrderMap_inverse K hs e.symm x)
    (by ext x; exact faceRingOrderMap_inverse K hs e x)

def barycentricRingOrderAut (e : P ≃o P) :
    BarycentricRing (P := P) K ≃ₐ[K] BarycentricRing (P := P) K :=
  AlgEquiv.ofAlgHom (barycentricRingOrderMap K e) (barycentricRingOrderMap K e.symm)
    (by ext x; exact barycentricRingOrderMap_inverse K e.symm x)
    (by ext x; exact barycentricRingOrderMap_inverse K e x)

@[simp] theorem faceRingOrderAut_generator (e : P ≃o P) (p : P) :
    faceRingOrderAut K hs e (faceRingGenerator K hs p) = faceRingGenerator K hs (e p) := by
  change Ideal.Quotient.mk (faceIdeal K hs)
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e) (faceSymbol K p)) = _
  rw [faceSymbol_rename]
  rfl

@[simp] theorem barycentricRingOrderAut_generator (e : P ≃o P) (p : P) :
    barycentricRingOrderAut K e (barycentricGenerator K p) = barycentricGenerator K (e p) := by
  change Ideal.Quotient.mk (barycentricIdeal K)
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e) (faceSymbol K p)) = _
  rw [faceSymbol_rename]
  rfl

theorem rankFaces_orderIso (e : P ≃o P) (r : ℕ) :
    (univ.filter fun p : P => faceRank p = r).image e =
      univ.filter fun p : P => faceRank p = r := by
  ext p
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [faceRank_eq_of_orderIso]
  · intro hp
    exact ⟨e.symm p, by simpa only [faceRank_eq_of_orderIso] using hp, e.apply_symm_apply p⟩

@[simp] theorem faceRingOrderAut_parameter (e : P ≃o P) (r : ℕ) :
    faceRingOrderAut K hs e (faceRankParameter K hs r) = faceRankParameter K hs r := by
  simp only [faceRankParameter, map_sum, faceRingOrderAut_generator]
  conv_rhs => rw [← rankFaces_orderIso e r]
  rw [Finset.sum_image]
  exact fun _ _ _ _ h => e.injective h

@[simp] theorem barycentricRingOrderAut_parameter (e : P ≃o P) (r : ℕ) :
    barycentricRingOrderAut K e (barycentricRankParameter K r) = barycentricRankParameter K r := by
  simp only [barycentricRankParameter, map_sum, barycentricRingOrderAut_generator]
  conv_rhs => rw [← rankFaces_orderIso e r]
  rw [Finset.sum_image]
  exact fun _ _ _ _ h => e.injective h

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGlobalEquivariance.lean -/
section

section
/-! # Equivariance on the actual quotient presentations

The global actions rename the original face variables.  Their compatibility
with polynomial and Boolean stalk evaluation is proved on those generators.
Consequently an equivariant coherent stalk comparison induces an equivariant
parameter-module equivalence on the original face rings.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

theorem stalkVertexSet_order (e : P ≃o P) (p q : P) :
    (stalkVertexSet p q).map (faceVertexOrderEquiv e p).toEmbedding =
      stalkVertexSet (e p) (e q) := by
  ext a
  simp only [Finset.mem_map_equiv, mem_stalkVertexSet, faceVertexOrderEquiv_symm_apply]
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using e.monotone h
  · intro h
    simpa only [e.symm_apply_apply] using e.symm.monotone h

theorem faceProduct_order (e : P ≃o P) (p q : P) :
    polynomialStalkOrderEquiv K e p (faceProduct K p q) = faceProduct K (e p) (e q) := by
  unfold faceProduct
  rw [map_prod, ← stalkVertexSet_order e p q, Finset.prod_map]
  simp only [polynomialStalkOrderEquiv_X, Function.Embedding.coeFn_mk]

theorem faceValue_order (e : P ≃o P) (p q : P) :
    polynomialStalkOrderEquiv K e p (faceValue K p q) = faceValue K (e p) (e q) := by
  by_cases h : q ≤ p
  · rw [faceValue, if_pos h, faceValue, if_pos (e.monotone h), faceProduct_order]
  · have he : ¬ e q ≤ e p := fun hh => h (e.le_iff_le.mp hh)
    rw [faceValue, if_neg h, faceValue, if_neg he, map_zero]

theorem faceRingEvaluation_orderAut (e : P ≃o P) (p : P) (x : FaceRing K hs) :
    faceRingEvaluation K hs (e p) (faceRingOrderAut K hs e x) =
      polynomialStalkOrderEquiv K e p (faceRingEvaluation K hs p x) := by
  have h : ((faceRingEvaluation K hs (e p)).comp (faceRingOrderAut K hs e).toAlgHom).comp
      (Ideal.Quotient.mkₐ K (faceIdeal K hs)) =
      ((polynomialStalkOrderEquiv K e p).toAlgHom.comp (faceRingEvaluation K hs p)).comp
        (Ideal.Quotient.mkₐ K (faceIdeal K hs)) := by
    apply MvPolynomial.algHom_ext
    intro a
    have hg : faceRingEvaluation K hs (e p)
        (faceRingOrderAut K hs e (faceRingGenerator K hs a.val)) =
          polynomialStalkOrderEquiv K e p (faceRingEvaluation K hs p (faceRingGenerator K hs a.val)) := by
      rw [faceRingOrderAut_generator, faceRingEvaluation_generator, faceRingEvaluation_generator]
      exact (faceValue_order K e p a.val).symm
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      faceRingGenerator, faceSymbol_nonzero] using hg
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

theorem booleanFaceInclusion_order (e : P ≃o P) (p : P)
    (F : BooleanFace (FaceVertex p)) :
    (booleanFaceInclusion hs (e p)
      (booleanFaceEmbedding (faceVertexOrderEquiv e p).toEmbedding F)).val =
        e (booleanFaceInclusion hs p F).val := by
  apply faceVertices_injective_below hs (booleanFaceInclusion_le hs (e p) _)
    (e.monotone (booleanFaceInclusion_le hs p F))
  rw [← image_stalkVertexSet (booleanFaceInclusion_le hs (e p) _),
    stalkVertexSet_booleanFaceInclusion,
    ← image_stalkVertexSet (e.monotone (booleanFaceInclusion_le hs p F)),
    ← stalkVertexSet_order e p (booleanFaceInclusion hs p F).val,
    stalkVertexSet_booleanFaceInclusion]
  rfl

theorem barycentricRingEvaluation_orderAut (e : P ≃o P) (p : P)
    (x : BarycentricRing (P := P) K) :
    barycentricRingEvaluation K hs (e p) (barycentricRingOrderAut K e x) =
      barycentricStalkOrderEquiv K e p (barycentricRingEvaluation K hs p x) := by
  have h : ((barycentricRingEvaluation K hs (e p)).comp (barycentricRingOrderAut K e).toAlgHom).comp
      (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)) =
      ((barycentricStalkOrderEquiv K e p).toAlgHom.comp (barycentricRingEvaluation K hs p)).comp
        (Ideal.Quotient.mkₐ K (barycentricIdeal (P := P) K)) := by
    apply MvPolynomial.algHom_ext
    intro a
    have hg : barycentricRingEvaluation K hs (e p)
        (barycentricRingOrderAut K e (barycentricGenerator K a.val)) =
          barycentricStalkOrderEquiv K e p
            (barycentricRingEvaluation K hs p (barycentricGenerator K a.val)) := by
      rw [barycentricRingOrderAut_generator]
      by_cases ha : a.val ≤ p
      · obtain ⟨F, rfl⟩ := (booleanFaceInclusion_range_iff hs p a).mpr ha
        rw [← booleanFaceInclusion_order hs e p F,
          barycentricRingEvaluation_included, barycentricRingEvaluation_included]
        exact (booleanVertexRelabelEquiv_face (K := K) (faceVertexOrderEquiv e p) F).symm
      · have he : ¬ e a.val ≤ e p := fun h => ha (e.le_iff_le.mp h)
        rw [barycentricRingEvaluation_outside K hs (e p) (e a.val) he,
          barycentricRingEvaluation_outside K hs p a.val ha, map_zero]
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk,
      barycentricGenerator, faceSymbol_nonzero] using hg
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

theorem originalComparison_equivariant_of_stalk
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (hE : ∀ (e : P ≃o P) p x, polynomialStalkOrderEquiv K e p (E.component p x) =
      E.component (e p) (barycentricStalkOrderEquiv K e p x))
    (e : P ≃o P) (x : BarycentricRing (P := P) K) :
    faceRingOrderAut K hs e (originalComparison K hs E x) =
      originalComparison K hs E (barycentricRingOrderAut K e x) := by
  apply (faceRingSectionEquiv K hs).injective
  apply Subtype.ext
  funext p
  obtain ⟨q, rfl⟩ := e.surjective p
  simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
  rw [faceRingEvaluation_orderAut, originalComparison_evaluation,
    originalComparison_evaluation, barycentricRingEvaluation_orderAut]
  exact hE e q _

theorem coherentNormalizedParameterComparison_equivariant (d : ℕ)
    (F : StalkLinearFamily (P := P) K)
    (hc : F ∈ coherentStalkFamilySubmodule K)
    (hp : F ∈ parameterStalkFamilySubmodule K)
    (hd : F ∈ gradedStalkFamilySubmodule K) (h₁ : ∀ p, F p 1 = 1)
    (he : ∀ (e : P ≃o P) p x, polynomialStalkOrderEquiv K e p (F p x) =
      F (e p) (barycentricStalkOrderEquiv K e p x))
    (e : P ≃o P) (x : BarycentricRing (P := P) K) :
    faceRingOrderAut K hs e ((coherentNormalizedParameterComparison hs d F hc hp hd h₁).toLinearEquiv x) =
      (coherentNormalizedParameterComparison hs d F hc hp hd h₁).toLinearEquiv
        (barycentricRingOrderAut K e x) :=
  originalComparison_equivariant_of_stalk K hs
    (coherentNormalizedFamilyEquiv hs F hc hp hd h₁) he e x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPositiveTheorem.lean -/
section


section

/-! # The positive direction of Theorem 1.3

The factorial-unit hypothesis first gives a full symmetric template on a
simplex of rank `d`.  Ordinary averaging handles the full-factorial branch;
the integral cyclic construction and relative trace handle prime top rank.
The template is then transported to every actual face of any finite
simplicial poset of maximum rank at most `d`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal

open Classical

structure SymmetricSimplexTemplate (K : Type*) [CommRing K] (d : ℕ) where
  Vertex : Type
  [fintypeVertex : Fintype Vertex]
  card_eq : Fintype.card Vertex = d
  family : StalkLinearFamily (P := Finset Vertex) K
  coherent : family ∈ coherentStalkFamilySubmodule K
  parameter : family ∈ parameterStalkFamilySubmodule K
  graded : family ∈ gradedStalkFamilySubmodule K
  normalized : ∀ s, family s 1 = 1
  symmetric : ∀ e : Equiv.Perm Vertex, stalkFamilyRelabel K (finsetOrderCongr e) family = family

attribute [instance] SymmetricSimplexTemplate.fintypeVertex

theorem exists_symmetric_simplex_template (K : Type*) [CommRing K]
    (d : ℕ) (hd : 1 ≤ d) (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    Nonempty (SymmetricSimplexTemplate K d) := by
  rcases full_factorial_isUnit_or_prime hd hD with hfull | hprime
  · obtain ⟨F, hc, hp, hg, hscalar, he⟩ := exists_integral_factorial_simplex_family (V := Fin d)
    have hm : IsUnit (((Fintype.card (Fin d)).factorial : ℕ) : K) := by simpa using hfull
    obtain ⟨L, hLc, hLp, hLg, hL₁, hLe⟩ := exists_normalized_scalar_extension K
      (simplex_isSimplicialPoset (V := Fin d)) F (Fintype.card (Fin d)).factorial hm hc hp hg hscalar
    exact ⟨{
      Vertex := Fin d
      card_eq := Fintype.card_fin d
      family := L
      coherent := hLc
      parameter := hLp
      graded := hLg
      normalized := hL₁
      symmetric := fun e => hLe (finsetOrderCongr e) (he e) }⟩
  · letI : Fact d.Prime := ⟨hprime⟩
    letI : LinearOrder (ZMod d) := LinearOrder.lift' ZMod.val (ZMod.val_injective d)
    obtain ⟨F, hc, hp, hg, hscalar, he⟩ := exists_integral_prime_symmetric_simplex_family d
    obtain ⟨L, hLc, hLp, hLg, hL₁, hLe⟩ := exists_normalized_scalar_extension K
      (simplex_isSimplicialPoset (V := ZMod d)) F (d - 1).factorial hD hc hp hg hscalar
    exact ⟨{
      Vertex := ZMod d
      card_eq := ZMod.card d
      family := L
      coherent := hLc
      parameter := hLp
      graded := hLg
      normalized := hL₁
      symmetric := fun e => hLe (finsetOrderCongr e) (he e) }⟩

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
include hs

/-- A genuine coherent graded parameter-module comparison, invariant under
every order automorphism.  The full automorphism group therefore works
simultaneously, and restriction to any automorphism-group action follows. -/
theorem exists_coherent_equivariant_parameter_comparison
    (d : ℕ) (hd : 1 ≤ d) (hrank : ∀ p : P, faceRank p ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      (∀ (p : P) (r : ℕ) x,
        E.component p (booleanRankParameter (r + 1) * x) =
          polynomialParameter K p (r + 1) * E.component p x) ∧
      (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) ∧
      (∀ p, E.component p 1 = 1) ∧
      ∀ (e : P ≃o P) (p : P) (x : BarycentricStalk K p),
        polynomialStalkOrderEquiv K e p (E.component p x) =
          E.component (e p) (barycentricStalkOrderEquiv K e p x) := by
  let T := Classical.choice (exists_symmetric_simplex_template K d hd hD)
  have hP : ∀ p : P, faceRank p ≤ Fintype.card T.Vertex := by
    intro p
    rw [T.card_eq]
    exact hrank p
  let F : StalkLinearFamily (P := P) K := symmetricSimplexStalkFamily T.family hP
  have hc : F ∈ coherentStalkFamilySubmodule K :=
    symmetricSimplexStalkFamily_coherent T.family hP T.coherent T.symmetric
  have hp : F ∈ parameterStalkFamilySubmodule K :=
    symmetricSimplexStalkFamily_parameter T.family hP T.parameter
  have hg : F ∈ gradedStalkFamilySubmodule K :=
    symmetricSimplexStalkFamily_graded T.family hP T.graded
  have h₁ : ∀ p, F p 1 = 1 := symmetricSimplexStalkFamily_normalized T.family hP T.normalized
  refine ⟨coherentNormalizedFamilyEquiv hs F hc hp hg h₁, hp, hg, h₁, ?_⟩
  intro e p x
  exact symmetricSimplexStalkFamily_equivariant T.family hP T.coherent T.symmetric e p x

/-- **Theorem 1.3, positive direction.**  All ranks up to `d`, arbitrary
commutative coefficient rings, actual coherent stalk isomorphisms, actual
parameter actions, and every order automorphism are retained. -/
theorem theorem_1_3_positive
    (d : ℕ) (hd : 1 ≤ d) (hrank : ∀ p : P, faceRank p ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      (∀ (p : P) (r : ℕ) x,
        E.component p (booleanRankParameter (r + 1) * x) =
          polynomialParameter K p (r + 1) * E.component p x) ∧
      (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) ∧
      (∀ p, E.component p 1 = 1) ∧
      ∀ (e : P ≃o P) (p : P) (x : BarycentricStalk K p),
        polynomialStalkOrderEquiv K e p (E.component p x) =
          E.component (e p) (barycentricStalkOrderEquiv K e p x) :=
  exists_coherent_equivariant_parameter_comparison K hs d hd hrank hD

/-- The same positive theorem on the original quotient presentations.  The
last conjunct retains the actual coherent family and its evaluation squares,
so the global equivalence includes the paper's compatibility with restriction.
The degree assertion is an equivalence for the usual quotient grading, rather
than a statement about an auxiliary choice of basis. -/
theorem theorem_1_3_positive_original
    (d : ℕ) (hd : 1 ≤ d) (hrank : ∀ p : P, faceRank p ≤ d)
    (hD : IsUnit (((d - 1).factorial : ℕ) : K)) :
    ∃ T : ParameterEquiv (barycentricParameterAction (P := P) K d)
        (faceParameterAction K hs d),
      (∀ n x, T.toLinearEquiv x ∈ usualFaceDegreePiece K hs n ↔
        x ∈ usualBarycentricDegreePiece K n) ∧
      T.toLinearEquiv 1 = 1 ∧
      (∀ (e : P ≃o P) x,
        faceRingOrderAut K hs e (T.toLinearEquiv x) =
          T.toLinearEquiv (barycentricRingOrderAut K e x)) ∧
      ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
        (∀ (p : P) (r : ℕ) x,
          E.component p (booleanRankParameter (r + 1) * x) =
            polynomialParameter K p (r + 1) * E.component p x) ∧
        (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
          (fun a => booleanOrdinaryDegree a.val) n →
            E.component p x ∈ polynomialDegreePiece n) ∧
        (∀ p, E.component p 1 = 1) ∧
        (∀ (e : P ≃o P) p x,
          polynomialStalkOrderEquiv K e p (E.component p x) =
            E.component (e p) (barycentricStalkOrderEquiv K e p x)) ∧
        ∀ x p, faceRingEvaluation K hs p (T.toLinearEquiv x) =
          E.component p (barycentricRingEvaluation K hs p x) := by
  obtain ⟨E, hp, hg, h₁, he⟩ :=
    exists_coherent_equivariant_parameter_comparison K hs d hd hrank hD
  let T := originalParameterComparison K hs d E hp
  have hdegree : ∀ (a b : StandardFaceIndex P),
      standardOrdinaryDegree b ≠ standardOrdinaryDegree a →
      (standardFaceBasis K hs).repr
        (T.toLinearEquiv (barycentricGlobalStandardBasis K a)) b = 0 :=
    originalComparison_degree K hs E
      (fun p => hasStandardDegree_of_ordinary_degree K hs p (E.component p).toLinearMap (hg p))
  refine ⟨T, ?_, ?_, ?_, E, hp, hg, h₁, he, ?_⟩
  · intro n x
    rw [usualFaceDegreePiece_eq, usualBarycentricDegreePiece_eq]
    exact basisOrdinaryDegreePiece_equiv_iff (barycentricGlobalStandardBasis K)
      (standardFaceBasis K hs) standardOrdinaryDegree T.toLinearEquiv hdegree n x
  · apply (faceRingSectionEquiv K hs).injective
    apply Subtype.ext
    funext p
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply]
    change faceRingEvaluation K hs p (originalComparison K hs E 1) =
      faceRingEvaluation K hs p 1
    rw [originalComparison_evaluation]
    exact (congrArg (E.component p) (map_one (barycentricRingEvaluation K hs p))).trans
      ((h₁ p).trans (map_one (faceRingEvaluation K hs p)).symm)
  · exact originalComparison_equivariant_of_stalk K hs E he
  · exact originalComparison_evaluation K hs E

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ObstructionEigenfunctional.lean -/
section

section
/-! # The modular obstruction without specialization machinery

A parameter-eigenfunctional on the polynomial ring, evaluated at a fixed root
assignment, cannot be transported to a ring whose active-parameter product is
a sum of monomials freely permuted in modular characteristic. This argument
works over the original coefficient ring; the functional may take values in
a polynomial ring over a residue field. It does not assume that an isomorphism
preserves constants, multiplication, a grading, or face restrictions.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal
open Classical Finset

variable {G T I K R B L : Type*}
  [Group G] [Fintype G] [Fintype T] [MulAction G T]
  [CommRing K] [CommRing R] [Algebra K R] [CommRing B] [Algebra K B]
  [CommRing L] [IsDomain L]

/-- The exact algebraic contradiction used for the prime-cycle obstruction.
All the expansion and action hypotheses are instantiated by actual polynomial
and Stanley--Reisner rings in `PrimeCycleObstruction`. -/
theorem no_equiv_of_free_parameter_expansion
    (a : I → R) (b : I → B) (s : Finset I)
    (ρR : G → R →ₐ[K] R) (ρB : G → B →ₐ[K] B)
    (ev : R →+* L) (hev : ∀ g x, ev (ρR g x) = ev x)
    (m : T → B) (hm : ∀ g t, m (g • t) = ρB g (m t))
    (hprod : (∏ i ∈ s, b i) = ∑ t, m t)
    (hactive : ∀ i ∈ s, ev (a i) ≠ 0)
    (hfree : ∀ t : T, Function.Injective (fun g : G => g • t))
    (horder : (Fintype.card G : L) = 0)
    (f : R ≃ₗ[K] B)
    (hparameter : ∀ i x, f (a i * x) = b i * f x)
    (hequivariant : ∀ g x, f (ρR g x) = ρB g (f x)) : False := by
  let ℓ : B →+ L := ev.toAddMonoidHom.comp f.symm.toLinearMap.toAddMonoidHom
  have hinvParameter : ∀ i x, f.symm (b i * x) = a i * f.symm x := by
    intro i x
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hparameter, LinearEquiv.apply_symm_apply]
  have hinvAction : ∀ g x, f.symm (ρB g x) = ρR g (f.symm x) := by
    intro g x
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hequivariant, LinearEquiv.apply_symm_apply]
  have hℓparameter : ∀ i x, ℓ (b i * x) = ev (a i) * ℓ x := by
    intro i x
    change ev (f.symm (b i * x)) = ev (a i) * ev (f.symm x)
    rw [hinvParameter, map_mul]
  have hℓaction : ∀ g x, ℓ (ρB g x) = ℓ x := by
    intro g x
    change ev (f.symm (ρB g x)) = ev (f.symm x)
    rw [hinvAction, hev]
  have hvector : ∀ g, ρB g (f 1) = f 1 := by
    intro g
    rw [← hequivariant, map_one]
  have hvalue : ℓ (f 1) = 1 := by
    change ev (f.symm (f 1)) = 1
    rw [LinearEquiv.symm_apply_apply, map_one]
  have hprodValue : ∀ t : Finset I,
      ℓ ((∏ i ∈ t, b i) * f 1) = ∏ i ∈ t, ev (a i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using hvalue
    | @insert i t hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_assoc, hℓparameter, ih]
  have hconst : ∀ (g : G) (t : T), ℓ (m (g • t) * f 1) = ℓ (m t * f 1) := by
    intro g t
    calc
      ℓ (m (g • t) * f 1) = ℓ (ρB g (m t) * ρB g (f 1)) := by
        rw [hm, hvector]
      _ = ℓ (ρB g (m t * f 1)) := congrArg ℓ (map_mul (ρB g) _ _).symm
      _ = ℓ (m t * f 1) := hℓaction g _
  have hzero : ℓ ((∏ i ∈ s, b i) * f 1) = 0 := by
    rw [hprod, Finset.sum_mul, map_sum]
    exact sum_eq_zero_of_free_action hfree horder (fun t => ℓ (m t * f 1)) hconst
  rw [hprodValue] at hzero
  exact (Finset.prod_ne_zero_iff.mpr hactive) hzero

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ColoredFlagCore.lean -/
section

section
/-! # Original-ring flag indexing and literal vertex actions

Only the definitions used by the unrestricted eigenfunctional obstruction
are collected here. The earlier quotient-fibre development remains in
`ColorFiberComponents.lean` and `ColoredAutomorphisms.lean` as an inactive
draft; the negative theorem does not depend on it. Each declaration body
below is copied exactly from those sources, with its original section
parameters retained. Extraction hashes are recorded in the audit manifest.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ProperlyColoredComplex
open Classical Finset MvPolynomial
section General
variable {V C K G : Type*} [Fintype V] [Fintype C] [CommRing K] [Group G]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C) (K)

def colorRename (e : Equiv.Perm V)
    (hface : ∀ s, D.face (s.image e) ↔ D.face s) : D.Ring K →ₐ[K] D.Ring K := by
  let f := (Ideal.Quotient.mkₐ K (forbiddenIdeal D.allowed)).comp (MvPolynomial.rename e)
  apply Ideal.Quotient.liftₐ (forbiddenIdeal D.allowed) f
  have hh : forbiddenIdeal D.allowed ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk (forbiddenIdeal D.allowed)
      (MvPolynomial.rename e (MvPolynomial.monomial a (1 : K))) = 0
    rw [MvPolynomial.rename_monomial]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    refine ⟨a.mapDomain e, ?_, rfl⟩
    intro h
    apply ha
    change D.face (a.mapDomain e).support at h
    rw [Finsupp.support_mapDomain_of_nonneg (fun _ => Nat.zero_le _)] at h
    exact (hface a.support).mp h
  exact fun p hp => hh hp

@[simp] theorem colorRename_mk (e : Equiv.Perm V)
    (hface : ∀ s, D.face (s.image e) ↔ D.face s) (p : MvPolynomial V K) :
    D.colorRename K e hface (Ideal.Quotient.mk (forbiddenIdeal D.allowed) p) =
      Ideal.Quotient.mk (forbiddenIdeal D.allowed) (MvPolynomial.rename e p) := rfl

def colorFiberEquiv (e : Equiv.Perm V) (hcolor : ∀ v, D.color (e v) = D.color v) (i : C) :
    {v : V // D.color v = i} ≃ {v : V // D.color v = i} where
  toFun v := ⟨e v.val, (hcolor v.val).trans v.property⟩
  invFun v := ⟨e.symm v.val, by
    have hh := hcolor (e.symm v.val)
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

variable {K}

abbrev ActiveColor (c : C → K) := {i : C // c i ≠ 0}

abbrev FiberAssignment (c : C → K) :=
  (i : ActiveColor c) → {v : V // D.color v = i.val}

def assignmentVertices (c : C → K) (a : D.FiberAssignment c) : Finset V :=
  Finset.univ.image (fun i => (a i).val)

def assignmentExponents (c : C → K) (a : D.FiberAssignment c) : V →₀ ℕ :=
  ∑ i : ActiveColor c, Finsupp.single (a i).val 1

theorem assignmentExponents_support (c : C → K) (a : D.FiberAssignment c) :
    (D.assignmentExponents c a).support = D.assignmentVertices c a := by
  ext v
  simp only [assignmentExponents, Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
    Finsupp.single_apply, assignmentVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h (Finset.sum_eq_zero (fun i hi => by rw [if_neg (hn i)]))
  · rintro ⟨i, hi⟩
    have hp : 0 < ∑ j : ActiveColor c, if (a j).val = v then 1 else 0 := by
      apply lt_of_lt_of_le (show 0 < (if (a i).val = v then 1 else 0 : ℕ) by simp [hi])
      exact Finset.single_le_sum
        (f := fun j : ActiveColor c => if (a j).val = v then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.ne_of_gt hp

end General

section Field
variable {V C K G : Type*} [Fintype V] [Fintype C] [Field K] [Group G]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C)
variable (ρ : G →* Equiv.Perm V)
  (hface : ∀ g s, D.face (s.image (ρ g)) ↔ D.face s)
  (hcolor : ∀ g v, D.color (ρ g v) = D.color v)

abbrev ActiveFlag (c : C → K) :=
  {a : D.FiberAssignment c // D.face (D.assignmentVertices c a)}

def assignmentRename (c : C → K) (e : Equiv.Perm V)
    (hcolor : ∀ v, D.color (e v) = D.color v) (a : D.FiberAssignment c) : D.FiberAssignment c :=
  fun i => D.colorFiberEquiv e hcolor i.val (a i)

theorem assignmentRename_vertices (c : C → K) (e : Equiv.Perm V)
    (hcolor : ∀ v, D.color (e v) = D.color v) (a : D.FiberAssignment c) :
    D.assignmentVertices c (D.assignmentRename c e hcolor a) =
      (D.assignmentVertices c a).image e := by
  simp only [assignmentVertices, assignmentRename, colorFiberEquiv, Finset.image_image]
  rfl

def activeFlagAction (c : C → K) : MulAction G (D.ActiveFlag c) where
  smul g a := ⟨D.assignmentRename c (ρ g) (hcolor g) a.val,
    by
      rw [D.assignmentRename_vertices]
      exact (hface g (D.assignmentVertices c a.val)).mpr a.property⟩
  one_smul a := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change ρ 1 ((a.val i).val) = (a.val i).val
    rw [ρ.map_one]
    rfl
  mul_smul g h a := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change ρ (g * h) ((a.val i).val) = ρ g (ρ h ((a.val i).val))
    rw [ρ.map_mul]
    rfl

end Field
end FourPapers.Universal.ProperlyColoredComplex

end
end
end

/- BEGIN FourPapers/Universal/ObstructionExpansion.lean -/
section

section
/-! # Active-rank expansion in the original face ring

The coefficients used to select ranks may belong to a different field from
the original coefficient ring. No base change of the original ring is made.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal.ProperlyColoredComplex
open Classical Finset MvPolynomial

variable {V C K L : Type*} [Fintype V] [Fintype C] [CommRing K] [Field L]
variable (D : FourPapers.Universal.ProperlyColoredComplex V C) (K)

def assignmentMonomial (c : C → L) (a : D.FiberAssignment c) : D.Ring K :=
  ∏ i : ActiveColor c, Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X (a i).val)

theorem assignmentMonomial_eq_monomial (c : C → L) (a : D.FiberAssignment c) :
    D.assignmentMonomial K c a = D.monomial K (D.assignmentExponents c a) := by
  rw [assignmentMonomial, ← map_prod]
  congr 1
  rw [assignmentExponents, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro i hi
  rfl

theorem assignmentMonomial_forbidden (c : C → L) (a : D.FiberAssignment c)
    (ha : ¬ D.face (D.assignmentVertices c a)) : D.assignmentMonomial K c a = 0 := by
  rw [D.assignmentMonomial_eq_monomial K c a]
  apply D.monomial_eq_zero_of_forbidden K
  unfold allowed
  rwa [D.assignmentExponents_support]

theorem sum_assignmentMonomial (c : C → L) :
    (∑ a : D.FiberAssignment c, D.assignmentMonomial K c a) =
      ∏ i : ActiveColor c, D.colorParameter K i.val := by
  unfold assignmentMonomial
  rw [← Fintype.prod_sum (fun (i : ActiveColor c)
    (v : {v : V // D.color v = i.val}) =>
      Ideal.Quotient.mk (forbiddenIdeal (K := K) D.allowed) (X v.val))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Finset.sum_subtype (Finset.univ.filter (fun v => D.color v = i.val))
    (fun v => by simp) (fun v =>
      Ideal.Quotient.mk (forbiddenIdeal D.allowed) (X v : MvPolynomial V K))).symm

/-- The product of active color sums is the sum of exactly the allowed flags.
This is an identity in the original Stanley--Reisner quotient. -/
theorem sum_activeFlagMonomial (c : C → L) :
    (∑ a : D.ActiveFlag c, D.assignmentMonomial K c a.val) =
      ∏ i : ActiveColor c, D.colorParameter K i.val := by
  rw [← D.sum_assignmentMonomial K c]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : D.FiberAssignment c =>
    D.face (D.assignmentVertices c a))) (fun a => by simp)]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hn
  exact D.assignmentMonomial_forbidden K c a (by simpa using hn)

/-- The same finite identity with explicitly supplied enumerations.  This
avoids unfolding large finite function spaces when a specialized application
uses a different, propositionally equal `Fintype` instance. -/
theorem sum_activeFlagMonomial_withFintypes (c : C → L)
    (ft : Fintype (D.ActiveFlag c)) (fi : Fintype (ActiveColor c)) :
    (∑ a ∈ @Finset.univ (D.ActiveFlag c) ft, D.assignmentMonomial K c a.val) =
      ∏ i ∈ @Finset.univ (ActiveColor c) fi, D.colorParameter K i.val := by
  have hi : fi = Subtype.fintype (fun i : C => c i ≠ 0) := Subsingleton.elim _ _
  subst fi
  have ht : ft = Subtype.fintype
      (fun a : D.FiberAssignment c => D.face (D.assignmentVertices c a)) := Subsingleton.elim _ _
  subst ft
  exact D.sum_activeFlagMonomial K c

theorem colorRename_assignmentMonomial (c : C → L) (e : Equiv.Perm V)
    (hface : ∀ s, D.face (s.image e) ↔ D.face s)
    (hcolor : ∀ v, D.color (e v) = D.color v) (a : D.FiberAssignment c) :
    D.colorRename K e hface (D.assignmentMonomial K c a) =
      D.assignmentMonomial K c (D.assignmentRename c e hcolor a) := by
  rw [assignmentMonomial, map_prod, assignmentMonomial]
  apply Finset.prod_congr rfl
  intro i hi
  rw [D.colorRename_mk K e hface, MvPolynomial.rename_X]
  rfl

end FourPapers.Universal.ProperlyColoredComplex

end
end
end

/- BEGIN FourPapers/Universal/ObstructionBoolean.lean -/
section

section
/-! # The actual Boolean order complex and its vertex permutations -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable {V K : Type*} [Fintype V] [CommRing K]

local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq (BooleanFace V) := Classical.decEq _

/-- The properly rank-colored order complex of the full Boolean simplex.
Its monomial quotient is definitionally the existing barycentric ring. -/
def booleanColoredComplex (V : Type*) [Fintype V] :
    ProperlyColoredComplex (BooleanFace V) (Fin (Fintype.card V)) where
  face s := ∀ F ∈ s, ∀ G ∈ s, F.val ⊆ G.val ∨ G.val ⊆ F.val
  downward := by
    intro s t hst ht F hF G hG
    exact ht F (hst hF) G (hst hG)
  color := BooleanFace.color
  proper s hs F hF G hG he := by
    apply Subtype.ext
    have hc := BooleanFace.card_eq_of_color_eq he
    rcases hs F hF G hG with h | h
    · exact Finset.eq_of_subset_of_card_le h hc.ge
    · exact (Finset.eq_of_subset_of_card_le h hc.le).symm

theorem booleanColored_ring_eq :
    (booleanColoredComplex V).Ring K = BooleanBarycentricRing V K := rfl

theorem booleanColored_colorParameter (i : Fin (Fintype.card V)) :
    (booleanColoredComplex V).colorParameter K i = colorSum (K := K) i := by
  unfold ProperlyColoredComplex.colorParameter colorSum facesOfColor faceVariable
  apply Finset.sum_congr
  · ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · intro F hF
    rfl

def booleanFacePermutation (e : Equiv.Perm V) : Equiv.Perm (BooleanFace V) where
  toFun F := ⟨F.val.image e, F.property.image e⟩
  invFun F := ⟨F.val.image e.symm, F.property.image e.symm⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id]
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]

@[simp] theorem booleanFacePermutation_val (e : Equiv.Perm V) (F : BooleanFace V) :
    (booleanFacePermutation e F).val = F.val.image e := rfl

theorem booleanFacePermutation_color (e : Equiv.Perm V) (F : BooleanFace V) :
    BooleanFace.color (booleanFacePermutation e F) = BooleanFace.color F := by
  apply Fin.ext
  change (F.val.image e).card - 1 = F.val.card - 1
  rw [Finset.card_image_of_injective _ e.injective]

theorem permutation_image_subset_iff (e : Equiv.Perm V) (s t : Finset V) :
    s.image e ⊆ t.image e ↔ s ⊆ t := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    exact e.injective he ▸ hw
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨w, h hw, rfl⟩

theorem booleanFacePermutation_face (e : Equiv.Perm V) (s : Finset (BooleanFace V)) :
    (booleanColoredComplex V).face (s.image (booleanFacePermutation e)) ↔
      (booleanColoredComplex V).face s := by
  constructor
  · intro h F hF G hG
    have hh := h (booleanFacePermutation e F) (Finset.mem_image.mpr ⟨F, hF, rfl⟩)
      (booleanFacePermutation e G) (Finset.mem_image.mpr ⟨G, hG, rfl⟩)
    simpa only [booleanFacePermutation_val, permutation_image_subset_iff] using hh
  · intro h F hF G hG
    obtain ⟨F₀, hF₀, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨G₀, hG₀, rfl⟩ := Finset.mem_image.mp hG
    simpa only [booleanFacePermutation_val, permutation_image_subset_iff] using h F₀ hF₀ G₀ hG₀

def booleanFacePermHom : Equiv.Perm V →* Equiv.Perm (BooleanFace V) where
  toFun := booleanFacePermutation
  map_one' := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change F.val.image id = F.val
    exact Finset.image_id
  map_mul' e f := by
    apply Equiv.ext
    intro F
    apply Subtype.ext
    change F.val.image (e * f) = (F.val.image f).image e
    rw [Finset.image_image]
    rfl

/-- Relabeling the genuine quotient ring by a vertex permutation. -/
def booleanRename (K : Type*) [CommRing K] (e : Equiv.Perm V) :
    BooleanBarycentricRing V K →ₐ[K] BooleanBarycentricRing V K :=
  (booleanColoredComplex V).colorRename K (booleanFacePermutation e)
    (booleanFacePermutation_face e)

theorem booleanRename_faceVariable (e : Equiv.Perm V) (F : BooleanFace V) :
    booleanRename K e (faceVariable (K := K) F) =
      faceVariable (K := K) (booleanFacePermutation e F) := by
  change (booleanColoredComplex V).colorRename K (booleanFacePermutation e)
    (booleanFacePermutation_face e) (Ideal.Quotient.mk _ (X F)) = _
  rw [(booleanColoredComplex V).colorRename_mk K (booleanFacePermutation e)
    (booleanFacePermutation_face e), MvPolynomial.rename_X]
  rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimeCycleCoefficients.lean -/
section

section
/-! # The actual generic character for the prime-cycle obstruction

The moved roots are all one; the fixed roots are algebraically independent
variables.  The parameter values are the coefficients of
`(1+T^p) ∏(1+b_i T)`, interpreted in the fraction field of the polynomial
ring.  A coefficient of a specified squarefree monomial proves exactly which
ranks are active, in every characteristic p.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
section GenericCoefficient
variable {k : Type*} [CommRing k]

def fiberFaceExponent {V : Type*} (s : Finset V) : V →₀ ℕ :=
  ∑ v ∈ s, Finsupp.single v 1

@[simp] theorem fiberFaceExponent_apply {V : Type*} (s : Finset V) (v : V) :
    fiberFaceExponent s v = if v ∈ s then 1 else 0 := by
  simp [fiberFaceExponent, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem fiberFaceExponent_injective {V : Type*} :
    Function.Injective (fiberFaceExponent (V := V)) := by
  intro s t h
  ext v
  have hh := congrArg (fun a : V →₀ ℕ => a v) h
  simp only [fiberFaceExponent_apply] at hh
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp_all

/-- The specified monomial occurs once, over any coefficient ring. -/
theorem esymm_face_coefficient {V : Type*} [Fintype V] (s : Finset V) (n : ℕ) :
    (MvPolynomial.esymm V k n).coeff (fiberFaceExponent s) =
      if s.card = n then 1 else 0 := by
  rw [MvPolynomial.esymm_eq_sum_monomial, MvPolynomial.coeff_sum]
  change (∑ t ∈ Finset.powersetCard n Finset.univ,
    (MvPolynomial.monomial (fiberFaceExponent t) (1 : k)).coeff (fiberFaceExponent s)) = _
  simp only [MvPolynomial.coeff_monomial, fiberFaceExponent_injective.eq_iff]
  simp [Finset.mem_powersetCard]

theorem esymm_eq_zero_of_card_lt {V : Type*} [Fintype V] (n : ℕ) (hn : Fintype.card V < n) :
    MvPolynomial.esymm V k n = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr (by simpa using hn), Finset.sum_empty]

end GenericCoefficient

variable (p r : ℕ) (k : Type*) [CommRing k]

def primeFiberCoefficient (n : ℕ) : MvPolynomial (Fin r) k :=
  MvPolynomial.esymm (Fin r) k n +
    if p ≤ n then MvPolynomial.esymm (Fin r) k (n - p) else 0

theorem primeFiberCoefficient_nonzero_iff [Nontrivial k] (hp : 0 < p) (n : ℕ) :
    primeFiberCoefficient p r k n ≠ 0 ↔ n ≤ r ∨ (p ≤ n ∧ n ≤ p + r) := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    rw [primeFiberCoefficient, esymm_eq_zero_of_card_lt n (by simpa using hn.1)]
    by_cases hp' : p ≤ n
    · rw [if_pos hp', esymm_eq_zero_of_card_lt (n - p) (by
        have hh := hn.2 hp'
        simp only [Fintype.card_fin]
        omega), zero_add]
    · rw [if_neg hp', add_zero]
  · rintro (hn | ⟨hp', hn⟩)
    · obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin r))) (by simpa using hn)
      intro hz
      have he := congrArg (fun f : MvPolynomial (Fin r) k => f.coeff (fiberFaceExponent s)) hz
      rw [primeFiberCoefficient, MvPolynomial.coeff_add, esymm_face_coefficient, hc,
        if_pos rfl, MvPolynomial.coeff_zero] at he
      by_cases hp' : p ≤ n
      · rw [if_pos hp', esymm_face_coefficient, hc, if_neg (by omega), add_zero] at he
        exact one_ne_zero he
      · simp only [if_neg hp', MvPolynomial.coeff_zero, Finsupp.zero_apply, add_zero] at he
        exact one_ne_zero he
    · obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin r))) (show n - p ≤ (Finset.univ : Finset (Fin r)).card by
          rw [Finset.card_univ, Fintype.card_fin]
          omega)
      intro hz
      have he := congrArg (fun f : MvPolynomial (Fin r) k => f.coeff (fiberFaceExponent s)) hz
      rw [primeFiberCoefficient, MvPolynomial.coeff_add, if_pos hp',
        esymm_face_coefficient, esymm_face_coefficient, hc, if_neg (by omega),
        if_pos rfl, zero_add, MvPolynomial.coeff_zero] at he
      exact one_ne_zero he

theorem primeFiberCoefficient_active [Nontrivial k] [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    primeFiberCoefficient p r k n ≠ 0 ↔ n ∈ primeCycleActiveRanks p r := by
  rw [primeFiberCoefficient_nonzero_iff p r k (Fact.out : p.Prime).pos]
  simp only [primeCycleActiveRanks, Finset.mem_union, Finset.mem_Icc]
  omega

def polynomialPrimeRoots [Fact p.Prime] : PrimeCycleVertex p r → MvPolynomial (Fin r) k :=
  Sum.elim (fun _ => 1) MvPolynomial.X

def fixedRootPolynomial : Polynomial (MvPolynomial (Fin r) k) :=
  ∏ b : Fin r, (Polynomial.X + Polynomial.C (MvPolynomial.X b))

theorem fixedRootPolynomial_coefficient (n : ℕ) (hn : n ≤ r) :
    (fixedRootPolynomial r k).coeff n = MvPolynomial.esymm (Fin r) k (r - n) := by
  have hh := Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin r))
    (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k) (k := n) (by simpa using hn)
  simpa only [fixedRootPolynomial, Finset.card_univ, Fintype.card_fin, MvPolynomial.esymm] using hh

theorem fixedRootPolynomial_natDegree [Nontrivial k] :
    (fixedRootPolynomial r k).natDegree = r := by
  have hh := Polynomial.natDegree_finsetProd_X_sub_C_eq_card
    (Finset.univ : Finset (Fin r)) (fun b => -(MvPolynomial.X b : MvPolynomial (Fin r) k))
  simpa only [fixedRootPolynomial, map_neg, sub_neg_eq_add, Finset.card_univ,
    Fintype.card_fin] using hh

theorem fixedRootPolynomial_coefficient_zero [Nontrivial k] (n : ℕ) (hn : r < n) :
    (fixedRootPolynomial r k).coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rwa [fixedRootPolynomial_natDegree]

theorem primeRootPolynomial_factorization [Fact p.Prime] [CharP k p] :
    (∏ v : PrimeCycleVertex p r,
      (Polynomial.X + Polynomial.C (polynomialPrimeRoots p r k v))) =
      (Polynomial.X ^ p + 1) * fixedRootPolynomial r k := by
  rw [Fintype.prod_sum_type]
  simp only [polynomialPrimeRoots, Sum.elim_inl, Sum.elim_inr, map_one,
    Finset.prod_const, Finset.card_univ, ZMod.card, fixedRootPolynomial]
  rw [add_pow_char, one_pow]

/-- The displayed generic coefficients are the actual elementary symmetric
parameter values at the fixed root assignment. -/
theorem primeRoots_esymm [Nontrivial k] [Fact p.Prime] [CharP k p]
    (n : ℕ) (hn : n ≤ p + r) :
    MvPolynomial.aeval (polynomialPrimeRoots p r k)
      (MvPolynomial.esymm (PrimeCycleVertex p r) k n) = primeFiberCoefficient p r k n := by
  have hcard : Fintype.card (PrimeCycleVertex p r) = p + r := by
    rw [Fintype.card_sum, ZMod.card, Fintype.card_fin]
  have he := Finset.prod_X_add_C_coeff (Finset.univ : Finset (PrimeCycleVertex p r))
    (polynomialPrimeRoots p r k) (k := p + r - n) (by
      rw [Finset.card_univ, hcard]
      omega)
  have he' : MvPolynomial.aeval (polynomialPrimeRoots p r k)
      (MvPolynomial.esymm (PrimeCycleVertex p r) k n) =
      (∏ v : PrimeCycleVertex p r,
        (Polynomial.X + Polynomial.C (polynomialPrimeRoots p r k v))).coeff (p + r - n) := by
    rw [he]
    rw [MvPolynomial.esymm, map_sum]
    simp only [map_prod, MvPolynomial.aeval_X, Finset.card_univ, hcard,
      Nat.sub_sub_self hn]
  rw [he', primeRootPolynomial_factorization, add_mul, one_mul, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', primeFiberCoefficient]
  have hleft : (if p ≤ p + r - n then
      (fixedRootPolynomial r k).coeff (p + r - n - p) else 0) =
      MvPolynomial.esymm (Fin r) k n := by
    by_cases hnr : n ≤ r
    · rw [if_pos (by omega), fixedRootPolynomial_coefficient r k _ (by omega)]
      congr 1
      omega
    · rw [if_neg (by omega), esymm_eq_zero_of_card_lt n (by simpa using Nat.lt_of_not_ge hnr)]
  rw [hleft]
  congr 1
  by_cases hpn : p ≤ n
  · rw [if_pos hpn, fixedRootPolynomial_coefficient r k _ (by omega)]
    congr 1
    omega
  · rw [if_neg hpn, fixedRootPolynomial_coefficient_zero r k _ (by omega)]

section Field
variable [IsDomain k]
abbrev PrimeFiberField := FractionRing (MvPolynomial (Fin r) k)

def primeFiberCharacter (n : ℕ) : PrimeFiberField r k :=
  algebraMap (MvPolynomial (Fin r) k) (PrimeFiberField r k) (primeFiberCoefficient p r k n)

theorem primeFiberCharacter_active [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    primeFiberCharacter p r k n ≠ 0 ↔ n ∈ primeCycleActiveRanks p r := by
  have he : primeFiberCharacter p r k n = 0 ↔ primeFiberCoefficient p r k n = 0 := by
    change algebraMap (MvPolynomial (Fin r) k) (PrimeFiberField r k) _ = 0 ↔ _
    rw [← map_zero (algebraMap (MvPolynomial (Fin r) k) (PrimeFiberField r k))]
    exact (IsFractionRing.injective (MvPolynomial (Fin r) k) (PrimeFiberField r k)).eq_iff
  exact (not_congr he).trans (primeFiberCoefficient_active p r k hn)

end Field
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimeCycleFlagAction.lean -/
section

section
/-! # Free prime-cycle action on the actual active-flag indexing set -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial ProperlyColoredComplex

variable (p r : ℕ) [Fact p.Prime] (k : Type*) [Field k]

local instance (priority := 2000) : DecidableEq (PrimeCycleVertex p r) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace (PrimeCycleVertex p r)) :=
  Classical.decEq _

abbrev PrimeBooleanComplex := booleanColoredComplex (PrimeCycleVertex p r)

theorem primeCycleVertex_card : Fintype.card (PrimeCycleVertex p r) = p + r := by
  rw [Fintype.card_sum, ZMod.card, Fintype.card_fin]

theorem primeActiveRanks_pos_bound {n : ℕ} (hn : n ∈ primeCycleActiveRanks p r) :
    0 < n ∧ n ≤ p + r := by
  have hp := (Fact.out : p.Prime).pos
  simp only [primeCycleActiveRanks, Finset.mem_union, Finset.mem_Icc] at hn
  omega

/-- A mask for the active ranks. Its values are only used to select ranks;
the actual eigencharacter is the generic polynomial character. -/
def primeRankMask (i : Fin (Fintype.card (PrimeCycleVertex p r))) : k :=
  if i.val + 1 ∈ primeCycleActiveRanks p r then 1 else 0

@[simp] theorem primeRankMask_active (i : Fin (Fintype.card (PrimeCycleVertex p r))) :
    primeRankMask p r k i ≠ 0 ↔ i.val + 1 ∈ primeCycleActiveRanks p r := by
  simp [primeRankMask]

def primeRankIndex (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    ActiveColor (primeRankMask p r k) := by
  have hi := primeActiveRanks_pos_bound p r i.property
  refine ⟨⟨i.val - 1, by rw [primeCycleVertex_card]; omega⟩, ?_⟩
  rw [primeRankMask_active]
  have he : i.val - 1 + 1 = i.val := by omega
  simpa only [he] using i.property

@[simp] theorem primeRankIndex_succ (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    (primeRankIndex p r k i).val.val + 1 = i.val := by
  have hi := (primeActiveRanks_pos_bound p r i.property).1
  change i.val - 1 + 1 = i.val
  omega

def primeActiveRankFace
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k))
    (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) : Finset (PrimeCycleVertex p r) :=
  (a.val (primeRankIndex p r k i)).val.val

theorem primeActiveRankFace_card
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k))
    (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    (primeActiveRankFace p r k a i).card = i.val := by
  have h := congrArg Fin.val (a.val (primeRankIndex p r k i)).property
  have hs := BooleanFace.color_succ (a.val (primeRankIndex p r k i)).val
  change ((a.val (primeRankIndex p r k i)).val.val).card = i.val
  change (BooleanFace.color (a.val (primeRankIndex p r k i)).val).val =
    (primeRankIndex p r k i).val.val at h
  rw [h, primeRankIndex_succ] at hs
  exact hs.symm

def primeActiveRankFlag
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k)) :
    RankFlag (PrimeCycleVertex p r) (primeCycleActiveRanks p r) where
  face := primeActiveRankFace p r k a
  card := primeActiveRankFace_card p r k a
  nested i j hij := by
    have hi : (a.val (primeRankIndex p r k i)).val ∈
        (PrimeBooleanComplex p r).assignmentVertices (primeRankMask p r k) a.val :=
      Finset.mem_image.mpr ⟨primeRankIndex p r k i, Finset.mem_univ _, rfl⟩
    have hj : (a.val (primeRankIndex p r k j)).val ∈
        (PrimeBooleanComplex p r).assignmentVertices (primeRankMask p r k) a.val :=
      Finset.mem_image.mpr ⟨primeRankIndex p r k j, Finset.mem_univ _, rfl⟩
    rcases a.property _ hi _ hj with h | h
    · exact h
    · have he : primeActiveRankFace p r k a j = primeActiveRankFace p r k a i :=
        Finset.eq_of_subset_of_card_le h (by
          rw [primeActiveRankFace_card, primeActiveRankFace_card]
          exact hij)
      rw [he]

def primeBooleanPermutation : PrimeCycleGroup p →* Equiv.Perm (BooleanFace (PrimeCycleVertex p r)) :=
  booleanFacePermHom.comp (primeCyclePermutation p r)

theorem primeBooleanPermutation_face (g : PrimeCycleGroup p)
    (s : Finset (BooleanFace (PrimeCycleVertex p r))) :
    (PrimeBooleanComplex p r).face (s.image (primeBooleanPermutation p r g)) ↔
      (PrimeBooleanComplex p r).face s :=
  booleanFacePermutation_face (primeCyclePermutation p r g) s

theorem primeBooleanPermutation_color (g : PrimeCycleGroup p)
    (F : BooleanFace (PrimeCycleVertex p r)) :
    (PrimeBooleanComplex p r).color (primeBooleanPermutation p r g F) =
      (PrimeBooleanComplex p r).color F :=
  booleanFacePermutation_color (primeCyclePermutation p r g) F

def primeFlagAction : MulAction (PrimeCycleGroup p)
    ((PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k)) :=
  (PrimeBooleanComplex p r).activeFlagAction (primeBooleanPermutation p r)
    (primeBooleanPermutation_face p r) (primeBooleanPermutation_color p r)
    (primeRankMask p r k)

@[simp] theorem primeFlagAction_val (g : PrimeCycleGroup p)
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k)) :
    ((primeFlagAction p r k).smul g a).val =
      (PrimeBooleanComplex p r).assignmentRename (primeRankMask p r k)
        (primeBooleanPermutation p r g) (primeBooleanPermutation_color p r g) a.val := rfl

theorem primeBooleanRename_eq {K : Type*} [CommRing K] (g : PrimeCycleGroup p) :
    booleanRename K (primeCyclePermutation p r g) =
      (PrimeBooleanComplex p r).colorRename K (primeBooleanPermutation p r g)
        (primeBooleanPermutation_face p r g) := rfl

theorem primeFlagAction_faces (g : PrimeCycleGroup p)
    (a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k))
    (i : {n : ℕ // n ∈ primeCycleActiveRanks p r}) :
    (primeActiveRankFlag p r k ((primeFlagAction p r k).smul g a)).face i =
      ((primeActiveRankFlag p r k a).face i).image (primeCyclePermutation p r g) := rfl

/-- The exact active-flag indexing set used in the original-ring expansion
has a free action, for every prime and every positive number of fixed vertices. -/
theorem primeFlagAction_free (hr : 0 < r) :
    ∀ a : (PrimeBooleanComplex p r).ActiveFlag (primeRankMask p r k),
      Function.Injective (fun g : PrimeCycleGroup p => (primeFlagAction p r k).smul g a) := by
  letI := primeFlagAction p r k
  intro a g h heq
  change g • a = h • a at heq
  have hfix : (h⁻¹ * g) • a = a := by
    rw [mul_smul, heq, inv_smul_smul]
  have hunit : h⁻¹ * g = 1 := by
    by_contra hg
    apply primeCycleActiveFlag_not_fixed p r hr (primeActiveRankFlag p r k a) (h⁻¹ * g) hg
    intro i
    have hh := congrArg (fun b => (primeActiveRankFlag p r k b).face i) hfix
    change (primeActiveRankFlag p r k ((primeFlagAction p r k).smul (h⁻¹ * g) a)).face i =
      (primeActiveRankFlag p r k a).face i at hh
    rw [primeFlagAction_faces] at hh
    apply Finset.ext
    intro v
    have hv := congrArg (fun S : Finset (PrimeCycleVertex p r) => v ∈ S) hh
    simpa only [Finset.mem_image] using Iff.of_eq hv
  exact (inv_mul_eq_one.mp hunit).symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/PrimeCycleObstruction.lean -/
section

section
/-! # The unrestricted prime-cycle obstruction on the actual rings

The comparison is not assumed graded, coherent, multiplicative, or normalized.
Its only hypotheses are linear bijectivity, universal-parameter linearity, and
equivariance for a prime cycle with at least one fixed vertex.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial ProperlyColoredComplex

variable (p r : ℕ) [Fact p.Prime]
variable {K k : Type*} [CommRing K] [Field k] [CharP k p]

local instance (priority := 2000) : DecidableEq (PrimeCycleVertex p r) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace (PrimeCycleVertex p r)) :=
  Classical.decEq _

/-- Evaluate the moved variables at one and the fixed variables at independent
indeterminates, reducing the original coefficient ring through `φ`. -/
def primeCycleEvaluation (φ : K →+* k) :
    MvPolynomial (PrimeCycleVertex p r) K →+* MvPolynomial (Fin r) k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) (polynomialPrimeRoots p r k)

theorem primeCycleEvaluation_esymm (φ : K →+* k) (n : ℕ) (hn : n ≤ p + r) :
    primeCycleEvaluation p r φ (MvPolynomial.esymm (PrimeCycleVertex p r) K n) =
      primeFiberCoefficient p r k n := by
  rw [← primeRoots_esymm p r k n hn]
  simp only [primeCycleEvaluation, MvPolynomial.esymm, map_sum, map_prod,
    MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]

theorem primeCycleEvaluation_invariant (φ : K →+* k)
    (g : PrimeCycleGroup p) (x : MvPolynomial (PrimeCycleVertex p r) K) :
    primeCycleEvaluation p r φ (MvPolynomial.rename (primeCyclePermutation p r g) x) =
      primeCycleEvaluation p r φ x := by
  have hroots : polynomialPrimeRoots p r k ∘ primeCyclePermutation p r g =
      polynomialPrimeRoots p r k := by
    funext v
    rcases v with v | v <;> rfl
  rw [primeCycleEvaluation, MvPolynomial.eval₂Hom_rename, hroots]

/-- Proposition 9.5 for the prime cycle needed in Theorem 1.3, over an
arbitrary original coefficient ring with a residue characteristic p. The
conclusion concerns the actual polynomial and barycentric quotient rings. -/
theorem no_primeCycle_equivariant_parameter_equiv (hr : 0 < r) (φ : K →+* k)
    (f : MvPolynomial (PrimeCycleVertex p r) K ≃ₗ[K]
      BooleanBarycentricRing (PrimeCycleVertex p r) K)
    (hparameter : ∀ (i : Fin (Fintype.card (PrimeCycleVertex p r))) x,
      f (MvPolynomial.esymm (PrimeCycleVertex p r) K (i.val + 1) * x) =
        colorSum (K := K) i * f x)
    (hequivariant : ∀ (g : PrimeCycleGroup p) x,
      f (MvPolynomial.rename (primeCyclePermutation p r g) x) =
        booleanRename K (primeCyclePermutation p r g) (f x)) : False := by
  let D := PrimeBooleanComplex p r
  let c := primeRankMask p r k
  letI flagFintype : Fintype (D.ActiveFlag c) := inferInstance
  letI colorFintype : Fintype (ActiveColor c) := inferInstance
  letI := primeFlagAction p r k
  apply no_equiv_of_free_parameter_expansion
    (G := PrimeCycleGroup p) (T := D.ActiveFlag c) (I := ActiveColor c)
    (K := K) (R := MvPolynomial (PrimeCycleVertex p r) K)
    (B := D.Ring K) (L := MvPolynomial (Fin r) k)
    (a := fun i : ActiveColor c =>
      MvPolynomial.esymm (PrimeCycleVertex p r) K (i.val.val + 1))
    (b := fun i : ActiveColor c => D.colorParameter K i.val) (s := Finset.univ)
    (ρR := fun g => MvPolynomial.rename (primeCyclePermutation p r g))
    (ρB := fun g => booleanRename K (primeCyclePermutation p r g))
    (ev := primeCycleEvaluation p r φ)
    (hev := primeCycleEvaluation_invariant p r φ)
    (m := fun a : D.ActiveFlag c => D.assignmentMonomial K c a.val)
    (hm := ?_) (hprod := ?_) (hactive := ?_)
    (hfree := primeFlagAction_free p r k hr) (horder := ?_)
    (f := f) (hparameter := ?_) (hequivariant := hequivariant)
  · intro g a
    change D.assignmentMonomial K c ((primeFlagAction p r k).smul g a).val = _
    rw [primeFlagAction_val, primeBooleanRename_eq]
    exact (D.colorRename_assignmentMonomial K c
      (primeBooleanPermutation p r g) (primeBooleanPermutation_face p r g)
      (primeBooleanPermutation_color p r g) a.val).symm
  · change (∏ i : ActiveColor c, D.colorParameter K i.val) =
      ∑ a : D.ActiveFlag c, D.assignmentMonomial K c a.val
    have hsum := D.sum_activeFlagMonomial_withFintypes K c flagFintype colorFintype
    exact hsum.symm
  · intro i hi
    rw [primeCycleEvaluation_esymm p r φ _ (by
      exact Nat.succ_le_of_lt
        (lt_of_lt_of_eq i.val.isLt (primeCycleVertex_card p r)))]
    apply (primeFiberCoefficient_active p r k (Nat.succ_pos _)).mpr
    exact (primeRankMask_active p r k i.val).mp i.property
  · have hc : Fintype.card (PrimeCycleGroup p) = p := by
      simp only [PrimeCycleGroup, Fintype.card_multiplicative, ZMod.card]
    rw [hc]
    exact CharP.cast_eq_zero (MvPolynomial (Fin r) k) p
  · intro i x
    have hb : D.colorParameter K i.val = colorSum (K := K) i.val :=
      booleanColored_colorParameter i.val
    rw [hb]
    exact hparameter i.val x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ObstructionRelabel.lean -/
section

section
/-! # Relabeling the Boolean simplex preserves the actual ring and parameters -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable {U V W K : Type*} [Fintype U] [Fintype V] [Fintype W] [CommRing K]

local instance (priority := 2000) : DecidableEq U := Classical.decEq U
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq W := Classical.decEq W
local instance (priority := 2000) : DecidableEq (BooleanFace U) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace V) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (BooleanFace W) := Classical.decEq _

def booleanFaceCongr (e : U ≃ V) : BooleanFace U ≃ BooleanFace V where
  toFun F := ⟨F.val.image e, F.property.image e⟩
  invFun F := ⟨F.val.image e.symm, F.property.image e.symm⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.symm_comp_self, Finset.image_id]
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]

theorem booleanFaceCongr_subset_iff (e : U ≃ V) (F G : BooleanFace U) :
    (booleanFaceCongr e F).val ⊆ (booleanFaceCongr e G).val ↔ F.val ⊆ G.val := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    exact e.injective he ▸ hw
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨w, h hw, rfl⟩

theorem chainExponent_mapDomain_iff (e : U ≃ V) (a : BooleanFace U →₀ ℕ) :
    IsChainExponent (a.mapDomain (booleanFaceCongr e)) ↔ IsChainExponent a := by
  have hs : (a.mapDomain (booleanFaceCongr e)).support =
      a.support.image (booleanFaceCongr e) :=
    Finsupp.support_mapDomain_of_nonneg (fun _ => Nat.zero_le _) _
  constructor
  · intro h F hF G hG
    have hh := h (booleanFaceCongr e F) (by rw [hs]; exact Finset.mem_image.mpr ⟨F, hF, rfl⟩)
      (booleanFaceCongr e G) (by rw [hs]; exact Finset.mem_image.mpr ⟨G, hG, rfl⟩)
    simpa only [booleanFaceCongr_subset_iff] using hh
  · intro h F hF G hG
    rw [hs] at hF hG
    obtain ⟨F₀, hF₀, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨G₀, hG₀, rfl⟩ := Finset.mem_image.mp hG
    simpa only [booleanFaceCongr_subset_iff] using h F₀ hF₀ G₀ hG₀

def booleanRelabelHom (K : Type*) [CommRing K] (e : U ≃ V) :
    BooleanBarycentricRing U K →ₐ[K] BooleanBarycentricRing V K := by
  let f := (Ideal.Quotient.mkₐ K (forbiddenIdeal (IsChainExponent (V := V)))).comp
    (MvPolynomial.rename (booleanFaceCongr e))
  apply Ideal.Quotient.liftₐ (forbiddenIdeal (IsChainExponent (V := U))) f
  have hh : forbiddenIdeal (IsChainExponent (V := U)) ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk (forbiddenIdeal (IsChainExponent (V := V)))
      (MvPolynomial.rename (booleanFaceCongr e) (MvPolynomial.monomial a (1 : K))) = 0
    rw [MvPolynomial.rename_monomial]
    exact chainMonomial_eq_zero (fun h => ha ((chainExponent_mapDomain_iff e a).mp h))
  exact fun x hx => hh hx

@[simp] theorem booleanRelabelHom_mk (e : U ≃ V) (x : MvPolynomial (BooleanFace U) K) :
    booleanRelabelHom K e (Ideal.Quotient.mk (forbiddenIdeal IsChainExponent) x) =
      Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
        (MvPolynomial.rename (booleanFaceCongr e) x) := rfl

@[simp] theorem booleanRelabelHom_variable (e : U ≃ V) (F : BooleanFace U) :
    booleanRelabelHom K e (faceVariable (K := K) F) =
      faceVariable (K := K) (booleanFaceCongr e F) := by
  rw [faceVariable, booleanRelabelHom_mk, MvPolynomial.rename_X]
  rfl

theorem booleanRelabelHom_trans (e : U ≃ V) (f : V ≃ W)
    (x : BooleanBarycentricRing U K) :
    booleanRelabelHom K f (booleanRelabelHom K e x) =
      booleanRelabelHom K (e.trans f) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [booleanRelabelHom_mk, booleanRelabelHom_mk, booleanRelabelHom_mk,
    MvPolynomial.rename_rename]
  have he : (booleanFaceCongr f : BooleanFace V → BooleanFace W) ∘ booleanFaceCongr e =
      booleanFaceCongr (e.trans f) := by
    funext F
    apply Subtype.ext
    change (F.val.image e).image f = F.val.image (e.trans f)
    rw [Finset.image_image]
    rfl
  rw [he]

theorem booleanRelabelHom_refl (x : BooleanBarycentricRing U K) :
    booleanRelabelHom K (Equiv.refl U) x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [booleanRelabelHom_mk]
  have he : (booleanFaceCongr (Equiv.refl U) : BooleanFace U → BooleanFace U) = id := by
    funext F
    apply Subtype.ext
    exact Finset.image_id
  rw [he, MvPolynomial.rename_id_apply]

def booleanRelabelEquiv (K : Type*) [CommRing K] (e : U ≃ V) :
    BooleanBarycentricRing U K ≃ₐ[K] BooleanBarycentricRing V K :=
  AlgEquiv.ofAlgHom (booleanRelabelHom K e) (booleanRelabelHom K e.symm)
    (by
      ext x
      rw [AlgHom.comp_apply, booleanRelabelHom_trans]
      simpa using booleanRelabelHom_refl (K := K) x)
    (by
      ext x
      rw [AlgHom.comp_apply, booleanRelabelHom_trans]
      simpa using booleanRelabelHom_refl (K := K) x)

theorem booleanRelabelHom_eq_booleanRename (e : Equiv.Perm V) :
    booleanRelabelHom K e = booleanRename K e := by
  rfl

theorem booleanFaceCongr_color_val (e : U ≃ V) (F : BooleanFace U) :
    (BooleanFace.color (booleanFaceCongr e F)).val = (BooleanFace.color F).val := by
  change (F.val.image e).card - 1 = F.val.card - 1
  rw [Finset.card_image_of_injective _ e.injective]

def booleanColorFaceCongr (e : U ≃ V)
    (i : Fin (Fintype.card U)) (j : Fin (Fintype.card V)) (hij : i.val = j.val) :
    {F : BooleanFace U // BooleanFace.color F = i} ≃
      {F : BooleanFace V // BooleanFace.color F = j} where
  toFun F := ⟨booleanFaceCongr e F.val, by
    apply Fin.ext
    rw [booleanFaceCongr_color_val, F.property]
    exact hij⟩
  invFun F := ⟨booleanFaceCongr e.symm F.val, by
    apply Fin.ext
    rw [booleanFaceCongr_color_val, F.property]
    exact hij.symm⟩
  left_inv F := by
    apply Subtype.ext
    exact (booleanFaceCongr e).symm_apply_apply F.val
  right_inv F := by
    apply Subtype.ext
    exact (booleanFaceCongr e).apply_symm_apply F.val

theorem colorSum_eq_sum_fiber (i : Fin (Fintype.card V)) :
    colorSum (K := K) i =
      ∑ F : {F : BooleanFace V // BooleanFace.color F = i}, faceVariable (K := K) F.val := by
  exact Finset.sum_subtype (facesOfColor i) (fun F => by simp) (faceVariable (K := K))

theorem booleanRelabelHom_colorSum (e : U ≃ V)
    (i : Fin (Fintype.card U)) (j : Fin (Fintype.card V)) (hij : i.val = j.val) :
    booleanRelabelHom K e (colorSum (K := K) i) = colorSum (K := K) j := by
  rw [colorSum_eq_sum_fiber, map_sum, colorSum_eq_sum_fiber]
  simp only [booleanRelabelHom_variable]
  exact Fintype.sum_equiv (booleanColorFaceCongr e i j hij) _ _ (fun _ => rfl)

theorem booleanRelabelHom_naturality (e : U ≃ V) (g : Equiv.Perm U) (h : Equiv.Perm V)
    (hgh : ∀ u, e (g u) = h (e u)) (x : BooleanBarycentricRing U K) :
    booleanRelabelHom K e (booleanRename K g x) =
      booleanRename K h (booleanRelabelHom K e x) := by
  rw [← booleanRelabelHom_eq_booleanRename, ← booleanRelabelHom_eq_booleanRename,
    booleanRelabelHom_trans, booleanRelabelHom_trans]
  have he : g.trans e = e.trans h := Equiv.ext hgh
  rw [he]

theorem polynomialRename_naturality (e : U ≃ V) (g : Equiv.Perm U) (h : Equiv.Perm V)
    (hgh : ∀ u, e (g u) = h (e u)) (x : MvPolynomial U K) :
    MvPolynomial.rename e (MvPolynomial.rename g x) =
      MvPolynomial.rename h (MvPolynomial.rename e x) := by
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  have he : (e : U → V) ∘ g = (h : V → V) ∘ e := funext hgh
  rw [he]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/FactorialResidueField.lean -/
section

section
/-! # Exact reduction of a nonunit factorial to modular characteristic

No finiteness, domain, reducedness, or Noetherian assumption is imposed on
the coefficient ring.  A nonunit factorial produces a prime below the rank
and a genuine maximal-ideal residue field of that characteristic.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
variable {K : Type*} [CommRing K]

lemma natCast_product_isUnit (l : List ℕ)
    (h : ∀ p ∈ l, IsUnit (p : K)) : IsUnit (l.prod : K) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.prod_cons, Nat.cast_mul]
      exact (h a (List.mem_cons_self)).mul (ih (fun p hp => h p (List.mem_cons_of_mem _ hp)))

/-- Every nonunit factorial has a nonunit prime factor in the exact range. -/
theorem exists_nonunit_prime_of_factorial (n : ℕ)
    (h : ¬ IsUnit (n.factorial : K)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ ¬ IsUnit (p : K) := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  rw [← Nat.prod_primeFactorsList (Nat.factorial_ne_zero n)]
  apply natCast_product_isUnit
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactorsList hp
  exact hn p hprime (hprime.dvd_factorial.mp (Nat.dvd_of_mem_primeFactorsList hp))

/-- The exact residue-characteristic reduction used in the rank-d obstruction. -/
theorem factorial_nonunit_residueField (d : ℕ) (hd : 1 ≤ d)
    (h : ¬ IsUnit ((d - 1).factorial : K)) :
    ∃ p : ℕ, p.Prime ∧ p < d ∧
      ∃ I : Ideal K, I.IsMaximal ∧ CharP (K ⧸ I) p := by
  obtain ⟨p, hp, hpd, hunit⟩ := exists_nonunit_prime_of_factorial (K := K) (d - 1) h
  obtain ⟨I, hI, hpI⟩ := exists_max_ideal_of_mem_nonunits hunit
  letI : I.IsMaximal := hI
  refine ⟨p, hp, by omega, I, hI, ?_⟩
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  rw [← map_natCast (Ideal.Quotient.mk I) p]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI

end FourPapers.Universal

#print axioms FourPapers.Universal.exists_nonunit_prime_of_factorial

#print axioms FourPapers.Universal.factorial_nonunit_residueField

end
end
end

/- BEGIN FourPapers/Universal/FactorialObstruction.lean -/
section

section
/-! # The nonunit-factorial obstruction over every commutative ring

The result is stated for every finite vertex type and the full permutation
group. Thus it is independent of a chosen labeling of the rank-d simplex.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (V K : Type*) [Fintype V] [CommRing K]

local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq (BooleanFace V) := Classical.decEq _

/-- The actual parameter actions, stated independently of an auxiliary
linear ordering on the vertex type. -/
def simplexPolynomialColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] MvPolynomial V K :=
  MvPolynomial.aeval (fun i => MvPolynomial.esymm V K (i.val + 1))

def simplexBooleanColorMap :
    MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] BooleanBarycentricRing V K :=
  MvPolynomial.aeval colorSum

/-- Exactly an unrestricted equivariant universal-parameter module comparison
on one simplex. Grading, coherence, and multiplication preservation are absent. -/
structure SimplexEquivariantParameterComparison where
  equiv : MvPolynomial V K ≃ₗ[K] BooleanBarycentricRing V K
  parameter : ∀ (i : Fin (Fintype.card V)) x,
    equiv (MvPolynomial.esymm V K (i.val + 1) * x) = colorSum (K := K) i * equiv x
  equivariant : ∀ (g : Equiv.Perm V) x,
    equiv (MvPolynomial.rename g x) = booleanRename K g (equiv x)

variable {V K} {U : Type*} [Fintype U]

local instance (priority := 2000) : DecidableEq U := Classical.decEq U
local instance (priority := 2000) : DecidableEq (BooleanFace U) := Classical.decEq _

/-- The explicit generator conditions are genuine linearity over the entire
parameter polynomial ring, via the verified `ParameterEquiv` API. -/
def SimplexEquivariantParameterComparison.parameterEquiv
    (f : SimplexEquivariantParameterComparison V K) :
    ParameterEquiv (simplexPolynomialColorMap V K)
      (simplexBooleanColorMap V K) where
  toLinearEquiv := f.equiv
  map_X_mul i x := by
    simpa only [simplexPolynomialColorMap, simplexBooleanColorMap, MvPolynomial.aeval_X] using
      f.parameter i x

def simplexComparisonOfParameterEquiv
    (e : ParameterEquiv (simplexPolynomialColorMap V K)
      (simplexBooleanColorMap V K))
    (he : ∀ (g : Equiv.Perm V) x,
      e.toLinearEquiv (MvPolynomial.rename g x) =
        booleanRename K g (e.toLinearEquiv x)) :
    SimplexEquivariantParameterComparison V K where
  equiv := e.toLinearEquiv
  parameter i x := by
    simpa only [simplexPolynomialColorMap, simplexBooleanColorMap, MvPolynomial.aeval_X] using
      e.map_X_mul i x
  equivariant := he

/-- Relabeling preserves every condition in the unrestricted comparison. -/
def SimplexEquivariantParameterComparison.relabel
    (f : SimplexEquivariantParameterComparison V K) (e : U ≃ V) :
    SimplexEquivariantParameterComparison U K := by
  let P := MvPolynomial.renameEquiv K e
  let B := booleanRelabelEquiv K e
  refine ⟨P.toLinearEquiv.trans (f.equiv.trans B.toLinearEquiv.symm), ?_, ?_⟩
  · intro i x
    let j : Fin (Fintype.card V) := ⟨i.val, by
      rw [← Fintype.card_congr e]
      exact i.isLt⟩
    apply B.injective
    change B (B.symm (f.equiv (P (MvPolynomial.esymm U K (i.val + 1) * x)))) =
      B (colorSum (K := K) i * B.symm (f.equiv (P x)))
    rw [B.apply_symm_apply, map_mul B, B.apply_symm_apply]
    change f.equiv (MvPolynomial.rename e (MvPolynomial.esymm U K (i.val + 1) * x)) =
      booleanRelabelHom K e (colorSum (K := K) i) * f.equiv (P x)
    rw [map_mul, MvPolynomial.rename_esymm (σ := U) (R := K) (i.val + 1) e,
      booleanRelabelHom_colorSum e i j rfl]
    exact f.parameter j (P x)
  · intro g x
    let h : Equiv.Perm V := e.symm.trans (g.trans e)
    have hgh : ∀ u, e (g u) = h (e u) := by
      intro u
      simp only [h, Equiv.trans_apply, Equiv.symm_apply_apply]
    apply B.injective
    change B (B.symm (f.equiv (P (MvPolynomial.rename g x)))) =
      B (booleanRename K g (B.symm (f.equiv (P x))))
    rw [AlgEquiv.apply_symm_apply]
    change f.equiv (MvPolynomial.rename e (MvPolynomial.rename g x)) =
      booleanRelabelHom K e (booleanRename K g (B.symm (f.equiv (P x))))
    rw [polynomialRename_naturality e g h hgh, f.equivariant,
      booleanRelabelHom_naturality e g h hgh]
    change booleanRename K h (f.equiv (P x)) =
      booleanRename K h (B (B.symm (f.equiv (P x))))
    rw [AlgEquiv.apply_symm_apply]

/-- The negative half of Theorem 1.3 in its full stated strength: a nonunit
factorial excludes even an ungraded, incoherent parameter-module isomorphism
equivariant under the entire symmetric group. -/
theorem factorial_nonunit_no_simplex_comparison
    (hd : 1 ≤ Fintype.card V)
    (hfactorial : ¬ IsUnit (((Fintype.card V - 1).factorial : ℕ) : K)) :
    IsEmpty (SimplexEquivariantParameterComparison V K) := by
  obtain ⟨p, hp, hpd, I, hI, hchar⟩ :=
    factorial_nonunit_residueField (K := K) (Fintype.card V) hd hfactorial
  letI : Fact p.Prime := ⟨hp⟩
  letI : I.IsMaximal := hI
  letI : Field (K ⧸ I) := Ideal.Quotient.field I
  letI : CharP (K ⧸ I) p := hchar
  let r := Fintype.card V - p
  have hr : 0 < r := Nat.sub_pos_of_lt hpd
  have hcard : Fintype.card (PrimeCycleVertex p r) = Fintype.card V := by
    rw [primeCycleVertex_card]
    dsimp [r]
    exact Nat.add_sub_of_le hpd.le
  let e : PrimeCycleVertex p r ≃ V := Fintype.equivOfCardEq hcard
  refine ⟨fun f => ?_⟩
  let f' := f.relabel e
  exact no_primeCycle_equivariant_parameter_equiv p r hr (Ideal.Quotient.mk I)
    f'.equiv f'.parameter (fun g x => f'.equivariant (primeCyclePermutation p r g) x)

theorem factorial_nonunit_no_equivariant_parameterEquiv
    (hd : 1 ≤ Fintype.card V)
    (hfactorial : ¬ IsUnit (((Fintype.card V - 1).factorial : ℕ) : K))
    (e : ParameterEquiv (simplexPolynomialColorMap V K)
      (simplexBooleanColorMap V K))
    (he : ∀ (g : Equiv.Perm V) x,
      e.toLinearEquiv (MvPolynomial.rename g x) =
        booleanRename K g (e.toLinearEquiv x)) : False :=
  (factorial_nonunit_no_simplex_comparison (V := V) (K := K) hd hfactorial).false
    (simplexComparisonOfParameterEquiv e he)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/EquivariantUniformCriterion.lean -/
section

section
/-! # The exact uniform criterion in Theorem 1.3

The positive theorem is combined with the unrestricted simplex obstruction.
The bridge uses actual coherent maps on the Boolean simplex, transports a
component along its literal vertex identification, and proves equality of
the two existing definitions of the Boolean permutation action on generators.
The uniform statement does not impose constant normalization.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section BooleanAction
variable {V : Type u} [Fintype V] (K : Type v) [CommRing K]

theorem booleanRename_eq_vertexRelabel (g : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanRename K g x = booleanVertexRelabelEquiv g x := by
  have h : (booleanRename K g).comp
      (Ideal.Quotient.mkₐ K (forbiddenIdeal (IsChainExponent (V := V)))) =
      (booleanVertexRelabelEquiv (K := K) g).toAlgHom.comp
        (Ideal.Quotient.mkₐ K (forbiddenIdeal (IsChainExponent (V := V)))) := by
    apply MvPolynomial.algHom_ext
    intro F
    change booleanRename K g (faceVariable (K := K) F) =
      booleanVertexRelabelEquiv g (faceVariable F)
    rw [booleanRename_faceVariable, booleanVertexRelabelEquiv_face]
    congr 1
    apply Subtype.ext
    exact (Finset.map_eq_image g.toEmbedding F.val).symm
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

end BooleanAction

section CoherentSymmetry
variable {P : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type v) [CommRing K]

theorem coherentEquiv_family_fixed
    (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (hE : ∀ (e : P ≃o P) p x, polynomialStalkOrderEquiv K e p (E.component p x) =
      E.component (e p) (barycentricStalkOrderEquiv K e p x)) (e : P ≃o P) :
    stalkFamilyRelabel K e (fun p => (E.component p).toLinearMap) =
      (fun p => (E.component p).toLinearMap) := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K e.symm p).symm
    (E.component (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)) = E.component p x
  rw [← hE, AlgEquiv.symm_apply_apply]

end CoherentSymmetry

section SimplexBridge
variable {V : Type u} [Fintype V] (K : Type v) [CommRing K]

/-- A comparison on the actual Boolean face diagram gives the unrestricted
simplex comparison used by the negative theorem.  This bridge itself does
not require grading or normalization. -/
def simplexComparisonOfCoherentEquiv
    (E : CoherentEquiv (barycentricDiagram (P := Finset V) K) (polynomialDiagram K))
    (hp : ∀ (s : Finset V) (r : ℕ) x,
      E.component s (booleanRankParameter (r + 1) * x) =
        polynomialParameter K s (r + 1) * E.component s x)
    (he : ∀ (e : Finset V ≃o Finset V) s x,
      polynomialStalkOrderEquiv K e s (E.component s x) =
        E.component (e s) (barycentricStalkOrderEquiv K e s x)) :
    SimplexEquivariantParameterComparison V K := by
  let F : StalkLinearFamily (P := Finset V) K := fun s => (E.component s).toLinearMap
  have hc : F ∈ coherentStalkFamilySubmodule K := E.naturality
  have hs : ∀ g : Equiv.Perm V, stalkFamilyRelabel K (finsetOrderCongr g) F = F :=
    fun g => coherentEquiv_family_fixed K E he (finsetOrderCongr g)
  let i : V ↪ V := Function.Embedding.refl V
  let a := embeddingPlacementVertex i
  let L : BooleanBarycentricRing V K ≃ₗ[K] MvPolynomial V K :=
    (booleanVertexRelabelEquiv (K := K) a).toLinearEquiv.trans
      ((E.component (embeddingPlacementFace i)).trans
        (MvPolynomial.renameEquiv K a).symm.toLinearEquiv)
  have hL : ∀ x, L x = finiteVertexMap F (le_refl (Fintype.card V)) x := by
    intro x
    exact (LinearMap.congr_fun
      (finiteVertexMap_eq_placement F hs (le_refl (Fintype.card V)) i) x).symm
  have hparam : ∀ r x, L (booleanRankParameter (r + 1) * x) =
      MvPolynomial.esymm V K (r + 1) * L x := by
    intro r x
    rw [hL, hL]
    exact finiteVertexMap_parameter F (fun s r x => hp s r x) (le_refl (Fintype.card V)) r x
  have hsym : ∀ (g : Equiv.Perm V) x, MvPolynomial.rename g (L x) =
      L (booleanVertexRelabelEquiv g x) := by
    intro g x
    rw [hL, hL]
    exact finiteVertexMap_relabel F hc hs (le_refl (Fintype.card V))
      (le_refl (Fintype.card V)) g x
  refine ⟨L.symm, ?_, ?_⟩
  · intro j x
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, ← booleanRankParameter_color, hparam,
      LinearEquiv.apply_symm_apply]
  · intro g x
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, booleanRename_eq_vertexRelabel,
      ← hsym, LinearEquiv.apply_symm_apply]

end SimplexBridge

/-- The paper's uniform existence assertion, in arbitrary finite-poset
universe.  Coherence and ordinary grading are explicit.  Equivariance for
the entire order automorphism group implies equivariance for each of its
group actions, without any hypothesis on the group order in `K`. -/
def UniformCoherentEquivariantComparisons (K : Type v) [CommRing K] (d : ℕ) : Prop :=
  ∀ (P : Type u) [PartialOrder P] [OrderBot P] [Fintype P]
    (hs : IsSimplicialPoset P), (∀ p : P, faceRank p ≤ d) →
    ∃ E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K),
      (∀ (p : P) (r : ℕ) x,
        E.component p (booleanRankParameter (r + 1) * x) =
          polynomialParameter K p (r + 1) * E.component p x) ∧
      (∀ (p : P) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → E.component p x ∈ polynomialDegreePiece n) ∧
      ∀ (e : P ≃o P) (p : P) (x : BarycentricStalk K p),
        polynomialStalkOrderEquiv K e p (E.component p x) =
          E.component (e p) (barycentricStalkOrderEquiv K e p x)

/-- **Theorem 1.3, literal uniform if and only if.**  Necessity is obtained
from a rank-d Boolean simplex in the quantified universe, and the explicit
bridge above supplies the exact polynomial/barycentric rings and actions
required by the unrestricted negative theorem. -/
theorem theorem_1_3_uniform_iff (K : Type v) [CommRing K]
    (d : ℕ) (hd : 1 ≤ d) :
    UniformCoherentEquivariantComparisons.{u, v} K d ↔
      IsUnit (((d - 1).factorial : ℕ) : K) := by
  constructor
  · intro H
    by_contra hD
    let V := ULift.{u} (Fin d)
    have hV : Fintype.card V = d := by simp [V]
    have hrank : ∀ s : Finset V, faceRank s ≤ d := by
      intro s
      rw [simplex_faceRank]
      calc
        s.card ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ s)
        _ = d := by rw [Finset.card_univ, hV]
    obtain ⟨E, hp, hg, he⟩ := H (Finset V) (simplex_isSimplicialPoset (V := V)) hrank
    have hnot := factorial_nonunit_no_simplex_comparison (V := V) (K := K)
      (by simpa only [hV] using hd) (by simpa only [hV] using hD)
    exact hnot.false (simplexComparisonOfCoherentEquiv K E hp he)
  · intro hD P _ _ _ hs hrank
    obtain ⟨E, hp, hg, h₁, he⟩ := theorem_1_3_positive K hs d hd hrank hD
    exact ⟨E, hp, hg, he⟩

end FourPapers.Universal

end
end
end
