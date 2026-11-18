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


-- Close only the anonymous source scopes reopened by the next shard.
end
end
