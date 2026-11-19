/- Exact quotient lattices underlying the signed 2- and 3-sums.
   The common port module is arbitrary; rank one and two are specializations. -/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.SignedSums

variable {R P A B : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- The actual identified port vectors `(p,-p)` in the two summands. -/
def portRelation : P →ₗ[R] ((P × A) × (P × B)) where
  toFun p := ((p, 0), (-p, 0))
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp

/-- Coordinates on the glued lattice retain one copy of the port. -/
def amalgamation : ((P × A) × (P × B)) →ₗ[R] P × (A × B) where
  toFun x := (x.1.1 + x.2.1, (x.1.2, x.2.2))
  map_add' x y := by ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by ext <;> simp [smul_add]

theorem ker_amalgamation :
    LinearMap.ker (amalgamation (R := R) (P := P) (A := A) (B := B)) =
      LinearMap.range portRelation := by
  ext x
  rcases x with ⟨⟨p, a⟩, ⟨q, b⟩⟩
  change (p + q, (a, b)) = 0 ↔ ∃ t, ((t, 0), (-t, 0)) = ((p, a), (q, b))
  constructor
  · intro h
    have hpq : p + q = 0 := congrArg Prod.fst h
    have ha : a = 0 := congrArg (fun z : P × (A × B) => z.2.1) h
    have hb : b = 0 := congrArg (fun z : P × (A × B) => z.2.2) h
    have hq : q = -p := eq_neg_of_add_eq_zero_right hpq
    exact ⟨p, by simp only [ha, hb, hq]⟩
  · rintro ⟨t, ht⟩
    have he := congrArg (amalgamation (R := R) (P := P) (A := A) (B := B)) ht
    simpa [amalgamation] using he.symm

theorem amalgamation_surjective :
    Function.Surjective (amalgamation (R := R) (P := P) (A := A) (B := B)) := by
  rintro ⟨p, a, b⟩
  exact ⟨((p, a), (0, b)), by simp [amalgamation]⟩

/-- The displayed quotient in the paper, not a finite-index replacement. -/
abbrev Glued := ((P × A) × (P × B)) ⧸
  LinearMap.range (portRelation (R := R) (P := P) (A := A) (B := B))

noncomputable def quotientEquiv :
    Glued (R := R) (P := P) (A := A) (B := B) ≃ₗ[R] P × (A × B) := by
  let f : ((P × A) × (P × B)) →ₗ[R] P × (A × B) := amalgamation
  let h : LinearMap.ker f = LinearMap.range
      (portRelation (R := R) (P := P) (A := A) (B := B)) := ker_amalgamation
  let e := Submodule.quotEquivOfEq _ _ h.symm
  exact e.trans (f.quotKerEquivOfSurjective amalgamation_surjective)

@[simp] theorem quotientEquiv_mk (x : (P × A) × (P × B)) :
    quotientEquiv (R := R) (P := P) (A := A) (B := B)
      (Submodule.Quotient.mk x) = amalgamation (R := R) x := by
  simp [quotientEquiv]

/-- An actual integral basis witnesses freeness of the glued lattice. -/
noncomputable def quotientBasis {I J K : Type*}
    (bP : Module.Basis I R P) (bA : Module.Basis J R A) (bB : Module.Basis K R B) :
    Module.Basis (I ⊕ (J ⊕ K)) R (Glued (R := R) (P := P) (A := A) (B := B)) :=
  (bP.prod (bA.prod bB)).map quotientEquiv.symm

/-- Images of surviving columns from the left side. -/
def sumLeft : (P × A) →ₗ[R] P × (A × B) where
  toFun x := (x.1, (x.2, 0))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Images of surviving columns from the right side. -/
def sumRight : (P × B) →ₗ[R] P × (A × B) where
  toFun x := (x.1, (0, x.2))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

def joinedFamily {I J : Type*} (u : I → P × A) (v : J → P × B) :
    I ⊕ J → P × (A × B) :=
  Sum.elim (fun i => sumLeft (R := R) (u i)) (fun j => sumRight (R := R) (v j))

/-- Deletion-spanning hypotheses imply integral spanning in the full quotient.
No rank bound or determinant assumption is used in this algebraic statement. -/
theorem joinedFamily_spans {I J : Type*} (u : I → P × A) (v : J → P × B)
    (hu : Submodule.span R (range u) = ⊤) (hv : Submodule.span R (range v) = ⊤) :
    Submodule.span R (range (joinedFamily (R := R) u v)) = ⊤ := by
  let S := Submodule.span R (range (joinedFamily (R := R) u v))
  have hleft : Submodule.span R (range u) ≤ S.comap (sumLeft (R := R)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hright : Submodule.span R (range v) ≤ S.comap (sumRight (R := R)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  rw [hu] at hleft
  rw [hv] at hright
  apply top_unique
  rintro ⟨p, a, b⟩ _
  have hl : sumLeft (R := R) (p, a) ∈ S := hleft (by trivial)
  have hr : sumRight (R := R) ((0 : P), b) ∈ S := hright (by trivial)
  simpa [sumLeft, sumRight] using S.add_mem hl hr

/-- The literal quotient classes of the surviving side columns. -/
def quotientFamily {I J : Type*} (u : I → P × A) (v : J → P × B) :
    I ⊕ J → Glued (R := R) (P := P) (A := A) (B := B) :=
  Sum.elim (fun i => Submodule.Quotient.mk (u i, 0))
    (fun j => Submodule.Quotient.mk (0, v j))

@[simp] theorem quotientEquiv_family {I J : Type*} (u : I → P × A)
    (v : J → P × B) (i : I ⊕ J) :
    quotientEquiv (quotientFamily (R := R) u v i) = joinedFamily (R := R) u v i := by
  cases i <;> simp [quotientFamily, joinedFamily, amalgamation, sumLeft, sumRight]

theorem quotientFamily_spans {I J : Type*} (u : I → P × A) (v : J → P × B)
    (hu : Submodule.span R (range u) = ⊤) (hv : Submodule.span R (range v) = ⊤) :
    Submodule.span R (range (quotientFamily (R := R) u v)) = ⊤ := by
  let e : Glued (R := R) (P := P) (A := A) (B := B) ≃ₗ[R] P × (A × B) := quotientEquiv
  let S := Submodule.span R (range (quotientFamily (R := R) u v))
  have hle : Submodule.span R (range (joinedFamily (R := R) u v)) ≤
      S.comap e.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change e.symm (joinedFamily (R := R) u v i) ∈ S
    have he : e.symm (joinedFamily (R := R) u v i) = quotientFamily (R := R) u v i := by
      apply e.injective
      simp [e]
    rw [he]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [joinedFamily_spans u v hu hv] at hle
  apply top_unique
  intro x _
  have hx := hle (show e x ∈ (⊤ : Submodule R (P × (A × B))) from trivial)
  simpa using hx

end Unimodular.SignedSums

#print axioms Unimodular.SignedSums.ker_amalgamation
#print axioms Unimodular.SignedSums.quotientEquiv
#print axioms Unimodular.SignedSums.quotientBasis
#print axioms Unimodular.SignedSums.quotientFamily_spans
