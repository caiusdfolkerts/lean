module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Int.Basic

/-! # Integral bases retaining a prescribed part of an ambient basis

An ambient basis vector already contained in a submodule need not be replaced
by a multiple. Splitting the projection onto those coordinates proves that
all selected vectors extend together to an integral basis of the submodule.
-/

@[expose] public noncomputable section
open Module
open scoped Classical

namespace ToricPower

variable {R M P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

/-- The direct product decomposition associated to a genuine linear section. -/
def splitLinearMapProdKerEquiv (p : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : ∀ y, p (s y) = y) : (P × p.ker) ≃ₗ[R] M := by
  let f : (P × p.ker) →ₗ[R] M := s.coprod p.ker.subtype
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    have hab' : s a.1 + a.2.val = s b.1 + b.2.val := hab
    have hfirst : a.1 = b.1 := by
      have h := congrArg p hab'
      have ha : p a.2.val = 0 := a.2.property
      have hb : p b.2.val = 0 := b.2.property
      simpa only [map_add, hs, ha, hb, add_zero] using h
    apply Prod.ext hfirst
    apply Subtype.ext
    rw [hfirst] at hab'
    exact add_left_cancel hab'
  · intro x
    have hx : x - s (p x) ∈ p.ker := by
      change p (x - s (p x)) = 0
      rw [map_sub, hs, sub_self]
    refine ⟨(p x, ⟨x - s (p x), hx⟩), ?_⟩
    change s (p x) + (x - s (p x)) = x
    abel

@[simp]
theorem splitLinearMapProdKerEquiv_apply (p : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : ∀ y, p (s y) = y) (x : P) (y : p.ker) :
    splitLinearMapProdKerEquiv p s hs (x, y) = s x + y.val := rfl

/-- A selected finite family of distinct ambient basis vectors extends to
an integral basis of any submodule containing the whole selected family. -/
theorem submodule_exists_basis_extending
    {N ι κ : Type*} [AddCommGroup N] [Finite ι] [Finite κ]
    (b : Basis ι ℤ N) (r : κ ↪ ι) (S : Submodule ℤ N)
    (hb : ∀ j, b (r j) ∈ S) :
    ∃ (n : ℕ) (c : Basis (Fin n) ℤ S) (t : κ ↪ Fin n),
      ∀ j, (c (t j)).val = b (r j) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  let p : S →ₗ[ℤ] (κ → ℤ) :=
    LinearMap.pi (fun j => (b.coord (r j)).comp S.subtype)
  let s : (κ → ℤ) →ₗ[ℤ] S :=
    (Pi.basisFun ℤ κ).constr ℤ (fun j => ⟨b (r j), hb j⟩)
  have hps : p.comp s = LinearMap.id := by
    apply (Pi.basisFun ℤ κ).ext
    intro j
    simp only [LinearMap.comp_apply, s, Basis.constr_basis, LinearMap.id_apply]
    ext l
    change b.repr (b (r j)) (r l) = (Pi.basisFun ℤ κ j) l
    rw [b.repr_self]
    simp only [Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply,
      r.injective.eq_iff, eq_comm]
  have hs (x : κ → ℤ) : p (s x) = x := LinearMap.congr_fun hps x
  let bs := S.basisOfPid b
  let bk := p.ker.basisOfPid bs.2
  let e := splitLinearMapProdKerEquiv p s hs
  let c := ((Pi.basisFun ℤ κ).prod bk.2).map e
  let index := Fintype.equivFin (κ ⊕ Fin bk.1)
  refine ⟨Fintype.card (κ ⊕ Fin bk.1), c.reindex index,
    ⟨fun j => index (Sum.inl j), index.injective.comp Sum.inl_injective⟩, ?_⟩
  intro j
  change ((c.reindex index) (index (Sum.inl j))).val = b (r j)
  rw [Basis.reindex_apply, Equiv.symm_apply_apply, Basis.map_apply]
  change (s (((Pi.basisFun ℤ κ).prod bk.2) (Sum.inl j)).1 +
    ((((Pi.basisFun ℤ κ).prod bk.2) (Sum.inl j)).2).val).val = b (r j)
  rw [Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
  simp [s]

end ToricPower
