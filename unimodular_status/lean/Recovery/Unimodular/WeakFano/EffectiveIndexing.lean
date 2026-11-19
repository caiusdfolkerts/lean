module

public import Unimodular
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Logic.Equiv.Finset

@[expose] public section
set_option autoImplicit false

namespace Unimodular.EffectiveIndexing

/-- Constructive finite indexing by sorting a computable natural-number
encoding. This uses neither `Fintype.equivFin` nor choice of an enumeration. -/
def finiteIndex (I : Type*) [Fintype I] [Encodable I] : Fin (Fintype.card I) ≃ I :=
  letI : LinearOrder I := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  (Fintype.orderIsoFinOfCardEq I rfl).toEquiv

variable {I J : Type*}

/-- Literal permutation of integer coordinates. -/
def reindex (e : I ≃ J) : (I → ℤ) ≃+ (J → ℤ) where
  toFun c j := c (e.symm j)
  invFun c i := c (e i)
  left_inv c := by ext i; simp
  right_inv c := by ext j; simp
  map_add' c d := rfl

@[simp] theorem reindex_apply (e : I ≃ J) (c : I → ℤ) (j : J) :
    reindex e c j = c (e.symm j) := rfl

@[simp] theorem reindex_apply_image (e : I ≃ J) (c : I → ℤ) (i : I) :
    reindex e c (e i) = c i := by simp

@[simp] theorem reindex_symm_apply (e : I ≃ J) (c : J → ℤ) (i : I) :
    (reindex e).symm c i = c (e i) := rfl

theorem conformal_reindex_iff (e : I ≃ J) (h g : I → ℤ) :
    Graver.ConformalLE (reindex e h) (reindex e g) ↔ Graver.ConformalLE h g := by
  constructor
  · intro hh i
    simpa only [reindex_apply_image] using hh (e i)
  · intro hh j
    exact hh (e.symm j)

theorem nonnegative_reindex_iff (e : I ≃ J) (c : I → ℤ) :
    (∀ j, 0 ≤ reindex e c j) ↔ ∀ i, 0 ≤ c i := by
  constructor
  · intro hc i
    simpa only [reindex_apply_image] using hc (e i)
  · intro hc j
    exact hc (e.symm j)

/-- Conformal minimality, including every integer coordinate and nonzero
condition, is invariant under the exact kernel correspondence. -/
theorem primitive_reindex_iff (e : I ≃ J) (L : AddSubgroup (I → ℤ))
    (K : AddSubgroup (J → ℤ))
    (hker : ∀ c, reindex e c ∈ K ↔ c ∈ L) (g : I → ℤ) :
    Graver.Primitive K (reindex e g) ↔ Graver.Primitive L g := by
  constructor
  · rintro ⟨hgK, hg0, hgmin⟩
    refine ⟨(hker g).1 hgK, ?_, ?_⟩
    · intro hz
      exact hg0 (by rw [hz, map_zero])
    · intro h hhL hh0 hhg
      have hhK := (hker h).2 hhL
      have hh0' : reindex e h ≠ 0 := by
        intro hz
        exact hh0 ((reindex e).injective (hz.trans (map_zero _).symm))
      exact (reindex e).injective
        (hgmin (reindex e h) hhK hh0' ((conformal_reindex_iff e h g).2 hhg))
  · rintro ⟨hgL, hg0, hgmin⟩
    refine ⟨(hker g).2 hgL, ?_, ?_⟩
    · intro hz
      exact hg0 ((reindex e).injective (hz.trans (map_zero _).symm))
    · intro h hhK hh0 hhg
      let h' := (reindex e).symm h
      have he : reindex e h' = h := (reindex e).apply_symm_apply h
      have hhL : h' ∈ L := (hker h').1 (he.symm ▸ hhK)
      have hh0' : h' ≠ 0 := by
        intro hz
        apply hh0
        rw [← he, hz, map_zero]
      have hhg' : Graver.ConformalLE h' g := by
        apply (conformal_reindex_iff e h' g).1
        rwa [he]
      have hm := hgmin h' hhL hh0' hhg'
      rw [← he, hm]

end Unimodular.EffectiveIndexing

#print axioms Unimodular.EffectiveIndexing.finiteIndex
#print axioms Unimodular.EffectiveIndexing.primitive_reindex_iff
#check Unimodular.EffectiveIndexing.primitive_reindex_iff
