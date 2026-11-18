module

public import ToricPower.FiniteTriangularAcyclic

/-!
# Finite descending elimination of cycles

This elementary lemma isolates the second direction of the finite-width
bicomplex argument. If an actual boundary can remove the highest remaining
coordinate of a cycle, without creating any higher coordinates, finitely
many such boundaries remove the whole cycle. No bound on its integer degree
or on the dimensions of any coefficient modules is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

universe u v

variable {R : Type u} [Ring R] {width : ℕ}
  (K : CochainComplex (ModuleCat.{v} R) ℤ)
  (coordinate : ℤ → Fin width → ModuleCat.{v} R)
  (project : ∀ (a : ℤ) (q : Fin width), K.X a ⟶ coordinate a q)

/-- A finite descending boundary-removal procedure proves actual
acyclicity. The lifting hypothesis concerns the original differential. -/
theorem finiteDescending_acyclic
    (jointlyInjective : ∀ a : ℤ,
      Function.Injective (fun z : K.X a => fun q : Fin width => project a q z))
    (remove : ∀ (a : ℤ) (q : Fin width) (z : K.X a),
      K.d a (a+1) z = 0 →
      (∀ p : Fin width, q.val < p.val → project a p z = 0) →
      ∃ b : K.X (a-1),
        (∀ p : Fin width, q.val < p.val → project a p (K.d (a-1) a b) = 0) ∧
        project a q (K.d (a-1) a b) = project a q z) : K.Acyclic := by
  intro a
  rw [HomologicalComplex.exactAt_iff' K (a-1) a (a+1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ z : K.X a, K.d a (a+1) z = 0 →
    ∃ b : K.X (a-1), K.d (a-1) a b = z
  intro z closed
  have square (b : K.X (a-1)) : K.d a (a+1) (K.d (a-1) a b) = 0 := by
    exact congrArg (fun f : K.X (a-1) ⟶ K.X (a+1) => f b)
      (K.d_comp_d (a-1) a (a+1))
  have eliminate : ∀ k : ℕ, k ≤ width → ∃ b : K.X (a-1),
      ∀ q : Fin width, width-k ≤ q.val → project a q (z - K.d (a-1) a b) = 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨0,?_⟩
        intro q bound
        have := q.isLt
        omega
    | succ k ih =>
        intro bound
        obtain ⟨b,hb⟩ := ih (by omega)
        let q : Fin width := ⟨width-(k+1),by omega⟩
        let residual : K.X a := z - K.d (a-1) a b
        have residual_closed : K.d a (a+1) residual = 0 := by
          dsimp [residual]
          rw [map_sub,closed,square,sub_self]
        obtain ⟨y,hyHigher,hy⟩ := remove a q residual residual_closed (by
          intro p hp
          apply hb p
          dsimp [q] at hp
          omega)
        refine ⟨b+y,?_⟩
        intro p hp
        have residual_eq : z - K.d (a-1) a (b+y) = residual - K.d (a-1) a y := by
          dsimp [residual]
          rw [map_add,sub_add_eq_sub_sub]
        rw [residual_eq,map_sub]
        by_cases higher : q.val < p.val
        · rw [hyHigher p higher,hb p (by dsimp [q] at higher; omega),sub_self]
        · have pq : p = q := Fin.ext (by dsimp [q] at higher ⊢; omega)
          subst p
          rw [hy,sub_self]
  obtain ⟨b,hb⟩ := eliminate width le_rfl
  refine ⟨b,?_⟩
  change K.d (a-1) a b = z
  have residual_zero : z - K.d (a-1) a b = 0 := by
    apply jointlyInjective a
    funext q
    change project a q (z - K.d (a-1) a b) = project a q 0
    rw [hb q (by omega),map_zero]
  exact (sub_eq_zero.mp residual_zero).symm

end ToricPower

end
