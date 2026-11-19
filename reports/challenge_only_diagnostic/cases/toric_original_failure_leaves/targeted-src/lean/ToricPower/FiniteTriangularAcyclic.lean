module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Exactness for finitely many triangular rows

The vertical degree is an arbitrary integer. Only the number of rows is
finite. Successively removing the lowest nonzero coordinate of a cycle
constructs an actual boundary after finitely many steps. This is the
finite-width total-complex argument, stated independently of a choice of
categorical biproducts or of signs in the shifted rows.
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
  (row : Fin width → CochainComplex (ModuleCat.{v} R) ℤ)
  (project : ∀ (a : ℤ) (q : Fin width), K.X a ⟶ (row q).X a)
  (insert : ∀ (a : ℤ) (q : Fin width), (row q).X a ⟶ K.X a)

/-- The diagonal differential is the differential of the indicated row
once every lower coordinate vanishes. Off-diagonal terms may be
arbitrary strictly increasing maps. -/
def HasTriangularDifferential : Prop :=
  ∀ (a : ℤ) (q : Fin width) (z : K.X a),
    (∀ p : Fin width, p.val < q.val → project a p z = 0) →
    project (a+1) q (K.d a (a+1) z) =
      (row q).d a (a+1) (project a q z)

variable
  (diagonal : HasTriangularDifferential K row project)
  (project_insert : ∀ (a : ℤ) (q : Fin width) (z : (row q).X a),
    project a q (insert a q z) = z)
  (project_insert_lower : ∀ (a : ℤ) (p q : Fin width), p.val < q.val →
    ∀ z : (row q).X a, project a p (insert a q z) = 0)

include diagonal project_insert_lower in
theorem triangular_boundary_lower (a : ℤ) (p q : Fin width) (lower : p.val < q.val)
    (z : (row q).X a) :
    project (a+1) p (K.d a (a+1) (insert a q z)) = 0 := by
  rw [diagonal a p (insert a q z)
    (fun r hr => project_insert_lower a r q (lt_trans hr lower) z)]
  rw [project_insert_lower a p q lower z, map_zero]

include diagonal project_insert project_insert_lower in
theorem triangular_boundary_diagonal (a : ℤ) (q : Fin width)
    (z : (row q).X a) :
    project (a+1) q (K.d a (a+1) (insert a q z)) = (row q).d a (a+1) z := by
  rw [diagonal a q (insert a q z)
    (fun p hp => project_insert_lower a p q hp z),project_insert]

include diagonal project_insert project_insert_lower in
/-- Exact rows imply an exact total complex of finite width. In
particular, no lower or upper bound on the input complex is used. -/
theorem finiteTriangular_acyclic
    (jointlyInjective : ∀ a : ℤ, Function.Injective
      (fun z : K.X a => fun q : Fin width => project a q z))
    (exactRows : ∀ q : Fin width, (row q).Acyclic) : K.Acyclic := by
  intro a
  rw [HomologicalComplex.exactAt_iff' K (a-1) a (a+1) (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : K.X a, K.d a (a+1) z = 0 →
    ∃ b : K.X (a-1), K.d (a-1) a b = z
  intro z closed
  change K.d a (a+1) z = 0 at closed
  have square (b : K.X (a-1)) : K.d a (a+1) (K.d (a-1) a b) = 0 := by
    have h := congrArg (fun f : K.X (a-1) ⟶ K.X (a+1) => f b)
      (K.d_comp_d (a-1) a (a+1))
    exact h
  have eliminate : ∀ k : ℕ, k ≤ width → ∃ b : K.X (a-1),
      ∀ q : Fin width, q.val < k → project a q (z - K.d (a-1) a b) = 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨0,fun q h => False.elim (Nat.not_lt_zero q.val h)⟩
    | succ k ih =>
        intro bound
        obtain ⟨b,hb⟩ := ih (by omega)
        let q : Fin width := ⟨k,by omega⟩
        let residual : K.X a := z - K.d (a-1) a b
        have residual_closed : K.d a (a+1) residual = 0 := by
          dsimp [residual]
          rw [map_sub,closed,square,sub_self]
        have q_closed : (row q).d a (a+1) (project a q residual) = 0 := by
          rw [← diagonal a q residual (fun p hp => hb p hp),residual_closed,map_zero]
        have row_exact := exactRows q a
        rw [HomologicalComplex.exactAt_iff' (row q) (a-1) a (a+1)
          (by simp) (by simp),ShortComplex.moduleCat_exact_iff] at row_exact
        obtain ⟨y,hy⟩ := row_exact (project a q residual) q_closed
        change (row q).d (a-1) a y = project a q residual at hy
        refine ⟨b + insert (a-1) q y,?_⟩
        intro p hp
        have residual_eq : z - K.d (a-1) a (b + insert (a-1) q y) =
            residual - K.d (a-1) a (insert (a-1) q y) := by
          dsimp [residual]
          rw [map_add,sub_add_eq_sub_sub]
        rw [residual_eq,map_sub]
        by_cases lower : p.val < k
        · rw [hb p lower]
          have vanishing := triangular_boundary_lower K row project insert diagonal
            project_insert_lower (a-1) p q lower y
          have arithmetic : a-1+1=a := by omega
          rw [arithmetic] at vanishing
          rw [vanishing,sub_self]
        · have pq : p = q := Fin.ext (by dsimp [q]; omega)
          subst p
          have onDiagonal := triangular_boundary_diagonal K row project insert diagonal
            project_insert project_insert_lower (a-1) q y
          have arithmetic : a-1+1=a := by omega
          rw [arithmetic] at onDiagonal
          rw [onDiagonal,hy,sub_self]
  obtain ⟨b,hb⟩ := eliminate width le_rfl
  refine ⟨b,?_⟩
  change K.d (a-1) a b = z
  have residual_zero : z - K.d (a-1) a b = 0 := by
    apply jointlyInjective a
    funext q
    change project a q (z - K.d (a-1) a b) = project a q 0
    rw [hb q q.isLt,map_zero]
  exact (sub_eq_zero.mp residual_zero).symm

end ToricPower

end
