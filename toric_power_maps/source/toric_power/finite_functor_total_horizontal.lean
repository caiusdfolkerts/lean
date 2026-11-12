module

public import ToricPower.FiniteFunctorTotalCoordinates
public import ToricPower.FiniteDescendingAcyclic

/-!
# Horizontal exactness of the unbounded finite total

A finite-width total of horizontally acyclic complexes is acyclic.
The proof uses the original horizontal differentials, working from the
highest remaining coordinate downwards. The input complex remains
arbitrary and unbounded; the terminal zero is the actual horizontal
term immediately beyond the finite total.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive]
  {width : ℕ} (K : CochainComplex A ℤ)
  {k : Type} [CommRing k] (F : B ⥤ ModuleCat.{0} k) [F.Additive]

theorem mapped_transportedHorizontal_surjective_on_cycles
    (x y : ℤ) (p q : ℕ) (equality : x = y)
    (predecessor : (ComplexShape.up ℕ).prev q = p)
    (exactRow : ((F.mapHomologicalComplex (.up ℕ)).obj (Φ.obj (K.X x))).ExactAt q)
    (z : F.obj ((Φ.obj (K.X y)).X q))
    (closed : F.map ((Φ.obj (K.X y)).d q (q+1)) z = 0) :
    ∃ w : F.obj ((Φ.obj (K.X x)).X p),
      F.map (transportedHorizontal Φ K x y p q equality) w = z := by
  subst equality
  rw [HomologicalComplex.exactAt_iff' _ p q (q+1) predecessor (by simp),
    ShortComplex.moduleCat_exact_iff] at exactRow
  obtain ⟨w,hw⟩ := exactRow z closed
  refine ⟨w,?_⟩
  simp only [transportedHorizontal,eqToHom_refl,Category.comp_id]
  exact hw

/-- A cycle's highest remaining coordinate is a cycle for the original
horizontal differential, including at the final retained degree. -/
theorem mapped_total_highest_horizontal_closed
    (lastZero : ∀ x : ℤ, IsZero (F.obj ((Φ.obj (K.X x)).X width)))
    (a : ℤ) (q : Fin width) (z : F.obj ((total Φ width K).X a))
    (closed : F.map ((total Φ width K).d a (a+1)) z = 0)
    (higher : ∀ r : Fin width, q.val < r.val →
      F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) r) z = 0) :
    F.map ((Φ.obj (K.X (a + -(q.val : ℤ)))).d q.val (q.val+1))
      (F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) q) z) = 0 := by
  by_cases below : q.val+1 < width
  · let r : Fin width := ⟨q.val+1,below⟩
    have next : q.val+1=r.val := rfl
    have equation := mapped_total_d_project Φ K F a q r next z
    rw [closed,map_zero,higher r (by dsimp [r]; omega),map_zero,zero_add] at equation
    have horizontal_zero :
        F.map (transportedHorizontal Φ K (a + -(q.val : ℤ))
          (a+1 + -(r.val : ℤ)) q.val r.val (by dsimp [r]; omega))
          (F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) q) z) = 0 := by
      simp only [offEntry,dif_pos next] at equation
      exact equation.symm
    exact (mapped_transportedHorizontal_zero_iff Φ K F _ _ _ _ _ _).mp horizontal_zero
  · have last : q.val+1=width := by omega
    have zeroMap : F.map ((Φ.obj (K.X (a + -(q.val : ℤ)))).d q.val (q.val+1)) = 0 := by
      have hz : IsZero (F.obj ((Φ.obj (K.X (a + -(q.val : ℤ)))).X (q.val+1))) := by
        rw [last]
        exact lastZero _
      exact hz.eq_of_tgt _ _
    rw [zeroMap]
    rfl

/-- Horizontal exactness proves exactness of the actual total. The
hypotheses involve only original coefficient complexes and the actual
terminal term; there is no bound on the input complex. -/
theorem mapped_total_acyclic_of_horizontal
    (exactRows : ∀ x : ℤ,
      ((F.mapHomologicalComplex (.up ℕ)).obj (Φ.obj (K.X x))).Acyclic)
    (lastZero : ∀ x : ℤ, IsZero (F.obj ((Φ.obj (K.X x)).X width))) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (total Φ width K)).Acyclic := by
  apply finiteDescending_acyclic
    ((F.mapHomologicalComplex (.up ℤ)).obj (total Φ width K))
    (fun a q => F.obj ((row Φ K q).X a))
    (fun a q => F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) q))
    (FiniteTotal.mapped_projections_injective (row Φ K) F)
  intro a q z closed higher
  have horizontal_closed :=
    mapped_total_highest_horizontal_closed Φ K F lastZero a q z closed higher
  by_cases bottom : q.val = 0
  · have positiveWidth : 0 < width := lt_of_le_of_lt (Nat.zero_le q.val) q.isLt
    have qzero : q = ⟨0,positiveWidth⟩ := Fin.ext bottom
    subst q
    have exactRow := exactRows (a + -(0 : ℤ)) 0
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at exactRow
    obtain ⟨y,hy⟩ := exactRow
      (F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) ⟨0,positiveWidth⟩) z)
      horizontal_closed
    have zeroEntry : (Φ.obj (K.X (a + -(0 : ℤ)))).d 0 0 = 0 :=
      (Φ.obj (K.X (a + -(0 : ℤ)))).shape 0 0 (by decide)
    change F.map ((Φ.obj (K.X (a + -(0 : ℤ)))).d 0 0) y = _ at hy
    rw [zeroEntry,F.map_zero] at hy
    change (0 : F.obj ((Φ.obj (K.X (a + -(0 : ℤ)))).X 0)) = _ at hy
    refine ⟨0,?_,?_⟩
    · intro r _
      simp only [map_zero]
    · simp only [map_zero]
      exact hy
  · let p : Fin width := ⟨q.val-1,by omega⟩
    have next : p.val+1=q.val := by dsimp [p]; omega
    have different : p ≠ q := by intro h; have := congrArg Fin.val h; omega
    have equality : (a-1) + -(p.val : ℤ) = a + -(q.val : ℤ) := by omega
    obtain ⟨y,hy⟩ := mapped_transportedHorizontal_surjective_on_cycles Φ K F
      ((a-1) + -(p.val : ℤ)) (a + -(q.val : ℤ)) p.val q.val equality
      ((ComplexShape.up ℕ).prev_eq' next)
      (exactRows _ _) _ horizontal_closed
    let b : F.obj ((total Φ width K).X (a-1)) :=
      F.map (biproduct.ι (fun p : Fin width => (row Φ K p).X (a-1)) p) y
    have arithmetic : a-1+1=a := by omega
    refine ⟨b,?_,?_⟩
    · intro r higher_r
      have pr : p ≠ r := by intro h; have := congrArg Fin.val h; omega
      have notNext : ¬p.val+1=r.val := by omega
      have entry := total_d_entry_ne Φ K (a-1) p r pr
      simp only [offEntry,dif_neg notNext] at entry
      rw [arithmetic] at entry
      have h := congrArg (fun f => F.map f y) entry
      simp only [F.map_comp,ModuleCat.comp_apply,
        F.map_zero,ModuleCat.hom_zero,LinearMap.zero_apply] at h
      exact h
    · have entry := total_d_entry_next Φ K (a-1) a arithmetic p q next
      have h := congrArg (fun f => F.map f y) entry
      simp only [F.map_comp,ModuleCat.comp_apply] at h
      exact h.trans hy

end ToricPower.FunctorTotal

end
