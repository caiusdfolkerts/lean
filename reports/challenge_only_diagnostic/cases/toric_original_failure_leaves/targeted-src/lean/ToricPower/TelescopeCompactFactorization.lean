module

public import ToricPower.TelescopeCoproductMap

/-!
# Compact maps into an actual sequential telescope

A telescope is a distinguished cone of the genuine `1 - shift` map on
the sequence coproduct. Every map from a compact object into this cone
factors through one stage, provided the negative shift of the source is
also compact. We also construct comparison maps from compatible stage
maps by the ordinary distinguished-triangle exactness theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{0} C]

/-- An actual distinguished mapping telescope; the existence proof below
constructs this data from the triangulated-category axioms. -/
structure Telescope (F : ℕ ⥤ C) where
  obj : C
  inclusion : (∐ F.obj) ⟶ obj
  boundary : obj ⟶ (∐ F.obj)⟦(1 : ℤ)⟧
  distinguished : Triangle.mk (telescopeMap F) inclusion boundary ∈ distTriang C

theorem telescope_nonempty (F : ℕ ⥤ C) : Nonempty (Telescope F) := by
  obtain ⟨X, i, d, distinguished⟩ := distinguished_cocone_triangle (telescopeMap F)
  exact ⟨⟨X, i, d, distinguished⟩⟩

namespace Telescope

variable {F : ℕ ⥤ C} (T : Telescope F)

abbrev triangle : Triangle C := Triangle.mk (telescopeMap F) T.inclusion T.boundary

def ι (n : ℕ) : F.obj n ⟶ T.obj := Sigma.ι F.obj n ≫ T.inclusion

theorem transition_ι (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ T.ι (n + 1) = T.ι n := by
  have zero := congrArg (fun f => Sigma.ι F.obj n ≫ f)
    (comp_distTriang_mor_zero₁₂ T.triangle T.distinguished)
  change Sigma.ι F.obj n ≫ telescopeMap F ≫ T.inclusion = _ at zero
  rw [← Category.assoc, ι_telescopeMap, Preadditive.sub_comp, comp_zero] at zero
  simpa only [ι, Category.assoc] using (sub_eq_zero.mp zero).symm

theorem map_ι {i j : ℕ} (le : i ≤ j) : F.map (homOfLE le) ≫ T.ι j = T.ι i := by
  induction j, le using Nat.le_induction with
  | base => simp
  | succ j le induction =>
      rw [show homOfLE (Nat.le_trans le (Nat.le_succ j)) =
        homOfLE le ≫ homOfLE (Nat.le_succ j) from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_comp, Category.assoc, T.transition_ι, induction]

/-- Compatible maps out of the stages induce a map out of the actual
telescope. No uniqueness is asserted for arbitrary sources. -/
theorem exists_desc {Y : C} (maps : ∀ n, F.obj n ⟶ Y)
    (compatible : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ maps (n + 1) = maps n) :
    ∃ (desc : T.obj ⟶ Y), ∀ n, T.ι n ≫ desc = maps n := by
  let total : (∐ F.obj) ⟶ Y := Sigma.desc maps
  have zero : telescopeMap F ≫ total = 0 := by
    apply Sigma.hom_ext
    intro n
    rw [ι_telescopeMap_assoc, Preadditive.sub_comp]
    simp only [total, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      compatible, sub_self, comp_zero]
  obtain ⟨desc, equation⟩ := T.triangle.yoneda_exact₂ T.distinguished total zero
  change total = T.inclusion ≫ desc at equation
  refine ⟨desc, fun n => ?_⟩
  dsimp only [ι]
  rw [Category.assoc, ← equation]
  exact Sigma.ι_comp_desc maps n

/-- Every map from a compact source into the actual telescope comes
from one finite stage. Both required compactness hypotheses are explicit. -/
theorem factor_from_compact {X : C}
    (compact : CoproductCompact.{u, v, 0} X)
    (compactShift : CoproductCompact.{u, v, 0} (X⟦(-1 : ℤ)⟧))
    (f : X ⟶ T.obj) : ∃ (n : ℕ) (lift : X ⟶ F.obj n), lift ≫ T.ι n = f := by
  have boundaryZero : f ≫ T.boundary = 0 := by
    apply shifted_telescopeMap_comp_injective compactShift F
    rw [Category.assoc]
    change f ≫ (T.triangle.mor₃ ≫ T.triangle.mor₁⟦(1 : ℤ)⟧') = 0
    rw [comp_distTriang_mor_zero₃₁ T.triangle T.distinguished, comp_zero]
  obtain ⟨total, totalEq⟩ := T.triangle.coyoneda_exact₃ T.distinguished f boundaryZero
  obtain ⟨s, lift, factor⟩ := compact ℕ F.obj total
  let n := s.sup id
  let collapse : (∐ fun i : s => F.obj i) ⟶ F.obj n :=
    Sigma.desc (fun i : s => F.map (homOfLE (Finset.le_sup (f := id) i.property)))
  have collapseEq : collapse ≫ T.ι n = finiteCoproductInclusion F.obj s ≫ T.inclusion := by
    apply Sigma.hom_ext
    intro i
    dsimp only [collapse, finiteCoproductInclusion]
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
    exact T.map_ι (Finset.le_sup (f := id) i.property)
  refine ⟨n, lift ≫ collapse, ?_⟩
  rw [Category.assoc, collapseEq, ← Category.assoc, factor]
  exact totalEq.symm

end Telescope
end ToricPower.CompactExtraction

end
