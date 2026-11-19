module

public import ToricPower.CoproductProjectorMap
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.Interval

/-!
# Finite-support complexes are compact for actual coproducts

A complex with finitely many nonzero terms is compact whenever those
terms are compact. One finite union of coefficient supports works for
the entire chain map; applying the canonical projector preserves the
differential equations automatically.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.CompactExtraction

universe u v w t
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasCoproducts.{w} A]
variable {ι : Type t} {shape : ComplexShape ι}

theorem complex_coproductCompact_of_finite_support
    (P : HomologicalComplex A shape) (support : Finset ι)
    (outside : ∀ q, q ∉ support → IsZero (P.X q))
    (compact : ∀ q, q ∈ support → CoproductCompact.{u,v,w} (P.X q)) :
    CoproductCompact.{max u v t,max v t,w} P := by
  classical
  apply coproductCompact_iff_projector.mpr
  intro I family f
  have localSupport (q : support) :
      ∃ s : Finset I,
        (((eval A shape q.val).map f ≫
          (PreservesCoproduct.iso (eval A shape q.val) family).hom) ≫
            finiteCoproductProjector (fun i => (family i).X q.val) s) =
          (eval A shape q.val).map f ≫
            (PreservesCoproduct.iso (eval A shape q.val) family).hom :=
    (coproductCompact_iff_projector.mp (compact q.val q.property)) I
      (fun i => (family i).X q.val)
      ((eval A shape q.val).map f ≫
        (PreservesCoproduct.iso (eval A shape q.val) family).hom)
  choose supports equations using localSupport
  let total := Finset.univ.biUnion supports
  refine ⟨total, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q ∈ support
  · let j : support := ⟨q,hq⟩
    have componentSupport := finiteSupport_mono
      (fun i => (family i).X q)
      ((eval A shape q).map f ≫ (PreservesCoproduct.iso (eval A shape q) family).hom)
      (Finset.subset_biUnion_of_mem supports (Finset.mem_univ j)) (equations j)
    exact support_of_mapped_support (eval A shape q) family f total componentSupport
  · exact (outside q hq).eq_of_src _ _

theorem boundedComplex_coproductCompact
    (P : CochainComplex A ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (compact : ∀ q, CoproductCompact.{u,v,w} (P.X q)) :
    CoproductCompact.{max u v,v,w} P := by
  apply complex_coproductCompact_of_finite_support P (Finset.Icc a b) _
    (fun q _ => compact q)
  intro q hq
  by_cases h : q < a
  · exact P.isZero_of_isStrictlyGE a q h
  · exact P.isZero_of_isStrictlyLE b q (by
      simp only [Finset.mem_Icc] at hq
      omega)

end ToricPower.CompactExtraction

end
