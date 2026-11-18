module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Bounded derived objects with prescribed homology

Canonical truncations retain any isomorphism-closed property of homology
which contains zero. The proof uses actual isomorphisms on surviving
homology groups, not an unjustified closure under subobjects or quotients.
Finite truncation induction then assembles a bounded object from its
single-degree homology objects.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]

/-- Every actual homology object has the indicated property. -/
def derivedHomologyIn (Q : ObjectProperty B) : ObjectProperty (DerivedCategory B) :=
  fun X => ∀ q : ℤ, Q ((DerivedCategory.homologyFunctor B q).obj X)

variable (Q : ObjectProperty B) [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]

theorem derivedHomologyIn_truncLT (X : DerivedCategory B)
    (members : derivedHomologyIn Q X) (b : ℤ) :
    derivedHomologyIn Q ((DerivedCategory.TStructure.t.truncLT b).obj X) := by
  let t := DerivedCategory.TStructure.t (C := B)
  let T := (t.triangleLTGE b).obj X
  have distinguished := t.triangleLTGE_distinguished b X
  intro q
  by_cases hq : q < b
  · letI : Mono ((DerivedCategory.homologyFunctor B q).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T distinguished (q - 1) q (by omega)).mpr
        ((DerivedCategory.isZero_of_isGE T.obj₃ b (q - 1) (by omega)).eq_of_src _ _)
    letI : Epi ((DerivedCategory.homologyFunctor B q).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
        T distinguished q).mpr
        ((DerivedCategory.isZero_of_isGE T.obj₃ b q hq).eq_of_tgt _ _)
    letI : IsIso ((DerivedCategory.homologyFunctor B q).map T.mor₁) :=
      isIso_of_mono_of_epi _
    exact Q.prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor B q).map T.mor₁)).symm (members q)
  · exact Q.prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((t.truncLT b).obj X) (b - 1) q (by omega))

theorem derivedHomologyIn_truncGE (X : DerivedCategory B)
    (members : derivedHomologyIn Q X) (b : ℤ) :
    derivedHomologyIn Q ((DerivedCategory.TStructure.t.truncGE b).obj X) := by
  let t := DerivedCategory.TStructure.t (C := B)
  let T := (t.triangleLTGE b).obj X
  have distinguished := t.triangleLTGE_distinguished b X
  intro q
  by_cases hq : b ≤ q
  · letI : Mono ((DerivedCategory.homologyFunctor B q).map T.mor₂) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff
        T distinguished q).mpr
        ((DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) q (by omega)).eq_of_src _ _)
    letI : Epi ((DerivedCategory.homologyFunctor B q).map T.mor₂) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        T distinguished q (q + 1) rfl).mpr
        ((DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (q + 1) (by omega)).eq_of_tgt _ _)
    letI : IsIso ((DerivedCategory.homologyFunctor B q).map T.mor₂) :=
      isIso_of_mono_of_epi _
    exact Q.prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor B q).map T.mor₂)) (members q)
  · exact Q.prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((t.truncGE b).obj X) b q (by omega))

variable (P : ObjectProperty (DerivedCategory B))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  (single : ∀ (M : B) (n : ℤ), Q M → P ((DerivedCategory.singleFunctor B n).obj M))

include single

theorem concentrated_mem_of_homology_in (X : DerivedCategory B)
    (members : derivedHomologyIn Q X) (n : ℤ) [X.IsGE n] [X.IsLE n] : P X := by
  obtain ⟨M, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let eH := (DerivedCategory.homologyFunctor B n).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).app M
  exact P.prop_of_iso e.symm (single M n (Q.prop_of_iso eH (members n)))

/-- A finite induction on the cohomological interval, using the actual
canonical truncation triangles. -/
theorem bounded_mem_of_homology_in (X : DerivedCategory B)
    (bounded : DerivedCategory.TStructure.t.bounded X)
    (members : derivedHomologyIn Q X) : P X := by
  let t := DerivedCategory.TStructure.t (C := B)
  have interval : ∀ n : ℕ, ∀ (K : DerivedCategory B) (a : ℤ),
      K.IsGE a → K.IsLE (a + n) → derivedHomologyIn Q K → P K := by
    intro n
    induction n with
    | zero =>
        intro K a ge le mem
        letI := ge
        letI : K.IsLE a := by simpa using le
        exact concentrated_mem_of_homology_in Q P single K mem a
    | succ n ih =>
        intro K a ge le mem
        letI := ge
        letI := le
        let b : ℤ := a + (n + 1 : ℕ)
        have hb : b - 1 = a + n := by dsimp [b]; omega
        have leftLE : ((t.truncLT b).obj K).IsLE (a + n) := by
          have h : ((t.truncLT b).obj K).IsLE (b - 1) := inferInstance
          simpa only [hb] using h
        have left : P ((t.truncLT b).obj K) :=
          ih _ a inferInstance leftLE (derivedHomologyIn_truncLT Q K mem b)
        have right : P ((t.truncGE b).obj K) := by
          letI : ((t.truncGE b).obj K).IsLE b := by
            change ((t.truncGE b).obj K).IsLE (a + (n + 1 : ℕ))
            infer_instance
          exact concentrated_mem_of_homology_in Q P single _
            (derivedHomologyIn_truncGE Q K mem b) b
        exact P.ext_of_isTriangulatedClosed₂ _ (t.triangleLTGE_distinguished b K) left right
  obtain ⟨⟨a, ge⟩, ⟨b, le⟩⟩ := bounded
  letI := ge
  letI := le
  exact interval (b - a).toNat X a ge
    (t.isLE_of_le X b _ (by omega)) members

end ToricPower

end
