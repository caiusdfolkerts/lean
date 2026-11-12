module

public import ToricPower.DiagonalGlobalComplex
public import ToricPower.DivisorWeightAdditive
public import ToricPower.SheafTensor

/-!
# The actual global map to the diagonal structure sheaf

The augmentation is defined on the genuine product scheme.  On a cell
labelled by `x`, multiplication gives
`L(-x) ⊗ L(x) → O_X`, since the sum of the two divisor coefficients is
zero on a ray wall and minus one off it.  Pullback along the actual
diagonal, followed by its actual sheaf adjunction, gives the required
map from the exterior product to `δ_* O_X`.

This file constructs the morphism, without assuming any boundary law or
local comparison.  Those are further proof obligations; the definition
does not encode them.  Development source, pending Lean checking.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones)
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "δX" => pullback.diagonal fan.algebraicRealizationStructureMap

/-- The diagonal is the literal diagonal of the actual toric scheme over
the coefficient field. -/
abbrev toricDiagonal : X ⟶ toricDiagonalProduct fan := δX

/-- Both factors of an exterior product restrict to the original sheaf
along the diagonal.  These are the canonical pullback composition and
identity isomorphisms. -/
def diagonalFirstPullbackIso :
    Scheme.Modules.pullback (toricDiagonalFirst fan) ⋙
      Scheme.Modules.pullback (toricDiagonal fan) ≅ 𝟭 (X).Modules :=
  Scheme.Modules.pullbackComp (toricDiagonal fan) (toricDiagonalFirst fan) ≪≫
    Scheme.Modules.pullbackCongr
      (pullback.diagonal_fst fan.algebraicRealizationStructureMap) ≪≫
    Scheme.Modules.pullbackId X

def diagonalSecondPullbackIso :
    Scheme.Modules.pullback (toricDiagonalSecond fan) ⋙
      Scheme.Modules.pullback (toricDiagonal fan) ≅ 𝟭 (X).Modules :=
  Scheme.Modules.pullbackComp (toricDiagonal fan) (toricDiagonalSecond fan) ≪≫
    Scheme.Modules.pullbackCongr
      (pullback.diagonal_snd fan.algebraicRealizationStructureMap) ≪≫
    Scheme.Modules.pullbackId X

/-- The canonical tensor comparison on the diagonal for arbitrary two
module sheaves; its naturality is used for the cellular character maps. -/
def diagonalPullbackExternalMap (M P : (X).Modules) :
    (Scheme.Modules.pullback (toricDiagonal fan)).obj
        ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj M ⊗
          (Scheme.Modules.pullback (toricDiagonalSecond fan)).obj P) ⟶ M ⊗ P :=
  Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (toricDiagonal fan))
      ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj M)
      ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj P) ≫
    ((diagonalFirstPullbackIso fan).hom.app M ⊗ₘ
      (diagonalSecondPullbackIso fan).hom.app P)

@[reassoc]
theorem diagonalPullbackExternalMap_natural {M M' P P' : (X).Modules}
    (f : M ⟶ M') (g : P ⟶ P') :
    (Scheme.Modules.pullback (toricDiagonal fan)).map
        ((Scheme.Modules.pullback (toricDiagonalFirst fan)).map f ⊗ₘ
          (Scheme.Modules.pullback (toricDiagonalSecond fan)).map g) ≫
      diagonalPullbackExternalMap fan M' P' =
    diagonalPullbackExternalMap fan M P ≫ (f ⊗ₘ g) := by
  have hfirst := (diagonalFirstPullbackIso fan).hom.naturality f
  have hsecond := (diagonalSecondPullbackIso fan).hom.naturality g
  simp only [Functor.comp_map, Functor.id_map] at hfirst hsecond
  dsimp only [diagonalPullbackExternalMap]
  rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
    tensorHom_comp_tensorHom,
    hfirst, hsecond,
    ← tensorHom_comp_tensorHom, Category.assoc]

/-- The coefficient sum is computed from the actual arrangement wall
label.  No integrality of the chosen vertex is assumed. -/
theorem diagonalCoefficient_sum {d : ℕ} (c : NormalizedCell A d) (ρ : fan.Ray) :
    diagonalLeftCoefficients fan basis rays c ρ +
        diagonalRightCoefficients fan basis rays c ρ =
      if Sum.inl (rays.symm ρ) ∈ c.val.val.2 then 0 else -1 := by
  unfold diagonalLeftCoefficients diagonalRightCoefficients reflectedCeiling
  split_ifs <;> omega

theorem diagonalCoefficient_sum_nonpos {d : ℕ}
    (c : NormalizedCell A d) (ρ : fan.Ray) :
    diagonalLeftCoefficients fan basis rays c ρ +
      diagonalRightCoefficients fan basis rays c ρ ≤ 0 := by
  rw [diagonalCoefficient_sum]
  split_ifs <;> omega

/-- Multiplication of the actual two Cartier sheaves, followed by the
actual character-zero inclusion into the structure sheaf. -/
def diagonalTensorToStructure {d : ℕ} (c : NormalizedCell A d) :
    diagonalLeftSheaf fan nonempty regular basis rays c ⊗
        diagonalRightSheaf fan nonempty regular basis rays c ⟶
      SheafOfModules.unit (X).ringCatSheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantCartierTensorIso fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c)
      (diagonalRightCoefficients fan basis rays c)).hom ≫
    toricCartierMonomialMap fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c +
        diagonalRightCoefficients fan basis rays c) 0 0
      (by
        intro ρ
        have h := diagonalCoefficient_sum_nonpos fan basis rays c ρ
        simpa only [Pi.zero_apply, Pi.add_apply, AddMonoidHom.zero_apply,
          zero_sub, add_zero, neg_nonneg] using h) ≫
    (invariantCartierZeroSheafIso fan nonempty regular).inv

/-- Pullback of the actual exterior product along the actual diagonal,
using the canonical tensor comparison. -/
def diagonalPullbackProductMap {d : ℕ} (c : NormalizedCell A d) :
    (Scheme.Modules.pullback (toricDiagonal fan)).obj
        (diagonalProductSheaf fan nonempty regular basis rays c) ⟶
      diagonalLeftSheaf fan nonempty regular basis rays c ⊗
        diagonalRightSheaf fan nonempty regular basis rays c :=
  diagonalPullbackExternalMap fan
    (diagonalLeftSheaf fan nonempty regular basis rays c)
    (diagonalRightSheaf fan nonempty regular basis rays c)

/-- The target is the genuine direct image of the structure sheaf along
the scheme diagonal, rather than a separately defined quotient module. -/
abbrev diagonalStructureSheaf : (toricDiagonalProduct fan).Modules :=
  (Scheme.Modules.pushforward (toricDiagonal fan)).obj
    (SheafOfModules.unit (X).ringCatSheaf)

/-- The global augmentation of one labelled line-bundle term, defined by
the actual pullback--pushforward adjunction. -/
def diagonalProductAugmentation {d : ℕ} (c : NormalizedCell A d) :
    diagonalProductSheaf fan nonempty regular basis rays c ⟶
      diagonalStructureSheaf fan :=
  (Scheme.Modules.pullbackPushforwardAdjunction (toricDiagonal fan)).homEquiv _ _
    (diagonalPullbackProductMap fan nonempty regular basis rays c ≫
      diagonalTensorToStructure fan nonempty regular basis rays c)

local instance diagonalGlobalAugmentationBiproducts :
    HasFiniteBiproducts (toricDiagonalProduct fan).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance diagonalGlobalAugmentationCellsFintype (d : ℕ) : Fintype (NormalizedCell A d) := Fintype.ofFinite _

/-- The degree-zero augmentation is assembled from the individual maps
by the finite biproduct universal property. -/
def diagonalGlobalAugmentation :
    diagonalGlobalSheafTerm fan nonempty regular basis rays 0 ⟶
      diagonalStructureSheaf fan :=
  biproduct.desc (fun c : NormalizedCell A 0 =>
    diagonalProductAugmentation fan nonempty regular basis rays c)

@[reassoc]
theorem diagonalGlobalAugmentation_column (c : NormalizedCell A 0) :
    biproduct.ι
        (fun j : NormalizedCell A 0 => diagonalProductSheaf fan nonempty regular basis rays j) c ≫
      diagonalGlobalAugmentation fan nonempty regular basis rays =
    diagonalProductAugmentation fan nonempty regular basis rays c := by
  simp only [diagonalGlobalAugmentation, biproduct.ι_desc]

end ToricPower
