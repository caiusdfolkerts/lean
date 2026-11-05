import cubical_indecomposability.block.interfaces
import cubical_indecomposability.projective_geometry

/-!
# An affine equivalence of the two interfaces

The normalized block admits a rank-one affine shear carrying F onto H and
fixing their common quadrilateral pointwise. Invertibility is proved from
the exact kernel relation between its direction and its linear functional.
The body equality follows from affine transport of convex hulls.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

/-- The linear functional in the interface shear. -/
def interfaceLinear : E 4 →ₗ[ℝ] ℝ :=
  (-1 / 165 : ℝ) • (EuclideanSpace.proj (0 : Fin 4)).toLinearMap +
  (-4468 / 156585 : ℝ) • (EuclideanSpace.proj (2 : Fin 4)).toLinearMap +
  (-77459 / 7985835 : ℝ) • (EuclideanSpace.proj (3 : Fin 4)).toLinearMap

def interfaceDirection : E 4 := WithLp.toLp 2 ![-11, 11, -15, 51]

def interfaceConstant : ℝ := 18851 / 313170

theorem interface_kernel : interfaceLinear interfaceDirection = 0 := by
  change (-1 / 165 : ℝ) * (-11) + (-4468 / 156585) * (-15) +
    (-77459 / 7985835) * 51 = 0
  norm_num

/-- The ambient affine equivalence, with an explicit inverse shear. -/
def interfaceShear : E 4 ≃ᵃ[ℝ] E 4 :=
  affineShear interfaceLinear interfaceDirection interfaceConstant interface_kernel

def interfaceSource : Fin 8 → Fin 32 := ![24, 25, 26, 27, 28, 29, 30, 31]
def interfaceTarget : Fin 8 → Fin 32 := ![24, 8, 26, 10, 28, 12, 30, 14]

theorem interfaceSource_image : Finset.univ.image interfaceSource = FLabels := by decide
theorem interfaceTarget_image : Finset.univ.image interfaceTarget = HLabels := by decide

/-- The exact correspondence between all eight interface vertices. -/
theorem interfaceShear_vertex (b : Fin 8) :
    interfaceShear (p (interfaceSource b)) = p (interfaceTarget b) := by
  fin_cases b
  · ext i
    fin_cases i
    · change ((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
    · change ((-306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((-306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
    · change ((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
    · change ((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((0 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
    · change ((-51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((0 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
    · change ((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((51 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
    · change ((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((51 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
    · change ((-2388959 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((-2388959 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
    · change ((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
    · change ((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((272 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
    · change ((-357 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((-17 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
    · change ((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((510 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
    · change ((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((408 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
    · change ((3096445 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((3096445 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
    · change ((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
    · change ((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((0 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
    · change ((701 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((121 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
    · change ((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((102 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
    · change ((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((102 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
    · change ((24668895 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((24668895 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
    · change ((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
    · change ((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((544 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num
    · change ((4907 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((1121 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num
    · change ((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((1020 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num
    · change ((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((816 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num

/-- The shear maps the complete set of F vertices onto the H vertices. -/
theorem interfaceShear_image_vertices :
    interfaceShear '' (p '' (FLabels : Set (Fin 32))) =
      p '' (HLabels : Set (Fin 32)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hv' : v ∈ Finset.univ.image interfaceSource := by
      rwa [interfaceSource_image]
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv'
    refine ⟨interfaceTarget b, ?_, (interfaceShear_vertex b).symm⟩
    change interfaceTarget b ∈ HLabels
    rw [← interfaceTarget_image]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ Finset.univ.image interfaceTarget := by
      rwa [interfaceTarget_image]
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv'
    refine ⟨p (interfaceSource b), ⟨interfaceSource b, ?_, rfl⟩,
      interfaceShear_vertex b⟩
    change interfaceSource b ∈ FLabels
    rw [← interfaceSource_image]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

/-- Equality of entire geometric facets, obtained from their vertex hulls. -/
theorem interfaceShear_image : interfaceShear '' F = H := by
  change interfaceShear.toAffineMap '' facet 5 = facet 21
  rw [facet_eq_hull, facet_eq_hull, F_labels, H_labels,
    AffineMap.image_convexHull]
  exact congrArg (convexHull ℝ) interfaceShear_image_vertices

/-- The interface equivalence fixes the common quadrilateral pointwise. -/
theorem interfaceShear_fixes_Q : ∀ x ∈ Q, interfaceShear x = x := by
  have hvertices : (p '' (QLabels : Set (Fin 32))).EqOn
      interfaceShear.toAffineMap (AffineMap.id ℝ (E 4)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = 24 ∨ v = 26 ∨ v = 28 ∨ v = 30 := by
      simpa only [QLabels, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton] using hv
    rcases hv' with rfl | rfl | rfl | rfl
    · exact interfaceShear_vertex 0
    · exact interfaceShear_vertex 2
    · exact interfaceShear_vertex 4
    · exact interfaceShear_vertex 6
  intro x hx
  rw [Q, indexedFace_eq_hull, Q_labels] at hx
  exact AffineMap.eqOn_affineSpan hvertices (convexHull_subset_affineSpan _ hx)

/-- Proposition 5(iv), with the identity projectivity on this normalized block. -/
theorem affine_interface_normalization :
    HasAffineInterfaceNormalization polytope F H Q :=
  affine_interface_normalization_of_affine polytope F H Q interfaceShear
    interfaceShear_image interfaceShear_fixes_Q

end CubicalIndecomposability.Block
