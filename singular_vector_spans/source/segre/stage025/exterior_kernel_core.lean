module
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs
public import SegreVerified.Stage001
public import SegreVerified.Stage002
public import SegreVerified.Stage003
public import SegreVerified.Stage004
public import SegreVerified.Stage005
public import SegreVerified.Stage006
public import SegreVerified.Stage007
public import SegreVerified.Stage008
public import SegreVerified.Stage009
public import SegreVerified.Stage010
public import SegreVerified.Stage011
public import SegreVerified.Stage012
public import SegreVerified.Stage013
public import SegreVerified.Stage014
public import SegreVerified.Stage015
public import SegreVerified.Stage016
public import SegreVerified.Stage017
public import SegreVerified.Stage018
public import SegreVerified.Stage019
public import SegreVerified.Stage020
public import SegreVerified.Stage021
public import SegreVerified.Stage022
public import SegreVerified.Stage023
public import SegreVerified.Stage024

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.Push
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Sym2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Logic.Equiv.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Lean.Util.CollectAxioms
import all Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Lean.Util.Sorry
public import Lean.Elab.Command
public import Lean.PrettyPrinter

public import SegreVerified.Stage025.ProjectiveCech
public import SegreVerified.Stage025.ProjectiveSections
public import SegreVerified.Stage025.Euler

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreProjectiveCohomology

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreProjectiveCohomology"
  out.flush

/-!
# Projective exterior cohomology and the full Koszul gap

The named sections preserve the original proof stages and local scopes.
-/


section SegreSheafExteriorKernel

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreSheafExteriorKernel"
  out.flush
set_option maxHeartbeats 600000

/-!
# Canonical exterior-kernel comparison for actual sheaves

The map from the exterior power of the kernel sheaf to contraction cycles is
constructed before any splitting is chosen. On a section module on which the
functional takes the value one, it is a full isomorphism by the explicit split
exterior-kernel calculation. This makes the local comparisons compatible on
intersections: their forward map is always the same canonical exterior inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false



namespace PaperVerification.Segre.SheafExteriorKernel

open CategoryTheory Limits
open TauCeti
open TauCeti.SheafOfModules (ringCatSheaf)
open SheafKoszul

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}
variable {M : SheafOfModules.{u} (ringCatSheaf R)}

open Opposite TopologicalSpace

/-- Injectivity on every subopen of a cover gives local injectivity. -/
theorem locallyInjective_of_injective_on_cover_subopens
    {X : Type u} [TopologicalSpace X]
    {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ G)
    {ι : Type u} (V : ι → Opens X) (hV : iSup V = ⊤)
    (hf : ∀ i U, U ≤ V i → Function.Injective (f.app (op U))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f where
  equalizerSieve_mem {U} a b h := by
    intro x hxU
    have hx : x ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    let W := U.unop ⊓ V i
    have hWU : W ≤ U.unop := inf_le_left
    refine ⟨W, homOfLE hWU, ?_, ⟨hxU, hi⟩⟩
    apply hf i W inf_le_right
    change f.app (op W) (F.map (homOfLE hWU).op a) =
      f.app (op W) (F.map (homOfLE hWU).op b)
    calc
      f.app (op W) (F.map (homOfLE hWU).op a) =
          G.map (homOfLE hWU).op (f.app U a) :=
        congrArg (fun q : F.obj U ⟶ G.obj (op W) => q a)
          (f.naturality (homOfLE hWU).op)
      _ = G.map (homOfLE hWU).op (f.app U b) := congrArg _ h
      _ = f.app (op W) (F.map (homOfLE hWU).op b) :=
        (congrArg (fun q : F.obj U ⟶ G.obj (op W) => q b)
          (f.naturality (homOfLE hWU).op)).symm

/-- Surjectivity on every subopen of a cover gives local surjectivity. -/
theorem locallySurjective_of_surjective_on_cover_subopens
    {X : Type u} [TopologicalSpace X]
    {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ G)
    {ι : Type u} (V : ι → Opens X) (hV : iSup V = ⊤)
    (hf : ∀ i U, U ≤ V i → Function.Surjective (f.app (op U))) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f where
  imageSieve_mem {U} a := by
    intro x hxU
    have hx : x ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    let W := U ⊓ V i
    have hWU : W ≤ U := inf_le_left
    exact ⟨W, homOfLE hWU, hf i W inf_le_right
      (G.map (homOfLE hWU).op a), ⟨hxU, hi⟩⟩

/-- Evaluation is additive because both the forgetful functor and presheaf evaluation are. -/
local instance evaluation_additive (U : Cᵒᵖ) :
    (SheafOfModules.evaluation (ringCatSheaf R) U).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- Actual kernel-sheaf sections equal the full algebraic kernel of the section functional. -/
def sheafKernelSectionsEquiv (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (U : Cᵒᵖ) :
    (kernel φ).val.obj U ≃ₗ[R.obj.obj U] LinearMap.ker (sectionFunctional φ U) :=
  ((PreservesKernel.iso (SheafOfModules.evaluation (ringCatSheaf R) U) φ) ≪≫
    ModuleCat.kernelIsoKer ((SheafOfModules.evaluation (ringCatSheaf R) U).map φ)).toLinearEquiv

@[simp] theorem sheafKernelSectionsEquiv_val
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (U : Cᵒᵖ) (z : (kernel φ).val.obj U) :
    (sheafKernelSectionsEquiv φ U z).val=(kernel.ι φ).val.app U z := by
  let F := SheafOfModules.evaluation (ringCatSheaf R) U
  have h : ((PreservesKernel.iso F φ) ≪≫ ModuleCat.kernelIsoKer (F.map φ)).hom ≫
      ModuleCat.ofHom (F.map φ).hom.ker.subtype=F.map (kernel.ι φ) := by
    simp only [Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype]
    erw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact ConcreteCategory.congr_hom h z

/-- Evaluation of the categorical presheaf contraction kernel gives its full algebraic kernel. -/
def cycleSectionsEquiv (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) (U : Cᵒᵖ) :
    (kernel (presheafDifferential φ p)).obj U ≃ₗ[R.obj.obj U]
      LinearMap.ker (koszulDifferential (sectionFunctional φ U) p) :=
  ((PreservesKernel.iso (PresheafOfModules.evaluation (ringCatSheaf R).obj U)
      (presheafDifferential φ p)) ≪≫
    ModuleCat.kernelIsoKer ((PresheafOfModules.evaluation (ringCatSheaf R).obj U).map
      (presheafDifferential φ p))).toLinearEquiv

@[simp] theorem cycleSectionsEquiv_val
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) (U : Cᵒᵖ)
    (z : (kernel (presheafDifferential φ p)).obj U) :
    (cycleSectionsEquiv φ p U z).val=(kernel.ι (presheafDifferential φ p)).app U z := by
  let F := PresheafOfModules.evaluation (ringCatSheaf R).obj U
  have h : ((PreservesKernel.iso F (presheafDifferential φ p)) ≪≫
      ModuleCat.kernelIsoKer (F.map (presheafDifferential φ p))).hom ≫
      ModuleCat.ofHom (F.map (presheafDifferential φ p)).hom.ker.subtype=
        F.map (kernel.ι (presheafDifferential φ p)) := by
    simp only [Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype]
    erw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact ConcreteCategory.congr_hom h z

set_option maxHeartbeats 2000000 in
/-- Whenever a section has functional value one, every full presheaf cycle
is the image of the next contraction differential. -/
theorem presheafBoundary_surjective_of_unit_value
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) (U : Cᵒᵖ)
    (m : M.val.obj U) (hm : sectionFunctional (R := R) (M := M) φ U m = 1) :
    Function.Surjective
      ((kernel.lift (presheafDifferential (R := R) (M := M) φ p)
        (presheafDifferential (R := R) (M := M) φ (p + 1))
        (presheafDifferential_squared (R := R) (M := M) φ p)).app U) := by
  intro y
  let ecycle : (kernel (presheafDifferential (R := R) (M := M) φ p)).obj U
      ≃ₗ[R.obj.obj U]
        LinearMap.ker (koszulDifferential (sectionFunctional (R := R) (M := M) φ U) p) :=
    cycleSectionsEquiv (R := R) (M := M) φ p U
  let z : LinearMap.ker
      (koszulDifferential (sectionFunctional (R := R) (M := M) φ U) p) := ecycle y
  have hex := SplitKoszul.exact_koszul_of_unit_value
    (sectionFunctional (R := R) (M := M) φ U) m hm p
  obtain ⟨w, hw⟩ := (hex z.val).mp z.property
  refine ⟨w, ?_⟩
  apply ecycle.injective
  apply Subtype.ext
  change (cycleSectionsEquiv (R := R) (M := M) φ p U
    ((kernel.lift (presheafDifferential (R := R) (M := M) φ p)
      (presheafDifferential (R := R) (M := M) φ (p + 1))
      (presheafDifferential_squared (R := R) (M := M) φ p)).app U w)).val = z.val
  rw [cycleSectionsEquiv_val]
  have h := congrArg
    (fun f :
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+2)).obj M.val) ⟶
        ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj M.val) =>
      (f.app' U).hom w)
    (kernel.lift_ι (presheafDifferential (R := R) (M := M) φ p)
      (presheafDifferential (R := R) (M := M) φ (p + 1))
      (presheafDifferential_squared (R := R) (M := M) φ p))
  exact h.trans hw

/-- Exterior inclusion of the actual kernel sheaf, before taking contraction cycles. -/
def presheafExteriorInclusion (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj (kernel φ).val) ⟶
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj M.val) :=
  (PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).map (kernel.ι φ).val

/-- The canonical exterior inclusion lands in contraction cycles. -/
theorem presheafExteriorInclusion_differential
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) :
    presheafExteriorInclusion (R := R) φ p ≫
      presheafDifferential (R := R) (M := M) φ p = 0 := by
  ext U : 1
  apply ModuleCat.exteriorPower.hom_ext
    (R := R.obj.obj U)
    (M := PresheafOfModulesOfCommRing.obj (R := R.obj) (kernel φ).val U)
    (n := p + 1)
  ext v
  change koszulDifferential (sectionFunctional (R := R) φ U) p
    (exteriorPower.map (p+1) ((kernel.ι φ).val.app' U).hom
      (exteriorPower.ιMulti (R.obj.obj U) (p+1) v)) = 0
  erw [exteriorPower.map_apply_ιMulti, koszulDifferential_ιMulti]
  apply Finset.sum_eq_zero
  intro i _
  have hz : sectionFunctional (R := R) φ U (((kernel.ι φ).val.app' U).hom (v i)) = 0 := by
    exact congrArg
      (fun f : kernel φ ⟶ SheafOfModules.unit (ringCatSheaf R) =>
        (f.val.app' U).hom (v i)) (kernel.condition φ)
  erw [hz, mul_zero, zero_smul]

/-- The canonical exterior power of the kernel maps to the categorical contraction kernel. -/
def presheafExteriorKernelMap (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj (kernel φ).val) ⟶
      kernel (presheafDifferential φ p) :=
  kernel.lift (presheafDifferential (R := R) φ p)
    (presheafExteriorInclusion (R := R) φ p)
    (presheafExteriorInclusion_differential (R := R) φ p)

@[simp] theorem presheafExteriorKernelMap_val
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) (U : Cᵒᵖ)
    (z : ⋀[R.obj.obj U]^(p+1) (PresheafOfModulesOfCommRing.obj (R := R.obj) (kernel φ).val U)) :
    (cycleSectionsEquiv φ p U ((presheafExteriorKernelMap φ p).app U z)).val=
      exteriorPower.map (p+1) ((kernel.ι φ).val.app' U).hom z := by
  rw [cycleSectionsEquiv_val]
  exact congrArg
    (fun f :
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj (kernel φ).val) ⟶
        ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj M.val) =>
      (f.app' U).hom z)
    (kernel.lift_ι (presheafDifferential φ p)
      (presheafExteriorInclusion φ p) (presheafExteriorInclusion_differential φ p))

set_option maxHeartbeats 2000000 in
/-- On any open on which the functional takes the value one, the canonical map is a full
isomorphism. No bound is imposed on the exterior degree or on section coefficients. -/
theorem presheafExteriorKernelMap_bijective_of_unit_value
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) (U : Cᵒᵖ)
    (m : M.val.obj U) (hm : sectionFunctional φ U m=1) :
    Function.Bijective ((presheafExteriorKernelMap φ p).app U) := by
  let e := sheafKernelSectionsEquiv φ U
  let eext := LinearEquiv.ofBijective (exteriorPower.map (p+1) e.toLinearMap)
    (exteriorPower.map_bijective e.bijective)
  let esplit := SplitKoszul.exteriorKernelEquiv (sectionFunctional φ U) m hm p
  let ecycle : (kernel (presheafDifferential (R := R) (M := M) φ p)).obj U ≃ₗ[R.obj.obj U]
      LinearMap.ker (koszulDifferential (sectionFunctional (R := R) (M := M) φ U) p) :=
    cycleSectionsEquiv (R := R) (M := M) φ p U
  have hcomp (z : ⋀[R.obj.obj U]^(p+1)
      (PresheafOfModulesOfCommRing.obj (R := R.obj) (kernel φ).val U)) :
      ecycle ((presheafExteriorKernelMap φ p).app U z)=esplit (eext z) := by
    apply Subtype.ext
    change (cycleSectionsEquiv φ p U ((presheafExteriorKernelMap φ p).app U z)).val = _
    erw [presheafExteriorKernelMap_val]
    change exteriorPower.map (p+1) ((kernel.ι φ).val.app' U).hom z=
      exteriorPower.map (p+1) (LinearMap.ker (sectionFunctional φ U)).subtype
        (exteriorPower.map (p+1) e.toLinearMap z)
    rw [← LinearMap.comp_apply,← exteriorPower.map_comp]
    congr 2
    ext x
    exact (sheafKernelSectionsEquiv_val φ U x).symm
  have hb : Function.Bijective (fun z => ecycle ((presheafExteriorKernelMap φ p).app U z)) := by
    have heq : (fun z => ecycle ((presheafExteriorKernelMap (R := R) φ p).app U z)) =
        (fun z => esplit (eext z)) := funext hcomp
    rw [heq]
    exact esplit.bijective.comp eext.bijective
  exact Function.Bijective.of_comp_left
    (f := ecycle) (g := (presheafExteriorKernelMap (R := R) (M := M) φ p).app U)
    hb ecycle.injective

/-- Sheafification of the presheaf contraction cycles is canonically the
kernel of the actual sheaf contraction. -/
def cycleComparisonIso (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) :
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
      (kernel (presheafDifferential (R := R) (M := M) φ p)) ≅
        kernel (differential (R := R) (M := M) φ p) :=
  PreservesKernel.iso (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
      (presheafDifferential (R := R) (M := M) φ p) ≪≫
    kernel.mapIso
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (presheafDifferential (R := R) (M := M) φ p))
      (differential (R := R) (M := M) φ p)
      (SheafOfModules.exteriorPowerIso (R := R) (p+1) M).symm
      (SheafOfModules.exteriorPowerIso (R := R) p M).symm
      (by simp only [differential, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])

/-- The comparison preserves the canonical inclusion of cycles. -/
@[reassoc] theorem cycleComparisonIso_hom_comp_ι
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) :
    (cycleComparisonIso (R := R) (M := M) φ p).hom ≫
      kernel.ι (differential (R := R) (M := M) φ p) =
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (kernel.ι (presheafDifferential (R := R) (M := M) φ p)) ≫
        (SheafOfModules.exteriorPowerIso (R := R) (p+1) M).inv := by
  dsimp only [cycleComparisonIso, Iso.trans_hom]
  erw [Category.assoc, kernel.mapIso_hom]
  simp only [kernel.lift_ι, PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι_assoc _ _ _

/-- The resulting canonical map on actual sheaf exterior powers. -/
def exteriorKernelMap (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (p : ℕ) :
    (SheafOfModules.exteriorPower R (p+1)).obj (kernel φ) ⟶
      kernel (differential (R := R) (M := M) φ p) := by
  let F : PresheafOfModules.{u} ((ringCatSheaf R).obj) ⥤
      SheafOfModules.{u} (ringCatSheaf R) :=
    PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)
  let E (n : ℕ) (N : SheafOfModules.{u} (ringCatSheaf R)) :
      (SheafOfModules.exteriorPower R n).obj N ≅
        F.obj ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj N.val) :=
    SheafOfModules.exteriorPowerIso (R := R) n N
  let D : ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj M.val) ⟶
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) p).obj M.val) :=
    presheafDifferential (R := R) (M := M) φ p
  have hD : F.map D ≫ (E p M).inv =
      (E (p+1) M).inv ≫ differential (R := R) (M := M) φ p := by
    dsimp only [F, D, E]
    simp only [differential, Category.assoc, Iso.inv_hom_id_assoc]
  let eD : kernel (F.map D) ≅ kernel (differential (R := R) (M := M) φ p) :=
    kernel.mapIso (F.map D) (differential (R := R) (M := M) φ p)
      (E (p+1) M).symm (E p M).symm hD
  let eF : F.obj (kernel D) ≅ kernel (F.map D) :=
    PreservesKernel.iso F D
  let m :
      F.obj ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) (p+1)).obj
        (kernel φ).val) ⟶ F.obj (kernel D) :=
    F.map (presheafExteriorKernelMap (R := R) (M := M) φ p)
  exact (E (p+1) (kernel φ)).hom ≫ m ≫ eF.hom ≫ eD.hom

end PaperVerification.Segre.SheafExteriorKernel

end SegreSheafExteriorKernel


section SegreSchemeCycleComparison

namespace PaperVerification.Segre.SchemeCycleComparison

open AlgebraicGeometry CategoryTheory Limits

universe u
variable {Y : Scheme.{u}} {M : Y.Modules}

/-- The canonical cycle comparison in the native scheme-module presentation. -/
def iso (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf) (p : ℕ) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
      (kernel (SheafKoszul.presheafDifferential (R := Y.sheaf) (M := M) φ p)) ≅
        kernel (SheafKoszul.differential (R := Y.sheaf) (M := M) φ p) :=
  SheafExteriorKernel.cycleComparisonIso (R := Y.sheaf) (M := M) φ p

/-- The native scheme comparison preserves the actual kernel inclusions. -/
@[reassoc] theorem hom_comp_ι
    (φ : M ⟶ SheafOfModules.unit Y.ringCatSheaf) (p : ℕ) :
    (iso (Y := Y) (M := M) φ p).hom ≫
      kernel.ι (SheafKoszul.differential (R := Y.sheaf) (M := M) φ p) =
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
        (kernel.ι (SheafKoszul.presheafDifferential (R := Y.sheaf) (M := M) φ p)) ≫
        (SheafOfModules.exteriorPowerIso (R := Y.sheaf) (p + 1) M).inv :=
  SheafExteriorKernel.cycleComparisonIso_hom_comp_ι
    (R := Y.sheaf) (M := M) φ p

end PaperVerification.Segre.SchemeCycleComparison
end SegreSchemeCycleComparison


end SegreProjectiveCohomology

end
end
end ProbeLayer391

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
