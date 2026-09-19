import RBM3D.Basic
import RBM3D.Defs.Lattice
import RBM3D.Defs.Neighbours
import RBM3D.Defs.Shells
import RBM3D.Defs.Params
import RBM3D.Defs.Tail
import RBM3D.Defs.Block
import RBM3D.Defs.Domination
import RBM3D.Propagator.Basic
import RBM3D.Propagator.Props4
import RBM3D.Kernel.Evolution
import RBM3D.Propagator.Interface
import RBM3D.Graph.ScalingOrder
import RBM3D.Graph.Model
import RBM3D.Graph.Expansions
import RBM3D.Test.Axioms

/-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
#assert_rbm_axioms
