include("/Users/stefnomden/period_relations/Lattices/types.jl")

include("/Users/stefnomden/period_relations/Lattices/DivisorLattice.jl")
include("/Users/stefnomden/period_relations/Lattices/LatticeHom.jl")
include("/Users/stefnomden/period_relations/Lattices/Torus.jl")
include("/Users/stefnomden/period_relations/Lattices/TorusHom.jl")
include("/Users/stefnomden/period_relations/Lattices/Jacobian.jl")
include("/Users/stefnomden/period_relations/Lattices/GeometricPoint.jl")
include("/Users/stefnomden/period_relations/Lattices/Marking.jl")
include("/Users/stefnomden/period_relations/Lattices/GeneralizedJacobian.jl")


#include("/Users/stefnomden/period_relations/Lattices/include.jl")

#&#&#&#&#&#&#&#&#&#&#
#&&&&&& TESTS &&&&&&#
#&#&#&#&#&#&#&#&#&#&#

include("/Users/stefnomden/period_relations/Lattices/tests/lattice_test.jl")
include("/Users/stefnomden/period_relations/Lattices/tests/torus_test.jl")
include("/Users/stefnomden/period_relations/Lattices/tests/jacobian_test.jl")
include("/Users/stefnomden/period_relations/Lattices/tests/geopoint_test.jl"); GeometricPointTests.runtests(Main)
include("/Users/stefnomden/period_relations/Lattices/tests/generalized_jacobian_test.jl"); GeneralizedJacobianTests.runtests(Main)
