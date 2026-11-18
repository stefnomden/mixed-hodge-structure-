##############
#CONSTRUCTORS#
##############

function generalized_jacobian(J::Jacobian, punctures::Vector{GeometricPoint})

  F = function_field(J)
  @assert all(P -> function_field(P) === F, punctures)

  #maybe using place here is slow, however at some point these have 
  #to be computed perhaps not super nice to do this in the constructor 
  punctures = unique(place, punctures) 

  length(punctures) <= 1 && return J

  pivot = divisor(punctures[end])
  L = divisor_lattice(Divisor[divisor(P) - pivot for P in punctures[1:end - 1]])
  T = dual(L)

  return GeneralizedJacobian(J,T,punctures)
end

function generalized_jacobian(F::AbstractAlgebra.Generic.FunctionField, punctures::Vector{GeometricPoint})
  isempty(punctures) && return jacobian(F)

  @assert F === function_field(punctures[1])

  return generalized_jacobian(jacobian(F), punctures)
end

function generalized_jacobian(P::MPolyRingElem, punctures::Vector{GeometricPoint})
  isempty(punctures) && return jacobian(P)

  @assert plane_equation(punctures[1]) === P

  return generalized_jacobian(function_field(punctures[1]), punctures)
end

function generalized_jacobian_point(G::GeneralizedJacobian, P::TorusPoint, E::JacobianPoint; check = true)
  @assert parent(E) === jacobian(G)
  @assert parent(P) === torus(G)
  if check
    D = puncture_divisor(G)
    DE = divisor(E)
    iszero(gcd(D, lcm(DE, -DE))) || throw(ArgumentError("The divisor has support on the punctures"))
  end
  Q = GeneralizedJacobianPoint()
  Q.parent = G
  Q.torus_part = P 
  Q.jacobian_part = E
  return Q
end

function (G::GeneralizedJacobian)(P::TorusPoint, E::JacobianPoint; check = true)
  return generalized_jacobian_point(G,P,E; check = check)
end

function (G::GeneralizedJacobian)(P::TorusPoint)
  return G(P, zero(jacobian(G)) ;check = false)
end

function (G::GeneralizedJacobian)(E::JacobianPoint)
  return G(one(torus(G)), E)
end

function (G::GeneralizedJacobian)(E::Divisor)
  return G(jacobian(G)(E))
end

######################################################################

function Base.show(io::IO, G::GeneralizedJacobian)
  println(io, "Extension of the Jacobian of")
  J = jacobian(G)
  println(io, "  C : $(plane_equation(J)) = 0")
  T = torus(G)
  println(io, "By a torus of dimension $(dim(T))).")
end

function Base.show(io::IO, P::GeneralizedJacobianPoint)
  println(io, "QBar point of the extension of Jacobian J by a torus T")
  println(io, "represented by an element of T and a divisor of")
  show(io, function_field(P))
  println(io)
  print(io, "up to linear equivalence.")
end

######################################################################

Base.zero(G::GeneralizedJacobian) = generalized_jacobian_point(G, one(torus(G)), zero(jacobian(G)); check = false)
Base.zero(P::GeneralizedJacobianPoint) = zero(parent(P))

function iszero_with_data(P::GeneralizedJacobianPoint)
  A,f = iszero_with_data(P[2])

  if !A
    return A,nothing
  end

  G = parent(P)
  T = torus(G)
  puncs = punctures(G)

  f_at_pivot = evaluate(f,puncs[end])
  constant_pivot = T(QQBarFieldElem[f_at_pivot for _ in (1:dim(T))])
  f_at_other_pts = T(QQBarFieldElem[evaluate(f,P) for P in puncs[1:end - 1]])

  return P[1] == f_at_other_pts // constant_pivot, f
end

Base.iszero(P::GeneralizedJacobianPoint) = iszero_with_data(P)[1]

function Base.:+(P::GeneralizedJacobianPoint, Q::GeneralizedJacobianPoint)
  @assert parent(P) === parent(Q) 
  G = parent(P)
  #the check is false because we know that P and Q have support disjoint from the punctures
  return G(P[1] * Q[1], P[2] + Q[2]; check = false) 
end

function Base.:-(P::GeneralizedJacobianPoint)
  #the check is false because we know that P has support disjoint from the punctures
  return parent(P)(inv(P[1]), -P[2]; check = false)
end

Base.:-(P::GeneralizedJacobianPoint, Q::GeneralizedJacobianPoint) = P + (-Q)

Base.:(==)(P::GeneralizedJacobianPoint, Q::GeneralizedJacobianPoint) = parent(P) === parent(Q) && iszero(P - Q)
is_equal_with_data(P::GeneralizedJacobianPoint, Q::GeneralizedJacobianPoint) = iszero_with_data(P - Q)

function Base.:*(n::Int, P::GeneralizedJacobianPoint)
  #the check is false because we know that P has support disjoint from the punctures
  return parent(P)(P[1]^n, n * P[2]; check = false)
end

Base.:*(P::GeneralizedJacobianPoint, n::Int) = n * P
Base.:*(n::ZZRingElem, P::GeneralizedJacobianPoint) = Int(n) * P

function assure_has_structure(G::GeneralizedJacobian)
  if !isnothing(G.structure_morphism)
    return 
  end
  G.structure_morphism = extension_structure(torus(G), jacobian(G))
end

function extension_structure(G::GeneralizedJacobian)
  assure_has_structure(G)
  return G.structure_morphism
end

function assure_has_puncture_divisor(G::GeneralizedJacobian)
  if !isnothing(G.puncture_divisor)
    return
  end
  G.puncture_divisor = sum(divisor(P) for P in punctures(G); init = trivial_divisor(function_field(G)))
end

function puncture_divisor(G::GeneralizedJacobian)
  assure_has_puncture_divisor(G)
  return G.puncture_divisor
end

Base.getindex(P::GeneralizedJacobianPoint, i::Int) = [torus_part(P), jacobian_part(P)][i]

jacobian_part(P::GeneralizedJacobianPoint) = P.jacobian_part
torus_part(P::GeneralizedJacobianPoint) = P.torus_part
Hecke.parent(P::GeneralizedJacobianPoint) = P.parent

abelian_core(G::GeneralizedJacobian) = G.jacobian_core
jacobian(G::GeneralizedJacobian) = abelian_core(G)
Hecke.function_field(G::GeneralizedJacobian) = function_field(abelian_core(G))
Hecke.function_field(P::GeneralizedJacobianPoint) = function_field(parent(P))
torus(G::GeneralizedJacobian) = G.torus_part
Hecke.dim(G::GeneralizedJacobian) = dim(abelian_core(G)) + dim(torus(G))
plane_equation(G::GeneralizedJacobian) = plane_equation(abelian_core(G))
punctures(G::GeneralizedJacobian) = G.punctures
