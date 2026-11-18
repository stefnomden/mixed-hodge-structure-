#constant field is QQBar here.

##############
#CONSTRUCTORS#
##############
function jacobian(F::AbstractAlgebra.Generic.FunctionField)
  J = Jacobian{typeof(F)}()
  J.function_field = F

  J.plane_equation = function_field_to_plane_equation(F)

  return J
end

function jacobian(P::MPolyRingElem)
  F = plane_equation_to_function_field(P)
  return jacobian(F)
end

function Hecke.function_field(J::Jacobian)
  return J.function_field
end

function Hecke.function_field(P::JacobianPoint)
  return function_field(parent(P))
end

function jacobian_point(J::Jacobian, D::Divisor)
  @assert function_field(J) === function_field(D)
  @assert iszero(degree(D))
  P = JacobianPoint()
  P.divisor_representation = D
  P.parent = J
  return P
end

(J::Jacobian)(D::Divisor) = jacobian_point(J,D)
(J::Jacobian)(D1::Divisor, D2::Divisor) = J(D1 - D2)
(J::Jacobian)(v::DivisorLatticeElem) = J(Hecke.divisor(v))

###############################################################

function Base.show(io::IO, J::Jacobian)
  println(io,"Jacobian J of smooth curve C with plane equation")
  println(io)
  println(io,"  C : $(plane_equation(J)) = 0")
  println(io)
  println(io,"Closed points on J are represented as degree 0 divisors of")
  show(io, function_field(J))
end

function Base.show(io::IO, P::JacobianPoint)
  A,f = iszero_with_data(P) 
  J = parent(P)
  if A === true
    println(io, "Identity element of jacobian J of smooth curve C with plane equation")
    print(io, "  C : $(plane_equation(J)) = 0")
  elseif A === false
    println(io, "Non-trivial element of jacobian J of smooth curve C with plane equation")
    print(io, "  C : $(plane_equation(J)) = 0")
  else 
    println(io,"Point on the Jacobian of smooth curve C with plane equation")
    print(io, "  C : $(plane_equation(J)) = 0")
  end  
end


function Base.zero(J::Jacobian)
  P = J(trivial_divisor(function_field(J)))
  P.is_principal_with_data = (true, one(function_field(J)))
  return P
end

Base.zero(P::JacobianPoint) = zero(parent(P))

function Base.iszero(P::JacobianPoint)
  if !isnothing(P.is_principal_with_data[1])
    return P.is_principal_with_data[1]
  end

  A,f = is_principal_with_data(Hecke.divisor(P))
  if A
    P.is_principal_with_data = (A,f)
  else 
    P.is_principal_with_data = (A,nothing)
  end

  return A
end

function iszero_with_data(P::JacobianPoint)
  iszero(P)
  return P.is_principal_with_data
end

function Base.:+(P::JacobianPoint, Q::JacobianPoint)
  @assert parent(P) === parent(Q)
  J = parent(P)
  result = J(Hecke.divisor(P) + Hecke.divisor(Q))

  A,f = P.is_principal_with_data
  B,g = Q.is_principal_with_data

  if isnothing(A) || isnothing(B)
    return result
  end

  #if there is already data for P or Q being principal, 
  #pass it on to their sum
  if (A && B) === true
    result.is_principal_with_data = (true, f * g)
  elseif xor(A,B) === true 
  #exactly one of A or B is zero so the other one is not
    result.is_principal_with_data = (false, nothing)
  end
  return result
end

function Base.:-(P::JacobianPoint)
  J = parent(P)
  result = J(-Hecke.divisor(P))
  A,f = P.is_principal_with_data

  #if we know principal data of P then we pass it on
  if A === true
    result.is_principal_with_data = (A,inv(f))
  elseif A === false
    result.is_principal_with_data = (A,nothing)
  end
  return result
end

function Base.:*(n::Int, P::JacobianPoint)
  J = parent(P)
  result = J(n * Hecke.divisor(P))
  A,f = P.is_principal_with_data

  if iszero(n)
    result.is_principal_with_data = (true, one(function_field(J)))
  elseif A === true
    result.is_principal_with_data = (true, n < 0 ? inv(f)^(-n) : f^n)
  elseif A === false && (n == 1 || n == -1)
    result.is_principal_with_data = (false, nothing)
  end

  return result
end

Base.:*(P::JacobianPoint, n::Int) = n * P
Base.:*(n::ZZRingElem, P::JacobianPoint) = Int(n) * P
Base.:-(P::JacobianPoint, Q::JacobianPoint) = P + (-Q)
Base.:(==)(P::JacobianPoint, Q::JacobianPoint) = parent(P) === parent(Q) && iszero(P - Q)

is_equal_with_data(P::JacobianPoint, Q::JacobianPoint) = iszero_with_data(P-Q)

function Hecke.divisor(P::JacobianPoint)
  return P.divisor_representation
end

function Hecke.parent(P::JacobianPoint)
  return P.parent
end

Hecke.dim(J::Jacobian) = Hecke.genus(function_field(J))
plane_equation(J::Jacobian) = J.plane_equation

