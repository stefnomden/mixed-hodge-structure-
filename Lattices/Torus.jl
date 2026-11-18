function torus(X::AbstractLattice)
  T = Torus{typeof(X)}()
  T.character_lattice = X
  return T
end

function torus_point(T,P::MatType)
  num_row, num_col = size(P)
  @assert dim(T) == num_col
  @assert 1 == num_row
  @assert all(!iszero(a) for a in eachcol(P))
  point = TorusPoint()
  point.parent = T
  point.vector_realisation = P
  return point
end

function (T::Torus)(P::MatType)
  return torus_point(T,P)
end

function (T::Torus)(P::Vector{QQBarFieldElem})
  return T(reshape(QQBar.(P), 1, length(P)))
end

function (T::Torus)(P...)
  return T(QQBarFieldElem[QQBar(a) for a in P])
end


function Base.show(io::IO, T::Torus)
  n = dim(T)
  if iszero(n)
    println(io,"The trivial torus")
  else
    println(io,"Torus of dimension dimension $(n)")
    println(io,"represented as Hom(L,Gm) for a lattice L of rank $(n)")
  end
end

function Base.:(==)(T1::Torus, T2::Torus)
  return character_lattice(T1) === character_lattice(T2)
end

function Base.show(io::IO, P::TorusPoint)
  T = parent(P)
  n = dim(T)
  if iszero(n)
    println(io, "The trivial element of the trivial torus")
  else
    println(io,"Point on dimension $(n) torus Hom(L,Gm)")
    println(io,"represented with respect to a basis of L with vector of algebraic numbers:")
    print(io,"[")
    for a in coordinates(P)[1:end-1]
      show(io,a)
      print(io,"   ")
    end
    show(io,coordinates(P)[end])
    println(io,"]")
  end
end

function Base.:(==)(P::TorusPoint, Q::TorusPoint)
  return parent(P) === parent(Q) && coordinates(P) == coordinates(Q)
end

function Base.:*(P::TorusPoint, Q::TorusPoint)
  @assert parent(P) === parent(Q)
  v = coordinates(P)
  w = coordinates(Q)
  return parent(P)([a*b for (a,b) in zip(v,w)])
end

Base.:+(P::TorusPoint, Q::TorusPoint) = P * Q

function Base.:*(a::QQBarFieldElem, P::TorusPoint)
  return parent(P)([a * b for b in coordinates(P)])
end

Base.:*(a::Any, P::TorusPoint) = QQBar(a) * P
Base.:*(P::TorusPoint, a::Any) = a * P

function Base.://(P::TorusPoint, Q::TorusPoint)
  @assert parent(P) === parent(Q)
  v = coordinates(P)
  w = coordinates(Q)
  return parent(P)(QQBarFieldElem[a // b for (a,b) in zip(v,w)])
end

Base.:-(P::TorusPoint, Q::TorusPoint) = P // Q
Base.://(P::TorusPoint, a::QQBarFieldElem) = (1//a) * P

function Base.:^(P::TorusPoint, n::Int)
  return parent(P)(QQBarFieldElem[a^n for a in coordinates(P)])
end

function Base.:^(P::TorusPoint, q::Rational{Int})
  return parent(P)([a^q for a in coordinates(P)])
end

function Base.inv(P::TorusPoint)
  return parent(P)([1//a for a in coordinates(P)])
end

function Base.one(T::Torus)
  return T(QQBarFieldElem[1 for _ in 1:dim(T)])
end

function Base.one(P::TorusPoint)
  return one(parent(P))
end

function Base.isone(P::TorusPoint)
  return all(isone(a) for a in coordinates(P))
end

function Hecke.evaluate(P::TorusPoint, v::DivisorLatticeElem)
  @assert parent(P) === dual(parent(v))
  v_cor = coordinates(v)
  P_cor = coordinates(P)
  return prod(b^n for (n,b) in zip(v_cor, P_cor); init = one(QQBar))
end

function (P::TorusPoint)(v::DivisorLatticeElem)
  return evaluate(P,v)
end

function character_lattice(T::Torus)
  return T.character_lattice
end

Hecke.dim(T::Torus) = rank(dual(T::Torus))
dual(T::Torus) = character_lattice(T::Torus)

Hecke.function_field(T::Torus) = function_field(dual(T))
Hecke.function_field(P::TorusPoint) = function_field(parent(P))

function dual(X::AbstractLattice)
  return get!(torus_cache, X) do 
    torus(X)
  end
end

function Hecke.parent(P::TorusPoint)
  return P.parent
end

function Hecke.coordinates(P::TorusPoint)
  return P.vector_realisation
end