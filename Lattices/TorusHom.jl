function Hecke.hom(T1::Torus, T2::Torus, A::ZZMatrix)
  d1 = dim(T1)
  d2 = dim(T2)
  dims = size(A)
  @assert d1 == dims[1]
  @assert d2 == dims[2]
  f = TorusHom{typeof(T1), typeof(T2)}()
  f.domain = T1
  f.codomain = T2 
  f.representing_matrix = deepcopy(A)
  return f
end

function Hecke.hom(T1::Torus, T2::Torus, A::Vector{Vector{Int}})
  n, m = dim(T1), dim(T2)
  @assert length(A) == n
  @assert all(length(row) == m for row in A)
  entries = Int[a for row in A for a in row]
  return hom(T1, T2, matrix(ZZ, n, m, entries))
end

function Base.show(io::IO, f::TorusHom)
  println(io,"Morphism of tori from")
  show(io,domain(f))
  println(io)
  println(io,"to")
  println(io,codomain(f))
  println(io,"Represented by matrix:")
  show(io, MIME"text/plain"(), matrix(f))
end

Hecke.identity(T::Torus) = dual(identity(dual(T)))

function (f::TorusHom)(P::TorusPoint)
  @assert domain(f) === parent(P)
  v = coordinates(P)
  A = matrix(f)
  codomain(f)(QQBarFieldElem[prod(a^n for (a,n) in zip(v,col); init=one(QQBar)) for col in eachcol(A)])
end

function Base.:*(f::TorusHom, g::TorusHom)
  @assert codomain(f) === domain(g)
  return hom(domain(f), codomain(g), matrix(f) * matrix(g))
end

is_injective(f::TorusHom) = is_surjective(dual(f))
is_surjective(f::TorusHom) = is_injective(dual(f))
is_bijective(f::TorusHom) = is_bijective(dual(f))

function dual(f::TorusHom)
  T1 = domain(f)
  T2 = codomain(f)
  A = matrix(f)
  return hom(dual(T2), dual(T1), transpose(A))
end

function dual(f::LatticeHom)
  L1 = domain(f)
  L2 = codomain(f)
  A = matrix(f)
  return hom(dual(L2), dual(L1), transpose(A))
end

function Hecke.domain(f::TorusHom)
  return f.domain
end

function Hecke.codomain(f::TorusHom)
  return f.codomain
end

function Hecke.matrix(f::TorusHom)
  return f.representing_matrix
end