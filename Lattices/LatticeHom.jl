function Hecke.hom(L1::AbstractLattice, L2::AbstractLattice, A::ZZMatrix)
  f = LatticeHom{typeof(L1), typeof(L2)}()
  dims = size(A)
  r1,r2 = rank(L1), rank(L2)
  
  @assert r1 == dims[1]
  @assert r2 == dims[2]

  f.domain = L1
  f.codomain = L2
  A1 = Hecke.free_abelian_group(rank(L1))
  A2 = Hecke.free_abelian_group(rank(L2))
  f.group_hom = Hecke.hom(A1, A2, deepcopy(A))
  
  return f 
end

function Hecke.hom(L1::AbstractLattice, L2::AbstractLattice, A::Vector{Vector{Int}})

  n, m = rank(L1), rank(L2)

  @assert length(A) == n
  @assert all(length(row) == m for row in A)

  entries = Int[a for row in A for a in row]
  return hom(L1, L2, matrix(ZZ, n, m, entries))
end

function Base.show(io::IO, f::LatticeHom)
  println(io,"Morphism of lattices from")
  show(io,domain(f))
  println(io)
  println(io,"to")
  println(io,codomain(f))
  println(io)
  println(io,"Represented by matrix:")
  show(io, MIME"text/plain"(), matrix(f))
end

function Hecke.identity(L::AbstractLattice)
  return hom(L,L,identity_matrix(ZZ, rank(L)))
end

function Base.:*(a::Int, f::LatticeHom)
  A = matrix(f)
  return hom(domain(f), codomain(f), a * A)
end

Base.:*(f::LatticeHom, a::Int) = a * f
Base.:-(f::LatticeHom) = (-1) * f

function Base.:(==)(f::LatticeHom, g::LatticeHom)
  return (
    codomain(f) === codomain(g) &&
    domain(f) === domain(g) &&
    matrix(f) == matrix(g)
  )
end

function Base.:*(f::LatticeHom, g::LatticeHom)
  @assert codomain(f) === domain(g)
  return hom(domain(f), codomain(g), matrix(f) * matrix(g))
end

function (f::LatticeHom)(v::AbstractLatticeElem)
  @assert f.domain === parent(v)
  A = matrix(f)
  return f.codomain(coordinates(v) * A)
end

is_injective(f::LatticeHom) = Hecke.is_injective(f.group_hom)
is_surjective(f::LatticeHom) = Hecke.is_surjective(f.group_hom)
is_bijective(f::LatticeHom) = Hecke.is_bijective(f.group_hom)

function is_identity(f::LatticeHom)
  return matrix(f) == identity(domain(f))
end

function Hecke.matrix(f::LatticeHom)
  return f.group_hom.map
end

function Hecke.domain(f::LatticeHom)
  return f.domain
end

function Hecke.codomain(f::LatticeHom)
  return f.codomain
end