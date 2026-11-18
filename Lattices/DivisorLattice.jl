function divisor_lattice(generators::Vector{<:Divisor})
  if isempty(generators)
    error("When there are no generating elements, please specify a function field")
  end
  F = Hecke.function_field(generators[1])
  return divisor_lattice(F,generators)
end

function divisor_lattice(generators::Vector{<:Hecke.GenOrdIdl})
  if isempty(generators)
    error("When there are no generating elements, please specify a function field")
  end
  F = function_field(order(generators[1]))
  return divisor_lattice(F,Hecke.divisor.(generators))
end

function divisor_lattice(F::AbstractAlgebra.Generic.AbsSimpleFunctionField, generators::Vector{<:Divisor})
  L = DivisorLattice()
  L.ambient_field = F
  @assert all(Hecke.function_field(D) == F for D in generators)
  #TODO: add option that checks whether divisors are actually linearly independent
  #this would be computationally expensive
  L.divisor_basis = generators
  return L
end

function Base.show(io::IO, L::DivisorLattice)
  r = rank(L)
  if iszero(r)
    println(io, "Zero lattice")
  else
    F = function_field(L)
    println(io,"Lattice of rank $(r) spanned by divisors of")
    show(io, F)
  end
end

function divisor_lattice_elem(L::DivisorLattice, M::ZZMatrix)

  num_row,num_col = size(M)
  @assert num_row == 1
  @assert num_col == rank(L)

  v = DivisorLatticeElem()
  v.parent = L
  v.vector_realisation = M
  v.divisor_realisation = nothing
  v.divisor_summands = nothing

  return v
end

function Base.show(io::IO, v::DivisorLatticeElem)
  F = function_field(v)
  if isnothing(F)
    println(io,"Zero element of the zero lattice")
  end
  println(io,"Element of lattice spanned by divisors of")
  show(io,F)
  println()
  println(io,"Row vector representation: ")
  show(io,v.vector_realisation)
  if !isnothing(v.divisor_realisation)
    println(io)
    println(io,"Divisor representation: ")
    show(io, v.divisor_realisation)
  end
end

function Base.:(==)(v::DivisorLatticeElem, w::DivisorLatticeElem)
  return parent(v) === parent(w) && coordinates(v) == coordinates(w)
end

function Base.:+(v::DivisorLatticeElem, w::DivisorLatticeElem)
  @assert parent(v) === parent(w)
  result = parent(v)(v.vector_realisation + w.vector_realisation)

  Dv = if !isnothing(v.divisor_realisation)
    [(v.divisor_realisation, 1)]
  else
    v.divisor_summands
  end

  Dw = if !isnothing(w.divisor_realisation)
    [(w.divisor_realisation, 1)]
  else
    w.divisor_summands
  end

  if !isnothing(Dv) && !isnothing(Dw)
    result.divisor_summands = vcat(Dv,Dw)
  end

  return result
end

function Base.:*(a::Int, v::DivisorLatticeElem)
  result = parent(v)(ZZ(a) * v.vector_realisation)

  Dv = if !isnothing(v.divisor_realisation)
    [(v.divisor_realisation, a)]
  elseif !isnothing(v.divisor_summands)
    [(D,a * b) for (D,b) in v.divisor_summands]
  else
    nothing
  end

  if !isnothing(Dv)
    result.divisor_summands = Dv
  end

  return result
end

Base.:*(v::DivisorLatticeElem, a::Int) = a * v
Base.:-(v::DivisorLatticeElem) = (-1) * v
Base.:-(v::DivisorLatticeElem, w::DivisorLatticeElem) = v + (-w)

function (L::DivisorLattice)(v::Vector{ZZRingElem})
  return L(matrix(ZZ, 1, length(v), v))
end

function (L::DivisorLattice)(v::Vector{Int64})
  return L(ZZ.(v))
end

function (L::DivisorLattice)(v::ZZMatrix)
  return divisor_lattice_elem(L,v)
end

function (L::DivisorLattice)(v::Vararg{Integer})
  return L(ZZRingElem[a for a in v])
end

function sublattice(L::DivisorLattice, generators::Vector{DivisorLatticeElem})
  n = rank(L)
  @assert all(n == size(coordinates(v))[2] for v in generators)

  A = reduce(vcat, [coordinates(v) for v in generators])
  H = hnf(A)
  r = Hecke.rank(H)
  B = H[1:r, :]
  min_gen_set = [L(B[j:j, :]) for j in 1:r]

  K = divisor_lattice([Hecke.divisor(v) for v in min_gen_set])
  i = hom(K,L,B)

  return K,i

end


function Hecke.divisor(v::DivisorLatticeElem)
  if !isnothing(v.divisor_realisation)
    return v.divisor_realisation
  end

  if !isnothing(v.divisor_summands)
    zero = trivial_divisor(function_field(v))
    result = sum(Int(a) * D for (D,a) in v.divisor_summands ;init = zero)
  else
    zero = trivial_divisor(function_field(v))
    coeffs = first(eachrow(v.vector_realisation))
    divs = basis(parent(v))
    result = sum(Int(a) * D for (a,D) in zip(coeffs, divs); init = zero)
  end

  v.divisor_realisation = result
  v.divisor_summands = nothing
  return Hecke.divisor(v)
end



function Hecke.coordinates(v::DivisorLatticeElem)
  return v.vector_realisation
end

function Hecke.rank(L::DivisorLattice)
  return length(L.divisor_basis)
end

function Hecke.basis(L::DivisorLattice)
  return L.divisor_basis
end

function Base.zero(L::DivisorLattice)
  return L(ZZRingElem[0 for _ in 1:rank(L)])
end

Base.zero(v::DivisorLatticeElem) = zero(parent(v))
Base.iszero(v::DivisorLatticeElem) = iszero(coordinates(v))

function Hecke.parent(v::DivisorLatticeElem)
  return v.parent
end

function Hecke.function_field(L::DivisorLattice)
  return L.ambient_field
end

function Hecke.function_field(v::DivisorLatticeElem)
  return function_field(parent(v))
end