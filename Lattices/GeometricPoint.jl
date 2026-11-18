function (C::PuncturedMarkedCurve)(p::Hecke.GenOrdIdl)
  F = function_field(C)
  eq = plane_equation(C)
  @assert function_field(order(p)) === F
  @assert is_prime(p)
  P = GeometricPoint()
  P.parent_object = C
  P.place = p
  ev = evaluate(p)
  P.ev = ev

  x,y = F(gen(base_ring(F))), gen(F)
  O = order(p)
  t = anti_uniformizer(p)
  e = base_ring(O) isa KInftyRing ? Hecke.ramification_index(p) : nothing

  if base_ring(O) isa KInftyRing
    x_val = -Hecke.ramification_index(p)
  else
    q = minimum(p)
    x_val = iszero(q(0)) ? Hecke.ramification_index(p) : 0
  end

  if base_ring(O) isa KInftyRing
    y_n, y_d = Hecke.integral_split(y,O)
    y_n = F(y_n)
    y_val = 0
    while iszero(ev(F(y_n)))
      y_val += 1
      y_n *= t
    end
    if parent(y_d) isa KInftyRing
      y_val -= e * valuation(y_d)
    else 
      y_val -= e * valuation(y_d,minimum(p))
    end
  else 
    y_val = 0
  end

  P.is_infinite = x_val < 0 ? true : false
  if P.is_infinite
    if y_val < x_val
      P.coordinates = (ev(x//y), one(QQBar), ev(1//y))
    else
      P.coordinates = (one(QQBar), ev(y//x), ev(1//x))
    end
  else
    P.coordinates = (ev(x), ev(y), one(QQBar))
  end

  h_eq = homogenise(plane_equation(P))
  @assert iszero(h_eq(P.coordinates...))
  derivatives = [derivative(h_eq,i) for i in (1:3)]
  if all(iszero(f(P.coordinates...)) for f in derivatives)
    P.is_singular = true
  else
    P.is_singular = false
  end

  return P
end

function (C::PuncturedMarkedCurve)(p::Vector{QQBarFieldElem}; index = nothing)
  @assert length(p) in [2,3]
  h_eq = homogenise(plane_equation(C))
  coords = length(p) == 2 ? (p[1],p[2],one(QQBar)) : (p[1],p[2],p[3])

  all(iszero, coords) && throw(ArgumentError("Projective coordinates cannot all be zero"))
  iszero(h_eq(coords...)) || throw(ArgumentError("The point does not lie on F = 0"))

  field = function_field(C)

  P = GeometricPoint()
  P.coordinates = coords
  P.parent_object = C

  derivatives = [derivative(h_eq,i) for i in (1:3)]
  if all(iszero(f(P.coordinates...)) for f in derivatives)
    P.is_singular = true
    isnothing(index) && error("The point is singular, add 'index' to choose point in normalization")
  else
    P.is_singular = false
  end

  P.is_infinite = iszero(coords[3]) ? true : false

  if !P.is_singular
    return P
  end

  O = P.is_infinite ? infinite_maximal_order(field) : finite_maximal_order(field)

  x,y = field(gen(base_ring(field))), gen(field)
  if P.is_infinite
    a,b = coords[1], coords[2]
    if !iszero(a)
      u = inv(x)
      v = y/x - b/a
    else
      u = inv(y)
      v = x/y
    end

    I = u * O + v * O

    J = Hecke.simplify(intersect(I,ideal(O,one(O))))

    places = [a for (a,_) in factor(numerator(J))]
    P.associated_places = places
    P.place = places[index]

  else
    a,b = coords[1]//coords[3], coords[2]//coords[3]
    I = ideal(O,x - a, y - b)
    places = [a for (a,_) in factor(I)]
    P.associated_places = places
    P.place = places[index]
  end

  return P
end

function (C::PuncturedMarkedCurve)(p::AbstractVector; index = nothing)
  return C(QQBarFieldElem[QQBar(a) for a in p]; index)
end

function (C::PuncturedMarkedCurve)(p...; index = nothing)
  return C(QQBarFieldElem[QQBar(a) for a in p]; index)
end


function Base.show(io::IO, P::GeometricPoint)
  println(io, "Point defined over the algebraic numbers on the normalisation of")
  h_eq = homogenise(plane_equation(P))
  println(io, "   C: $(h_eq) = 0")
  c = coordinates(P)
  if is_singular(P)
    print(io, "Lying above the plane point ")
    println(io, "($(c[1]) : $(c[2]) : $(c[3]))")
    print(io, "and represented by a place of the function field")
  else
    println(io, "represented by the point ($(c[1]) : $(c[2]) : $(c[3]))")
    print(io, "which is smooth on the plane model.")
  end
end 

function places_above(P::GeometricPoint)
  !is_singular(P) && return GeometricPoint[P]

  C = parent(P)

  if isnothing(P.associated_places)
    Q = C(collect(coordinates(P)); index = 1)
    return GeometricPoint[C(p) for p in Q.associated_places]
  end

  return GeometricPoint[C(p) for p in P.associated_places]
end

places_above(C::PuncturedMarkedCurve, p::Vector{QQBarFieldElem}) = places_above(C(p; index = 1))
Hecke.divisor(P::GeometricPoint) = Hecke.divisor(place(P))

function Hecke.evaluate(
  f::AbstractAlgebra.Generic.FunctionFieldElem,
  P::GeometricPoint
)
  @assert parent(f) === function_field(P)
  iszero(f) && return zero(QQBar)

  X,Y,Z = coordinates(P)
  
  if !iszero(Z)
    a,b = X/Z, Y/Z
    den = denominator(f)(a)
    if !iszero(den)
      #in this case we can just plug in (a,b) into f.
      n = numerator(f) #element of k[x][y]
      num = n(b)(a)
      return num / den
    end
  end

  return evaluate(P)(f)

end

#TODO evaluate(f,P), when P is smooth just compute it by plugging in

function assure_has_place(P::GeometricPoint)
  if !isnothing(P.place)
    return 
  end

  F = function_field(P)
  x,y = F(gen(base_ring(F))), gen(F)
  C = coordinates(P)

  #in the constructor we always define P.place except 
  #when P is given as a smooth point in the plane model 
  if is_infinite(P)
    O = infinite_maximal_order(function_field(P))
    a,b = C[1], C[2]
    if !iszero(a)
      u = inv(x)
      v = y/x - b/a
    else
      u = inv(y)
      v = x/y
    end

    I = u * O + v * O

    P.place = numerator(Hecke.simplify(intersect(I,ideal(O,one(O)))))

  else
    O = finite_maximal_order(F)
    a,b = C[1]//C[3], C[2]//C[3]
    P.place = Hecke.ideal(O, x - a, y - b)
  end
end

function Base.:(==)(P::GeometricPoint, Q::GeometricPoint)
  parent(P) === parent(Q) || return false
  xor(is_smooth(P), is_smooth(Q)) && return false
  is_singular(P) && return place(P) == place(Q)

  p,q = coordinates(P), coordinates(Q)

  return all(
    p[i] * q[j] == p[j] * q[i] for i in 1:3 for j in (i+1):3
  )
end

function assure_has_ev(P::GeometricPoint)
  if !isnothing(P.ev)
    return
  end
  assure_has_place(P)
  P.ev = evaluate(place(P))
end

function place(P::GeometricPoint)
  assure_has_place(P)
  return P.place
end

function Hecke.evaluate(P::GeometricPoint)
  assure_has_ev(P)
  return P.ev
end

Hecke.parent(P::GeometricPoint) = P.parent_object
Hecke.function_field(P::GeometricPoint) = function_field(parent(P))
plane_equation(P::GeometricPoint) = plane_equation(parent(P))
Hecke.coordinates(P::GeometricPoint) = P.coordinates
is_singular(P::GeometricPoint) = P.is_singular
is_smooth(P::GeometricPoint) = !is_singular(P)
Hecke.is_infinite(P::GeometricPoint) = P.is_infinite
is_affine(P::GeometricPoint) = !is_infinite(P)
Base.getindex(P::GeometricPoint, i::Int) = coordinates(P)[i]



###########################################
#                                         #
#          Helper functions below         #
#                                         #
###########################################

function Hecke.evaluate(p::Hecke.GenOrdIdl)
  O = Hecke.order(p)
  F = Hecke.field(O)
  R = base_ring(O)

  @assert base_ring(base_ring(F)) === QQBar

  k,reduce = Hecke.residue_field(R, minimum(p))
  @assert k === QQBar
  reduce_coeff(c) = reduce(R(c))

  M = map_entries(reduce, basis_matrix(p))
  K = kernel(M; side = :right)
  K_vec = QQBarFieldElem[a for a in K] 

  @assert size(K, 2) == 1

  #evaluation of 1
  defect = sum(reduce_coeff(c) * a for (c,a) in zip(coordinates(one(O)), K_vec); init = zero(QQBar)) 
  K_vec = QQBarFieldElem[inv(defect) * a for a in K_vec]

  ev_order_el(f) = sum(reduce_coeff(c) * a for (c,a) in zip(coordinates(f),K_vec); init = zero(QQBar))

  function ev(f)
    @assert parent(f) === F
    iszero(f) && return zero(QQBar)

    n,d = Hecke.integral_split(f,O)
    ev_d = reduce_coeff(d)

    !iszero(ev_d) && return ev_order_el(n) * inv(ev_d)

    e = Hecke.ramification_index(p)

    if R isa Hecke.KInftyRing
      v = e * valuation(d)
    else 
      v = e * valuation(d,minimum(p))
    end

    t = Hecke.anti_uniformizer(p)

    correction = t^v
    new_n = F(n) * correction
    new_d = F(O(d)) * correction

    new_n in O || error("f has a pole here")

    return ev_order_el(O(new_n)) * inv(ev_order_el(O(new_d)))

  end

  return Hecke.map_from_func(F,QQBar,ev)

end

function homogenise(P::MPolyRingElem; target_degree = nothing)
  R,(X,Y,Z) = polynomial_ring(base_ring(parent(P)), [:X, :Y, :Z])

  d = total_degree(P)
  if !isnothing(target_degree)
    @assert target_degree >= d
    d = target_degree
  end


  return sum(f(X,Y) * Z^(d - total_degree(f)) for f in Hecke.terms(P); init = zero(R))
end

function is_monic_in_2nd_coord(f::MPolyRingElem)
  iszero(f) && return false

  dy = degree(f,2)

  for (c,e) in zip(Hecke.coefficients(f), Hecke.exponent_vectors(f))
    if e[2] == dy
      if !iszero(e[1]) || !isone(c)
        return false 
      end
    end
  end

  return true
end