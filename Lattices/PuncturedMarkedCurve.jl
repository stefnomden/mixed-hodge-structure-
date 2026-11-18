#TODO: actually implement the punctures and marks
#have curve store critical data like jacobian / mhs
#have it be the central object around everything


function punctured_marked_curve(F::AbstractAlgebra.Generic.FunctionField)
  C = PuncturedMarkedCurve()
  C.function_field = F
  C.plane_equation = function_field_to_plane_equation(F)
  !is_monic_in_2nd_coord(C.plane_equation) && throw(ArgumentError("non-monic polynomials are not yet supported"))
  return C
end

function punctured_marked_curve(F::MPolyRingElem)
  @assert base_ring(parent(F)) === QQBar #TODO: accept non-QQBar poly's
  @assert length(gens(parent(F))) == 2
  !is_monic_in_2nd_coord(F) && throw(ArgumentError("non-monic polynomials are not yet supported"))
  C = PuncturedMarkedCurve()
  C.function_field = plane_equation_to_function_field(F)
  C.plane_equation = F
  return C
end

function Base.show(io::IO, C::PuncturedMarkedCurve)
  println(io,"Parent object for geometric points on")
  h_eq = homogenise(plane_equation(C))
  print(io, "   C: $(h_eq) = 0")
end

Hecke.function_field(C::PuncturedMarkedCurve) = C.function_field
plane_equation(C::PuncturedMarkedCurve) = C.plane_equation

###########################################
#                                         #
#          Helper functions below         #
#                                         #
###########################################

#find the plane equation defining F
function function_field_to_plane_equation(F::AbstractAlgebra.Generic.FunctionField)
  q = numerator(F)
  k = base_ring(base_ring(q))
  q = divexact(q,content(q))

  R,(x,y) = polynomial_ring(k, [:x,:y])

  P = zero(R)

  for i in 0:degree(q)
    P += evaluate(coeff(q,i),x) * y^i
  end

  return P
end

function plane_equation_to_function_field(P::MPolyRingElem)
  @assert length(gens(parent(P))) == 2

  k = base_ring(P)
  if k == rational_field()
    P = map_coefficients(QQBar, P)
  elseif k isa NumField
    v = infinite_places(k)[1]
    i = embeddings(v)[1]
    Kemb, _ = Hecke.embedded_field(k,i)

    ims = [QQBar(Kemb(s)) for s in gens(k)]

    emb = length(ims) == 1 ? hom(k,QQBar,only(ims)) : hom(k,QQBar,ims)
    P = map_coefficients(a -> emb(a), P)
  elseif k != QQBar
    error("Constant field not supported")
  end

  #@assert is_irreducible(P) 

  K, x = rational_function_field(QQBar,:x)
  KY, Y = polynomial_ring(K, :Y)
  F, _ = function_field(P(x,Y), :y)

  return F
end

