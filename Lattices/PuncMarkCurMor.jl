function punctured_marked_curve_morphism(
  C1::PuncturedMarkedCurve, 
  C2::PuncturedMarkedCurve, 
  images::NTuple{2,AbstractAlgebra.Generic.FunctionFieldElem};
  check = true
  )
  a,b = images
  @assert parent(a) === function_field(C1)
  @assert parent(b) === function_field(C1)

  if check
    @assert iszero(plane_equation(C2)(f,g))
    @assert is_constant_image(f) && is_constant_image(g)
  end

  return PuncturedMarkedCurveMorphism(C1,C2,images,nothing)

end

function is_constant_image(h)
  c = coeff(h, 0)
  return Hecke.is_constant(c) && h == F(c)
end

const PMCM = PuncturedMarkedCurveMorphism

function(phi::PMCM)(h::AbstractAlgebra.Generic.FunctionFieldElem)
  @assert function_field(codomain(phi)) === parent(h)
  f,g = images(phi)
  F = function_field(domain(phi))
  im_den = denominator(h)(f)
  num = numerator(h)
  im_num = sum(
    coeff(num,i)(f) * g^i for i in (0:degree(num)); init = zero(F)
  )
  return F(im_num) // F(im_den)
end

function(phi::PMCM)(points::Vector{GeometricPoint})
  return GeometricPoint[phi(P) for P in points]
end

function(phi::PMCM)(P::GeometricPoint)
  @assert domain(phi) === parent(P)

  f,g = images(phi)

  if is_affine(P)
    try 
      return handle_coordinate_image(phi,P,[evaluate(f,P), evaluate(g,P), one(QQBar)])
    catch 
    end
  end
  return evaluate_exception(phi,P)
end


function evaluate_exception(phi::PMCM, P::GeometricPoint)
  #here we are in the case where evaluating P at f and g 
  #produces an error (so there is a pole there or something like that)
  #or the point P is at infinity.
  coords = coordinates(phi)
  f,g = images(phi)
  p = coordinates(P)

  ev = [F(p...) for F in coords]

  !all((iszero).(ev)) && return handle_coordinate_image(phi, ev)

  Ptilde = place(P)
  O = order(Ptilde)
  spec_val(f) = iszero(f) ? 1 : valuation(f * O, P)
  valuations = [spec_val(f * O, Ptilde), spec_val(g * O, Ptilde), 0]
  i = argmin(valuations)
  h = [f,g,one(function_field(P))][i]

  return handle_coordinate_image(phi,[evaluate(f//h,P), evaluate(g//h,P), evaluate(1//h,P)])

end

function handle_coordinate_image(phi::PMCM, P::GeometricPoint, Q::Vector{QQBarFieldElem})
  places = places_above(codomain(phi), Q)
  F = function_field(codomain(phi))
  length(places) == 1 && return only(places)

  for R in places
    r = place(R)
    all(iszero(evaluate(phi(F(b)), P)) for b in basis(r)) && return R
  end
  error("Something went wrong; this is a bug")
end


function Hecke.coordinates(phi::PMCM)
  if !isnothing(phi.coordinates)
    return phi.coordinates
  end

  (f,g) = images(phi)

  df,dg = denominator(f), denominator(g)
  nf,ng = numerator(f), numerator(g)
  d = lcm(df,dg) #happening in QBar[x] so efficient

  R,(X,Y,Z) = polynomial_ring(QQBar, [:X,:Y,:Z])

  to_R(poly) = sum(coeff(poly,i)(X) * Y^i for i in (0:degree(poly)); init = zero(R))

  coords = (to_R(nf) * div(d,df)(X), to_R(ng) * div(d,dg)(X), d(X))
  D = maximum(total_degree(poly) for poly in coords)

  phi.coordinates = (pol -> homogenise(pol;target_degree=D)).(coords)

  return phi.coordinates
end

Hecke.domain(f::PMCM) = f.domain
Hecke.codomain(f::PMCM) = f.codomain
images(f::PMCM) = f.images

###########################################
#                                         #
#          Helper functions below         #
#                                         #
###########################################

