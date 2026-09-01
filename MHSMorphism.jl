mutable struct MixedHodgeStructureMorphism

  domain::MixedHodgeStructure
  codomain::MixedHodgeStructure

  x_image::AbstractAlgebra.Generic.FunctionFieldElem
  y_image::AbstractAlgebra.Generic.FunctionFieldElem

  constant_field_QQBar::Bool

  #these only when not working over QQBar
  function_field1::AbstractAlgebra.Generic.AbsSimpleFunctionField
  function_field2::AbstractAlgebra.Generic.AbsSimpleFunctionField

  gens1::Tuple{T,T} where T <: AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem
  gens2::Tuple{T,T} where T <: AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem

  k1_to_K::NumFieldHom
  k2_to_K::NumFieldHom

  constant_field::NumField
  embedding::NumFieldHom

  phi_star:: S where S

  function MixedHodgeStructureMorphism(HS1::MixedHodgeStructure, HS2::MixedHodgeStructure)
    phi = new()
    phi.domain = HS1
    phi.codomain = HS2
    return phi
  end

end

function Base.show(io::IO, phi::MixedHodgeStructureMorphism)
  println("Wrapper for morphism of the function fields underlying the mixed hodge structure")
  print(phi.domain)
  println("and codomain:")
  print(phi.codomain)
  if isdefined(phi, :x_image) && isdefined(phi, :y_image)
    println("The morphism is defined on function fields by")
    emb = phi.embedding
    F = phi.codomain.function_field_Qbar
    println("x |--> $(map_function_field_coeffs(phi.x_image, emb, F))")
    println("y |--> $(map_function_field_coeffs(phi.y_image, emb, F))")
  end
end

function induced_morphism(
  HS1::MixedHodgeStructure,
  HS2::MixedHodgeStructure,
  images::Tuple{
    AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem{QQBarFieldElem, AbstractAlgebra.Generic.Poly{QQBarFieldElem}},
    AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem{QQBarFieldElem, AbstractAlgebra.Generic.Poly{QQBarFieldElem}}
  }
)

  (g,h) = images 

  g_num, g_denom = homogenize(g)
  h_num, h_denom = homogenize(h)

  dl = lcm(g_denom,h_denom)
  coords = (g_num * dl//g_denom, h_num * dl//h_denom, dl)

  function phi_star(P::Vector{QQBarFieldElem})
    @assert length(P) in [2,3] "Input needs to be length 2 or 3"
    if length(P) == 2
      return [F(P[1],P[2],one(QQBar)) for F in coords[1:2]]
    end
    return [F(P[1],P[2],P[3]) for F in coords]
  end

  i1,i2 = HS1.embedding_QBar, HS2.embedding_QBar

  F,G = coords[1], coords[2]

  I=ideal(parent(F), F,G)
  println(F," ",G)

  imE = Set(phi_star(i1.(P)) for P in HS1.E)
  @assert issubset(imE, Set(i2.(P) for P in HS2.E)) "Marked points of domain are not mapped to marked points of codomain"
  #TODO: check if preimage of D_2 is contained in D_1. This can be done using resultants
  #(a:b:c) = (F:G:H), if c=1 then Res(P1, bF(x,y,1) - aG(x,y,1)) gives the x-coords
  #of solutions  

  phi = MixedHodgeStructureMorphism(HS1,HS2)

  phi.phi_star = phi_star

  if !all(HS.D_defined_over_k for HS in (HS1, HS2))
    phi.constant_field_QQBar = true
    phi.x_image, phi.y_image = images
    phi.gens1 = (HS1.x2, HS1.y2)
    phi.gens2 = (HS2.x2, HS2.y2)
    return phi
  end

  k1,k2 = (constant_field(HS.function_field) for HS in (HS1, HS2))
  k, k1_to_k, k2_to_k = compositum(k1,k2)

  #here we figure out what the right embedding is for k. 
  gamma = gen(k)
  alpha = gen(k1)
  beta = gen(k2)

  R,Y = polynomial_ring(QQBar, :Y)
  f_gam = change_base_ring(R, minpoly(gamma))

  gamma_emb = nothing
  for (c,d) in Iterators.product((1:30),(1:30))
    
    theta1 = c * k1_to_k(alpha) + gamma 
    theta2 = d * k2_to_k(beta) + gamma

    f1 = change_base_ring(R,minpoly(theta1))
    f2 = change_base_ring(R,minpoly(theta2))


    fac = gcd(gcd(f1(c * i1(alpha) + Y), f2(d * i2(beta) + Y)), f_gam(Y))

    if isone(degree(fac))
      gamma_emb = -coeff(fac,0) // coeff(fac,1)
      break
    end
    (c,d) == (30,30) && error("degen error")
  end

  iota = hom(k,QQBar, gamma_emb)

  x_im, y_im = images

  x_denom = denominator(x_im)
  x_num = numerator(x_im)
  y_denom = denominator(y_im)
  y_num = numerator(y_im)

  coeffs = Vector{QQBarFieldElem}([
    [c for b in Hecke.coefficients(x_num) for c in Hecke.coefficients(b)];
    [c for c in Hecke.coefficients(x_denom)];
    [c for b in Hecke.coefficients(y_num) for c in Hecke.coefficients(b)];
    [c for c in Hecke.coefficients(y_denom)];
  ])

  K, embedding, k_to_K, _ = adjoin(k, iota, coeffs)

  phi.k1_to_K = k1_to_k * k_to_K
  phi.k2_to_K = k2_to_k * k_to_K
  phi.constant_field = K
  phi.embedding = embedding

  for (i,HS) in enumerate((HS1, HS2))
    em = (i==1 ? k1_to_k : k2_to_k)
    P = map_coefficients(z -> k_to_K(em(z)), HS.defining_poly)
    rational_ff, x = rational_function_field(K, :x)
    _, Y = polynomial_ring(rational_ff, :Y)
    F,y = function_field(P(x,Y), :y)
    if i == 1
      phi.function_field1 = F
      phi.gens1 = (F(x), y)
    elseif i == 2
      phi.function_field2 = F
      phi.gens2 = (F(x), y)
    end
  end

  #convert the images of x and y to elements of phi.function_field2
  F = phi.function_field2
  (x,y) = phi.gens2 
  #r is the retraction of K -> QQBar
  r = z -> find_preim(K,embedding,z)

  phi.x_image = map_function_field_coeffs(x_im,r,F)
  phi.y_image = map_function_field_coeffs(y_im,r,F)


  E_permutation = Vector{Tuple{Int,Int}}()

  for (i,P) in enumerate([i1.(P) for P in HS2.E])
    imP = phi_star(P)
    if imP in HS2.singular_points_in_E
      for p in HS2.E_pts_places_corr[(P[1], P[2])]
        ev = evaluate(p)
        if all(ev * phi(gi) == zero(QQBar) for gi in basis(p))

        end
      end
    end
    j = findfirst(==(imP), HS2.E_for_eval)
    push!(E_permutation, (i,j))
  end

  return phi

end
    
function cohom_pullback(phi::MixedHodgeStructureMorphism)

  #preperation on the codomain's end (mainly converting everything)
  #to the larger function field
  F2 = phi.function_field2
  dummy_hs = deepcopy(phi.codomain)
  (x,y) = phi.gens2
  dx2 = differential(x)
  emb = phi.k2_to_K
  dummy_hs.zero_res_basis = [map_function_field_coeffs(omega.f, emb, F2) * dx2 for omega in _zero_res_basis(phi.codomain)]
  dummy_hs.res_basis = [map_function_field_coeffs(omega.f, emb, F2) * dx2 for omega in _residue_basis(phi.codomain)]

  dummy_hs.canon_div = canonical_divisor(F2)
  dummy_hs.D_div = trivial_divisor(F2)
  (i,j) = phi.domain.R_data
  dummy_hs.R = i * pole_divisor(x) + j * pole_divisor(y)

  red = reduction(dummy_hs)

  #preperation on the domain's end
  F1 = phi.function_field1
  emb = phi.k1_to_K
  (x,_) = phi.gens1
  cohom_basis = [
    [map_function_field_coeffs(omega.f, emb, F2) for omega in _zero_res_basis(phi.domain)];
    [map_function_field_coeffs(omega.f, emb, F2) for omega in _residue_basis(phi.domain)]
  ]
  dphi_x = differential(phi.x_image)

  mat = Vector{Vector{NumFieldElem}}()

  for f in cohom_basis
    omega = sum([
      sum([a * phi.x_image^(j-1) for (j,a) in enumerate(coefficients(b))], init = zero(phi.x_image)) * 
      phi.y_image^(i-1) for (i,b) in enumerate(coefficients(numerator(f)))], init = zero(phi.y_image)
    ) // sum([a * phi.x_image^(j-1) for (j,a) in enumerate(coefficients(denominator(f)))], init=zero(phi.x_image))
    omega = omega * dphi_x
    push!(mat,red(omega))
  end

  return matrix(mat)


end