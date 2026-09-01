mutable struct FunctionFieldHomWithMHS
  
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
  coords::Tuple{T,T,T} where T <: AbstractAlgebra.Generic.MPoly

  function FunctionFieldHomWithMHS(HS1::MixedHodgeStructure, HS2::MixedHodgeStructure)
    phi = new()
    phi.domain = HS1
    phi.codomain = HS2
    return phi
  end 

end

function Base.show(io::IO, phi::FunctionFieldHomWithMHS)
  println("Morphism of the function fields k(C1) -> k(C2) which underly mixed hodge structures")
  show(stdout, phi.domain; C="C1")
  println("\nand")
  show(stdout, phi.codomain; C="C2")
  if isdefined(phi, :x_image)
    emb = phi.embedding
    F = phi.codomain.function_field_Qbar
    println("\ngiven by")
    println("     x |--> $(map_function_field_coeffs(phi.x_image, emb, F))")
    println("     y |--> $(map_function_field_coeffs(phi.y_image, emb, F))")
  end
  if isdefined(phi, :phi_star)
    println()
    println("The morphism C2 -> C1 on points is given by")
    println("     (X : Y : Z) |--> ($(phi.coords[1]) : $(phi.coords[2]) : $(phi.coords[3]))")
  end
  
end


function function_field_hom(
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

  R = parent(g_num)

  dl = lcm(g_denom,h_denom)
  coords = (div(g_num * dl, g_denom), div(h_num * dl, h_denom), dl)

  function phi_star(P::Vector{QQBarFieldElem})
    @assert length(P) in [2,3] "Input needs to be length 2 or 3"
    if length(P) == 2
      return [F(P[1],P[2],one(QQBar)) for F in coords[1:2]]
    end
    return [F(P[1],P[2],P[3]) for F in coords]
  end

  i1,i2 = HS1.embedding_QBar, HS2.embedding_QBar

  phi = FunctionFieldHomWithMHS(HS1,HS2)

  phi.phi_star = phi_star
  phi.coords = coords

  k1,k2 = (constant_field(HS.function_field) for HS in (HS1, HS2))
  if k1 == k2
    k,k1_to_k, k2_to_k = k1, hom(k1,k1), hom(k1,k1)
  else
    k, k1_to_k, k2_to_k = compositum(k1,k2)
  end

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

  return phi

end

function (phi::FunctionFieldHomWithMHS)(f::AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem{
  AbsSimpleNumFieldElem, AbstractAlgebra.Generic.Poly{AbsSimpleNumFieldElem}
  })

  @assert parent(f) == phi.function_field1 (
    "element not in domain")
  return sum([
    sum([a * phi.x_image^(j-1) for (j,a) in enumerate(Hecke.coefficients(b))], init = zero(phi.x_image)) * 
    phi.y_image^(i-1) for (i,b) in enumerate(Hecke.coefficients(numerator(f)))], init = zero(phi.y_image)
    ) // sum([a * phi.x_image^(j-1) for (j,a) in enumerate(Hecke.coefficients(denominator(f)))], init=zero(phi.x_image))
end


function (phi::FunctionFieldHomWithMHS)(f::AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem{
  QQBarFieldElem, AbstractAlgebra.Generic.Poly{QQBarFieldElem}
  })
  x_im = map_function_field_coeffs(phi.x_image, phi.embedding, phi.codomain.function_field_Qbar)
  y_im = map_function_field_coeffs(phi.y_image, phi.embedding, phi.codomain.function_field_Qbar)

  @assert parent(f) == phi.domain.function_field_Qbar ( 
    "element not in domain"
  )

  return sum([
    sum([a * x_im^(j-1) for (j,a) in enumerate(Hecke.coefficients(b))], init = zero(x_im)) * 
    y_im^(i-1) for (i,b) in enumerate(Hecke.coefficients(numerator(f)))], init = zero(y_im)
  ) // sum([a * x_im^(j-1) for (j,a) in enumerate(Hecke.coefficients(denominator(f)))], init=zero(x_im))

end

function trace_map_alt(phi::FunctionFieldHomWithMHS)
  F1 = phi.function_field1
  F2 = phi.function_field2
  T = matrix([[zero(base_ring(F1)) for _ in 1:degree(F1)] for _ in 1:degree(F1)])
  bs1 = basis(F1)
  for (i,bi) in enumerate(bs1)
    for (j,bj) in enumerate(bs1[i:end])
      t = trace(bi * bj)
      T[j + i - 1,i] = t
      T[i,j + i - 1] = t
    end
  end

  im_basis = [phi(b) for b in bs1]
  Tinv = inv(T)

  function tr(f::AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem)
    v = [trace(imb * f) for imb in im_basis] #wrong: computes trace from k(C_2) to k(x) but should compute 
    #from k(C_2) to k(phi(x))
    c = Tinv * v
    return sum(b * ci for (b,ci) in zip(bs1, c))
  end
end

function trace_map(phi::FunctionFieldHomWithMHS)
  F1 = phi.function_field1
  F2 = phi.function_field2
  T = matrix([[zero(base_ring(F1)) for _ in 1:degree(F1)] for _ in 1:degree(F1)])
  bs1 = basis(F1)
  for (i,bi) in enumerate(bs1)
    for (j,bj) in enumerate(bs1[i:end])
      t = trace(bi * bj)
      T[j + i - 1,i] = t
      T[i,j + i - 1] = t
    end
  end

  im_basis = [phi(b) for b in bs1]
  Tinv = inv(T)
  
  A = numerator(phi.x_image)
  B = denominator(phi.x_image)
  x2,y2 = phi.gens2

  R,(x,y,T,S) = polynomial_ring(base_ring(parent(B)), [:x,:y,:T,:S])
  kt,t = rational_function_field(base_ring(parent(B)), :t)
  kts,Y = polynomial_ring(kt, :Y)

  F = sum([coeff(A,i)(x) * y^i for i in 0:(degree(A))], init = zero(R)) - T * B(x)
  
  target_degree = degree(pole_divisor(phi.x_image))

  L = nothing
  x2_in_L = nothing
  C = nothing

  for c in 1:30
    w = c * x2 + y2
    G = minpoly(w)
    @assert all(isone(denominator(c)) for c in coefficients(G)) "$w is not integral"
    G = sum(numerator(coeff(G,i))(x) * S^i for i in 0:(degree(G)))
    H = resultant(G, F(x, S - c*x, T, 0), 1)(0,0,t,Y)
    if degree(H) == target_degree
      L,s = function_field(H,:s)
      Lx, x3 = polynomial_ring(L, :x3)      
      d = gcd(F(x3, s - c*x3, t, 0), G(x3,0,0,s))
      if degree(d) == 1
        x2_in_L = L(-coeff(d,0)//coeff(d,1))
        C = c
        break
      end
    end
  end

  isnothing(x2_in_L) && error("degenerate error, unlikely to happen")

  y2_in_L = gen(L) - C * x2_in_L
  F2_to_L = f -> sum(coeff(numerator(f),i)(x2_in_L) * y2_in_L^i for i in 0:degree(numerator(f))) // denominator(f)(x2_in_L)
  im_basis_in_L = [F2_to_L(imb) for imb in im_basis]

  x1 = phi.gens1[1]
  function tr(f::AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem)
    f_in_L = F2_to_L(f)
    T_to_x1 = c -> numerator(c)(x1) // denominator(c)(x1)
    println([trace(c * f_in_L) for c in im_basis_in_L])
    vec = Tinv * [T_to_x1(trace(c * f_in_L)) for c in im_basis_in_L]
    return sum(c*b for (c,b) in zip(vec,bs1))
  end

  return tr

end


function _find_E_permutation(phi::FunctionFieldHomWithMHS)

  E_permutation = Vector{Tuple{Int, Int}}()

  HS1 = phi.domain
  HS2 = phi.codomain
  F = HS1.function_field_Qbar


  for P in [HS2.embedding_QBar.(P) for P in HS2.E]
    imP = phi.phi_star(P)
    if P in HS2.singular_points_in_E && !(imP in HS1.singular_points_in_E)
      #if P is singular and it mapped to a nonsingular point, then all places above
      #P are mapped to this non-singular point
      j = findfirst(==(imP), HS1.E_for_eval)
      for p in HS2.E_pts_places_corr[(P[1],P[2])]
        i = findfrst(==(p), HS2.E_for_eval)
        @assert !isnothing(i) && !isnothing(j) "ERROR: this should not happen"
        push!(E_permutation, (i,j))
      end

    elseif !(P in HS2.singular_points_in_E) && imP in HS1.singular_points_in_E
      #if P is a smooth point and gets mapped to a singular point. we must figure out 
      #which place P gets mapped to (i.e. which point on the normalization)
      for p in HS1.E_pts_places_corr[(imP[1], imP[2])]
        to_ev = [phi(F(gi)) for gi in basis(p)]
        if all([numerator(h)(P[2])(P[1]) // denominator(h)(P[1])==zero(QQBar) for h in to_ev])
          i = findfirst(==(P), HS2.E_for_eval)
          j = findfirst(==(p), HS1.E_for_eval)
          @assert !isnothing(i) && !isnothing(j) "ERROR: this should not happen"
          push!(E_permutation, (i,j))
        end
      end
      
    elseif P in HS2.singular_points_in_E && imP in HS1.singular_points_in_E
      #if both points are singular, we figure out which places map to which places
      for p2 in HS2.E_pts_places_corr[(imP[1], imP[2])]
        ev = _evaluate(p2)
        for p1 in HS1.E_pts_places_corr[(P[1], P[2])]
          if all([ev(phi(F(gi))) == zero(QQBar) for gi in basis(p1)])
            i = findfirst(==(p2), HS2.E_for_eval)
            j = findfirst(==(p1), HS1.E_for_eval)
            @assert !isnothing(i) && !isnothing(j) "ERROR: this should not happen"
            push!(E_permutation, (i,j))
            break
          end
        end
      end

    else
      #in the final case, both P and its image are smooth so this one is easy
      i = findfirst(==(P), HS2.E_for_eval)
      j = findfirst(==(imP), HS1.E_for_eval)
      @assert !isnothing(i) && !isnothing(j) "ERROR: this should not happen"
      push!(E_permutation, (i,j))
    end
  end

  return E_permutation

end