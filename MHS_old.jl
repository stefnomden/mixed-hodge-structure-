
using Plots
using Hecke.RiemannSurfaces

mutable struct MixedHodgeStructure

  defining_poly::MPolyRingElem
  D::Vector{Vector{Union{QQBarFieldElem, NumFieldElem, QQFieldElem}}}
  D_inf::Vector{Vector{Union{QQBarFieldElem, NumFieldElem, QQFieldElem}}}
  E::Vector{Vector{Union{QQBarFieldElem, NumFieldElem, QQFieldElem}}}
  finite_maximal_ord::Hecke.GenOrd
  infinite_maximal_ord::Hecke.GenOrd
  x::AbstractAlgebra.Generic.FunctionFieldElem
  y::AbstractAlgebra.Generic.FunctionFieldElem
  x2::AbstractAlgebra.Generic.FunctionFieldElem
  y2::AbstractAlgebra.Generic.FunctionFieldElem

  embedding_QBar::NumFieldHom

  RS_object::RiemannSurface 

  precision::Int64

  function_field::AbstractAlgebra.Generic.FunctionField
  function_field_Qbar::AbstractAlgebra.Generic.FunctionField

  genus::ZZRingElem

  zero_res_basis::Vector{FunFldDiff}
  res_basis::Vector{FunFldDiff}
  cohomology_basis::Vector{Any}
  homology_basis::Vector{Vector{ZZRingElem}}

  R::Divisor
  R_data::Tuple{Int,Int}
  D_div::Divisor
  canon_div::Divisor

  D_defined_over_k::Bool
  E_defined_over_k::Bool
  E_empty::Bool
  E_for_eval::Vector{Union{Vector{QQBarFieldElem}, <:Hecke.GenOrdIdl}}
  E_abstract_vertices::Vector{Union{Tuple{Int64, Int64}, Tuple{Tuple{Int64,Int64},Tuple{Int64,Int64}}}}
  E_pts_places_corr::Dict{Tuple{QQBarFieldElem, QQBarFieldElem}, Vector{<:Hecke.GenOrdIdl}}
  singular_points_in_E::Vector{Vector{QQBarFieldElem}}

  branch_points::Vector{QQBarFieldElem}
  plane_edges::Vector{Any}
  plane_loops::Vector{Any}
  plane_verts::Vector{Any}

  upstairs_edges::Vector{Tuple{Tuple{Int64,Int64},Tuple{Int64,Int64}}}
  upstairs_vertices::Vector{Tuple{Int64, Int64}}
  problematic_vertices::Vector{Tuple{Int64, Int64}}

  master_matrix::Vector{Vector{Union{Nothing, AcbFieldElem}}}
  period_matrix::AcbMatrix 

  function MixedHodgeStructure()

    HS = new()

    return HS
  end
end

function mixed_hodge_structure(
  P::MPolyRingElem; 
  D::Vector{Vector{QQBarFieldElem}} = Vector{Vector{QQBarFieldElem}}(),
  E::Vector{Vector{QQBarFieldElem}} = Vector{Vector{QQBarFieldElem}}(),
  prec::Int64 = 256
  )

  HS = MixedHodgeStructure()

  #embed the base field of P into QQBar, if needed. 
  K = base_ring(P)
  if K == rational_field()
    Q = rationals_as_number_field()[1]
    HS.defining_poly = change_base_ring(Q,P)
    iota = hom(Q,QQBar,QQBar(1))
  else
    HS.defining_poly = P
    v = infinite_places(K)[1]
    emb = embeddings(v)[1]
    C = AcbField(100)
    println("WARNING: Base field of $P is not embedded in QQBar. The embedding chosen is \n $emb")
    embedded_generators = []
    for s in gens(K)
      candidates = roots(change_base_ring(QQBar,minpoly(s)))
      j = findfirst(alpha -> overlaps(emb(s), C(alpha)),candidates)
      push!(embedded_generators,candidates[j])
    end
    if length(embedded_generators) == 1
      iota = hom(K,QQBar,embedded_generators[1])
    else
      iota = hom(K,QQBar,embedded_generators)
    end
  end

  HS.embedding_QBar = iota

  if length(E) == 0
    HS.E_empty = true
  else
    HS.E_empty = false
  end

  HS.D_inf = [a[1:end-1] for a in D if (length(a) == 3 && iszero(a[end]))]
  HS.D = [
    [a for a in D if length(a) == 2];
    [(a[1]//a[end], a[2]//a[end]) for a in D if (length(a) == 3 && !iszero(a[end]))]
  ]

  HS.E = E #what if points in E are at infinity ... :(
  P_y = _change_ring(derivative(HS.defining_poly,2), HS.embedding_QBar)
  P_x = _change_ring(derivative(HS.defining_poly,1), HS.embedding_QBar)
  singular_points_in_E = Vector{Vector{QQBarFieldElem}}()
  for (a,b) in E 
    if all([iszero(P_y(a,b)), iszero(P_x(a,b))])
      push!(singular_points_in_E,[a,b])
    end
  end

  #singular points are really branch points
  HS.singular_points_in_E = singular_points_in_E
  
  HS.precision = prec 

  k = base_ring(HS.defining_poly)
  rational_ff, x = rational_function_field(k,"x")
  KY, Y = polynomial_ring(rational_ff, "Y")
  kC, y = function_field(HS.defining_poly(x,Y), "y")
  HS.function_field = kC
  HS.x,HS.y = kC(x),y

  rational_ff_Qbar, x2 = rational_function_field(QQBar, "x")
  KY, Y2 = polynomial_ring(rational_ff_Qbar, "Y")
  Pbar = _change_ring(HS.defining_poly,iota)
  kC, y2 = function_field(Pbar(x2,Y2), "y")
  HS.function_field_Qbar = kC
  HS.x2, HS.y2 = kC(x2), y2
  

  #this part checks whether D and E are defined over k.
  #this only works for k = QQ so far, for it to work for general k
  #an embedding f : k -> QQbar is needed. 
  for (i,S) in enumerate([[HS.D; HS.D_inf], E])
    flag = true
    new_S = Vector{Vector{elem_type(k)}}()
    for (a,b) in S
      a_factors = [f for (f,_) in factor(change_base_ring(k,minpoly(a))) if degree(f) == 1]
      b_factors = [f for (f,_) in factor(change_base_ring(k,minpoly(b))) if degree(f) == 1]
      println(a_factors)
      println(b_factors)
      a_check = [evaluate(_change_ring(f,iota),a) == 0 for f in a_factors]
      b_check = [evaluate(_change_ring(f,iota),b) == 0 for f in b_factors]
      if (!any(a_check) || !any(b_check))
        flag = false
        break 
      end
      f_a = a_factors[findfirst(a_check)]
      f_b = b_factors[findfirst(b_check)]
      push!(new_S, [-coeff(f_a,0)//Hecke.leading_coefficient(f_a), -coeff(f_b,0)//Hecke.leading_coefficient(f_b)])
    end
    if i == 1
      HS.D_defined_over_k = flag
    elseif i == 2 
      HS.E_defined_over_k = flag
    end
    if flag
      if i == 1
        println("hello")
        println(typeof(new_S))
        HS.D = new_S[1:length(HS.D)]
        HS.D_inf = new_S[length(HS.D) + 1:end]
      else 
        HS.E = new_S
      end
    end
  end

  #Compute branch points
  Qbart,t = polynomial_ring(QQBar)
  Qbarts,s = polynomial_ring(Qbart)
  P_univariate = _change_ring(HS.defining_poly,iota)(t,s)
  Pdiscx = discriminant(P_univariate)
  branch_points = roots(Pdiscx)
  HS.branch_points = branch_points

  #defines all the necessary data for 'analytic_continuation' to work
  RS = RiemannSurface()
  RS.initial_precision = HS.precision
  v = infinite_places(k)[1]
  RS.embedding = v
  RS.defining_polynomial = HS.defining_poly 
  HS.RS_object = RS

  return HS
end


function Base.show(io::IO, HS::MixedHodgeStructure; C::String="C")
  print(io, "Mixed Hodge Structure of the punctured marked curve with planar equation $C : $(HS.defining_poly)")
end

function fiber(HS::MixedHodgeStructure, z::AcbFieldElem)
  _,t = polynomial_ring(AcbField(HS.precision),:t)
  #sheet ordering is a function in RiemannSurfaces which orders the fiber in a certain way
  #this is relevant for analytic_continuation

  fib = nothing
  try 
    fib = roots(change_base_ring(AcbField(HS.precision),_change_ring(HS.defining_poly,HS.embedding_QBar))(z,t); initial_prec=HS.precision, max_prec=10000)
  catch 
    #in this case we must have that z is a branch point
    CC = AcbField(HS.precision)
    i = findfirst(alpha -> overlaps(CC(alpha),z),HS.branch_points)
    z_exact = HS.branch_points[i]
    _,t = polynomial_ring(QQBar,:t)
    fib = [CC(alpha) for alpha in roots(change_base_ring(QQBar, HS.defining_poly)(z_exact,t))]
  end

  return sort(fib, lt = sheet_ordering)

end

function fiber_exact(HS::MixedHodgeStructure, z::QQBarFieldElem)
  _,t = polynomial_ring(QQBar,:t)
  fib = roots(_change_ring(HS.defining_poly,HS.embedding_QBar)(z,t))
  return sort(fib, lt = (alpha,beta) -> sheet_ordering(AcbField(HS.precision)(alpha), AcbField(HS.precision)(beta)))
end

function _zero_res_basis(HS::MixedHodgeStructure, c::Int = 1)

  if isdefined(HS, :zero_res_basis)
    return HS.zero_res_basis
  end


  function ev_infty(f::AbstractAlgebra.Generic.RationalFunctionFieldElem)
    if degree(denominator(f)) > degree(numerator(f))
      return zero(k)
    end
    return k(Hecke.leading_coefficient(numerator(f)))
  end

  function prep_diff(omega::FunFldDiff, p::Hecke.GenOrdIdl)

    start = time()
    cords = coordinates(omega.f)
    i = findfirst(c -> !iszero(c), cords) - 1
    j = degree(numerator(cords[i+1]))
    vf = j * xvals[p] + i * yvals[p] + dxvals[p]
    println(time() - start,"time to valuate: ")

    t = unifs[p] 
    dt = differential(t)

    f = omega // dt

    if vf > -1 
      println([k(0) for _ in ev_vecs[p]])
      println(ev_vecs[p])
      return [k(0) for _ in ev_vecs[p][1]]
    end
    start = time()
    vf = -vf 
    g = t^(vf) * f
    for n in (1:vf-1)
      g = differential(g) // dt 
      g = g // kC(n) 
    end
    println(time() - start,"time it took to take ", vf-1, " derivatives: ")

    start = time()
    
    den = nothing

    try 
      O(g)
      den = one(kC)
      println(time() - start, ":time for checking if in order")
    catch 
      den = denominator(g * O) 
    end

    ev_den = Hecke.leading_coefficient(numerator(den)) 

    #this is the vector to evaluate
    start = time()
    coords = coordinates(O(inv(ev_den)) * O(kC(den) * g))
    println("time to get coords: ", time() - start)
    return [k(ev_infty(a)) for a in coords]

  end

  kC  = HS.function_field
  O = infinite_maximal_ord(HS)
  x,y = HS.x, HS.y
  k   = constant_field(kC)

  places = [p[1] for p in factor(ideal(O, O(1//x)))]
  unifs = Dict()
  for p in places 
    B = basis(p)
    i = findfirst(b -> valuation(ideal(O,b), p) == 1, B)
    isnothing(i) && error("No uniformizer found; this should not happen and is probably a bug")
    unifs[p] = kC(B[i])
  end


  println("unifs:")
  for p in places 
    println(unifs[p])
    println(Hecke.divisor(unifs[p]))
  end

  if sum(degree(norm(p)) for p in places) == -1
    inert_at_inf = true
  else 
    inert_at_inf = false 
  end 

  ev_vecs = Dict()

  for p in places
    M = basis_matrix(p)
    M_ev = matrix(k, [ev_infty(base_field(kC)(M[i,j])) for i in 1:nrows(M), j in 1:ncols(M)])
    ker = kernel(transpose(M_ev))
    ev_vecs[p] = [collect(v) for v in eachrow(ker)]
  end

  genus = hs_genus(HS)
  index = c * (ceil(Int, 4 * genus / degree(kC)) + 1)

  functions = [y^i * x^j for j in (0:index) for i in (1:degree(kC) - 1)]

  println("hi")
  start = time()
  dx = differential(kC(x))
  if !inert_at_inf
    dxvals = Dict(p => valuation(dx, p) for p in places)
    xvals = Dict(p => valuation(x * O, p) for p in places)
    yvals = Dict(p => valuation(y * O, p) for p in places)
  end
  println(time() - start,"initial vals: ")

  forms = [f * dx for f in functions]

  R = index * pole_divisor(x) + (degree(kC) - 1) * pole_divisor(y)  
  HS.R = R
  HS.R_data = (index, degree(kC) - 1)

  L_of_R = riemann_roch_space(R+pole_divisor(canonical_divisor(kC)))
  println(L_of_R)

  residues = Vector{Vector{elem_type(k)}}()
  form_basis = Vector{FunFldDiff{<:AbstractAlgebra.Generic.FunctionFieldElem}}()

  A = zero_matrix(k, 0, 0)
  ker_size = 0

  for omega in forms

    res_vec = Vector{elem_type(k)}()
    for p in places
      append!(
        res_vec, 
        [if inert_at_inf zero(k) else dot(prep_diff(omega,p),v) end for v in ev_vecs[p]]
      )
    end
    
    push!(residues, res_vec)
    A = matrix(residues)
    println(A)

    ker = kernel(A)

    if number_of_rows(ker) >= 2 * genus && number_of_rows(ker) > ker_size
      start = time()
      ker_size = number_of_rows(ker)
      zero_residue_forms = [
        sum(kC(a) * omega for (a,omega) in zip(v,forms)) for v in eachrow(kernel(A))
        ]
      form_basis = Vector{FunFldDiff{<:AbstractAlgebra.Generic.FunctionFieldElem}}()

      for zero_form in zero_residue_forms
        potential = [form_basis; [zero_form]]
        if _check_dim(potential, L_of_R) > length(form_basis)
          push!(form_basis, zero_form)
        end
      end
      println(time() - start, "time spent in linalg zone: ")
    end

    if length(form_basis) == 2 * genus 
      HS.zero_res_basis = form_basis
      return form_basis
    end
  end

  return _zero_res_basis(HS, c + 1)

end


function _residue_basis(HS::MixedHodgeStructure)

  if isdefined(HS, :res_basis)
    return HS.res_basis
  end

  if length([HS.D; HS.D_inf]) == 0
    return Vector{FunFldDiff{<:AbstractAlgebra.Generic.FunctionFieldElem}}()
  end 

  if HS.D_defined_over_k
    F = HS.function_field
    x,y = HS.x,HS.y
  else 
    F = HS.function_field_Qbar
    x,y = HS.x2,HS.y2
  end
  K_F = canonical_divisor(F)
  HS.canon_div = K_F
  O = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
  dx = differential(x)

  println([(a,b) for (a,b) in HS.D])
  D_ideals = [ideal(O, O(x - a), O(y - b)) for (a,b) in HS.D]
  t = nothing
  try 
    t = Oinf(y//x)
  catch 
    g = y//x
    t = Oinf(F(denominator(g * Oinf)) * g)
  end
  #if y//x is not in Oinf, then i am not certain whether basis(Oinf)[2] will always be an element which
  #'acts the same' as y//x. i.e. t - d//c vanishes at (c : d : 0)
  println(t)
  D_ideals_inf = [
    iszero(c) ? ideal(Oinf, Oinf(x//y)) :
    ideal(Oinf, Oinf(1//x), t - Oinf(d//c))
    for (c,d) in HS.D_inf
  ]
  println(D_ideals_inf)
  D_div = sum(Hecke.divisor(I) for I in [D_ideals; D_ideals_inf])
  HS.D_div = D_div

  zero_res = copy(_zero_res_basis(HS))
  #this converts the zero residue basis to the same basis but with constant field QQBar
  if HS.D_defined_over_k
    form_basis = zero_res
  else
    form_basis = [
        sum(
            sum(
                QQBar(c) * (x)^(j - 1)
                for (j, c) in enumerate(Hecke.coefficients(numerator(a)));
                init = zero(F)
            ) * (y)^(i - 1)
            for (i, a) in enumerate(coordinates(omega.f));
            init = zero(F)
        ) * dx
        for omega in zero_res
    ]
  end
  j = maximum([maximum([degree(numerator(a)) for a in Hecke.coefficients(omega.f)]) for omega in zero_res])
  i = degree(HS.function_field) - 1
  R = 3 * (i * pole_divisor(x) + j * pole_divisor(y))
  HS.R = R


  L = riemann_roch_space(R + D_div + K_F)
  forms_to_check = [f * dx for f in riemann_roch_space(D_div + K_F)]
  println(forms_to_check)

  res_forms = Vector{FunFldDiff{<:AbstractAlgebra.Generic.FunctionFieldElem}}()

  for omega in forms_to_check
    potential = [form_basis; [omega]]
    if _check_dim(potential, L) > length(form_basis)
      push!(form_basis, omega)
      println("omega: ", omega)
      println("forms: ", _zero_res_basis(HS))
      push!(res_forms, omega)
    end
  end

  HS.res_basis = res_forms
  return res_forms
  

end

function cohomology(HS::MixedHodgeStructure)
  if isdefined(HS, :cohomology_basis)
    return HS.cohomology_basis
  end


  if HS.E_empty
    HS.cohomology_basis = [_zero_res_basis(HS); _residue_basis(HS)]
    return HS.cohomology_basis
  end

  iota = HS.embedding_QBar

  places_above_sing_pts = Dict()
  E_pts_places_corr = Dict((iota(a),iota(b)) => Vector{Hecke.GenOrdIdl}() for (a,b) in HS.E)
  for (a,b) in HS.singular_points_in_E
    F = HS.function_field_Qbar
    O = finite_maximal_order(F)
    I = ideal(O, O(HS.x2 - a), O(HS.y2 - b))
    for (p,_) in factor(I)
      places_above_sing_pts[p] = (a,b)
      push!(E_pts_places_corr[(a,b)], p)
    end
  end

  
  if HS.E_defined_over_k
    E_smooth = [[iota(a), iota(b)] for (a,b) in HS.E if !([iota(a),iota(b)] in HS.singular_points_in_E)]
  else 
    E_smooth = [[QQBar(a), QQBar(b)] for (a,b) in HS.E if !([QQBar(a),QQBar(b)] in HS.singular_points_in_E)]
  end
  E_size = length(E_smooth) + length(places_above_sing_pts)

  """
  for (a,b) in E_smooth
    push!(E_pts_places_corr[(a,b)], ideal(O, O(HS.x2 - a, HS.y2 - b)))
  end
  """

  HS.E_pts_places_corr = E_pts_places_corr

  E_vecs = [QQBar.(i .== 1:E_size) for i in 1:E_size][1:end-1]
  zero_vec = [QQBar(0) for _ in 1:E_size]
  forms = [_zero_res_basis(HS); _residue_basis(HS)]
  if HS.D_defined_over_k 
    zero_form = differential(HS.function_field(1))
  else 
    zero_form = differential(HS.function_field_Qbar(1))
  end

  println(typeof([p for (p,_) in places_above_sing_pts]))
  HS.E_for_eval = [E_smooth; [p for (p,_) in places_above_sing_pts]]

  HS.cohomology_basis = [
    [[omega, zero_vec] for omega in forms];
    [[zero_form, v] for v in E_vecs]
  ]

  return HS.cohomology_basis

end


function reduction(HS::MixedHodgeStructure)

  H_basis = [_zero_res_basis(HS); _residue_basis(HS)]

  if !isdefined(HS, :canon_div)
    F = HS.function_field
    HS.canon_div = canonical_divisor(F)
    HS.D_div = trivial_divisor(F)
  end
  K_F = HS.canon_div
  D = HS.D_div
  R = HS.R


  function reduction_wrt_basis(eta::Union{FunFldDiff, Vector{Any}}; return_f = false)
    if HS.D_defined_over_k
      k = constant_field(parent(H_basis[1].f))
    else 
      k = QQBar
    end

    if !HS.E_empty
      (eta,vec) = eta
    end

    if iszero(eta.f)
      eta_div = trivial_divisor(parent(eta.f))
    else
      eta_div = pole_divisor(eta.f) + pole_divisor(K_F)
    end
    
    L = riemann_roch_space(2 * (eta_div + R + D)) #figure out the exact divisor to put here

    big_space = [[differential(f).f for f in L]; [omega.f for omega in H_basis]; [eta.f]]
    Dx = lcm([lcm([denominator(a) for a in coordinates(f)]) for f in big_space])
    big_space_cleared = [Dx * f for f in big_space]
    N = maximum(maximum(degree(numerator(a)) for a in coordinates(f)) for f in big_space_cleared) + 1

    to_be_matrix = Vector{Vector{elem_type(k)}}()

    for f in big_space_cleared
      row = Vector{elem_type(k)}()
      for a in coordinates(f)
        coeff = [k(c) for c in Tuple(Hecke.coefficients(numerator(a)))]
        append!(row, [coeff; fill(zero(k), N - length(coeff))])
      end
      push!(to_be_matrix, row)
    end

    A = matrix(to_be_matrix)

    ker = eachrow(kernel(A))
    i = findfirst(v -> v[end] != 0, ker)
    v = ker[i]

    f = inv(-v[end]) * sum(a * g for (a,g) in zip(v[1:length(L)], L))
    cord = [inv(-v[end]) * c for c in v[length(L) + 1:end - 1]]

    if HS.E_empty
      if return_f
        return cord,f
      else 
        return cord
      end
    end

    f_eval = Vector{QQBarFieldElem}()
    iota = HS.embedding_QBar

    for p in HS.E_for_eval
      if typeof(p) <: Vector 
        (a,b) = p
        den = inv(_change_ring(denominator(f),iota)(a))
        num = sum([_change_ring(f,iota)(a) * b^(i - 1) for (i,f) in enumerate(Hecke.coefficients(numerator(f)))], init = zero(QQBar))
        push!(f_eval, num * den)
      else 
        ev = _evaluate(p)
        push!(f_eval, ev(f))
      end
    end

    v = [a - b for (a,b) in zip(vec, f_eval)]
    v = [i - v[end] for i in v[1:end-1]]

    return [cord; v]

  end

  return reduction_wrt_basis

end

function _set_plane_graph(HS::MixedHodgeStructure)

  branch_points = HS.branch_points
  iota = HS.embedding_QBar
  xD = [HS.D_defined_over_k ? iota(a) : a for (a,_) in HS.D]
  xE = [HS.E_defined_over_k ? iota(a) : a for (a,_) in HS.E]

  prec = HS.precision
  CC = AcbField(prec)
  
  #vertices are the actual points stored as AcbFieldElems, 
  #cells denote the index of the points
  vertices, _, cells, boundary, _ = voronoi_diagram([CC(P) for P in unique([branch_points; xD])])
  println([branch_points; xD])
  append!(vertices, unique([CC(a) for a in xE]))
  
  plane_edges = Vector{Tuple{Int,Int}}()
  plane_loops = []

  for (i,C) in enumerate(cells)
    center = [branch_points; xD][i]
    sorted_vert = sort(C, by = (j -> angle(CC(vertices[j]) - CC(center))))

    local_edges = collect(zip(sorted_vert, [sorted_vert[2:end]; sorted_vert[1]]))

    println([branch_points; xD][i])
    if [branch_points; xD][i] in xE

      e = CC([branch_points; xD][i])
      println("e: ", e)
      close_to_e = argmin(j -> abs(vertices[j] - e), sorted_vert)
      push!(local_edges, (findfirst(j -> overlaps(vertices[j],e), eachindex(vertices)), close_to_e))

    end

    push!(plane_loops, local_edges)
    append!(
      plane_edges,
      filter(e -> !(e in plane_edges || reverse(e) in plane_edges),local_edges)
    )
  end

  for e in filter(a -> !((HS.E_defined_over_k ? iota(a[1]) : a[1]) in branch_points), HS.E)
    e = CC(HS.E_defined_over_k ? iota(e[1]) : e[1])
    index_of_e = findfirst(j -> overlaps(vertices[j],e), eachindex(vertices))
    close_to_e = argmin(j -> abs(vertices[j] - e), [k for k in eachindex(vertices) if k != index_of_e])
    push!(plane_edges, (close_to_e,findfirst(j -> overlaps(vertices[j],e), eachindex(vertices))))
  end 

  c = sum(boundary)/length(boundary)
  sort!(boundary, by = z -> angle(ComplexF64(z - c)))
  boundary_indices = [findfirst(s -> overlaps(s,z), vertices) for z in boundary]
  push!(plane_loops, collect(zip(boundary_indices, [boundary_indices[2:end]; boundary_indices[1]])))

  HS.plane_loops = plane_loops
  HS.plane_edges = plane_edges
  HS.plane_verts = vertices

  return plane_loops, plane_edges, boundary, vertices

end 

function _set_upstairs_graph(HS::MixedHodgeStructure)

  if !isdefined(HS, :plane_edges)
    _set_plane_graph(HS)
  end

  #riemann surface object 
  RS = HS.RS_object
  
  upstairs_graph = Vector{Tuple{Tuple{Int64,Int64},Tuple{Int64,Int64}}}()
  remaining_edges = []

  verts = HS.plane_verts
  for edge in HS.plane_edges 

    gamma = CPath(verts[edge[1]], verts[edge[2]], 0) #straight line path datatype 

    lift_data = nothing

    try
      lift_data = analytic_continuation(
        RS, gamma, [ArbField()(r) for r in [-1 + 2*(i - 1)/100 for i in (2:100)]]
        )
    catch 
      #since every edge with endpoints not in x(E) avoids the branch points, this 
      #situation only occurs when the initial point or endpoint of the edge is in x(E)
      #and this point is a branch point
      push!(remaining_edges, edge)
      continue 
    end 
    
    endpts = lift_data[2][end]
    println(verts[edge[2]])
    endpts_ordered = fiber(HS, verts[edge[2]]) 

    new_edges = Vector{Tuple{Tuple{Int64,Int64},Tuple{Int64,Int64}}}()
    for i in eachindex(endpts)
      j = findfirst(z -> overlaps(endpts[i],z), endpts_ordered)
      push!(new_edges, ((edge[1], i), (edge[2], j)))
    end

    append!(upstairs_graph, new_edges)

  end

  problematic_vertices = []
  println(remaining_edges)
  for edge in remaining_edges
    #the plane edges are chosen that they start at a branch (if there is one)
    branch_point = verts[edge[1]] #is acb el, want: QQBar
    i = findfirst(z -> overlaps(AcbField(HS.precision)(z), branch_point), HS.branch_points)
    branch_point_exact = HS.branch_points[i] 
    ramif_pts = fiber_exact(HS, branch_point_exact)
    length(ramif_pts) > 1 && error("Implementation issue, a point in E is too problematic")

    new_edges = [((edge[1], 1), (edge[2], j)) for j in 1:degree(HS.function_field)]
    append!(upstairs_graph, new_edges)
    #problematic edges are those which start at branch points 
    push!(problematic_vertices, (edge[1],1))
  end

  HS.upstairs_edges = upstairs_graph 
  HS.upstairs_vertices = unique([[e[1] for e in upstairs_graph]; [e[2] for e in upstairs_graph]])
  HS.problematic_vertices = problematic_vertices

  return upstairs_graph 

end

function homology_basis(HS::MixedHodgeStructure)

  if isdefined(HS, :homology_basis)
    return HS.homology_basis
  end

  if !isdefined(HS, :upstairs_edges)
    _set_upstairs_graph(HS)
  end

  plane_points = HS.plane_verts
  vertices = HS.upstairs_vertices
  edges = HS.upstairs_edges
  CC = AcbField(HS.precision)
  iota = HS.embedding_QBar
  E_def = HS.E_defined_over_k

  indices_E = [
    findfirst(((i,j),) -> !((i,j) in HS.problematic_vertices) && 
    overlaps(plane_points[i], E_def ? CC(iota(P[1])) : CC(P[1])) && 
    overlaps(fiber(HS,plane_points[i])[j], E_def ? CC(iota(P[2])) : CC(P[2])), vertices) for P in HS.E
    ]
  vertices_E = [[vertices[i] for i in indices_E if !isnothing(i)]; HS.problematic_vertices]

  A = matrix(integer_ring(),[[if v in vertices_E 0 else get(Dict(e[1] => 1, e[2] => -1),v,0) end for v in vertices] for e in edges])
  graph_hom = eachcol(nullspace(transpose(A))[2])
  test_matrix = A
  println("length(kernel):", length(graph_hom))

  K = []
  lifted_loops = []
  #distinct_loops_above_pts contains on it's i-th index the distinct loops above the 
  #loop which has i-th index in the set HS.plane_loops
  distinct_loops_above_pts = []

  for O in HS.plane_loops

    lifted_loop = [e for e in edges if (e[1][1], e[2][1]) in O || (e[2][1], e[1][1]) in O]
    push!(lifted_loops, lifted_loop)
    local_vertices = unique([[e[1] for e in lifted_loop];[e[2] for e in lifted_loop]])

    A_O = matrix(integer_ring(),[[get(Dict(e[1] => 1, e[2] => -1),v,0) for v in local_vertices] for e in lifted_loop])

    ker = eachcol(nullspace(transpose(A_O))[2])

    dicts = [Dict(e => a for (e,a) in zip(lifted_loop, v)) for v in ker]
    distinct_loops = [[if a == 1 e elseif a == -1 (e[2],e[1]) end for (e,a) in zip(lifted_loop, v) if a != 0] for v in ker]

    push!(distinct_loops_above_pts,distinct_loops)

    append!(K,[[integer_ring()(get(D,e,0)) for e in edges] for D in dicts])

  end

  winding_number = (
    (z,loop) 
    -> abs(sum(angle(ComplexF64((plane_points[a] - z)/(plane_points[b] - z))) for (a,b) in loop))
  )
  #below we indentify which of the lifted loops encircle the points in D. to do this, for every d in D
  #we identify the loop in P1(C) which goes around x(d), then we lift an edge which goes from d to the 
  #nearest vertex. then we lift this edge and see to which loop the lift with initial condition d connects.
  to_be_removed = [] 
  for d in HS.D

    CCd = CC(HS.D_defined_over_k ? iota(d[1]) : d[1])

    #check if x(d) is a branch point for testing purposes
    if any([overlaps(CCd, CC(z)) for z in HS.branch_points])
      d_branch = true 
      length(fiber_exact(HS, HS.D_defined_over_k ? iota(d[1]) : d[1])) != 1 && error("the point $d lies above a branch point which is too complex")
    else 
      d_branch = false
    end
    
    #first we find the loop which encircles x(d)
    loop_round_d = argmax(winding_number(CCd, O) for O in HS.plane_loops[1:end-1])
    verts = [plane_points[e[1]] for e in HS.plane_loops[loop_round_d]]

    #array which consists of loops which lie above loop around x(d)
    lifted_loops_around_d = distinct_loops_above_pts[loop_round_d]

    #this is the special case where there is only one ramified point above x(d)
    #temporariy fix for the ramified case
    if d_branch
      append!(to_be_removed, [[e in O ? 1 : (e[2],e[1]) in O ? -1 : 0 for e in edges] for O in lifted_loops_around_d])
      continue 
    end

    #find the vertex closest to x(d)
    i = argmin(abs(z - CCd) for z in verts)
    close_to_d = verts[i]

    #create path and lift
    gamma = CPath(CCd, close_to_d,0)
    _,y_vals = analytic_continuation(HS.RS_object, gamma, [ArbField()(0)])

    #identify which of the lifts starts at d 
    j = findfirst(z -> overlaps(CC(HS.D_defined_over_k ? iota(d[2]) : d[2]), z),y_vals[1])
    enpt = y_vals[end][j]

    #identify the vertex that is the endpoint (calling fiber like millions of times, 
    #there should be a better way to do this)
    k = findfirst(v -> overlaps(fiber(HS,HS.plane_verts[v[1]])[v[2]], enpt), vertices)
    vertex = vertices[k]

    relevant_loops = []
    for O in lifted_loops_around_d
      if any([e[1] == vertex || e[2] == vertex for e in O])
        push!(relevant_loops, O)
      end
    end

    !d_branch && length(relevant_loops) != 1 && error("$d is not a branch point but it lies in two different loops")
    
    append!(to_be_removed,[[e in O ? 1 : (e[2],e[1]) in O ? -1 : 0 for e in edges] for O in relevant_loops])

  end

  #by design, the loop around infinity is placed at the last index in HS.plane_loops
  loops_around_inf = distinct_loops_above_pts[end]
  if length(loops_around_inf) == length(HS.D_inf)
    append!(to_be_removed, [[e in O ? 1 : (e[2],e[1]) in O ? -1 : 0 for e in edges] for O in loops_around_inf])
  else
    for d in HS.D_inf
      #note that we need both cases for d[1] zero and nonzero. if d[1] is zero then there is only one
      #point at infinity for the *plane equation* but this point may split under a normalization
      g = ((a,b),) -> (
        !iszero(d[1]) ? b//a - AcbField(256)(HS.D_defined_over_k ? iota(d[2]/d[1]) : d[2]/d[1])
        : a//b
      ) 

      for loop in loops_around_inf 
        winding = 0
        for (ini,ter) in loop 
          to_p = ((i,j),) -> (plane_points[i], fiber(HS, plane_points[i])[j])

          en = g(to_p(ter))
          st = g(to_p(ini))
          dif = en/st
          if contains_zero(imag(dif)) && contains_negative(real(dif))
            winding += ArbField(256)(1//2)
          else
            winding += angle(en/st) // (2 * const_pi(ArbField(256)))
          end
        end
        println(winding)
        if !contains_zero(winding)
          println("hello")
          println(d)
          push!(to_be_removed, [e in loop ? 1 : (e[2],e[1]) in loop ? -1 : 0 for e in edges])
        end
      end
    end
  end


  all([k in K for k in to_be_removed]) || error("something is wrong")

  K = [k for k in K if !(k in to_be_removed)]
  println("length(K): ", length(K))
  vector_basis = Vector{Vector{ZZRingElem}}()
  r = 0 
  for v in graph_hom 
    println(rank(matrix(Vector{Vector{ZZRingElem}}([[v]; vector_basis; K]))))
    if rank(matrix(Vector{Vector{ZZRingElem}}([[v]; vector_basis; K]))) - rank(matrix(K)) > r
      push!(vector_basis, v)
      r += 1
    end
  end

  HS.homology_basis = vector_basis
  return vector_basis

end

function reduce_homology(HS::MixedHodgeStructure)

  function reduction_function(w::Vector{ZZRingElem})

    p_mat = period_matrix(HS)
    m = length(cohomology(HS))
    v_basis = [QQBar.(i .== 1:m) for i in 1:m]
    println(length(v_basis))
    integrated_vector = [integrate_as_vectors(HS,w,v) for v in v_basis]

    approx_coords = is_invertible_with_inverse(p_mat)[2] * integrated_vector

    a = ArbField(HS.precision)(1/2)

    #test if there are unique integers in the balls. 
    all(overlaps(a, radius(real(z))) && !is_nonzero(imag(z)) for z in approx_coords) && error("Precision not high enough")

    return [round(ZZRingElem, real(z)) for z in approx_coords]

  end

  return reduction_function

end


#Strategy 1 of Nils Bruin, Linden Disney-Hogg, and Wuqian Effie Gao
#as presented in [BDG24] https://arxiv.org/pdf/2208.12377.
function integrate(HS::MixedHodgeStructure, omega::Union{FunFldDiff, Vector{Any}}, edge::Tuple{Tuple{Int64, Int64}, Tuple{Int64, Int64}}, Etol::Union{ArbFieldElem, Nothing} = nothing)

  if isdefined(HS, :master_matrix)
    i = findfirst(==(omega), cohomology(HS))
    j = findfirst(==(edge), HS.upstairs_edges) 
    if !(isnothing(i) || isnothing(j))
      val = HS.master_matrix[i][j]
      !isnothing(val) && return val 
    end
  end

  if !HS.E_empty
    (omega,vec) = omega 
  end

  iota = HS.embedding_QBar
  CC = AcbField(HS.precision)
  RR = ArbField(HS.precision)
  Etol = RR(2)^(-(HS.precision + 10))
  println(Etol)

  #if there is a singular point in E, then there is a correspondence between 
  #the paths going in/out of the singular point and the places extending the singular point.
  #the correspondence between the is not yet implemented
  if !isdefined(HS, :E_abstract_vertices) && !HS.E_empty
    (i,j) = HS.upstairs_vertices[end]
    (a,b) = HS.E_for_eval[1]
    overlaps(HS.plane_verts[i], CC(QQBar(a)))
    overlaps(fiber(HS,HS.plane_verts[i])[j], CC(QQBar(b)))
    indices = [
      findfirst(((i,j),) -> overlaps(HS.plane_verts[i], CC(QQBar(a))) && overlaps(fiber(HS,HS.plane_verts[i])[j], CC(QQBar(b))),
      HS.upstairs_vertices) for (a,b) in HS.E_for_eval
    ]
    HS.E_abstract_vertices = [HS.upstairs_vertices[j] for j in indices]
  end

  _,CCx = polynomial_ring(CC, :z)
  ini, ter = HS.plane_verts[edge[1][1]], HS.plane_verts[edge[2][1]]

  g = minpoly(omega.f)
  g = lcm([denominator(a) for a in Hecke.coefficients(g)]) * g
  a0 = numerator(Hecke.leading_coefficient(g))
  sq_free = divexact(a0, gcd(a0, derivative(a0)))
  #do something different if not defined over QQ 
  alphas = roots(change_base_ring(CC, _change_ring(sq_free,iota))(inv(2) * (CCx + 1) * ter - inv(2) * (CCx - 1) * ini))
  beta = RR(0.912)

  #Step 1&2: Interval bisection
  interval_bisection = [RR(-1)]
  delta_j = []
  current_endpoint = RR(1)
  while interval_bisection[end] != 1
    rho = minimum([abs(alpha - inv(2) * (interval_bisection[end] + current_endpoint)) for alpha in alphas], init = RR(1))
    delta = inv(2) * abs(current_endpoint - interval_bisection[end])
    if rho > delta 
      push!(interval_bisection, current_endpoint)
      push!(delta_j, inv(2) * (delta + rho))
      current_endpoint = RR(1)
    else 
      current_endpoint = inv(2) * (current_endpoint + interval_bisection[end])
    end
  end

  #Step 2&3: Compute M_j and N_j
  g_coeffs = [numerator(a) for a in Hecke.coefficients(g)]
  CC_g_coeffs = [change_base_ring(CC,_change_ring(a,iota))(inv(2) * (CCx + 1) * ter - inv(2) * (CCx - 1) * ini) for a in g_coeffs]
  Mj_vals = []
  for (i,d) in enumerate(delta_j)
    z0 = inv(2) * (interval_bisection[i] + interval_bisection[i+1])
    A0 = RR(1)
    for (fac,m) in factor(Hecke.leading_coefficient(g))
      fac_alphas = roots(change_base_ring(CC,fac)(inv(2) * (CCx + 1) * ter - inv(2) * (CCx - 1) * ini))
      A0 *= prod([abs(z0 - alpha) - d for alpha in fac_alphas], init = RR(1))^m
    end
    A0 *= abs(Hecke.leading_coefficient(CC_g_coeffs[end]))
    #A0 = abs(Hecke.leading_coefficient(CC_g_coeffs[end])) * prod([abs(z0 - alpha) - d for alpha in alphas], init = RR(1))
    Ai = [sum([abs(coeff(a,j)) * (abs(z0) + d)^j for j in 0:degree(a)], init = RR(0)) for a in CC_g_coeffs[1:end-1]]
    reverse!(Ai)
    Mj = 2.5 * maximum((A/A0)^(inv(k)) for (k,A) in enumerate(Ai))
    push!(Mj_vals, Mj)
  end
  rj_values = [acosh(2 * d * inv(abs(interval_bisection[j] - interval_bisection[j+1]))) for (j,d) in enumerate(delta_j)]
  #See remark 3.4
  Nj_values_arb = [
    inv(2*r) * log((RR(pi) + 64*inv(15 * (exp(2*r) - 1))) * M * inv(Etol))
    for (r,M) in zip(rj_values, Mj_vals)
  ]
  if all(isinfinite(z) for z in Nj_values_arb)
    Nj_values = [Int(2) for _ in Nj_values_arb]
  else
    #
    Nj_values = [2*Int(ceil(BigFloat(x) + BigFloat(radius(x)))) for x in Nj_values_arb]
  end
  println(Nj_values)
  println(Nj_values_arb)
  #Step 4: Computing Gauss-Legendre approximates
  path = z -> inv(2) * (z + 1) * ter - inv(2) * (z - 1) * ini 
  num = numerator(omega.f)
  denom = change_base_ring(CC,_change_ring(denominator(omega.f),iota))
  coeffs = [change_base_ring(CC,_change_ring(f,iota)) for f in Hecke.coefficients(num)]
  ev_f = (a,b) -> inv(denom(a)) * sum([f(a) * b^(i - 1) for (i,f) in enumerate(coeffs)])
  
  int_values = []
  continuations = []
  for (j,N) in enumerate(Nj_values)
    z1,z2 = interval_bisection[j:j+1]
    abscissae, weights = gauss_legendre_integration_points(N, HS.precision)
    gamma = CPath(path(z1),path(z2),0)
    x_vals, y_vals = analytic_continuation(HS.RS_object, gamma, abscissae)
    #keep track of how the sheets permute, if the last analytic continuation switched around sheets i and j, then we want 
    #to add the integral of this part in the j-th position to the i-th integral of the previous part 
    if length(continuations) != 0
      sheet_permutation = Dict(i => findfirst(z -> overlaps(z,Y), continuations[end][end])  for (i,Y) in enumerate(y_vals[1]))
    else
      sheet_permutation = Dict(i => i for (i,_) in enumerate(y_vals[1]))
    end
    println(sheet_permutation)
    push!(continuations, y_vals)
    x_vals, y_vals = x_vals[2:end - 1], y_vals[2:end - 1]
    ints = [RR(0) for _ in y_vals[1]] #length(y_vals[1]) is the degree of the covering 
    for (i,(x,w)) in enumerate(zip(x_vals, weights))
      if !iszero(omega)
        ints += [w * ev_f(x,y) for y in y_vals[i]]
      end
    end
    ints = [inv(2) * (path(z2) - path(z1)) * v for v in ints]
    ints_permuted = [ints[sheet_permutation[i]] for (i,_) in enumerate(ints)]
    push!(int_values, ints_permuted)
  end
  sheet_permutation = Dict(findfirst(z -> overlaps(z,Y), continuations[end][end]) => i for (i,Y) in enumerate(fiber(HS, ter)))
  
  #final_vals are the values of omega integrated along all the paths above x(edge)
  final_vals_no_bound = sum(int_values)

  #here we give the outputs the error such that the 
  #value of the integral lies within the ball
  final_vals = Vector{AcbFieldElem}()
  for z in final_vals_no_bound
    w = deepcopy(z)
    rew = real(w)
    imw = imag(w)
    add_error!(rew,Etol)
    add_error!(imw,Etol)
    push!(final_vals, rew + onei(CC) * imw)
  end


  edge_indices = [
    findfirst(((v1,v2),) -> (v1 == (edge[1][1], i)) && (v2[1] == edge[2][1]), HS.upstairs_edges)
    for (i,_) in enumerate(final_vals)
  ]
  
  edges = [HS.upstairs_edges[e] for e in edge_indices] 
  sign = Dict(edge[1] => CC(-1), edge[2] => CC(1))
  if !HS.E_empty
    for (k,_) in enumerate(final_vals)
      final_vals[k] += sum(CC(vec[j]) * get(sign,v,CC(0)) for (j,v) in enumerate(HS.E_abstract_vertices))
    end
  end

  if isdefined(HS, :master_matrix)
    i = findfirst(==(HS.E_empty ? omega : [omega,vec]), cohomology(HS))
    if !isnothing(i)
      for (k,j) in enumerate(edge_indices)
        HS.master_matrix[i][j] = final_vals[k] 
      end
    end
  end

  return final_vals[edge[1][2]]
  
end

function integrate_as_vectors(HS::MixedHodgeStructure, gamma::Vector{ZZRingElem}, v::Vector{QQBarFieldElem})
  
  _set_master_matrix(HS)
  cohom_basis = cohomology(HS)

  @assert length(cohom_basis) == length(v)
  @assert length(gamma) == length(HS.upstairs_edges)

  form_indices = [i for (i,a) in enumerate(v)     if !iszero(a)]
  edge_indices = [j for (j,a) in enumerate(gamma) if !iszero(a)]

  CC = AcbField(HS.precision)
  output = CC(0)

  for (i,j) in Iterators.product(form_indices, edge_indices)
    output += CC(v[i]) * CC(gamma[j]) * integrate(HS, cohom_basis[i], HS.upstairs_edges[j])
  end

  return output


  if length(HS.singular_points_in_E) != 0
    error("singular point in E: this does not work for now")
  end 

end

function period_matrix(HS::MixedHodgeStructure)

  if isdefined(HS, :period_matrix)
    return HS.period_matrix
  end

  hom_basis = homology_basis(HS)
  cohom_basis = cohomology(HS)

  v_basis = [QQBar.(i .== 1:length(cohom_basis)) for (i,_) in enumerate(cohom_basis)]

  period_matrix = [[integrate_as_vectors(HS, gamma, v) for gamma in hom_basis] for v in v_basis]
  HS.period_matrix = matrix(period_matrix)
  
  return matrix(period_matrix)
end

function holom_period_matrix(HS::MixedHodgeStructure)
  P = period_matrix(HS)
  r = reduction(HS)
  B = basis_of_differentials(HS.function_field)
  CC = AcbField(HS.precision)
  iota = HS.embedding_QBar
  return [[CC(iota(a)) for a in r(b)] * P for b in B]

end


function _set_master_matrix(HS::MixedHodgeStructure)

  if isdefined(HS, :master_matrix)
    return 
  end

  _set_upstairs_graph(HS)
  cohom_basis = cohomology(HS)

  HS.master_matrix = [[nothing for _ in HS.upstairs_edges] for _ in cohom_basis]
end


function _show_plane_graph(HS::MixedHodgeStructure)

  if !isdefined(HS, :plane_edges)
    _set_plane_graph(HS)
  end

  verts = HS.plane_verts
  plane_edges = HS.plane_edges

  plot()
  for (i,j) in plane_edges 
    a,b = ComplexF64(verts[i]), ComplexF64(verts[j])
    plot!([real(a),real(b)],[imag(a),imag(b)],color=:black, legend=false)
  end

  iota = HS.embedding_QBar
  for z in [HS.branch_points; [HS.D_defined_over_k ? QQBar(iota(a)) : a for (a,_) in HS.D]]
    z = ComplexF64(z)
    scatter!([real(z)],[imag(z)],legend=false)
  end
  display(current())
end


function _abstract_graph_of_triangulation(HS::MixedHodgeStructure)
  if !isdefined(HS, :upstairs_edges)
    _set_upstairs_graph(HS)
  end

  edges = HS.upstairs_edges
  verts = unique([[e[1] for e in edges]; [e[2] for e in edges]])
  abstractification = Dict(v => i for (i,v) in enumerate(verts))

  return [(abstractification[e[1]], abstractification[e[2]]) for e in edges]
end

function function_field_for_morphism(HS::MixedHodgeStructure)
  return HS.function_field_Qbar, (HS.x2, HS.y2)
end


function finite_maximal_ord(HS::MixedHodgeStructure)
  if isdefined(HS, :finite_maximal_ord)
    return HS.finite_maximal_ord
  end
  return finite_maximal_order(HS.function_field)
end

function infinite_maximal_ord(HS::MixedHodgeStructure)
  if isdefined(HS, :infinite_maximal_ord)
    return HS.infinite_maximal_ord
  end
  return infinite_maximal_order(HS.function_field)
end

function hs_genus(HS::MixedHodgeStructure)
  if isdefined(HS, :genus)
    return HS.genus
  end
  return genus(HS.function_field)
end