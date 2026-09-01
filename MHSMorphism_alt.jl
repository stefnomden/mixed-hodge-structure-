
abstract type AbstractMixedHodgeStructureMorphism end
abstract type AbstractInducedMixHdgStrucMorph <: AbstractMixedHodgeStructureMorphism end

mutable struct PullBackMHSMorphism <: AbstractInducedMixHdgStrucMorph 
  domain::MixedHodgeStructure
  codomain::MixedHodgeStructure
  underlying_morphism::FunctionFieldHomWithMHS
  E_permutation::Vector{Tuple{Int,Int}}

  cohomology_matrix::Vector{Vector{Union{NumFieldElem, QQBarFieldElem}}}
  homology_matrix::ZZMatrix

  function PullBackMHSMorphism(HS1::MixedHodgeStructure, HS2::MixedHodgeStructure)
    Phi = new()
    Phi.domain = HS1
    Phi.codomain = HS2
    return Phi
  end

end

mutable struct TransferMHSMorphism <: AbstractInducedMixHdgStrucMorph 
  domain::MixedHodgeStructure
  codomain::MixedHodgeStructure
  underlying_morphism::FunctionFieldHomWithMHS

  cohomology_matrix::Vector{Vector{Union{NumFieldElem, QQBarFieldElem}}}
  homology_matrix::ZZMatrix

  function TransferMHSMorphism(HS1::MixedHodgeStructure, HS2::MixedHodgeStructure)
    Phi = new()
    Phi.domain = HS1 
    Phi.codomain = HS2
    return Phi
  end
end

###################################################################################################

function Base.show(io::IO, Phi::AbstractMixedHodgeStructureMorphism)
  if typeof(Phi) <: TransferMHSMorphism
    println("Transfer morphism:")
    curve_str = ("C2", "C1")
  end
  if typeof(Phi) <: PullBackMHSMorphism
    println("Pull-back morphism:")
    curve_str = ("C1", "C2")
  end
  println("Morphism of mixed hodge structures")
  print("  from ")
  show(stdout, Phi.domain; C = curve_str[1])
  println()
  print("  to ")
  show(stdout, Phi.codomain; C = curve_str[2])
  if isdefined(Phi, :cohomology_matrix)
    println()
    println("defined on cohomology H^1($(curve_str[1])) --> H^1($(curve_str[2])) by")
    emb = Phi.underlying_morphism.embedding
    mat = Phi.cohomology_matrix
    display(transpose(matrix([[parent(a) == QQBar ? a : emb(a) for a in v] for v in mat])))
  end
  if isdefined(Phi, :homology_matrix)
    println()
    println("defined on homology H_1($(curve_str[2])) --> H_1($(curve_str[1])) by")
    display(Phi.homology_matrix)
  end
end


function pull_back(phi::FunctionFieldHomWithMHS)

  HS1 = phi.domain
  HS2 = phi.codomain

  imE = Set(phi.phi_star(HS2.embedding_QBar.(P)) for P in HS2.E)
  @assert issubset(imE, Set(HS1.embedding_QBar.(P) for P in HS1.E)) (
    "Marked points of domain are not mapped into marekd points of codomain"
  )
  #TODO: check if preimage of D_1 is contained in D_2. This can be done using resultants
  #(a:b:c) = (F:G:H), if c=1 then Res(P1, bF(x,y,1) - aG(x,y,1)) gives the x-coords
  #of solutions  

  Phi = PullBackMHSMorphism(HS1, HS2)
  Phi.underlying_morphism = phi

  return Phi

end

function transfer(phi::FunctionFieldHomWithMHS)
  
  HS1 = phi.domain
  HS2 = phi.codomain

  #TODO: check conditions on preimage of D and E and containments.

  #note how the domain and codomain of Phi are flipped (phi : k(C1) -> k(C2)) and (Phi : H(C2) -> H(C1))
  Phi = TransferMHSMorphism(HS2, HS1)
  Phi.underlying_morphism = phi
  
  return Phi

end

function cohomology(Phi::PullBackMHSMorphism)
  
  if isdefined(Phi, :cohomology_matrix)
    phi = Phi.underlying_morphism
    return transpose(matrix([[parent(a) == QQBar ? a : phi.embedding(a) for a in v] for v in Phi.cohomology_matrix]))
  end

  phi = Phi.underlying_morphism
  Phi.E_permutation = _find_E_permutation(phi)
  perm = Dict(i => j for (i,j) in Phi.E_permutation)

  #preperation on the codomain's end (mainly converting everything)
  #to the larger function field
  F2 = phi.function_field2
  dummy_hs = deepcopy(phi.codomain)
  (x,y) = phi.gens2
  dx2 = differential(x)
  emb = phi.k2_to_K
  dummy_hs.zero_res_basis = [map_function_field_coeffs(omega.f, emb, F2) * dx2 for omega in _zero_res_basis(phi.codomain)]
  dummy_hs.res_basis = [map_function_field_coeffs(omega.f, emb, F2) * dx2 for omega in _residue_basis(phi.codomain)]

  #find divisors used in 'reduction'
  if isdefined(phi.codomain, :canon_div)
    Ofin = finite_maximal_order(F2)
    Oinf = infinite_maximal_order(F2)
    fin, inf = ideals(phi.codomain.canon_div)
    fin_new = sum(Ofin * map_function_field_coeffs(f,emb,F2) for f in basis(fin))
    inf_new = sum(Oinf * map_function_field_coeffs(f,emb,F2) for f in basis(inf))
    dummy_hs.canon_div = Hecke.divisor(fin_new,inf_new)
  else 
    dummy_hs.canon_div = canonical_divisor(F2)
  end

  if isdefined(phi.codomain, :D_div)
    Ofin = finite_maximal_order(F2)
    Oinf = infinite_maximal_order(F2)
    fin, inf = ideals(phi.codomain.D_div)
    fin_new = sum(Ofin * map_function_field_coeffs(f,emb,F2) for f in basis(fin))
    inf_new = sum(Oinf * map_function_field_coeffs(f,emb,F2) for f in basis(inf))
    dummy_hs.D_div = Hecke.divisor(fin_new,inf_new)
  else
    dummy_hs.D_div = trivial_divisor(F2)
  end

  (i,j) = phi.codomain.R_data
  dummy_hs.R = i * pole_divisor(x) + j * pole_divisor(y)

  dummy_hs.embedding_QBar = phi.embedding

  red = reduction(dummy_hs)

  #preperation on the domain's end
  F1 = phi.function_field1
  emb = phi.k1_to_K
  if phi.domain.E_empty
    cohom_basis = [map_function_field_coeffs(omega.f, emb, F1) for omega in cohomology(phi.domain)]
  else
    cohom_basis = [[map_function_field_coeffs(omega[1].f, emb, F1), omega[2]] for omega in cohomology(phi.domain)]
  end

  dphi_x = differential(phi.x_image)

  mat = Vector{Vector{Union{NumFieldElem, QQBarFieldElem}}}()

  for f in cohom_basis
    println(f)
    if phi.codomain.E_empty
      omega = phi(f) * dphi_x
    else
      f,vec = f
      omega = [phi(f) * dphi_x, [vec[perm[i]] for i in 1:length(phi.domain.E_for_eval)]]
    end
    println(omega)
    push!(mat,red(omega))
  end

  Phi.cohomology_matrix = mat

  return transpose(matrix([[parent(a) == QQBar ? a : phi.embedding(a) for a in v] for v in mat]))

end

function homology(Phi::AbstractMixedHodgeStructureMorphism)
  if isdefined(Phi, :homology_matrix)
    return Phi.homology_matrix
  end

  p1 = period_matrix(Phi.domain)
  p2 = period_matrix(Phi.codomain)
  cohom_mat = cohomology(Phi)

  prec = max(Phi.domain.precision, Phi.codomain.precision)
  CC = AcbField(prec)

  pull_back_candidate = is_invertible_with_inverse(p1)[2] * transpose(map_entries(z -> CC(z), cohom_mat)) * p2
  println(pull_back_candidate)

  a = ArbField(prec)(1/2)
  Z = ArbField(prec)(0)

  output = zero_matrix(integer_ring(), size(pull_back_candidate)...)
  
  for i in 1:nrows(pull_back_candidate)
    row = pull_back_candidate[i, 1:end]
    all(!overlaps(radius(real(z)),a) && !is_nonzero(imag(z)) for z in row) || error("precision too low") 
    start = time()
    output[i, 1:end] = [round(ZZRingElem, real(z)) for z in row]
    println(time() - start)
  end

  Phi.homology_matrix = output

  return Phi.homology_matrix

end


function cohomology(Phi::TransferMHSMorphism)

  if isdefined(Phi, :cohomology_matrix)
    phi = Phi.underlying_morphism
    return transpose(matrix([[parent(a) == QQBar ? a : phi.embedding(a) for a in v] for v in Phi.cohomology_matrix]))
  end

  start = time()
  phi = Phi.underlying_morphism

  #preperation on the codomain's end (mainly converting everything)
  #to the larger function field
  F1 = phi.function_field1
  dummy_hs = deepcopy(Phi.codomain)
  (x,y) = phi.gens1
  dx1 = differential(x)
  emb = phi.k1_to_K
  dummy_hs.zero_res_basis = [map_function_field_coeffs(omega.f, emb, F1) * dx1 for omega in _zero_res_basis(Phi.codomain)]
  dummy_hs.res_basis = [map_function_field_coeffs(omega.f, emb, F1) * dx1 for omega in _residue_basis(Phi.codomain)]

  #find the map on Q^E2 -> Q^E1
  F2 = phi.codomain.function_field_Qbar
  x2,y2 = phi.codomain.x2, phi.codomain.y2
  x1,y1 = phi.domain.x2, phi.domain.y2
  O = finite_maximal_order(F2)

  if !phi.codomain.E_empty
    #elements in E_image are indexed by E1 and represent the image of E1 in 
    #E2 indexed by E2
    E_for_eval_plc = [typeof(P) <: Vector ? ideal(O,O(x2-P[1]), O(y2-P[2])) : P for P in phi.codomain.E_for_eval]
    E_image = Vector{Vector{QQBarFieldElem}}()
    for P in phi.domain.E_for_eval
      if typeof(P) <: Vector 
        (a,b) = phi.phi_star(P)
        I = ideal(O, O(phi(x1) - a), O(phi(y1) - b))
      else
        I = sum(ideal(O,O(phi(phi.domain.function_field_Qbar(b)))) for b in basis(P))
      end
      fac = factor(I)
      push!(E_image,[get(fac,p,zero(QQBar)) for p in E_for_eval_plc])
    end
  end

  #find divisors used in 'reduction'
  if isdefined(Phi.codomain, :canon_div)
    Ofin = finite_maximal_order(F1)
    Oinf = infinite_maximal_order(F1)
    fin, inf = ideals(Phi.codomain.canon_div)
    fin_new = sum(Ofin * map_function_field_coeffs(f,emb,F1) for f in basis(fin))
    inf_new = sum(Oinf * map_function_field_coeffs(f,emb,F1) for f in basis(inf))
    dummy_hs.canon_div = Hecke.divisor(fin_new,inf_new)
  else 
    dummy_hs.canon_div = canonical_divisor(F1)
  end

  if isdefined(Phi.codomain, :D_div)
    Ofin = finite_maximal_order(F1)
    Oinf = infinite_maximal_order(F1)
    fin, inf = ideals(Phi.codomain.D_div)
    fin_new = sum(Ofin * map_function_field_coeffs(f,emb,F1) for f in basis(fin))
    inf_new = sum(Oinf * map_function_field_coeffs(f,emb,F1) for f in basis(inf))
    dummy_hs.D_div = Hecke.divisor(fin_new,inf_new)
  else
    dummy_hs.D_div = trivial_divisor(F1)
  end

  (i,j) = Phi.codomain.R_data
  dummy_hs.R = i * pole_divisor(x) + j * pole_divisor(y)
  dummy_hs.embedding_QBar = phi.embedding

  red = reduction(dummy_hs)
  #prep on the domain's end
  F2 = phi.function_field2
  emb = phi.k2_to_K

  if Phi.domain.E_empty
    cohom_basis = [map_function_field_coeffs(omega.f, emb, F2) for omega in cohomology(Phi.domain)]
  else
    cohom_basis = [[map_function_field_coeffs(omega[1].f, emb, F2), omega[2]] for omega in cohomology(Phi.domain)]
  end

  t = trace_map(phi)
  dtrx = differential(t(phi.gens2[1]))
  dx2_over_dphix1 = differential(phi.gens2[1]) // differential(phi(x))

  mat = Vector{Vector{Union{NumFieldElem, QQBarFieldElem}}}()

  for f in cohom_basis
    if Phi.codomain.E_empty
      omega = t(f * dx2_over_dphix1) * dx1
    else
      f,vec = f
      omega = [t(f * dx2_over_dphix1) * dx1, sum([a * ei for ei in e] for (a,e) in zip(vec,E_image))]
    end
    push!(mat,red(omega))
  end

  Phi.cohomology_matrix = mat

  return transpose(matrix([[parent(a) == QQBar ? a : phi.embedding(a) for a in v] for v in mat]))

end
