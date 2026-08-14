
abstract type AbstractMixedHodgeStructureMorphism end
abstract type AbstractInducedMixHdgStrucMorph <: AbstractMixedHodgeStructureMorphism end

mutable struct PullBackMHSMorphism <: AbstractInducedMixHdgStrucMorph 
  domain::MixedHodgeStructure
  codomain::MixedHodgeStructure
  underlying_morphism::FunctionFieldHomWithMHS
  E_permutation::Vector{Tuple{Int,Int}}

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

  function PullBackMHSMorphism(HS1::MixedHodgeStructure, HS2::MixedHodgeStructure)
    Phi = new()
    Phi.domain = HS1 
    Phi.codomain = HS2
    return Phi
  end
end

###################################################################################################


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

  Phi.E_permutation = _find_E_permutation(phi)

  return Phi

end