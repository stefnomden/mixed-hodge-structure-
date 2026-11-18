function Base.show(io::IO, phi::MarkingMorphism)
  s = typeof(codomain(phi)) <: AbstractAbVar ? "abelian variety" : "semi abelian variety" 
  println(io, "Marking on a $(dim(codomain(phi)))-dimensional $(s)")
  println(io, "by a rank $(rank(domain(phi))) lattice.")
end


images(phi::MarkingMorphism) = phi.images
Hecke.domain(phi::MarkingMorphism) = phi.domain
Hecke.codomain(phi::MarkingMorphism) = phi.codomain

function extension_structure(L::DivisorLattice, J::Jacobian)
  #this function constructs the structure morphism L -> J which defines 
  #the element in Ext1(J,Hom(L,Gm)). When L is a divisor lattice, this map 
  #is obvious.
  @assert function_field(L) === function_field(J)
  phi = MarkingMorphism(L,J)
  divisors = basis(L)
  phi.images = JacobianPoint[J(D) for D in divisors]
  return phi
end

extension_structure(T::Torus, J::Jacobian) = extension_structure(dual(T), J)

function (phi::MarkingMorphism)(v::AbstractLatticeElem)
  @assert domain(phi) === parent(v)
  v_crd = coordinates(v)
  A = codomain(phi)
  return sum(a * P for (a,P) in zip(v_crd, images(phi)))
end
