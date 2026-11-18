abstract type AbstractLattice end
abstract type AbstractLatticeElem end

mutable struct DivisorLattice <: AbstractLattice

  divisor_basis::Vector{Divisor}
  ambient_field::AbstractAlgebra.Generic.AbsSimpleFunctionField

  function DivisorLattice()
    L = new()
    return L
  end

end #struct

mutable struct DivisorLatticeElem <: AbstractLatticeElem

  divisor_realisation::Union{Nothing, <:Divisor}
  divisor_summands::Union{Nothing, Vector{Tuple{<:Divisor, Int}}}
  parent::DivisorLattice

  #elements of the lattice Z^n are represented by row vectors
  vector_realisation::ZZMatrix

  function DivisorLatticeElem()
    v = new()
    return v
  end

end #struct

mutable struct LatticeHom{S <: AbstractLattice, T <: AbstractLattice}

  domain::S
  codomain::T

  group_hom::FinGenAbGroupHom 

  function LatticeHom{S,T}() where {S<:AbstractLattice, T<:AbstractLattice}
    f = new{S,T}()
    return f
  end
end #struct

mutable struct Torus{S <: AbstractLattice}

  character_lattice::S

  function Torus{S}() where {S <: AbstractLattice}
    return new{S}()
  end

end #struct

#We cache tori because they are constructed using a lattice
#this way, for a Torus T, dual(dual(T)) === T returns true.
const torus_cache = IdDict{AbstractLattice, Torus}()

MatType = Matrix{QQBarFieldElem}

mutable struct TorusPoint
  vector_realisation::MatType
  parent::Torus

  function TorusPoint()
    return new()
  end
end #struct

mutable struct TorusHom{S <: Torus, T <: Torus}

  domain::S
  codomain::T

  representing_matrix::ZZMatrix

  function TorusHom{S,T}() where {S <: Torus, T <: Torus}
    return new{S,T}()
  end
end #struct

abstract type AbstractSemiAbVar end
abstract type AbstractAbVar <: AbstractSemiAbVar end

mutable struct Jacobian{F} <: AbstractAbVar
  function_field::F
  plane_equation::MPolyRingElem
  function Jacobian{F}() where F
    J = new{F}()
    return J
  end
end #struct

mutable struct JacobianPoint
  parent::Jacobian
  divisor_representation::Divisor
  is_principal_with_data::Tuple{Union{Nothing, Bool}, Union{Nothing, AbstractAlgebra.Generic.FunctionFieldElem}}
  function JacobianPoint()
    P = new()
    P.is_principal_with_data = (nothing, nothing)
    return P
  end

end #struct

#jacobian hom / abstractabvar hom here

mutable struct PuncturedMarkedCurve
  plane_equation::MPolyRingElem
  function_field::AbstractAlgebra.Generic.FunctionField
  function PuncturedMarkedCurve()
    return new()
  end
end

mutable struct PuncturedMarkedCurveMorphism{
    S <: PuncturedMarkedCurve,
    T <: PuncturedMarkedCurve
}
  domain::S
  codomain::T
  images::NTuple{2, AbstractAlgebra.Generic.FunctionFieldElem}
  coordinates::Union{Nothing,NTuple{3, MPolyRingElem}}
end #struct

mutable struct GeometricPoint
  is_singular::Bool
  is_infinite::Bool
  place::Union{Nothing, Hecke.GenOrdIdl}
  associated_places::Union{Nothing, Vector{Hecke.GenOrdIdl}}
  parent_object::PuncturedMarkedCurve
  coordinates::NTuple{3, QQBarFieldElem}
  ev::Union{Nothing, MapFromFunc{<:AbstractAlgebra.Generic.FunctionField, QQBarField}}

  function GeometricPoint()
    P = new()
    P.place = nothing
    P.ev = nothing
    P.associated_places = nothing
    return P
  end

end

abstract type AbstractMarking end

mutable struct GeneralizedJacobian <: AbstractSemiAbVar
  jacobian_core::Jacobian
  torus_part::Torus
  punctures::Vector{GeometricPoint}
  structure_morphism::Union{Nothing, AbstractMarking}
  puncture_divisor::Union{Nothing, Divisor}
  function GeneralizedJacobian(
    J::Jacobian,
    T::Torus,
    punctures::Vector{GeometricPoint}
  )
    return new(J, T, punctures, nothing, nothing)
  end
end

mutable struct GeneralizedJacobianPoint
  parent::GeneralizedJacobian
  torus_part::TorusPoint
  jacobian_part::JacobianPoint
  function GeneralizedJacobianPoint()
    P = new()
    return P
  end
end

mutable struct MarkingMorphism{S <: AbstractLattice, T <: AbstractSemiAbVar} <: AbstractMarking
  domain::S
  codomain::T
  images::Union{Vector{GeneralizedJacobianPoint}, Vector{JacobianPoint}}
  function MarkingMorphism(domain::S,codomain::T) where {
    S <: AbstractLattice, 
    T <: AbstractSemiAbVar
  }
    return new{S,T}(domain,codomain)
  end
end #struct



