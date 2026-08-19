struct EmbeddedDivisorAmbient{T}
  R::Any
  X::MPolyIdeal{T}
  projective::Bool
  irrelevant::Union{Nothing, MPolyIdeal{T}}
  geometric_coordinate_ideal_cache::Base.RefValue{Union{Nothing, MPolyIdeal{T}}}
end

function EmbeddedDivisorAmbient{T}(R, X, projective, irrelevant) where {T}
  X0 = convert(MPolyIdeal{T}, X)
  p = convert(Bool, projective)
  irr = convert(Union{Nothing, MPolyIdeal{T}}, irrelevant)
  cache = Ref{Union{Nothing, MPolyIdeal{T}}}(p ? nothing : X0)
  return EmbeddedDivisorAmbient{T}(R, X0, p, irr, cache)
end

EmbeddedDivisorAmbient(R, X::MPolyIdeal{T}, projective::Bool,
                       irrelevant::Union{Nothing, MPolyIdeal{T}}) where {T} =
  EmbeddedDivisorAmbient{T}(R, X, projective, irrelevant)

struct EmbeddedDivisor{T}
  ambient::EmbeddedDivisorAmbient{T}
  num::MPolyIdeal{T}
  den::MPolyIdeal{T}
end

struct EmbeddedDivisorSections{T}
  divisor::EmbeddedDivisor{T}
  numerator::MPolyIdeal{T}
  denominator::T
end

struct EmbeddedGradedModuleSections{T}
  ambient::EmbeddedDivisorAmbient{T}
  module_object::Any
  numerator::MPolyIdeal{T}
  denominator::T
  sheaf_degree::Any
  numerator_degree::Any
  trivialization_shift::Any
  vector_space::Any
  embedding::Any
  numerators::Vector{T}
end

struct EmbeddedFormalDivisor{T}
  ambient::EmbeddedDivisorAmbient{T}
  summands::Vector{Tuple{Int, EmbeddedDivisor{T}}}
end

struct EmbeddedModuleTrivialization{T}
  ambient::EmbeddedDivisorAmbient{T}
  module_object::Any
  numerator::MPolyIdeal{T}
  denominator::T
  images::Vector{T}
  shift::Any
  method::Symbol
end

struct TrivializedSheafSectionBasis{T <: MPolyDecRingElem}
  basis::SheafSectionBasis{T}
  trivialization::EmbeddedModuleTrivialization{T}
  numerators::Vector{T}
  denominator::T
  twist::Int
end
