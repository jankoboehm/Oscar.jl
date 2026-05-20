struct EmbeddedDivisorAmbient{T}
  R::Any
  X::MPolyIdeal{T}
  projective::Bool
  irrelevant::Union{Nothing, MPolyIdeal{T}}
end

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
