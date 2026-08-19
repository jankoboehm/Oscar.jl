###############################################################################
# SectionBasis.jl
#
# Turn vector-valued finite-tail representatives into rational sections of a
# generically rank-one sheaf and into homogeneous coordinates for rational maps.
###############################################################################

@doc raw"""
    TrivializedSheafSectionBasis{T}

A scalar version of a [`SheafSectionBasis`](@ref), obtained from a rational
trivialization of its graded module.

Suppose that `B` represents sections ``v_i/g`` in a graded module ``M`` and
that `T` sends the chosen generators of ``M`` to ``h_j/f``.  The entries of
`section_numerators(S)` are the polynomials ``H_i`` obtained by applying `T` to
``v_i``, and

```math
  \frac{H_i}{fg}
```

are the corresponding rational sections.  The common denominator is returned
by `section_denominator(S)`.  If ``M`` represents a line bundle, the entries of
`projective_coordinates(S)` define the rational map associated to the computed
linear system.  They are not normalized and may retain a common fixed factor.

The construction also applies to a torsion-free, generically rank-one sheaf.
It does not make the module locally free or reflexive.
""" TrivializedSheafSectionBasis

Base.length(S::TrivializedSheafSectionBasis) = length(S.numerators)
Base.eltype(::Type{TrivializedSheafSectionBasis{T}}) where {T} = T
Base.eltype(::TrivializedSheafSectionBasis{T}) where {T} = T
Base.iterate(S::TrivializedSheafSectionBasis, state::Int=1) =
  state > length(S) ? nothing : (S.numerators[state], state + 1)

function Base.show(io::IO, S::TrivializedSheafSectionBasis)
  print(io, "TrivializedSheafSectionBasis(twist = ", S.twist,
        ", number of basis sections = ", length(S), ")")
end

underlying_section_basis(S::TrivializedSheafSectionBasis) = S.basis

underlying_module(S::TrivializedSheafSectionBasis) = underlying_module(S.basis)

section_trivialization(S::TrivializedSheafSectionBasis) = S.trivialization

section_numerators(S::TrivializedSheafSectionBasis) = S.numerators

section_basis_numerators(S::TrivializedSheafSectionBasis) = S.numerators

section_denominator(S::TrivializedSheafSectionBasis) = S.denominator

section_basis_rational(S::TrivializedSheafSectionBasis) =
  [(h, S.denominator) for h in S.numerators]

projective_coordinates(S::TrivializedSheafSectionBasis) = S.numerators

tail_degree(S::TrivializedSheafSectionBasis) = tail_degree(S.basis)

twist(S::TrivializedSheafSectionBasis) = S.twist

section_degree(S::TrivializedSheafSectionBasis) = S.twist

section_trivialization_shift(S::TrivializedSheafSectionBasis) =
  trivialization_shift(S.trivialization)

@doc raw"""
    rank_one_module_trivialization(A::EmbeddedDivisorAmbient, M; kwargs...)
    rank_one_module_trivialization(A::EmbeddedDivisorAmbient, M, images;
                                   denominator=one(A.R), shift=nothing,
                                   kwargs...)

Choose a rational trivialization of a generically rank-one module `M` on `A`.

The result records polynomials `images = [h_1, ..., h_r]` and a common
denominator `f`; the `i`-th chosen module generator is sent to ``h_i/f``.
Without explicit `images`, they are computed from the presentation of `M`.
The optional `shift` records the homogeneous degree of the trivialization and
is inferred when possible.
""" rank_one_module_trivialization

@doc raw"""
    trivialization_numerator(T::EmbeddedModuleTrivialization, m; check=true)

Apply the numerator map of the rational trivialization `T` to the module
element `m`.

If ``m=\sum_i c_i m_i`` in the generators of the module and `T` maps ``m_i``
to ``h_i/f``, this returns ``\sum_i c_i h_i``.  Thus the rational image of
`m` is the returned polynomial divided by `trivialization_denominator(T)`.
"""
function trivialization_numerator(T::EmbeddedModuleTrivialization{U}, m;
                                  check::Bool=true) where {U <: MPolyDecRingElem}
  M = T.module_object
  M isa OFPModule ||
    error("trivialization_numerator requires a module trivialization")
  if check
    parent(m) === M || error("the element does not belong to the trivialized module")
    length(T.images) == _number_of_module_generators(M) ||
      error("the trivialization has the wrong number of generator images")
    _check_module_trivialization_relations(T)
  end

  c = coordinates(m)
  h = zero(T.ambient.R)
  for i in 1:length(T.images)
    h += _as_ambient_poly(T.ambient, c[i]) * T.images[i]
  end
  return h
end

function _check_module_trivialization_relations(T::EmbeddedModuleTrivialization)
  M = T.module_object
  p = presentation(M)
  F0 = p[0]
  F1 = p[1]
  augmentation = map(p, 0)
  d1 = map(p, 1)
  images = [trivialization_numerator(T, augmentation(e); check=false)
            for e in gens(F0)]
  for e in gens(F1)
    c = coordinates(d1(e))
    h = zero(T.ambient.R)
    for i in 1:length(images)
      h += _as_ambient_poly(T.ambient, c[i]) * images[i]
    end
    _is_zero_on_X(T.ambient, h) ||
      error("the trivialization images do not satisfy the module relations on the embedded variety")
  end
  return nothing
end

function _check_module_supported_on_ambient(A::EmbeddedDivisorAmbient, M)
  for q in gens(A.X)
    for m in gens(M)
      is_zero(q*m) ||
        error("the coordinate ideal does not annihilate the graded module")
    end
  end
  return nothing
end

function _presentation_generator_images(B::SheafSectionBasis,
                                        T::EmbeddedModuleTrivialization)
  augmentation = _section_presentation_augmentation(B)
  return [trivialization_numerator(T, augmentation(e); check=false)
          for e in gens(B.presentation_free_module)]
end

function _check_trivialization_relations(B::SheafSectionBasis,
                                         T::EmbeddedModuleTrivialization)
  A = T.ambient
  images = _presentation_generator_images(B, T)
  for r in _section_presentation_relations(B)
    c = coordinates(r)
    h = zero(A.R)
    for i in 1:length(images)
      h += _as_ambient_poly(A, c[i]) * images[i]
    end
    _is_zero_on_X(A, h) ||
      error("the trivialization images do not satisfy the module relations on the embedded variety")
  end
  return nothing
end

function _check_rational_denominator(A::EmbeddedDivisorAmbient, f, name::String)
  _is_zero_on_X(A, f) && error("the $name vanishes on the embedded variety")
  _is_regular_on_X(A, f) ||
    error("the $name is a zero divisor on the embedded variety")
  return nothing
end

function _check_section_trivialization(B::SheafSectionBasis,
                                       T::EmbeddedModuleTrivialization)
  A = T.ambient
  M = underlying_module(B)
  A.projective || error("finite-tail section bases require a projective ambient")
  M === T.module_object ||
    error("the section basis and the trivialization refer to different modules")
  base_ring(M) === A.R ||
    error("the section module is not over the ambient homogeneous coordinate ring")
  length(T.images) == _number_of_module_generators(M) ||
    error("the trivialization has the wrong number of generator images")
  _check_module_supported_on_ambient(A, M)
  _check_rational_denominator(A, section_denominator(B),
                              "tail evaluation denominator")
  _check_rational_denominator(A, trivialization_denominator(T),
                              "trivialization denominator")
  is_homogeneous(section_denominator(B)) ||
    error("the tail evaluation denominator is not homogeneous")
  is_homogeneous(trivialization_denominator(T)) ||
    error("the trivialization denominator is not homogeneous")
  for h in trivialization_images(T)
    (is_zero(h) || is_homogeneous(h)) ||
      error("the trivialization images are not homogeneous")
  end
  _check_trivialization_relations(B, T)
  return nothing
end

function _check_scalar_section_numerators(A::EmbeddedDivisorAmbient, numerators)
  isempty(numerators) && return nothing
  first_degree = nothing
  for h in numerators
    _is_zero_on_X(A, h) &&
      error("a section basis element becomes zero under the trivialization")
    is_homogeneous(h) || error("a scalarized section numerator is not homogeneous")
    d = degree(Int, h; check=false)
    if first_degree === nothing
      first_degree = d
    else
      d == first_degree ||
        error("the scalarized section numerators do not have a common degree")
    end
  end
  return nothing
end

@doc raw"""
    trivialized_section_basis(B::SheafSectionBasis,
                              T::EmbeddedModuleTrivialization; check=true)

Convert the vector-valued finite-tail representatives in `B` to scalar rational
sections using `T`.

The actual presentation augmentation is used before applying the
trivialization.  Consequently this also works when the zeroth presentation
module has multiple generators or is not the same chosen presentation used to
construct `T`.
"""
function trivialized_section_basis(B::SheafSectionBasis{U},
                                   T::EmbeddedModuleTrivialization{U};
                                   check::Bool=true) where {U <: MPolyDecRingElem}
  check && _check_section_trivialization(B, T)
  augmentation = _section_presentation_augmentation(B)
  numerators = U[trivialization_numerator(T, augmentation(v); check=false)
                 for v in section_numerators(B)]
  denominator = trivialization_denominator(T) * section_denominator(B)
  check && _check_scalar_section_numerators(T.ambient, numerators)
  return TrivializedSheafSectionBasis{U}(B, T, numerators, denominator,
                                         twist(B))
end

@doc raw"""
    trivialized_section_basis(A::EmbeddedDivisorAmbient, B::SheafSectionBasis;
                              trivialization=nothing, images=nothing,
                              check=true, kwargs...)

Choose a rank-one trivialization over `A`, then scalarize the finite-tail section basis
`B`.  Pass `trivialization` to use an already constructed trivialization, or
pass `images` and optional trivialization keywords to specify the images of the
module generators.
"""
function trivialized_section_basis(A::EmbeddedDivisorAmbient,
                                   B::SheafSectionBasis;
                                   trivialization=nothing, images=nothing,
                                   cleanup::Symbol=:none,
                                   check::Bool=true, kwargs...)
  if trivialization !== nothing
    images === nothing || error("pass either trivialization or images, not both")
    cleanup == :none ||
      error("cleanup cannot be used with an existing trivialization")
    isempty(kwargs) ||
      error("trivialization keywords cannot be used with an existing trivialization")
    T = trivialization
    _check_same_ambient(A, T.ambient)
  elseif images === nothing
    T = rank_one_module_trivialization(A, underlying_module(B);
                                       cleanup=cleanup, kwargs...)
  else
    T = rank_one_module_trivialization(A, underlying_module(B), images;
                                       cleanup=cleanup, kwargs...)
  end
  return trivialized_section_basis(B, T; check=check)
end

@doc raw"""
    trivialized_section_basis(A::EmbeddedDivisorAmbient, M::OFPModule, d::Int=0;
                              tail_degree=nothing, bgg_denominator=nothing,
                              verify=false, trivialization=nothing,
                              images=nothing, check=true, kwargs...)

Compute ``H^0(\mathbb P^n, \widetilde M(d))`` from the regular multiplication
tail and return scalar rational representatives using a rank-one
trivialization on `A`.

`bgg_denominator` is the compatibility keyword for the homogeneous element at
which the finite ideal-transform maps are evaluated.
Remaining keyword arguments are passed to [`rank_one_module_trivialization`](@ref).
The coordinate ideal of `A` must annihilate `M`.  For a genuine line bundle,
`projective_coordinates` of the result are the coordinates of its
complete-linear-system rational map.
"""
function trivialized_section_basis(A::EmbeddedDivisorAmbient,
                                   M::OFPModule{U}, d::Int=0;
                                   tail_degree::Union{Nothing, Int}=nothing,
                                   bgg_denominator::Union{Nothing, U}=nothing,
                                   verify::Bool=false,
                                   trivialization=nothing, images=nothing,
                                   cleanup::Symbol=:none,
                                   check::Bool=true,
                                   kwargs...) where {U <: MPolyDecRingElem}
  B = sheaf_section_basis(M, d; tail_degree=tail_degree,
                          denominator=bgg_denominator, verify=verify)
  return trivialized_section_basis(A, B; trivialization=trivialization,
                                   images=images, cleanup=cleanup,
                                   check=check, kwargs...)
end

function _check_homogeneous_divisor_data(D::EmbeddedDivisor)
  A = ambient(D)
  A.projective || error("finite-tail section bases require a projective divisor")
  for h in gens(coordinate_ideal(A))
    (is_zero(h) || is_homogeneous(h)) ||
      error("the embedded coordinate ideal must be homogeneous")
  end
  for I in (positive_ideal(D), negative_ideal(D))
    for h in gens(I)
      (is_zero(h) || is_homogeneous(h)) ||
        error("the positive and negative divisor ideals must be homogeneous")
    end
  end
  return nothing
end

function _fractional_ideal_module(A::EmbeddedDivisorAmbient, N::MPolyIdeal,
                                  denominator_degree::Int)
  F = graded_free_module(A.R, [-denominator_degree])
  images = elem_type(A.R)[]
  for h in gens(N)
    (is_zero(h) || is_homogeneous(h)) ||
      error("the fractional section ideal must be homogeneous")
    _is_zero_on_X(A, h) || push!(images, h)
  end
  isempty(images) && error("the fractional section ideal is zero on the variety")
  module_generators = elem_type(F)[h*F[1] for h in images]
  module_relations = elem_type(F)[q*F[1] for q in gens(_geometric_coordinate_ideal(A))]
  return SubquoModule(F, module_generators, module_relations), images
end

@doc raw"""
    trivialized_section_basis(D::EmbeddedDivisor, d::Int=0;
                              tail_degree=nothing, bgg_denominator=nothing,
                              verify=false, check=true, cleanup=:primary,
                              algorithm=:GTZ, cache=true)

Compute sections of the rank-one sheaf ``\mathcal O_X(D)(d)`` from its regular
multiplication tail and return rational representatives suitable for
constructing a rational map.

First, `global_sections_ideal(D)` writes the sheaf as a homogeneous fractional
ideal ``N/f`` on the embedded projective variety ``X``.  The finite-tail
computation is then applied at twist `d` to the graded module
``((N+I_X)/I_X)e``, where ``\deg(e)=-\deg(f)``.  Thus ``he`` represents the
fractional element ``h/f`` with its correct degree.  If the tail computation
uses the evaluation element ``g``, the result consists of

```math
  \frac{H_i}{fg}.
```

Consequently `projective_coordinates` returns the homogeneous polynomials
``H_i``.  For a Cartier divisor these give the complete-linear-system rational
map.  For a non-Cartier divisor the same construction computes the associated
torsion-free rank-one sheaf; it does not assert local freeness.
"""
function trivialized_section_basis(D::EmbeddedDivisor{U}, d::Int=0;
                                   tail_degree::Union{Nothing, Int}=nothing,
                                   bgg_denominator::Union{Nothing, U}=nothing,
                                   verify::Bool=false, check::Bool=true,
                                   cleanup::Symbol=:primary,
                                   algorithm::Symbol=:GTZ,
                                   cache::Bool=true) where {U <: MPolyDecRingElem}
  check && _check_homogeneous_divisor_data(D)
  A = ambient(D)
  S = global_sections_ideal(D; cleanup=cleanup, algorithm=algorithm,
                            cache=cache)
  N = section_numerator_ideal(S)
  f = section_denominator(S)
  is_homogeneous(f) || error("the fractional-ideal denominator is not homogeneous")
  denominator_degree = degree(Int, f; check=true)
  M, images = _fractional_ideal_module(A, N, denominator_degree)
  B = sheaf_section_basis(M, d;
                          tail_degree=tail_degree,
                          denominator=bgg_denominator, verify=verify)
  T = rank_one_module_trivialization(A, M, images; denominator=f,
                                     cleanup=:none)
  return trivialized_section_basis(B, T; check=check)
end

function projective_coordinates(B::SheafSectionBasis,
                                T::EmbeddedModuleTrivialization;
                                check::Bool=true)
  return projective_coordinates(trivialized_section_basis(B, T; check=check))
end
