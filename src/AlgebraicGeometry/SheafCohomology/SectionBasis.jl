###############################################################################
# SectionBasis.jl
#
# Recover representatives for H^0(P^n, ~M(d)) from the regular BGG tail.
#
# The construction avoids ideal quotients.  It only uses the finite dimensional
# graded pieces M_s and M_{s+1} and the multiplication maps by the variables.
###############################################################################

@doc raw"""
    SheafSectionBasis{T}

Data returned by [`sheaf_section_basis`](@ref).

Let `M` be a finitely generated graded module over a standard ``\mathbb Z``-
graded polynomial ring `R = k[x_0, ..., x_n]`.  If `B` is the result of
`sheaf_section_basis(M, d; tail_degree = s, denominator = g)`, then the entries
of `B.numerators` are homogeneous elements of degree `s` in the zeroth free
module of a presentation of `M`, and `B.denominator` is a homogeneous polynomial
of degree `s-d`.  The represented sections are

```julia
B.numerators[i] // B.denominator
```

where the division is interpreted after sheafification.  If the presentation is
rank one, `projective_coordinates(B)` returns polynomial representatives for the
associated rational map.
"""
struct SheafSectionBasis{T <: MPolyDecRingElem}
  graded_module::OFPModule{T}
  presentation_free_module::FreeMod{T}
  twist::Int
  tail_degree::Int
  denominator::T
  numerators::Vector{FreeModElem{T}}
  degree_a_monomials::Vector{T}
  tail_basis::Vector{FreeModElem{T}}
end

Base.length(B::SheafSectionBasis) = length(B.numerators)
Base.eltype(::Type{SheafSectionBasis{T}}) where {T} = FreeModElem{T}
Base.eltype(::SheafSectionBasis{T}) where {T} = FreeModElem{T}
Base.iterate(B::SheafSectionBasis, state::Int = 1) = state > length(B) ? nothing : (B.numerators[state], state + 1)

@doc raw"""
    section_numerators(B::SheafSectionBasis)

Return the common-denominator numerators of a basis computed by
[`sheaf_section_basis`](@ref).
"""
section_numerators(B::SheafSectionBasis) = B.numerators

@doc raw"""
    section_denominator(B::SheafSectionBasis)

Return the common denominator used by a basis computed by
[`sheaf_section_basis`](@ref).
"""
section_denominator(B::SheafSectionBasis) = B.denominator

tail_degree(B::SheafSectionBasis) = B.tail_degree

twist(B::SheafSectionBasis) = B.twist

@doc raw"""
    projective_coordinates(B::SheafSectionBasis)

Return the polynomial coordinate functions corresponding to `B`, assuming that
`B.presentation_free_module` has rank one.

The returned polynomials are the numerators.  They define the same rational map
as the basis of sections, since all sections have the common denominator
`section_denominator(B)`.
"""
function projective_coordinates(B::SheafSectionBasis{T}) where {T}
  F = B.presentation_free_module
  ngens(F) == 1 || error("projective_coordinates is only available for rank-one presentation modules")
  R = base_ring(F)
  coords = T[]
  for v in B.numerators
    c = coordinates(v)
    push!(coords, c[1])
  end
  return coords
end

###############################################################################
# Internal finite dimensional linear algebra over the coefficient field.
###############################################################################

_zero_vector(K, n::Int) = [zero(K) for _ in 1:n]

function _is_zero_row(v::Vector)
  for a in v
    !iszero(a) && return false
  end
  return true
end

function _rref_rows(rows::Vector{Vector{T}}, K, ncols::Int) where {T}
  A = Vector{Vector{T}}()
  for r in rows
    _is_zero_row(r) || push!(A, copy(r))
  end
  pivots = Int[]
  row = 1
  for col in 1:ncols
    row > length(A) && break
    pivot_row = 0
    for i in row:length(A)
      if !iszero(A[i][col])
        pivot_row = i
        break
      end
    end
    pivot_row == 0 && continue
    if pivot_row != row
      A[row], A[pivot_row] = A[pivot_row], A[row]
    end
    inv_pivot = inv(A[row][col])
    for j in col:ncols
      A[row][j] *= inv_pivot
    end
    for i in 1:length(A)
      if i != row && !iszero(A[i][col])
        λ = A[i][col]
        for j in col:ncols
          A[i][j] -= λ*A[row][j]
        end
      end
    end
    push!(pivots, col)
    row += 1
  end
  return A[1:length(pivots)], pivots
end

function _free_columns(ncols::Int, pivots::Vector{Int})
  is_pivot = falses(ncols)
  for p in pivots
    is_pivot[p] = true
  end
  return [i for i in 1:ncols if !is_pivot[i]]
end

function _reduce_by_rref(v::Vector{T}, rref::Vector{Vector{T}}, pivots::Vector{Int}) where {T}
  w = copy(v)
  for (r, p) in zip(rref, pivots)
    if !iszero(w[p])
      λ = w[p]
      for j in p:length(w)
        w[j] -= λ*r[j]
      end
    end
  end
  return w
end

function _right_kernel_basis(rows::Vector{Vector{T}}, K, ncols::Int) where {T}
  rref, pivots = _rref_rows(rows, K, ncols)
  freecols = _free_columns(ncols, pivots)
  basis = Vector{Vector{T}}()
  for f in freecols
    v = _zero_vector(K, ncols)
    v[f] = one(K)
    for (r, p) in zip(rref, pivots)
      v[p] = -r[f]
    end
    push!(basis, v)
  end
  return basis
end

###############################################################################
# Internal model for a graded piece of a presented module.
###############################################################################

struct _SectionGradedPiece{T <: MPolyDecRingElem, U}
  free_module::FreeMod{T}
  degree::Int
  ambient_basis::Vector{FreeModElem{T}}
  quotient_basis::Vector{FreeModElem{T}}
  ambient_index::Dict{Tuple{Int, Tuple{Vararg{Int}}}, Int}
  rref_relation_rows::Vector{Vector{U}}
  pivot_columns::Vector{Int}
  free_columns::Vector{Int}
end

function _monomial_key(m)
  evs = collect(AbstractAlgebra.exponent_vectors(m))
  length(evs) == 1 || error("expected a monomial")
  return Tuple(Int.(evs[1]))
end

function _monomial_basis_safe(R, d::Int)
  d < 0 && return elem_type(R)[]
  return monomial_basis(R, d)
end

function _presentation_data(M::OFPModule{T}) where {T <: MPolyDecRingElem}
  R = base_ring(M)
  CR = base_ring(R)
  CR isa AbstractAlgebra.Field || error("the coefficient ring must be a field")
  is_standard_graded(ambient_free_module(M)) || error("only standard ZZ-graded modules are supported")
  is_graded(M) || error("the module must be graded")

  p = presentation(M)
  F0 = p[0]
  F1 = p[1]
  d1 = map(p, 1)
  rels = FreeModElem{T}[d1(v) for v in gens(F1)]
  rel_degrees = Int[degree(Int, v; check = false) for v in gens(F1)]
  return R, CR, F0, rels, rel_degrees
end

function _graded_piece_model(F::FreeMod{T}, rels::Vector{FreeModElem{T}}, rel_degrees::Vector{Int}, degree_value::Int, K) where {T <: MPolyDecRingElem}
  R = base_ring(F)
  ambient_basis = FreeModElem{T}[]
  ambient_index = Dict{Tuple{Int, Tuple{Vararg{Int}}}, Int}()

  gen_degrees = Int[degree(Int, F[i]; check = false) for i in 1:ngens(F)]
  for i in 1:ngens(F)
    for m in _monomial_basis_safe(R, degree_value - gen_degrees[i])
      push!(ambient_basis, m*F[i])
      ambient_index[(i, _monomial_key(m))] = length(ambient_basis)
    end
  end

  ncols = length(ambient_basis)
  Kelem = typeof(zero(K))
  relation_rows = Vector{Vector{Kelem}}()
  for (r, δ) in zip(rels, rel_degrees)
    for m in _monomial_basis_safe(R, degree_value - δ)
      row = _ambient_coordinate_vector(m*r, F, ambient_index, K, ncols)
      _is_zero_row(row) || push!(relation_rows, row)
    end
  end

  rref, pivots = _rref_rows(relation_rows, K, ncols)
  freecols = _free_columns(ncols, pivots)
  quotient_basis = FreeModElem{T}[ambient_basis[i] for i in freecols]
  return _SectionGradedPiece{T, Kelem}(F, degree_value, ambient_basis, quotient_basis, ambient_index, rref, pivots, freecols)
end

function _ambient_coordinate_vector(v::FreeModElem{T}, F::FreeMod{T}, ambient_index::Dict{Tuple{Int, Tuple{Vararg{Int}}}, Int}, K, ncols::Int) where {T <: MPolyDecRingElem}
  parent(v) === F || error("element belongs to the wrong free module")
  row = _zero_vector(K, ncols)
  c = coordinates(v)
  for i in 1:ngens(F)
    f = c[i]
    iszero(f) && continue
    coeffs = collect(coefficients(f))
    mons = collect(monomials(f))
    for j in 1:length(mons)
      key = (i, _monomial_key(mons[j]))
      idx = get(ambient_index, key, 0)
      if idx == 0
        error("encountered a term outside the expected homogeneous component")
      end
      row[idx] += K(coeffs[j])
    end
  end
  return row
end

function _quotient_coordinates(v::FreeModElem{T}, P::_SectionGradedPiece{T}, K) where {T <: MPolyDecRingElem}
  ambient = _ambient_coordinate_vector(v, P.free_module, P.ambient_index, K, length(P.ambient_basis))
  reduced = _reduce_by_rref(ambient, P.rref_relation_rows, P.pivot_columns)
  return [reduced[i] for i in P.free_columns]
end

function _coords_to_element(P::_SectionGradedPiece{T}, coords::Vector, K) where {T <: MPolyDecRingElem}
  F = P.free_module
  R = base_ring(F)
  v = zero(F)
  for i in 1:length(coords)
    iszero(coords[i]) && continue
    v += R(coords[i])*P.quotient_basis[i]
  end
  return v
end

function _denominator_coefficients(den, monoms::Vector{T}, K) where {T <: MPolyDecRingElem}
  monom_index = Dict{Tuple{Vararg{Int}}, Int}()
  for i in 1:length(monoms)
    monom_index[_monomial_key(monoms[i])] = i
  end
  coeffs = _zero_vector(K, length(monoms))
  for (c, m) in zip(coefficients(den), monomials(den))
    idx = get(monom_index, _monomial_key(m), 0)
    idx == 0 && error("denominator has terms outside the chosen degree")
    coeffs[idx] += K(c)
  end
  return coeffs
end

function _check_denominator(den::T, a::Int) where {T <: MPolyDecRingElem}
  iszero(den) && error("denominator must be non-zero")
  degree(Int, den) == a || error("denominator must be homogeneous of degree tail_degree - twist")
  return den
end

###############################################################################
# Public construction.
###############################################################################

@doc raw"""
    sheaf_section_basis(M::OFPModule{T}, d::Int = 0;
                        tail_degree::Union{Nothing, Int} = nothing,
                        denominator::Union{Nothing, T} = nothing,
                        verify::Bool = false) where {T <: MPolyDecRingElem}

Return representatives for a basis of ``H^0(\mathbb P^n, \widetilde M(d))``.

The module `M` must be a finitely generated graded module over a standard
``\mathbb Z``-graded polynomial ring over a field, as for
`sheaf_cohomology(M, l, h; algorithm = :bgg)`.  The optional `tail_degree = s`
chooses the regular tail degree.  If it is omitted, the Castelnuovo--Mumford
regularity of `M` is used and the actual tail degree is `max(d, reg(M))`.

The returned object `B` contains:

* `section_numerators(B)`: homogeneous elements of degree `s` in the zeroth free
  module of a presentation of `M`,
* `section_denominator(B)`: a homogeneous polynomial `g` of degree `s-d`, and
* `length(B)`: the computed dimension of the section space.

The represented sections are the fractions `section_numerators(B)[i]/g` after
sheafification.  Since the denominator is common, the numerators themselves are
the projective coordinates of the corresponding rational map.

# Mathematical method

Put `a = s-d`.  A section of ``\widetilde M(d)`` is recovered from its
multiplication table

```math
u \longmapsto u\sigma \in M_s, \qquad u \in R_a.
```

Writing unknowns ``q_u \in M_s`` for the monomials ``u`` of degree `a`, the
compatibility equations are

```math
x_i q_{x_j v} - x_j q_{x_i v} = 0 \quad \text{in } M_{s+1}
```

for all monomials ``v`` of degree `a-1` and all `i < j`.  The function solves
this finite-dimensional kernel problem over the coefficient field.  Finally it
evaluates the multiplication table at the chosen denominator `g`.

# Examples

```jldoctest
julia> R, (x, y, z) = graded_polynomial_ring(QQ, [:x, :y, :z]);

julia> F = graded_free_module(R, 1);

julia> B = sheaf_section_basis(F, 2; tail_degree = 2);

julia> length(B)
6

julia> projective_coordinates(B)
6-element Vector{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}:
 z^2
 y*z
 y^2
 x*z
 x*y
 x^2
```
"""
function sheaf_section_basis(M::OFPModule{T}, d::Int = 0; tail_degree::Union{Nothing, Int} = nothing, denominator::Union{Nothing, T} = nothing, verify::Bool = false) where {T <: MPolyDecRingElem}
  R, K, F0, rels, rel_degrees = _presentation_data(M)

  s = tail_degree === nothing ? max(d, Int(cm_regularity(M; check = false))) : tail_degree
  a = s - d
  a < 0 && error("tail_degree must be at least the requested twist")

  monoms_a = _monomial_basis_safe(R, a)
  isempty(monoms_a) && error("the degree tail_degree - twist component of the base ring is zero")

  den = denominator === nothing ? monoms_a[1] : denominator
  _check_denominator(den, a)
  den_coeffs = _denominator_coefficients(den, monoms_a, K)

  Ms = _graded_piece_model(F0, rels, rel_degrees, s, K)
  dim_s = length(Ms.quotient_basis)

  kernel_basis = Vector{Vector{typeof(zero(K))}}()
  if a == 0
    for i in 1:dim_s
      v = _zero_vector(K, dim_s)
      v[i] = one(K)
      push!(kernel_basis, v)
    end
  else
    Ms1 = _graded_piece_model(F0, rels, rel_degrees, s + 1, K)
    dim_s1 = length(Ms1.quotient_basis)
    variables = gens(R)

    mult = Vector{Vector{Vector{typeof(zero(K))}}}(undef, length(variables))
    for i in 1:length(variables)
      mult[i] = Vector{Vector{typeof(zero(K))}}(undef, dim_s)
      for k in 1:dim_s
        mult[i][k] = _quotient_coordinates(variables[i]*Ms.quotient_basis[k], Ms1, K)
      end
    end

    monom_index = Dict{Tuple{Vararg{Int}}, Int}()
    for i in 1:length(monoms_a)
      monom_index[_monomial_key(monoms_a[i])] = i
    end

    nunknowns = length(monoms_a)*dim_s
    Kelem = typeof(zero(K))
    rows = Vector{Vector{Kelem}}()
    for v in _monomial_basis_safe(R, a - 1)
      for i in 1:length(variables)-1
        for j in i+1:length(variables)
          idx_j = monom_index[_monomial_key(variables[j]*v)]
          idx_i = monom_index[_monomial_key(variables[i]*v)]
          for ℓ in 1:dim_s1
            row = _zero_vector(K, nunknowns)
            for k in 1:dim_s
              row[(idx_j - 1)*dim_s + k] += mult[i][k][ℓ]
              row[(idx_i - 1)*dim_s + k] -= mult[j][k][ℓ]
            end
            _is_zero_row(row) || push!(rows, row)
          end
        end
      end
    end
    kernel_basis = _right_kernel_basis(rows, K, nunknowns)
  end

  numerators = FreeModElem{T}[]
  for z in kernel_basis
    q = _zero_vector(K, dim_s)
    if a == 0
      for k in 1:dim_s
        q[k] += den_coeffs[1]*z[k]
      end
    else
      for u in 1:length(monoms_a)
        c = den_coeffs[u]
        iszero(c) && continue
        for k in 1:dim_s
          q[k] += c*z[(u - 1)*dim_s + k]
        end
      end
    end
    push!(numerators, _coords_to_element(Ms, q, K))
  end

  if verify
    tbl = sheaf_cohomology(M, d - ngens(R), d + ngens(R); algorithm = :bgg)
    h0 = tbl[0, d]
    h0 >= 0 || error("BGG cohomology table did not determine h^0 at the requested twist")
    h0 == length(numerators) || error("dimension mismatch: tail kernel gives $(length(numerators)), BGG gives $h0")
  end

  return SheafSectionBasis{T}(M, F0, d, s, den, numerators, monoms_a, Ms.quotient_basis)
end
