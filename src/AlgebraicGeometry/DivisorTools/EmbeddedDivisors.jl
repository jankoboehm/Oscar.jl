# Embedded Weil/Q-divisor style arithmetic for affine and projective varieties.

###############

ambient(D::EmbeddedDivisor) = D.ambient
ambient(F::EmbeddedFormalDivisor) = F.ambient
positive_ideal(D::EmbeddedDivisor) = D.num
negative_ideal(D::EmbeddedDivisor) = D.den
coordinate_ideal(A::EmbeddedDivisorAmbient) = A.X
is_projective(A::EmbeddedDivisorAmbient) = A.projective
section_numerator_ideal(S::EmbeddedDivisorSections) = S.numerator
section_denominator(S::EmbeddedDivisorSections) = S.denominator
section_numerator_ideal(S::EmbeddedGradedModuleSections) = S.numerator
section_denominator(S::EmbeddedGradedModuleSections) = S.denominator
section_basis_numerators(S::EmbeddedGradedModuleSections) = S.numerators
section_basis_rational(S::EmbeddedGradedModuleSections) = [(h, S.denominator) for h in S.numerators]
section_degree(S::EmbeddedGradedModuleSections) = S.sheaf_degree
section_numerator_degree(S::EmbeddedGradedModuleSections) = S.numerator_degree
section_vector_space(S::EmbeddedGradedModuleSections) = S.vector_space
section_embedding(S::EmbeddedGradedModuleSections) = S.embedding
section_trivialization_shift(S::EmbeddedGradedModuleSections) = S.trivialization_shift
trivialization_numerator(T::EmbeddedModuleTrivialization) = T.numerator
trivialization_denominator(T::EmbeddedModuleTrivialization) = T.denominator
trivialization_images(T::EmbeddedModuleTrivialization) = T.images
trivialization_shift(T::EmbeddedModuleTrivialization) = T.shift

function Base.show(io::IO, A::EmbeddedDivisorAmbient)
  kind = A.projective ? "projective" : "affine"
  print(io, "EmbeddedDivisorAmbient(", kind, ", coordinate ideal = ", A.X, ")")
end

function Base.show(io::IO, D::EmbeddedDivisor)
  print(io, "EmbeddedDivisor(num = ", D.num, ", den = ", D.den, ")")
end

function Base.show(io::IO, S::EmbeddedDivisorSections)
  print(io, "EmbeddedDivisorSections(numerator = ", S.numerator,
        ", denominator = ", S.denominator, ")")
end

function Base.show(io::IO, S::EmbeddedGradedModuleSections)
  print(io, "EmbeddedGradedModuleSections(degree = ", S.sheaf_degree,
        ", numerator degree = ", S.numerator_degree,
        ", shift = ", S.trivialization_shift,
        ", number of basis sections = ", length(S.numerators), ")")
end

function Base.show(io::IO, F::EmbeddedFormalDivisor)
  print(io, "EmbeddedFormalDivisor(", length(F.summands), " summands)")
end

function Base.show(io::IO, T::EmbeddedModuleTrivialization)
  print(io, "EmbeddedModuleTrivialization(method = ", T.method,
        ", numerator = ", T.numerator,
        ", denominator = ", T.denominator,
        ", shift = ", T.shift, ")")
end

_base_ring_check(R, I::MPolyIdeal) = base_ring(I) === R || error("ideal is not in the ambient polynomial ring")

function _zero_ideal(R)
  return ideal(R, elem_type(R)[])
end

function _unit_ideal(R)
  return ideal(R, [one(R)])
end

_unit_ideal(A::EmbeddedDivisorAmbient) = _unit_ideal(A.R)

_is_one_elem(f) = f == one(parent(f))

function _ideal_equal(I::MPolyIdeal, J::MPolyIdeal)
  return is_subset(I, J) && is_subset(J, I)
end

function _check_same_ambient(A::EmbeddedDivisorAmbient, B::EmbeddedDivisorAmbient)
  A.R === B.R || error("divisors have different ambient polynomial rings")
  A.projective == B.projective || error("cannot mix affine and projective divisors")
  if A.projective && B.projective
    if A.irrelevant === nothing || B.irrelevant === nothing
      A.irrelevant === B.irrelevant || error("different irrelevant ideals")
    else
      _ideal_equal(A.irrelevant, B.irrelevant) || error("different irrelevant ideals")
    end
  end
  _ideal_equal(_geometric_coordinate_ideal(A), _geometric_coordinate_ideal(B)) ||
    error("divisors live on different embedded varieties")
  return nothing
end

_check_same_ambient(D::EmbeddedDivisor, E::EmbeddedDivisor) = _check_same_ambient(D.ambient, E.ambient)

function _irrelevant_ideal(A::EmbeddedDivisorAmbient)
  A.projective || error("ambient is affine, it has no irrelevant ideal")
  A.irrelevant === nothing && error("projective ambient has no irrelevant ideal stored")
  return A.irrelevant
end

function _default_irrelevant(R)
  return ideal(R, collect(gens(R)))
end

function _as_ambient_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal)
  _base_ring_check(A.R, I)
  return I
end

function _as_ambient_ideal(A::EmbeddedDivisorAmbient, I::MPolyQuoIdeal)
  Q = base_ring(I)
  base_ring(Q) === A.R || error("quotient ideal is not over the ambient polynomial ring")
  _ideal_equal(_saturate_if_projective(A, modulus(Q)),
               _geometric_coordinate_ideal(A)) ||
    error("quotient ideal is not in the coordinate ring of the embedded ambient")
  V = elem_type(A.R)[]
  for f in gens(I)
    push!(V, _as_ambient_poly(A, f))
  end
  return ideal(A.R, V)
end

function _relative_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal)
  _base_ring_check(A.R, I)
  return I + A.X
end

function _saturate_if_projective(A::EmbeddedDivisorAmbient, I::MPolyIdeal)
  A.projective || return I
  return saturation(I, _irrelevant_ideal(A))
end

function _geometric_coordinate_ideal(A::EmbeddedDivisorAmbient)
  X = A.geometric_coordinate_ideal_cache[]
  X === nothing || return X
  X = _saturate_if_projective(A, A.X)
  A.geometric_coordinate_ideal_cache[] = X
  return X
end

function _as_ambient_poly(A::EmbeddedDivisorAmbient, f)
  if f isa elem_type(A.R)
    parent(f) === A.R || error("polynomial is not in the ambient polynomial ring")
    return f
  elseif f isa MPolyQuoRingElem
    base_ring(parent(f)) === A.R && return lift(f)
    error("quotient element is not over the ambient polynomial ring")
  else
    error("expected an ambient polynomial or a quotient-ring element")
  end
end

function _principal_ideal(A::EmbeddedDivisorAmbient, f)
  return ideal(A.R, [_as_ambient_poly(A, f)])
end

function _is_regular_on_X(A::EmbeddedDivisorAmbient, f)
  ff = _as_ambient_poly(A, f)
  _is_zero_on_X(A, ff) && return false
  X = _geometric_coordinate_ideal(A)
  (_is_one_elem(ff) || is_zero(X)) && return true
  annihilator = quotient(X, ideal(A.R, [ff])) + X
  annihilator = _saturate_if_projective(A, annihilator)
  return _ideal_equal(annihilator, X)
end

function _push_ideal_element_candidate!(candidates::Vector{T}, f::T) where {T}
  is_zero(f) && return candidates
  f in candidates || push!(candidates, f)
  return candidates
end

function _regular_ideal_element(A::EmbeddedDivisorAmbient, I::MPolyIdeal)
  candidates = elem_type(A.R)[]
  homogeneous_groups = Vector{Vector{elem_type(A.R)}}()
  for f in gens(I)
    is_zero(f) && continue
    if A.projective && !is_homogeneous(f)
      continue
    end
    _push_ideal_element_candidate!(candidates, f)
    A.projective || continue
    i = findfirst(group -> degree(group[1]) == degree(f), homogeneous_groups)
    if i === nothing
      push!(homogeneous_groups, elem_type(A.R)[f])
    else
      push!(homogeneous_groups[i], f)
    end
  end

  # Individual generators are cheapest and preserve the previous choice on
  # integral schemes.  Same-degree linear combinations are needed on reducible
  # schemes, where every listed generator may be a zero divisor although their
  # sum is regular.
  groups = A.projective ? homogeneous_groups : [copy(candidates)]
  for group in groups
    length(group) > 1 || continue
    _push_ideal_element_candidate!(candidates,
                                   sum(group; init=zero(A.R)))
    K = base_ring(A.R)
    for t in 2:9
      lambda = K(t)
      coefficient = one(K)
      f = zero(A.R)
      for h in group
        f += A.R(coefficient)*h
        coefficient *= lambda
      end
      _push_ideal_element_candidate!(candidates, f)
    end
  end

  for f in candidates
    _is_regular_on_X(A, f) && return f
  end
  kind = A.projective ? "homogeneous " : ""
  error("could not find a $(kind)non-zero-divisor in the positive divisor ideal; pass an equivalent divisor representation with a regular numerator element")
end

function _empty_primary_result_fallback(A::EmbeddedDivisorAmbient, K::MPolyIdeal)
  # Avoid returning an empty intersection.  If K is zero on X, keep X, otherwise
  # no divisor condition remains, hence the unit ideal.
  X = _geometric_coordinate_ideal(A)
  return _ideal_equal(K, X) ? X : _unit_ideal(A)
end

####################

function embedded_divisor_ambient(R; projective::Bool=false, irrelevant=nothing)
  X = _zero_ideal(R)
  irr = projective ? (irrelevant === nothing ? _default_irrelevant(R) : irrelevant) : nothing
  if irr !== nothing
    _base_ring_check(R, irr)
  end
  A = EmbeddedDivisorAmbient{elem_type(R)}(R, X, projective, irr)
  A.geometric_coordinate_ideal_cache[] = X
  return A
end

function embedded_divisor_ambient(X::MPolyIdeal; projective::Bool=false,
                                  irrelevant=nothing, saturate::Bool=true)
  R = base_ring(X)
  irr = projective ? (irrelevant === nothing ? _default_irrelevant(R) : irrelevant) : nothing
  if irr !== nothing
    _base_ring_check(R, irr)
  end
  X0 = X
  if projective && saturate
    X0 = saturation(X0, irr)
  end
  A = EmbeddedDivisorAmbient{elem_type(R)}(R, X0, projective, irr)
  (!projective || saturate) && (A.geometric_coordinate_ideal_cache[] = X0)
  return A
end

function embedded_divisor_ambient(A::MPolyQuoRing; kwargs...)
  return embedded_divisor_ambient(modulus(A); kwargs...)
end

###########################

function _primary_pairs(K::MPolyIdeal; algorithm::Symbol=:GTZ, cache::Bool=true)
  return primary_decomposition(K; algorithm=algorithm, cache=cache)
end


function _minimal_primes_of_X(A::EmbeddedDivisorAmbient; algorithm::Symbol=:GTZ)
  Ps = minimal_primes(_geometric_coordinate_ideal(A); algorithm=algorithm)
  if !A.projective
    return Ps
  end
  B = _irrelevant_ideal(A)
  return [P for P in Ps if !is_subset(B, P)]
end

function _prime_lies_over_component(P::MPolyIdeal, Xp::MPolyIdeal)
  return is_subset(Xp, P)
end

function _is_divisor_prime_on_X(A::EmbeddedDivisorAmbient, P::MPolyIdeal;
                                algorithm::Symbol=:GTZ)
  for Xp in _minimal_primes_of_X(A; algorithm=algorithm)
    if _prime_lies_over_component(P, Xp) && dim(P) == dim(Xp) - 1
      return true
    end
  end
  return false
end

function _is_rank_one_prime_on_X(A::EmbeddedDivisorAmbient, P::MPolyIdeal;
                                 algorithm::Symbol=:GTZ)
  for Xp in _minimal_primes_of_X(A; algorithm=algorithm)
    if _prime_lies_over_component(P, Xp) && dim(P) >= dim(Xp) - 1
      return true
    end
  end
  return false
end

function _clean_codim_one(A::EmbeddedDivisorAmbient, I::MPolyIdeal;
                          algorithm::Symbol=:GTZ, cache::Bool=true,
                          allow_zero::Bool=false)
  K = _saturate_if_projective(A, _relative_ideal(A, I))
  X = _geometric_coordinate_ideal(A)

  if _ideal_equal(K, X)
    allow_zero && return X
    error("input ideal is zero on the embedded variety, it is not a divisor ideal")
  end

  is_one(K) && return _unit_ideal(A)

  keep = MPolyIdeal{elem_type(A.R)}[]
  B = A.projective ? _irrelevant_ideal(A) : nothing
  for (Q, P) in _primary_pairs(K; algorithm=algorithm, cache=cache)
    if A.projective && is_subset(B, P)
      # Components contained in the irrelevant locus are not components of Proj.
      continue
    end
    if _is_divisor_prime_on_X(A, P; algorithm=algorithm)
      push!(keep, Q)
    end
  end

  isempty(keep) && return _unit_ideal(A)
  L = length(keep) == 1 ? keep[1] : intersect(keep...)
  L = _saturate_if_projective(A, L + A.X)
  return L
end

function _clean_rank_one_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal;
                               algorithm::Symbol=:GTZ, cache::Bool=true)
  # Cleanup for fractional/rank-one ideals such as global-section numerators.
  # Keep components of codimension 0 or 1 on X, drop codimension >= 2 and
  # irrelevant components.
  K = _saturate_if_projective(A, _relative_ideal(A, I))
  is_one(K) && return _unit_ideal(A)

  B = A.projective ? _irrelevant_ideal(A) : nothing
  keep = MPolyIdeal{elem_type(A.R)}[]
  for (Q, P) in _primary_pairs(K; algorithm=algorithm, cache=cache)
    if A.projective && is_subset(B, P)
      continue
    end
    if _is_rank_one_prime_on_X(A, P; algorithm=algorithm)
      push!(keep, Q)
    end
  end

  isempty(keep) && return _empty_primary_result_fallback(A, K)
  L = length(keep) == 1 ? keep[1] : intersect(keep...)
  L = _saturate_if_projective(A, L + A.X)
  return L
end

function _clean_divisor_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal;
                              cleanup::Symbol=:primary,
                              algorithm::Symbol=:GTZ, cache::Bool=true,
                              allow_zero::Bool=false)
  cleanup == :none && return _saturate_if_projective(A, _relative_ideal(A, I))
  cleanup == :primary || error("unknown cleanup mode $cleanup, use :primary or :none")
  return _clean_codim_one(A, I; algorithm=algorithm, cache=cache, allow_zero=allow_zero)
end

#####################################

function embedded_divisor(A::EmbeddedDivisorAmbient, I, J;
                          cleanup::Symbol=:primary,
                          algorithm::Symbol=:GTZ, cache::Bool=true)
  Iamb = _as_ambient_ideal(A, I)
  Jamb = _as_ambient_ideal(A, J)
  I0 = _clean_divisor_ideal(A, Iamb; cleanup=cleanup, algorithm=algorithm, cache=cache)
  J0 = _clean_divisor_ideal(A, Jamb; cleanup=cleanup, algorithm=algorithm, cache=cache)
  return EmbeddedDivisor{elem_type(A.R)}(A, I0, J0)
end

function effective_embedded_divisor(A::EmbeddedDivisorAmbient, I; kwargs...)
  return embedded_divisor(A, I, _unit_ideal(A); kwargs...)
end

function principal_embedded_divisor(A::EmbeddedDivisorAmbient, f, g=one(A.R); kwargs...)
  ff = _as_ambient_poly(A, f)
  gg = _as_ambient_poly(A, g)
  is_zero(ff) && error("zero cannot define a principal divisor")
  is_zero(gg) && error("zero cannot be the denominator of a principal divisor")
  return embedded_divisor(A, ideal(A.R, [ff]), ideal(A.R, [gg]); kwargs...)
end

function Base.zero(A::EmbeddedDivisorAmbient)
  return embedded_divisor(A, _unit_ideal(A), _unit_ideal(A); cleanup=:none)
end

function Base.:+(D::EmbeddedDivisor, E::EmbeddedDivisor)
  _check_same_ambient(D, E)
  A = D.ambient
  return embedded_divisor(A, D.num * E.num + A.X, D.den * E.den + A.X)
end

function Base.:-(D::EmbeddedDivisor)
  return EmbeddedDivisor{elem_type(D.ambient.R)}(D.ambient, D.den, D.num)
end

function Base.:-(D::EmbeddedDivisor, E::EmbeddedDivisor)
  return D + (-E)
end

function Base.:*(n::Integer, D::EmbeddedDivisor)
  n == 0 && return zero(D.ambient)
  n < 0 && return (-n) * (-D)
  ans = zero(D.ambient)
  base = D
  m = n
  while m > 0
    if isodd(m)
      ans = ans + base
    end
    m = div(m, 2)
    m > 0 && (base = base + base)
  end
  return ans
end

Base.:*(D::EmbeddedDivisor, n::Integer) = n * D

###################################

function normal_form_divisor(D::EmbeddedDivisor; algorithm::Symbol=:GTZ, cache::Bool=true)
  A = D.ambient
  N = quotient(D.num, D.den) + A.X
  M = quotient(D.den, D.num) + A.X
  return embedded_divisor(A, N, M; algorithm=algorithm, cache=cache)
end

function is_equal_divisor(D::EmbeddedDivisor, E::EmbeddedDivisor;
                          algorithm::Symbol=:GTZ, cache::Bool=true)
  _check_same_ambient(D, E)
  ND = normal_form_divisor(D; algorithm=algorithm, cache=cache)
  NE = normal_form_divisor(E; algorithm=algorithm, cache=cache)
  return _ideal_equal(ND.num, NE.num) && _ideal_equal(ND.den, NE.den)
end

function Base.:(==)(D::EmbeddedDivisor, E::EmbeddedDivisor)
  return is_equal_divisor(D, E)
end

function support_primary_ideals(D::EmbeddedDivisor; algorithm::Symbol=:GTZ,
                                cache::Bool=true, sign::Symbol=:both)
  sign in (:positive, :negative, :both) || error("sign must be :positive, :negative, or :both")
  A = D.ambient
  B = A.projective ? _irrelevant_ideal(A) : nothing
  out = Tuple{Int, MPolyIdeal{elem_type(A.R)}}[]

  function collect_from(I, sgn)
    is_one(I) && return nothing
    for (Q, P) in _primary_pairs(I + A.X; algorithm=algorithm, cache=cache)
      if A.projective && is_subset(B, P)
        continue
      end
      _is_divisor_prime_on_X(A, P; algorithm=algorithm) && push!(out, (sgn, Q))
    end
    return nothing
  end

  (sign == :positive || sign == :both) && collect_from(D.num, 1)
  (sign == :negative || sign == :both) && collect_from(D.den, -1)
  return out
end

function support_prime_ideals(D::EmbeddedDivisor; algorithm::Symbol=:GTZ,
                              cache::Bool=true, sign::Symbol=:both)
  sign in (:positive, :negative, :both) || error("sign must be :positive, :negative, or :both")
  A = D.ambient
  B = A.projective ? _irrelevant_ideal(A) : nothing
  out = Tuple{Int, MPolyIdeal{elem_type(A.R)}}[]

  function collect_from(I, sgn)
    is_one(I) && return nothing
    for (Q, P) in _primary_pairs(I + A.X; algorithm=algorithm, cache=cache)
      if A.projective && is_subset(B, P)
        continue
      end
      _is_divisor_prime_on_X(A, P; algorithm=algorithm) && push!(out, (sgn, P))
    end
    return nothing
  end

  (sign == :positive || sign == :both) && collect_from(D.num, 1)
  (sign == :negative || sign == :both) && collect_from(D.den, -1)
  return out
end

function degree_divisor(D::EmbeddedDivisor)
  return degree(D.num) - degree(D.den)
end

function degree_formal_divisor(F::EmbeddedFormalDivisor)
  return sum(n * degree_divisor(D) for (n, D) in F.summands; init=0)
end


function is_effective_divisor(D::EmbeddedDivisor; algorithm::Symbol=:GTZ, cache::Bool=true)
  N = normal_form_divisor(D; algorithm=algorithm, cache=cache)
  return is_one(N.den)
end

function linearly_equivalent(D::EmbeddedDivisor, E::EmbeddedDivisor, f, g=one(D.ambient.R);
                             algorithm::Symbol=:GTZ, cache::Bool=true)
  # Certificate check: D and E are linearly equivalent if D - E is the
  # principal divisor of the rational function f/g.
  _check_same_ambient(D, E)
  A = D.ambient
  P = principal_embedded_divisor(A, f, g; algorithm=algorithm, cache=cache)
  return is_equal_divisor(D - E, P; algorithm=algorithm, cache=cache)
end

#############################

function _check_module_base_ring(A::EmbeddedDivisorAmbient, M)
  Rm = base_ring(M)
  if Rm === A.R
    return :ambient
  elseif Rm isa MPolyQuoRing
    base_ring(Rm) === A.R ||
      error("module is over a quotient ring whose base ring is not the divisor ambient ring")
    _ideal_equal(_saturate_if_projective(A, modulus(Rm)),
                 _geometric_coordinate_ideal(A)) ||
      error("module quotient ring is not the coordinate ring of this embedded ambient")
    return :quotient
  else
    error("expected a module over the ambient polynomial ring or over its coordinate quotient")
  end
end

function _number_of_module_generators(M)
  try
    return ngens(M)
  catch
    return length(gens(M))
  end
end

function _module_generator_degrees(M)
  try
    return Any[degrees_of_generators(M)[i] for i in 1:_number_of_module_generators(M)]
  catch
    return Any[nothing for i in 1:_number_of_module_generators(M)]
  end
end

function _ambient_coordinate(A::EmbeddedDivisorAmbient, f, i::Int)
  c = coordinates(f)
  try
    return _as_ambient_poly(A, c[i])
  catch
    return zero(A.R)
  end
end

function _coordinate_row(A::EmbeddedDivisorAmbient, f, n::Int)
  return elem_type(A.R)[_ambient_coordinate(A, f, i) for i in 1:n]
end

function _is_zero_on_X(A::EmbeddedDivisorAmbient, f)
  ff = _as_ambient_poly(A, f)
  is_zero(ff) && return true
  return is_subset(ideal(A.R, [ff]), _geometric_coordinate_ideal(A))
end

function _nonzero_images_on_X(A::EmbeddedDivisorAmbient, images)
  return elem_type(A.R)[h for h in images if !_is_zero_on_X(A, h)]
end

function _dot_row(A::EmbeddedDivisorAmbient, a::Vector, b::Vector)
  length(a) == length(b) || error("coordinate rows have different lengths")
  s = zero(A.R)
  for i in 1:length(a)
    s += _as_ambient_poly(A, a[i]) * _as_ambient_poly(A, b[i])
  end
  return s
end

function _identity_rows(A::EmbeddedDivisorAmbient, n::Int)
  return [elem_type(A.R)[i == j ? one(A.R) : zero(A.R) for i in 1:n] for j in 1:n]
end

function _module_rows(A::EmbeddedDivisorAmbient, M::FreeMod)
  _check_module_base_ring(A, M)
  r = rank(M)
  return _identity_rows(A, r), Vector{Vector{elem_type(A.R)}}(), elem_type(A.R)[], r
end

function _module_rows(A::EmbeddedDivisorAmbient, M::SubquoModule)
  _check_module_base_ring(A, M)
  F = ambient_free_module(M)
  r = rank(F)
  gen_rows = [_coordinate_row(A, f, r) for f in ambient_representatives_generators(M)]
  rel_rows = [_coordinate_row(A, f, r) for f in relations(M)]
  return gen_rows, rel_rows, elem_type(A.R)[], r
end

function _combination_indices(n::Int, k::Int)
  k < 0 && return Vector{Int}[]
  k == 0 && return [Int[]]
  k > n && return Vector{Int}[]
  out = Vector{Int}[]
  cur = Int[]
  function rec(start::Int, left::Int)
    if left == 0
      push!(out, copy(cur))
      return nothing
    end
    stop = n - left + 1
    for i in start:stop
      push!(cur, i)
      rec(i + 1, left - 1)
      pop!(cur)
    end
    return nothing
  end
  rec(1, k)
  return out
end

function _minor_det(R, rows::Vector, rr::Vector{Int}, cc::Vector{Int})
  k = length(rr)
  k == 0 && return one(R)
  k == 1 && return rows[rr[1]][cc[1]]
  entries = elem_type(R)[]
  for i in rr
    for j in cc
      push!(entries, rows[i][j])
    end
  end
  return det(matrix(R, k, k, entries))
end

function _generic_row_rank_mod_X(A::EmbeddedDivisorAmbient, rows::Vector, ncols::Int;
                                 max_minors::Int=20000)
  isempty(rows) && return 0
  maxk = min(length(rows), ncols)
  checked = 0
  for k in maxk:-1:1
    row_combs = _combination_indices(length(rows), k)
    col_combs = _combination_indices(ncols, k)
    for rr in row_combs
      for cc in col_combs
        checked += 1
        checked > max_minors && return nothing
        h = _minor_det(A.R, rows, rr, cc)
        !_is_zero_on_X(A, h) && return k
      end
    end
  end
  return 0
end

function _verify_generic_rank_one(A::EmbeddedDivisorAmbient, gen_rows, rel_rows, ncols;
                                  max_minors::Int=20000, strict::Bool=false)
  rrel = _generic_row_rank_mod_X(A, rel_rows, ncols; max_minors=max_minors)
  rall = _generic_row_rank_mod_X(A, vcat(rel_rows, gen_rows), ncols; max_minors=max_minors)
  if rrel === nothing || rall === nothing
    strict && error("generic rank-one check exceeded max_minors=$max_minors, pass strict_rank_check=false or increase max_minors")
    return nothing
  end
  rall - rrel == 1 ||
    error("module is not generically rank one on the chosen embedded ambient, generic rank appears to be $(rall-rrel)")
  return nothing
end

function _kernel_vectors_annihilating_relations(A::EmbeddedDivisorAmbient,
                                                rel_rows::Vector, ncols::Int)
  isempty(rel_rows) && return _identity_rows(A, ncols)

  QX, _ = quo(A.R, _geometric_coordinate_ideal(A))
  E = free_module(QX, ncols)
  G = free_module(QX, length(rel_rows))

  imgs = typeof(zero(G))[]
  for i in 1:ncols
    v = zero(G)
    for j in 1:length(rel_rows)
      c = QX(rel_rows[j][i])
      is_zero(c) || (v += c * G[j])
    end
    push!(imgs, v)
  end

  phi = hom(E, G, imgs)
  K, inc = kernel(phi)
  out = Vector{Vector{elem_type(A.R)}}()
  for k in gens(K)
    w = inc(k)
    push!(out, elem_type(A.R)[_ambient_coordinate(A, w, i) for i in 1:ncols])
  end
  return out
end

function _images_from_lambda(A::EmbeddedDivisorAmbient, gen_rows, lambda)
  return elem_type(A.R)[_dot_row(A, row, lambda) for row in gen_rows]
end

function _select_trivializing_images(A::EmbeddedDivisorAmbient, gen_rows, rel_rows,
                                     ncols::Int)
  lambdas = _kernel_vectors_annihilating_relations(A, rel_rows, ncols)
  isempty(lambdas) && error("could not find a rational functional annihilating the module relations")

  for lambda in lambdas
    imgs = _images_from_lambda(A, gen_rows, lambda)
    !isempty(_nonzero_images_on_X(A, imgs)) && return imgs
  end

  if length(lambdas) > 1
    lambda = elem_type(A.R)[zero(A.R) for _ in 1:ncols]
    for (j, l) in enumerate(lambdas)
      for i in 1:ncols
        lambda[i] += A.R(j) * l[i]
      end
    end
    imgs = _images_from_lambda(A, gen_rows, lambda)
    !isempty(_nonzero_images_on_X(A, imgs)) && return imgs
  end

  error("all candidate generic trivializations vanish on the module, check the ambient coordinate ideal or pass explicit images")
end

function _rank_one_raw_ideal_from_images(A::EmbeddedDivisorAmbient, images)
  V = _nonzero_images_on_X(A, images)
  return isempty(V) ? _zero_ideal(A.R) : ideal(A.R, V)
end

function _degree_try(A::EmbeddedDivisorAmbient, f, like)
  ff = _as_ambient_poly(A, f)
  is_zero(ff) && return nothing
  try
    return _degree_like(A, ff, like)
  catch
    return nothing
  end
end

function _grading_group_or_nothing(A::EmbeddedDivisorAmbient)
  try
    return grading_group(A.R)
  catch
    return nothing
  end
end

function _default_degree(A::EmbeddedDivisorAmbient)
  G = _grading_group_or_nothing(A)
  G === nothing && return 0
  return zero(G)
end

function _degree_has_parent(d)
  try
    parent(d)
    return true
  catch
    return false
  end
end

_is_integer_degree_shape(d) = d isa Integer || d isa AbstractVector{<:Integer}

function _degree_is_zero(d)
  d === nothing && return true
  d isa Integer && return iszero(d)
  d isa AbstractVector && return all(iszero, d)
  try
    return is_zero(d)
  catch
  end
  if _degree_has_parent(d)
    try
      return d == zero(parent(d))
    catch
    end
  end
  return false
end

function _check_degree_compatible(a, b; name::String="degree", reference_name::String="reference degree")
  (a === nothing || b === nothing) && return nothing
  if a isa Integer && b isa Integer
    return nothing
  elseif a isa AbstractVector{<:Integer} && b isa AbstractVector{<:Integer}
    length(a) == length(b) || error("$name and $reference_name have different vector lengths")
    return nothing
  elseif _degree_has_parent(a) && _degree_has_parent(b)
    pa = parent(a)
    pb = parent(b)
    (pa === pb || pa == pb) || error("$name lies in grading group $pa, but $reference_name lies in $pb")
    return nothing
  end
  error("$name must have the same degree type as $reference_name, got $(typeof(a)) and $(typeof(b))")
end

function _strict_degree_arg(A::EmbeddedDivisorAmbient, d, like;
                            name::String="degree", reference_name::String="shift")
  d === nothing && return _zero_degree_like(A, like)
  like === nothing && return d

  if _degree_has_parent(like)
    _is_integer_degree_shape(d) &&
      error("$name must be an element of the grading group, not an integer/vector surrogate, use zero(grading_group(R)) or a multiple of a generator of grading_group(R)")
    _check_degree_compatible(d, like; name=name, reference_name=reference_name)
    return d
  elseif like isa Integer
    d isa Integer || error("$name must be an integer to match $reference_name")
    return d
  elseif like isa AbstractVector{<:Integer}
    d isa AbstractVector{<:Integer} || error("$name must be an integer vector to match $reference_name")
    length(d) == length(like) || error("$name and $reference_name have different vector lengths")
    return collect(d)
  end

  _check_degree_compatible(d, like; name=name, reference_name=reference_name)
  return d
end

function _normalize_explicit_shift(A::EmbeddedDivisorAmbient, shift)
  shift === nothing && return nothing
  if _grading_group_or_nothing(A) !== nothing && _is_integer_degree_shape(shift)
    error("shift must be an element of grading_group(R), not an integer/vector surrogate, pass zero(grading_group(R)) for the untwisted case")
  end
  return shift
end

function _zero_degree_like(A::EmbeddedDivisorAmbient, like)
  like === nothing && return _default_degree(A)
  if like isa Integer
    return 0
  elseif like isa AbstractVector{<:Integer}
    return zeros(Int, length(like))
  elseif _degree_has_parent(like)
    return zero(parent(like))
  else
    return _default_degree(A)
  end
end

function _degree_like(A::EmbeddedDivisorAmbient, f, like)
  is_zero(f) && error("zero has no homogeneous degree")
  _is_one_elem(f) && return _zero_degree_like(A, like)
  if like isa Integer
    return degree(Int, f)
  elseif like isa AbstractVector{<:Integer}
    return degree(Vector{Int}, f)
  else
    d = degree(f)
    if like === nothing
      return d
    end
    try
      _check_degree_compatible(d, like; name="polynomial degree", reference_name="reference degree")
      return d
    catch ambient_err
      try
        QX, _ = quo(A.R, _geometric_coordinate_ideal(A))
        dX = degree(QX(f))
        _check_degree_compatible(dX, like; name="quotient polynomial degree", reference_name="reference degree")
        return dX
      catch
        throw(ambient_err)
      end
    end
  end
end

function _degree_add(a, b)
  if a isa AbstractVector && b isa AbstractVector
    length(a) == length(b) || error("degree vectors have different lengths")
    return collect(a .+ b)
  end
  return a + b
end

function _degree_sub(a, b)
  if a isa AbstractVector && b isa AbstractVector
    length(a) == length(b) || error("degree vectors have different lengths")
    return collect(a .- b)
  end
  return a - b
end

function _compute_trivialization_shift(A::EmbeddedDivisorAmbient, M, images, denominator,
                                       explicit_shift)
  explicit_shift !== nothing && return _normalize_explicit_shift(A, explicit_shift)

  degs = _module_generator_degrees(M)
  isempty(degs) && return _default_degree(A)
  f = _as_ambient_poly(A, denominator)
  shifts = Any[]
  for i in 1:min(length(degs), length(images))
    _is_zero_on_X(A, images[i]) && continue
    degs[i] === nothing && continue
    fdeg = _degree_try(A, f, degs[i])
    hdeg = _degree_try(A, images[i], degs[i])
    fdeg === nothing && continue
    hdeg === nothing && continue
    push!(shifts, _degree_add(_degree_sub(degs[i], hdeg), fdeg))
  end

  isempty(shifts) && return nothing
  s = shifts[1]
  for t in shifts[2:end]
    t == s || error("the computed rank-one trivialization is not homogeneous, pass explicit images/denominator/shift")
  end
  return s
end

function _clean_module_numerator(A::EmbeddedDivisorAmbient, N::MPolyIdeal;
                                 cleanup::Symbol=:primary,
                                 algorithm::Symbol=:GTZ, cache::Bool=true)
  if cleanup == :none
    return _saturate_if_projective(A, N + A.X)
  elseif cleanup == :primary
    return _clean_rank_one_ideal(A, N; algorithm=algorithm, cache=cache)
  else
    error("unknown cleanup mode $cleanup, use :primary or :none")
  end
end

function rank_one_module_trivialization(A::EmbeddedDivisorAmbient, I::MPolyIdeal;
                                        denominator=one(A.R), shift=nothing,
                                        cleanup::Symbol=:primary,
                                        algorithm::Symbol=:GTZ, cache::Bool=true,
                                        kwargs...)
  Iamb = _as_ambient_ideal(A, I)
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  N = _clean_module_numerator(A, Iamb; cleanup=cleanup, algorithm=algorithm, cache=cache)
  imgs = elem_type(A.R)[_as_ambient_poly(A, g) for g in gens(Iamb)]
  isempty(imgs) && push!(imgs, zero(A.R))
  sh = shift === nothing ? _default_degree(A) : _normalize_explicit_shift(A, shift)
  return EmbeddedModuleTrivialization{elem_type(A.R)}(A, I, N, f, imgs, sh, :ideal)
end

function rank_one_module_trivialization(A::EmbeddedDivisorAmbient, I::MPolyQuoIdeal;
                                        kwargs...)
  return rank_one_module_trivialization(A, _as_ambient_ideal(A, I); kwargs...)
end

function rank_one_module_trivialization(A::EmbeddedDivisorAmbient, F::FreeMod;
                                        denominator=one(A.R), shift=nothing,
                                        cleanup::Symbol=:primary,
                                        algorithm::Symbol=:GTZ, cache::Bool=true,
                                        verify_rank_one::Bool=true,
                                        kwargs...)
  _check_module_base_ring(A, F)
  rank(F) == 1 || error("free module has rank $(rank(F)), only generically rank-one modules can be turned into divisors")
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  imgs = elem_type(A.R)[one(A.R)]
  N = _clean_module_numerator(A, ideal(A.R, imgs); cleanup=cleanup, algorithm=algorithm, cache=cache)
  sh = _compute_trivialization_shift(A, F, imgs, f, shift)
  return EmbeddedModuleTrivialization{elem_type(A.R)}(A, F, N, f, imgs, sh, :free_rank_one)
end

function rank_one_module_trivialization(A::EmbeddedDivisorAmbient, M::SubquoModule;
                                        denominator=one(A.R), shift=nothing,
                                        cleanup::Symbol=:primary,
                                        algorithm::Symbol=:GTZ, cache::Bool=true,
                                        verify_rank_one::Bool=true,
                                        max_minors::Int=20000,
                                        strict_rank_check::Bool=false,
                                        kwargs...)
  _check_module_base_ring(A, M)
  gen_rows, rel_rows, _, ncols = _module_rows(A, M)
  isempty(gen_rows) && error("zero module cannot be trivialized as a rank-one module")

  verify_rank_one && _verify_generic_rank_one(A, gen_rows, rel_rows, ncols;
                                              max_minors=max_minors,
                                              strict=strict_rank_check)

  imgs = if ncols == 1 && all(_is_zero_on_X(A, r[1]) for r in rel_rows)
    elem_type(A.R)[row[1] for row in gen_rows]
  else
    _select_trivializing_images(A, gen_rows, rel_rows, ncols)
  end

  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  raw = _rank_one_raw_ideal_from_images(A, imgs)
  N = _clean_module_numerator(A, raw; cleanup=cleanup, algorithm=algorithm, cache=cache)
  sh = _compute_trivialization_shift(A, M, imgs, f, shift)
  return EmbeddedModuleTrivialization{elem_type(A.R)}(A, M, N, f, imgs, sh, :generic_rank_one)
end

function rank_one_module_trivialization(A::EmbeddedDivisorAmbient, M, images;
                                        denominator=one(A.R), shift=nothing,
                                        cleanup::Symbol=:primary,
                                        algorithm::Symbol=:GTZ, cache::Bool=true,
                                        kwargs...)
  length(images) == _number_of_module_generators(M) ||
    error("number of images must match the number of module generators")
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  imgs = elem_type(A.R)[_as_ambient_poly(A, h) for h in images]
  raw = _rank_one_raw_ideal_from_images(A, imgs)
  N = _clean_module_numerator(A, raw; cleanup=cleanup, algorithm=algorithm, cache=cache)
  sh = _compute_trivialization_shift(A, M, imgs, f, shift)
  return EmbeddedModuleTrivialization{elem_type(A.R)}(A, M, N, f, imgs, sh, :explicit)
end

module_trivialization(args...; kwargs...) = rank_one_module_trivialization(args...; kwargs...)

default_trivialization(args...; kwargs...) = rank_one_module_trivialization(args...; kwargs...)

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, M::SubquoModule)
  return rank_one_module_trivialization(A, M).numerator
end

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, F::FreeMod)
  return rank_one_module_trivialization(A, F).numerator
end

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal)
  return _as_ambient_ideal(A, I)
end

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, I::MPolyQuoIdeal)
  return _as_ambient_ideal(A, I)
end

function rank_one_module_ideal(A::EmbeddedDivisorAmbient, M;
                               cleanup::Symbol=:primary,
                               algorithm::Symbol=:GTZ, cache::Bool=true,
                               kwargs...)
  T = rank_one_module_trivialization(A, M; cleanup=cleanup, algorithm=algorithm,
                                     cache=cache, kwargs...)
  return T.numerator
end

function rank_one_module_ideal(A::EmbeddedDivisorAmbient, M, images;
                               cleanup::Symbol=:primary,
                               algorithm::Symbol=:GTZ, cache::Bool=true,
                               kwargs...)
  T = rank_one_module_trivialization(A, M, images; cleanup=cleanup,
                                     algorithm=algorithm, cache=cache, kwargs...)
  return T.numerator
end

function _target_numerator_degree(A::EmbeddedDivisorAmbient, denominator,
                                  sheaf_degree, numerator_degree, shift)
  if shift === nothing
    numerator_degree !== nothing ||
      error("could not determine the graded trivialization shift, pass shift=... or numerator_degree=...")
    nd = _strict_degree_arg(A, numerator_degree, nothing; name="numerator_degree")
    q = _strict_degree_arg(A, sheaf_degree, nd; name="degree", reference_name="numerator_degree")
    return q, nd
  end

  q = _strict_degree_arg(A, sheaf_degree, shift; name="degree", reference_name="shift")
  if numerator_degree !== nothing
    nd = _strict_degree_arg(A, numerator_degree, shift; name="numerator_degree", reference_name="shift")
    return q, nd
  end

  f = _as_ambient_poly(A, denominator)
  fdeg = _degree_like(A, f, shift)
  return q, _degree_sub(_degree_add(q, fdeg), shift)
end

function _homogeneous_coordinate_basis(A::EmbeddedDivisorAmbient, deg)
  QX, _ = quo(A.R, _geometric_coordinate_ideal(A))
  L = homogeneous_component(QX, deg)
  V = L[1]
  emb = L[2]
  nums = elem_type(A.R)[]
  for v in gens(V)
    push!(nums, _as_ambient_poly(A, emb(v)))
  end
  return V, emb, nums
end

function _graded_piece_basis_of_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal, deg)
  X = _geometric_coordinate_ideal(A)
  N = _saturate_if_projective(A, I + X)

  if _ideal_equal(N, X)
    # The zero module on X has no sections in any degree.  Return the kernel
    # of the identity on the ambient degree piece as a zero vector space.
    QX, _ = quo(A.R, X)
    L = homogeneous_component(QX, deg)
    VX = L[1]
    embX = L[2]
    idVX = hom(VX, VX, gens(VX))
    K, inc = kernel(idVX)
    return K, (inc, embX), elem_type(A.R)[]
  end

  if is_one(N)
    return _homogeneous_coordinate_basis(A, deg)
  end

  QX, _ = quo(A.R, X)
  QC, _ = quo(A.R, N + X)

  LX = homogeneous_component(QX, deg)
  VX = LX[1]
  embX = LX[2]

  LC = homogeneous_component(QC, deg)
  VC = LC[1]
  embC = LC[2]

  imgs = [preimage(embC, QC(_as_ambient_poly(A, embX(v)))) for v in gens(VX)]

  phi = hom(VX, VC, imgs)
  K, inc = kernel(phi)

  nums = elem_type(A.R)[]
  for k in gens(K)
    push!(nums, _as_ambient_poly(A, embX(inc(k))))
  end
  return K, (inc, embX), nums
end

function graded_module_global_sections(A::EmbeddedDivisorAmbient, M;
                                       degree=nothing, numerator_degree=nothing,
                                       denominator=one(A.R), shift=nothing,
                                       cleanup::Symbol=:primary,
                                       algorithm::Symbol=:GTZ,
                                       cache::Bool=true,
                                       kwargs...)
  T = rank_one_module_trivialization(A, M; denominator=denominator, shift=shift,
                                     cleanup=cleanup, algorithm=algorithm,
                                     cache=cache, kwargs...)
  actual_degree, target_degree = _target_numerator_degree(A, T.denominator, degree,
                                                           numerator_degree, T.shift)
  V, emb, nums = _graded_piece_basis_of_ideal(A, T.numerator, target_degree)
  return EmbeddedGradedModuleSections{elem_type(A.R)}(A, M, T.numerator,
                                                      T.denominator, actual_degree,
                                                      target_degree, T.shift,
                                                      V, emb, nums)
end

function graded_module_global_sections(A::EmbeddedDivisorAmbient, M, images;
                                       degree=nothing, numerator_degree=nothing,
                                       denominator=one(A.R), shift=nothing,
                                       cleanup::Symbol=:primary,
                                       algorithm::Symbol=:GTZ,
                                       cache::Bool=true,
                                       kwargs...)
  T = rank_one_module_trivialization(A, M, images; denominator=denominator,
                                     shift=shift, cleanup=cleanup,
                                     algorithm=algorithm, cache=cache,
                                     kwargs...)
  actual_degree, target_degree = _target_numerator_degree(A, T.denominator, degree,
                                                           numerator_degree, T.shift)
  V, emb, nums = _graded_piece_basis_of_ideal(A, T.numerator, target_degree)
  return EmbeddedGradedModuleSections{elem_type(A.R)}(A, M, T.numerator,
                                                      T.denominator, actual_degree,
                                                      target_degree, T.shift,
                                                      V, emb, nums)
end

global_sections_from_graded_module(args...; kwargs...) = graded_module_global_sections(args...; kwargs...)

function _default_hyperplane_element(A::EmbeddedDivisorAmbient)
  A.projective || error("twist divisors are only available for projective ambients")
  for x in gens(A.R)
    try
      _degree_is_zero(degree(x)) && continue
    catch
      continue
    end
    !_is_zero_on_X(A, x) && return x
  end
  error("could not find a nonzero homogeneous coordinate for the twist divisor, pass hyperplane=... or twist_divisor=...")
end

function _zero_degree_of(like)
  if like isa Integer
    return 0
  elseif like isa AbstractVector{<:Integer}
    return zeros(Int, length(like))
  elseif _degree_has_parent(like)
    return zero(parent(like))
  end
  error("cannot construct zero degree for $(typeof(like))")
end

function _degree_multiple_of_unit(shift, unit; max_twist_multiple::Int=10000)
  _check_degree_compatible(shift, unit; name="shift", reference_name="hyperplane degree")
  _degree_is_zero(shift) && return 0
  _degree_is_zero(unit) && error("the chosen hyperplane has degree zero, pass twist_power=... explicitly")

  z = _zero_degree_of(unit)
  cur = z
  for n in 1:max_twist_multiple
    cur = _degree_add(cur, unit)
    cur == shift && return n
  end
  cur = z
  for n in 1:max_twist_multiple
    cur = _degree_sub(cur, unit)
    cur == shift && return -n
  end
  error("shift is not a small integral multiple of the chosen hyperplane degree, pass twist_power=... or twist_divisor=... explicitly")
end

function twist_hyperplane_divisor(A::EmbeddedDivisorAmbient, shift;
                                  hyperplane=nothing,
                                  hyperplane_degree=nothing,
                                  twist_power=nothing,
                                  max_twist_multiple::Int=10000,
                                  algorithm::Symbol=:GTZ, cache::Bool=true)
  sh = shift === nothing ? _default_degree(A) : _normalize_explicit_shift(A, shift)
  _degree_is_zero(sh) && return zero(A)
  A.projective || error("nonzero graded shifts can only be represented by divisors in projective ambients")

  h = hyperplane === nothing ? _default_hyperplane_element(A) : _as_ambient_poly(A, hyperplane)
  _is_zero_on_X(A, h) && error("chosen hyperplane element is zero on the embedded variety")

  n = if twist_power !== nothing
    twist_power isa Integer || error("twist_power must be an integer")
    Int(twist_power)
  elseif sh isa Integer
    Int(sh)
  else
    unit = hyperplane_degree === nothing ? _degree_like(A, h, sh) :
           _strict_degree_arg(A, hyperplane_degree, sh; name="hyperplane_degree", reference_name="shift")
    _degree_multiple_of_unit(sh, unit; max_twist_multiple=max_twist_multiple)
  end
  iszero(n) && return zero(A)

  H = effective_embedded_divisor(A, ideal(A.R, [h]); algorithm=algorithm, cache=cache)
  return n * H
end

function divisor_from_fractional_ideal(A::EmbeddedDivisorAmbient, N, denominator=one(A.R);
                                       convention::Symbol=:sections,
                                       shift=nothing,
                                       hyperplane=nothing,
                                       hyperplane_degree=nothing,
                                       twist_power=nothing,
                                       twist_divisor=nothing,
                                       max_twist_multiple::Int=10000,
                                       cleanup::Symbol=:primary,
                                       algorithm::Symbol=:GTZ,
                                       cache::Bool=true)
  convention in (:sections, :line_bundle, :ideal, :ideal_sheaf) ||
    error("convention must be :sections/:line_bundle or :ideal/:ideal_sheaf")
  Namb = _as_ambient_ideal(A, N)
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  Nclean = _clean_rank_one_ideal(A, Namb; algorithm=algorithm, cache=cache)
  Dfrac = principal_embedded_divisor(A, f; algorithm=algorithm, cache=cache) -
          effective_embedded_divisor(A, Nclean; cleanup=cleanup, algorithm=algorithm, cache=cache)

  sh = shift === nothing ? _default_degree(A) : _normalize_explicit_shift(A, shift)
  Tw = if twist_divisor !== nothing
    twist_divisor
  elseif !_degree_is_zero(sh)
    twist_hyperplane_divisor(A, sh; hyperplane=hyperplane,
                             hyperplane_degree=hyperplane_degree,
                             twist_power=twist_power,
                             max_twist_multiple=max_twist_multiple,
                             algorithm=algorithm, cache=cache)
  else
    zero(A)
  end
  D = normal_form_divisor(Dfrac - Tw; algorithm=algorithm, cache=cache)

  if convention in (:sections, :line_bundle)
    return D
  else
    return normal_form_divisor(-D; algorithm=algorithm, cache=cache)
  end
end

function divisor_from_graded_module(A::EmbeddedDivisorAmbient, M;
                                    denominator=one(A.R),
                                    shift=nothing,
                                    convention::Symbol=:sections,
                                    hyperplane=nothing,
                                    hyperplane_degree=nothing,
                                    twist_power=nothing,
                                    twist_divisor=nothing,
                                    max_twist_multiple::Int=10000,
                                    cleanup::Symbol=:primary,
                                    algorithm::Symbol=:GTZ,
                                    cache::Bool=true,
                                    kwargs...)
  T = rank_one_module_trivialization(A, M; denominator=denominator,
                                     shift=shift, cleanup=cleanup,
                                     algorithm=algorithm, cache=cache,
                                     kwargs...)
  return divisor_from_fractional_ideal(A, T.numerator, T.denominator;
                                       convention=convention, shift=T.shift,
                                       hyperplane=hyperplane,
                                       hyperplane_degree=hyperplane_degree,
                                       twist_power=twist_power,
                                       twist_divisor=twist_divisor,
                                       max_twist_multiple=max_twist_multiple,
                                       cleanup=cleanup, algorithm=algorithm,
                                       cache=cache)
end

function divisor_from_graded_module(A::EmbeddedDivisorAmbient, M, images;
                                    denominator=one(A.R),
                                    shift=nothing,
                                    convention::Symbol=:sections,
                                    hyperplane=nothing,
                                    hyperplane_degree=nothing,
                                    twist_power=nothing,
                                    twist_divisor=nothing,
                                    max_twist_multiple::Int=10000,
                                    cleanup::Symbol=:primary,
                                    algorithm::Symbol=:GTZ,
                                    cache::Bool=true,
                                    kwargs...)
  T = rank_one_module_trivialization(A, M, images; denominator=denominator,
                                     shift=shift, cleanup=cleanup,
                                     algorithm=algorithm, cache=cache,
                                     kwargs...)
  return divisor_from_fractional_ideal(A, T.numerator, T.denominator;
                                       convention=convention, shift=T.shift,
                                       hyperplane=hyperplane,
                                       hyperplane_degree=hyperplane_degree,
                                       twist_power=twist_power,
                                       twist_divisor=twist_divisor,
                                       max_twist_multiple=max_twist_multiple,
                                       cleanup=cleanup, algorithm=algorithm,
                                       cache=cache)
end

function divisor_from_graded_module(S::EmbeddedGradedModuleSections;
                                    convention::Symbol=:sections,
                                    hyperplane=nothing,
                                    hyperplane_degree=nothing,
                                    twist_power=nothing,
                                    twist_divisor=nothing,
                                    max_twist_multiple::Int=10000,
                                    cleanup::Symbol=:primary,
                                    algorithm::Symbol=:GTZ,
                                    cache::Bool=true)
  return divisor_from_fractional_ideal(S.ambient, S.numerator, S.denominator;
                                       convention=convention,
                                       shift=S.trivialization_shift,
                                       hyperplane=hyperplane,
                                       hyperplane_degree=hyperplane_degree,
                                       twist_power=twist_power,
                                       twist_divisor=twist_divisor,
                                       max_twist_multiple=max_twist_multiple,
                                       cleanup=cleanup, algorithm=algorithm,
                                       cache=cache)
end

embedded_divisor_from_graded_module(args...; kwargs...) = divisor_from_graded_module(args...; kwargs...)
divisor_from_rank_one_module(args...; kwargs...) = divisor_from_graded_module(args...; kwargs...)

########################################

function global_sections_ideal(D::EmbeddedDivisor; algorithm::Symbol=:GTZ,
                               cache::Bool=true, cleanup::Symbol=:primary)
  # Return the fractional ideal Γ(X, O_X(D)) as numerator/f:
  #   { h/f | h ∈ numerator }
  # for a non-zero-divisor f ∈ D.num.  This mirrors divisors.lib's computation
  # sat((f*D.den) : D.num)/f, but uses primary-decomposition cleanup as well.
  A = D.ambient
  f = _regular_ideal_element(A, D.num)
  raw = quotient(ideal(A.R, [f]) * D.den + A.X, D.num)
  N = if cleanup == :none
    _saturate_if_projective(A, raw + A.X)
  elseif cleanup == :primary
    _clean_rank_one_ideal(A, raw; algorithm=algorithm, cache=cache)
  else
    error("unknown cleanup mode $cleanup, use :primary or :none")
  end
  return EmbeddedDivisorSections{elem_type(A.R)}(D, N, f)
end

function section_effective_ideal(D::EmbeddedDivisor, h, g;
                                 algorithm::Symbol=:GTZ, cache::Bool=true)
  # For a rational section h/g, compute the effective divisor ideal defining
  # div(h/g) + D.  This is the embedded analogue of Singular's
  # sectionIdeal(h, g, D).
  A = D.ambient
  hh = _as_ambient_poly(A, h)
  gg = _as_ambient_poly(A, g)
  is_zero(hh) && error("zero section has no effective divisor")
  is_zero(gg) && error("zero denominator is invalid")
  first_colon = quotient(ideal(A.R, [hh]) * D.num + A.X, ideal(A.R, [gg]))
  second_colon = quotient(first_colon + A.X, D.den)
  return _clean_codim_one(A, second_colon; algorithm=algorithm, cache=cache)
end

function effective_representative(D::EmbeddedDivisor, h, g;
                                  algorithm::Symbol=:GTZ, cache::Bool=true)
  A = D.ambient
  I = section_effective_ideal(D, h, g; algorithm=algorithm, cache=cache)
  return effective_embedded_divisor(A, I; algorithm=algorithm, cache=cache)
end

function effective_representative(S::EmbeddedDivisorSections, h; kwargs...)
  return effective_representative(S.divisor, h, S.denominator; kwargs...)
end

#####################

function decompose_divisor(D::EmbeddedDivisor; algorithm::Symbol=:GTZ, cache::Bool=true)
  A = D.ambient
  terms = Tuple{Int, EmbeddedDivisor{elem_type(A.R)}}[]
  for (sgn, Q) in support_primary_ideals(D; algorithm=algorithm, cache=cache, sign=:both)
    E = effective_embedded_divisor(A, Q; algorithm=algorithm, cache=cache)
    push!(terms, (sgn, E))
  end
  return EmbeddedFormalDivisor{elem_type(A.R)}(A, terms)
end

function make_formal_divisor(terms::Vector{Tuple{Int, EmbeddedDivisor{T}}}) where {T}
  isempty(terms) && error("cannot infer ambient from an empty list of summands")
  A = terms[1][2].ambient
  for (_, D) in terms
    _check_same_ambient(A, D.ambient)
  end
  return EmbeddedFormalDivisor{T}(A, terms)
end

function evaluate_formal_divisor(F::EmbeddedFormalDivisor)
  ans = zero(F.ambient)
  for (n, D) in F.summands
    ans = ans + n * D
  end
  return ans
end

function Base.:+(F::EmbeddedFormalDivisor, G::EmbeddedFormalDivisor)
  _check_same_ambient(F.ambient, G.ambient)
  return EmbeddedFormalDivisor(F.ambient, vcat(F.summands, G.summands))
end

function Base.:-(F::EmbeddedFormalDivisor)
  return EmbeddedFormalDivisor(F.ambient, [(-n, D) for (n, D) in F.summands])
end

Base.:-(F::EmbeddedFormalDivisor, G::EmbeddedFormalDivisor) = F + (-G)
Base.:*(n::Integer, F::EmbeddedFormalDivisor) = EmbeddedFormalDivisor(F.ambient, [(n*m, D) for (m, D) in F.summands])
Base.:*(F::EmbeddedFormalDivisor, n::Integer) = n * F
