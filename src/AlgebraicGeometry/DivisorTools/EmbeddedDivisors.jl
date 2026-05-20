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
        ", number of basis sections = ", length(S.numerators), ")")
end

function Base.show(io::IO, F::EmbeddedFormalDivisor)
  print(io, "EmbeddedFormalDivisor(", length(F.summands), " summands)")
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
  _ideal_equal(A.X, B.X) || error("divisors live on different embedded varieties")
  A.projective == B.projective || error("cannot mix affine and projective divisors")
  if A.projective && B.projective
    if A.irrelevant === nothing || B.irrelevant === nothing
      A.irrelevant === B.irrelevant || error("different irrelevant ideals")
    else
      _ideal_equal(A.irrelevant, B.irrelevant) || error("different irrelevant ideals")
    end
  end
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
  _ideal_equal(modulus(Q), A.X) ||
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

function _first_nonzero_generator(I::MPolyIdeal)
  for f in gens(I)
    is_zero(f) || return f
  end
  error("the ideal has no nonzero generator")
end

function _empty_primary_result_fallback(A::EmbeddedDivisorAmbient, K::MPolyIdeal)
  # Avoid returning an empty intersection.  If K is zero on X, keep X, otherwise
  # no divisor condition remains, hence the unit ideal.
  return _ideal_equal(K, A.X) ? A.X : _unit_ideal(A)
end

####################

function embedded_divisor_ambient(R; projective::Bool=false, irrelevant=nothing)
  X = _zero_ideal(R)
  irr = projective ? (irrelevant === nothing ? _default_irrelevant(R) : irrelevant) : nothing
  if irr !== nothing
    _base_ring_check(R, irr)
  end
  return EmbeddedDivisorAmbient{elem_type(R)}(R, X, projective, irr)
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
  return EmbeddedDivisorAmbient{elem_type(R)}(R, X0, projective, irr)
end

function embedded_divisor_ambient(A::MPolyQuoRing; kwargs...)
  return embedded_divisor_ambient(modulus(A); kwargs...)
end

###########################

function _primary_pairs(K::MPolyIdeal; algorithm::Symbol=:GTZ, cache::Bool=true)
  return primary_decomposition(K; algorithm=algorithm, cache=cache)
end


function _minimal_primes_of_X(A::EmbeddedDivisorAmbient; algorithm::Symbol=:GTZ)
  Ps = minimal_primes(A.X; algorithm=algorithm)
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

  if _ideal_equal(K, A.X)
    allow_zero && return A.X
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
    _ideal_equal(modulus(Rm), A.X) ||
      error("module quotient ring is not the coordinate ring of this embedded ambient")
    return :quotient
  else
    error("expected a module over the ambient polynomial ring or over its coordinate quotient")
  end
end

function _rank_one_coordinate(A::EmbeddedDivisorAmbient, f)
  c = coordinates(f)
  return _as_ambient_poly(A, c[1])
end

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, M::SubquoModule)
  _check_module_base_ring(A, M)
  F = ambient_free_module(M)
  rank(F) == 1 ||
    error("automatic module-to-divisor conversion needs a module embedded in a rank-one free module, pass explicit images/trivialization otherwise")
  any(!is_zero(r) for r in relations(M)) &&
    error("automatic module-to-divisor conversion only handles submodules of a rank-one free module, pass explicit images/trivialization for presented modules with relations")

  V = elem_type(A.R)[]
  for f in ambient_representatives_generators(M)
    h = _rank_one_coordinate(A, f)
    is_zero(h) || push!(V, h)
  end
  return isempty(V) ? _zero_ideal(A.R) : ideal(A.R, V)
end

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, I::MPolyIdeal)
  return _as_ambient_ideal(A, I)
end

function _rank_one_raw_ideal(A::EmbeddedDivisorAmbient, I::MPolyQuoIdeal)
  return _as_ambient_ideal(A, I)
end

function _number_of_module_generators(M)
  try
    return ngens(M)
  catch
    return length(gens(M))
  end
end

function _rank_one_raw_ideal_from_images(A::EmbeddedDivisorAmbient, images)
  V = elem_type(A.R)[]
  for h in images
    hh = _as_ambient_poly(A, h)
    is_zero(hh) || push!(V, hh)
  end
  return isempty(V) ? _zero_ideal(A.R) : ideal(A.R, V)
end

function rank_one_module_ideal(A::EmbeddedDivisorAmbient, M;
                               cleanup::Symbol=:primary,
                               algorithm::Symbol=:GTZ, cache::Bool=true)
  N = _rank_one_raw_ideal(A, M)
  if cleanup == :none
    return _saturate_if_projective(A, N + A.X)
  elseif cleanup == :primary
    return _clean_rank_one_ideal(A, N; algorithm=algorithm, cache=cache)
  else
    error("unknown cleanup mode $cleanup, use :primary or :none")
  end
end

function rank_one_module_ideal(A::EmbeddedDivisorAmbient, M, images;
                               cleanup::Symbol=:primary,
                               algorithm::Symbol=:GTZ, cache::Bool=true)
  # Explicit trivialization: the i-th generator of M is sent to images[i]/f
  # for a common denominator f supplied to the higher-level routines.
  # We intentionally do not attempt to certify the map here, because that is a
  # separate homomorphism/well-definedness problem for arbitrary presentations.
  length(images) == _number_of_module_generators(M) ||
    error("number of images must match the number of module generators")
  N = _rank_one_raw_ideal_from_images(A, images)
  if cleanup == :none
    return _saturate_if_projective(A, N + A.X)
  elseif cleanup == :primary
    return _clean_rank_one_ideal(A, N; algorithm=algorithm, cache=cache)
  else
    error("unknown cleanup mode $cleanup, use :primary or :none")
  end
end

function _zero_degree_like(A::EmbeddedDivisorAmbient, like)
  if like isa Integer
    return 0
  elseif like isa AbstractVector{<:Integer}
    return zeros(Int, length(like))
  else
    return zero(grading_group(A.R))
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
    return degree(f)
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

function _degree_to_like(d, like)
  if like isa Integer
    try
      return Int(d)
    catch
      try
        return Int(d[1])
      catch
        error("could not convert module generator degree $d to an integer, pass numerator_degree explicitly")
      end
    end
  elseif like isa AbstractVector{<:Integer}
    try
      return Vector{Int}(d)
    catch
      try
        return [Int(d[i]) for i in 1:length(like)]
      catch
        error("could not convert module generator degree $d to an integer vector, pass numerator_degree explicitly")
      end
    end
  else
    return d
  end
end

function _rank_one_module_shift(A::EmbeddedDivisorAmbient, M, like)
  try
    F = ambient_free_module(M)
    rank(F) == 1 || return _zero_degree_like(A, like)
    return _degree_to_like(degrees_of_generators(F)[1], like)
  catch err
    msg = sprint(showerror, err)
    if occursin("ambient_free_module", msg) || occursin("degrees_of_generators", msg)
      return _zero_degree_like(A, like)
    end
    error("could not determine the degree shift of the rank-one ambient free module, pass numerator_degree explicitly")
  end
end

function _target_numerator_degree(A::EmbeddedDivisorAmbient, denominator,
                                  sheaf_degree, numerator_degree, M)
  numerator_degree !== nothing && return numerator_degree
  f = _as_ambient_poly(A, denominator)
  fdeg = _degree_like(A, f, sheaf_degree)
  shift = M === nothing ? _zero_degree_like(A, sheaf_degree) : _rank_one_module_shift(A, M, sheaf_degree)
  return _degree_sub(_degree_add(sheaf_degree, fdeg), shift)
end

function _homogeneous_coordinate_basis(A::EmbeddedDivisorAmbient, deg)
  QX, _ = quo(A.R, A.X)
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
  N = _saturate_if_projective(A, I + A.X)

  if _ideal_equal(N, A.X)
    # The zero module on X has no sections in any degree.  Return the kernel
    # of the identity on the ambient degree piece as a zero vector space.
    QX, _ = quo(A.R, A.X)
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

  QX, _ = quo(A.R, A.X)
  QC, _ = quo(A.R, N + A.X)

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
                                       degree=0, numerator_degree=nothing,
                                       denominator=one(A.R),
                                       cleanup::Symbol=:primary,
                                       algorithm::Symbol=:GTZ,
                                       cache::Bool=true)
  # Interpret M as a rank-one graded module embedded in a rank-one free module,
  # or as a homogeneous ideal.  If M is represented as N/f, then a section of
  # sheaf-degree q is represented by a numerator h with
  #   deg(h) = q + deg(f) - deg(e),
  # where deg(e) is the rank-one ambient free generator shift.
  N = rank_one_module_ideal(A, M; cleanup=cleanup, algorithm=algorithm, cache=cache)
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  target_degree = _target_numerator_degree(A, f, degree, numerator_degree, M)
  V, emb, nums = _graded_piece_basis_of_ideal(A, N, target_degree)
  return EmbeddedGradedModuleSections{elem_type(A.R)}(A, M, N, f, degree,
                                                      target_degree, V, emb, nums)
end

function graded_module_global_sections(A::EmbeddedDivisorAmbient, M, images;
                                       degree=0, numerator_degree=nothing,
                                       denominator=one(A.R),
                                       cleanup::Symbol=:primary,
                                       algorithm::Symbol=:GTZ,
                                       cache::Bool=true)
  N = rank_one_module_ideal(A, M, images; cleanup=cleanup, algorithm=algorithm, cache=cache)
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  target_degree = _target_numerator_degree(A, f, degree, numerator_degree, nothing)
  V, emb, nums = _graded_piece_basis_of_ideal(A, N, target_degree)
  return EmbeddedGradedModuleSections{elem_type(A.R)}(A, M, N, f, degree,
                                                      target_degree, V, emb, nums)
end

global_sections_from_graded_module(args...; kwargs...) = graded_module_global_sections(args...; kwargs...)

function divisor_from_fractional_ideal(A::EmbeddedDivisorAmbient, N, denominator=one(A.R);
                                       convention::Symbol=:sections,
                                       cleanup::Symbol=:primary,
                                       algorithm::Symbol=:GTZ,
                                       cache::Bool=true)
  # If J = N/f is interpreted as O_X(D), then v_P(J) = -coeff_P(D),
  # hence D = div(f) - div(N).  If J is interpreted as an ideal sheaf O_X(-D),
  # take the negative convention instead.
  convention in (:sections, :line_bundle, :ideal, :ideal_sheaf) ||
    error("convention must be :sections/:line_bundle or :ideal/:ideal_sheaf")
  Namb = _as_ambient_ideal(A, N)
  f = _as_ambient_poly(A, denominator)
  is_zero(f) && error("zero cannot be used as common denominator")
  Nclean = _clean_rank_one_ideal(A, Namb; algorithm=algorithm, cache=cache)
  D = principal_embedded_divisor(A, f; algorithm=algorithm, cache=cache) -
      effective_embedded_divisor(A, Nclean; cleanup=cleanup, algorithm=algorithm, cache=cache)
  D = normal_form_divisor(D; algorithm=algorithm, cache=cache)
  if convention in (:sections, :line_bundle)
    return D
  else
    return normal_form_divisor(-D; algorithm=algorithm, cache=cache)
  end
end

function divisor_from_graded_module(A::EmbeddedDivisorAmbient, M;
                                    denominator=one(A.R),
                                    convention::Symbol=:sections,
                                    cleanup::Symbol=:primary,
                                    algorithm::Symbol=:GTZ,
                                    cache::Bool=true)
  N = rank_one_module_ideal(A, M; cleanup=cleanup, algorithm=algorithm, cache=cache)
  return divisor_from_fractional_ideal(A, N, denominator;
                                       convention=convention, cleanup=cleanup,
                                       algorithm=algorithm, cache=cache)
end

function divisor_from_graded_module(A::EmbeddedDivisorAmbient, M, images;
                                    denominator=one(A.R),
                                    convention::Symbol=:sections,
                                    cleanup::Symbol=:primary,
                                    algorithm::Symbol=:GTZ,
                                    cache::Bool=true)
  N = rank_one_module_ideal(A, M, images; cleanup=cleanup, algorithm=algorithm, cache=cache)
  return divisor_from_fractional_ideal(A, N, denominator;
                                       convention=convention, cleanup=cleanup,
                                       algorithm=algorithm, cache=cache)
end

function divisor_from_graded_module(S::EmbeddedGradedModuleSections;
                                    convention::Symbol=:sections,
                                    cleanup::Symbol=:primary,
                                    algorithm::Symbol=:GTZ,
                                    cache::Bool=true)
  return divisor_from_fractional_ideal(S.ambient, S.numerator, S.denominator;
                                       convention=convention, cleanup=cleanup,
                                       algorithm=algorithm, cache=cache)
end

embedded_divisor_from_graded_module(args...; kwargs...) = divisor_from_graded_module(args...; kwargs...)
divisor_from_rank_one_module(args...; kwargs...) = divisor_from_graded_module(args...; kwargs...)

########################################

function global_sections_ideal(D::EmbeddedDivisor; algorithm::Symbol=:GTZ,
                               cache::Bool=true, cleanup::Symbol=:primary)
  # Return the fractional ideal Γ(X, O_X(D)) as numerator/f:
  #   { h/f | h ∈ numerator }
  # for a nonzero f ∈ D.num.  This mirrors divisors.lib's computation
  # sat((f*D.den) : D.num)/f, but uses primary-decomposition cleanup as well.
  A = D.ambient
  f = _first_nonzero_generator(D.num)
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
