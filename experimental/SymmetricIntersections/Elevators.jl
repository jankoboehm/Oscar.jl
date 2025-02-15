import Base: length, IteratorSize, eltype

export associated_bounds
export associated_function
export degree_of_elevations
export elevator
export number_of_elevations
export underlying_iterator
export underlying_list

###############################################################################
#
# Accessors
#
###############################################################################

# we need to select `d` indices among 1,...,length(lbs) and the number of
# times each index i can be chosen should be between lbs[i] and ubs[i]
function _iterate_size(lbs::Vector{Int}, ubs::Vector{Int}, d::Int)
  is_empty(lbs) && return 0
  if d == 0
    return any(bb -> bb > 0, lbs) ? 0 : 1
  end

  @assert length(lbs) == length(ubs)

  if length(lbs) == 1
    return (lbs[1] <= d <= ubs[1]) ? 1 : 0
  end

  absd = d-sum(lbs)
  if absd == 0
    return 1
  elseif absd < 0
    return 0
  else
    ubs = sort([ubs[i]-lbs[i] for i in 1:length(lbs)])
    return _iterate_size_no_lbs(ubs, absd)
  end
end

# same as before where we have removed the lower bounds condition
function _iterate_size_no_lbs(ubs::Vector{Int}, d::Int)
  if length(ubs) == 1
    return d <= ubs[1] ? 1 : 0
  end

  if all(k -> k >= d, ubs)
    return binomial(d+length(ubs)-1, d)
  end

  s = 0
  for i in 0:min(d, ubs[1])
    s += _iterate_size_no_lbs(ubs[2:end], d-i)
  end

  return s
end

# given an elevator context EC for a list L, with attached function f and with
# attributed degree d (degree of the elevations), this function returns the
# number of d-elevations of (L, f) as well as the type of sums with respect to
# f(L). The type of a sum is given by a partition of d on the elements of
# f(L). Several distinct indices could correspond to the same integers
# in f(L), and while enumerating EC, we want to know which partition of d on the
# elements of f(L) we have to consider.
@attr Tuple{Int, Vector{Vector{ZZRingElem}}} function _num_sum(EC::ElevCtx{T, U}) where {T, U}
  len = 0
  sumsum = Vector{ZZRingElem}[]
  it = underlying_iterator(EC)
  L = underlying_list(EC)
  f = associated_function(EC)
  lbs, ubs = associated_bounds(EC)
  fL = f.(L)
  fLu = unique(fL)
  __k = size(it)[1]
  for i in 1:__k
    s = it[end-i+1]
    s = [fLu[i] for i in 1:length(s) for j in 1:s[i]]
    if length(s) == 1
      for j in [i for i in 1:length(L) if fL[i] == s[1] && lbs[i] <= 1 <= ubs[i]]
        any(k -> k != j && lbs[k] > 0, 1:length(L)) ? continue : nothing
        len += 1
        push!(sumsum, s)
      end
      continue
    end
    ms = MSet(s)
    val = sort(unique(ms))
    LL = copy(fL)
    _lbs = deepcopy(lbs)
    _ubs = deepcopy(ubs)
    _iter = 0
    while val[1] in LL
      j = indexin([val[1]], LL)[1]
      if !(_lbs[j] <= Hecke.multiplicity(ms, val[1])) || any(i -> lbs[i] > 0, 1:_iter+j-1)
        LL = LL[j+1:end]
        _lbs = _lbs[j+1:end]
        _ubs = _ubs[j+1:end]
        _iter += j
        continue
      end
      aug = 0
      for k in max(1, _lbs[j]):min(Hecke.multiplicity(ms, val[1]), _ubs[j])
        if k == Hecke.multiplicity(ms, val[1])
          _p = any(i -> lbs[i] > 0, [i for i in _iter+j+1:length(lbs) if L[i] == val[1]]) ? Int(0) : Int(1)
        else
          _p = 1
        end
        ms2 = MSet(s[k+1:end])
        val2 = sort(unique(ms2))
        for l in val2
          idx = filter(m -> LL[m] == l, j+1:length(LL))
          _p *= _iterate_size(_lbs[idx], _ubs[idx], Hecke.multiplicity(ms2, l))
        end
        len += _p
        aug += _p
      end
      LL = LL[j+1:end]
      _lbs = _lbs[j+1:end]
      _ubs = _ubs[j+1:end]
      _iter += j
      if aug > 0
        push!(sumsum, s)
      end
    end
  end
  return len, unique(sumsum)
end
     
@doc Markdown.doc"""
    number_of_elevations(EC::ElevCtx) -> Int

Return the number of elevations of the underlying list in `EC`
"""
number_of_elevations(EC::ElevCtx) = _num_sum(EC)[1]

_possible_sums(EC::ElevCtx) = _num_sum(EC)[2]

@doc Markdown.doc"""
    underlying_list(EC::ElevCtx{T, U}) where {T, U} -> Vector{T}

Return the underlying list of `EC`.
"""
underlying_list(EC::ElevCtx) = EC.L

@doc Markdown.doc"""
    degree_of_elevations(EC::ElevCtx) -> Int

Return the degree of the elevations in `EC`.
"""
degree_of_elevations(EC::ElevCtx) = EC.d

@doc Markdown.doc"""
    associated_function(EC::ElevCtx{T, U}) where {T, U} -> U

Return the $\mathbb Z$-valued function associated to the underlying list
of `EC`.
"""
associated_function(EC::ElevCtx) = EC.f

@doc Markdown.doc"""
    underlying_iterator(EC::ElevCtx) -> SubObjectIterator{PointVector{ZZRingElem}}

Return the underlying iterator of `EC`.
"""
underlying_iterator(EC::ElevCtx) = EC.it

@doc Markdown.doc"""
    associated_bounds(EC::ElevCtx) -> Vector{Tuple{Int, Int}}

Return the bound conditions on the elevations of `EC`.
"""
associated_bounds(EC::ElevCtx) = EC.bounds

##############################################################################
#
#  Constructor
#
##############################################################################

# Here we create an iterator to avoid to keep stored all the elevations.
@doc Markdown.doc"""
    elevator(L::Vector{T}, f::U, d::Int;
             lbs::Vector{Int} = Int[0 for i in 1:length(L)],
             ubs::Vector{Int} = nothing) where {T, U} -> ElevCtx

Given a list `L` and a $\mathbb Z$-valued function `f` on `L` such that
$f(L)$ is a sorted list of integers, return the `d`-elevator associated to
`(L, f)`. We call `d`-elevator of `(L, f)` the list of all sets of indices for `L`
such that the sum of the corresponding elements in `f(L)` is `d`.

If `f` is not provided, `L` must be a list of integers and the function
returns the usual `d`-elevator of `L`.

One can provide lower bounds and upper bounds on the number of times which index
can be repeatedly taken to construct an elevation. By default, there is
no bound.

Note that the `d`-elevations of `(L, f)` are ordered lexicographically.
"""
function elevator(L::Vector{T}, f::U, d::Int; lbs::Vector{Int} = Int[0 for i in 1:length(L)], ubs::Vector{Int} = Int[-1 for i in 1:length(L)]) where {T, U}
  fL = f.(L)
  @req issorted(fL) "L is not sorted with respect to f"
  @req length(lbs) == length(L) "Bounds conditions must have the same length as the entry list"
  @req all(i -> i >= 0, lbs) "Bounds conditions must consist of non negative integers"

  no_ubs = any(i -> i < 0, ubs)

  _fL = unique(fL)
  _lbs = Int[sum([lbs[i] for i in 1:length(lbs) if fL[i] == _fL[j]]) for j in 1:length(_fL)]
  A = matrix(ZZ, 1, length(_fL), _fL)
  B = matrix(ZZ, 1, 1, [d])
  C = identity_matrix(ZZ, length(_fL))
  D = matrix(ZZ, length(_fL), 1, _lbs)

  if !no_ubs
    @req length(ubs) == length(L) "Bounds conditions must have the same length as the entry list"
    @req all(i -> lbs[i] <= ubs[i], 1:length(L)) "Incompatible bounds conditions"
    _ubs = Int[min(div(d, fL[j]), sum([ubs[i] for i in 1:length(ubs) if fL[i] == _fL[j]])) for j in 1:length(_fL)]
    C = vcat(C, -identity_matrix(ZZ, length(_fL)))
    ub = matrix(ZZ, length(_fL), 1, _ubs)
    D = vcat(D, -ub)
  else
    ubs =  [Int(div(d, fL[i])) for i in 1:length(L)]
  end

  it = solve_mixed(SubObjectIterator{PointVector{ZZRingElem}}, A, B, C, D)
  el = ElevCtx(L, d, it, f, (lbs, ubs))
  return el
end

elevator(L::Vector{Int}, d::Int; lbs::Vector{Int} = [0 for i in 1:length(L)], ubs::Vector{Int} = Int[-1 for i in 1:length(L)]) = elevator(L, (x -> ZZ(x)), d, lbs = lbs, ubs = ubs)

###############################################################################
#
#  Accessing the elevations
#
###############################################################################

# for a d-elevator of (L,f), return the first `d`-elevation of (L, f) associated
# to the partition sumtype of d on the elements of f(L). The order considered by
# default is the lexicographic order
function _first(EC::ElevCtx, sumtype::Vector{ZZRingElem})
  @assert sum(sumtype) == degree_of_elevations(EC)
  @assert any(s -> s == sumtype, _possible_sums(EC))
  lbs, ubs  = associated_bounds(EC)
  L = underlying_list(EC)
  f = associated_function(EC)
  fL = f.(L)
  ms = MSet(sumtype)
  val = sort(unique(ms))
  s = Int[]
  for l in val
    j = findfirst(j -> fL[j] == l, 1:length(L))
    idx = filter(m -> fL[m] == l, 1:length(L))
    sl = _first_homog(lbs[idx], ubs[idx], Hecke.multiplicity(ms, l))
    append!(s, [k+j-1 for k in sl])
  end
  return s
end

# given lower bounds and upper bounds conditions on the set of
# indices 1,..., length(lbs), and an integer d, it returns the first
# (in the lexicographic order) length-d vector of indices matching these
# restrictions
function _first_homog(lbs::Vector{Int}, ubs::Vector{Int}, d::Int)
  if any(i -> lbs[i] > ubs[i], 1:length(lbs))
    return Int[]
  end

  s = Int[i for i in 1:length(lbs) for j in 1:lbs[i]]

  if length(s) > d
    return Int[]
  end

  if length(s) == d
    return s
  end

  i = 1
  while length(s) != d
    if count(j -> j == i,s) < ubs[i]
      push!(s, i)
    else
      i += 1
    end
  end
  return sort(s)
end

# we keep track of the first elevation
@attr Vector{Int} _first(EC::ElevCtx) = _first(EC, _possible_sums(EC)[1])

# for a d-elevator of (L,f), return the last d-elevation of (L, f) associated
# to the partition sumtype of d on the elements of f(L). The order considered
# is the lexicographic order.
function _last(EC::ElevCtx, sumtype::Vector{ZZRingElem})
  @assert sum(sumtype) == degree_of_elevations(EC)
  @assert any(s -> s == sumtype, _possible_sums(EC))
  lbs, ubs  = associated_bounds(EC)
  L = underlying_list(EC)
  f = associated_function(EC)
  fL = f.(L)
  ms = MSet(sumtype)
  val = sort(unique(ms))
  s = Int[]
  for l in val
    j = findfirst(j -> fL[j] == l, 1:length(L))
    idx = filter(m -> fL[m] == l, 1:length(L))
    sl = _last_homog(lbs[idx], ubs[idx], Hecke.multiplicity(ms, l))
    append!(s, [k+j-1 for k in sl])
  end
  return s
end

# given lower bounds and upper bounds conditions on the set of
# indices 1,..., length(lbs), and an integer d, it returns the last
# (in the lexicographic order) length-d vector of indices matching these
# restrictions
function _last_homog(lbs::Vector{Int}, ubs::Vector{Int}, d::Int)
  if any(i -> lbs[i] > ubs[i], 1:length(lbs))
    return Int[]
  end

  s = Int[i for i in 1:length(lbs) for j in 1:lbs[i]]

  if length(s) == d
    return s
  end

  if length(s) > d
    return Int[]
  end

  i = length(lbs)
  while length(s) != d
    if count(j -> j == i, s) < ubs[i]
      push!(s, i)
    else
      i -= 1
    end
  end
  return sort(s)
end

# we keep track of the last elevation
@attr Vector{Int} _last(EC::ElevCtx) = _last(EC, _possible_sums(EC)[end])

function _next(EC::ElevCtx, elev::Vector{Int})
  lbs, ubs  = associated_bounds(EC)
  L = underlying_list(EC)
  f = associated_function(EC)
  fL = f.(L)
  sumtype = fL[elev]

  if elev == _last(EC, sumtype)
    sumsum = _possible_sums(EC)
    j = findlast(j -> sumsum[j] == sumtype, 1:length(sumsum))
    return _first(EC, sumsum[j+1])
  end

  ms = MSet(sumtype)
  val = sort(unique(ms))
  s = Int[]
  for i in length(val):-1:1
    l = val[i]
    j = findfirst(j -> fL[j] == l, 1:length(L))
    idx = filter(m -> fL[m] == l, 1:length(L))
    sl, change = _next_homog(lbs[idx], ubs[idx], [k-j+1 for k in elev if fL[k] == l])
    prepend!(s, [k+j-1 for k in sl])
    if !change
      prepend!(s, [k for k in elev if fL[k] < l])
      break
    end    
  end
  return s
end

# given lower bounds and upper bounds conditions on the set of
# indices 1,..., length(lbs), and a length-d vector satisfying these
# restrctions, it returns the next (in the lexicographic order)
# length-d vector of indices matching these restrictions. I elh
# was the last one, that it returns first matching length-d vectors
# as well as "true", meaning that it had cycled back to the first. If
# it has not cycled, then it returns the next vector and "false".
function _next_homog(lbs::Vector{Int}, ubs::Vector{Int}, elh::Vector{Int})
  d = length(elh)

  if elh == _last_homog(lbs, ubs, d)
    return _first_homog(lbs, ubs, d), true
  end

  s = Int[i for i in 1:length(lbs) for j in 1:lbs[i]]
  ubs = [ubs[i]-lbs[i] for i in 1:length(lbs)]
  s2 = deepcopy(s)
  adj = Int[]
  while s2 != elh
    j = findfirst(j -> s2[j] != elh[j], 1:length(s2))
    if j === nothing
      append!(adj, elh[length(s2)+1:end])
      append!(s2, elh[length(s2)+1:end])
    else
      push!(adj, elh[j])
      s2 = append!(s2[1:j-1], [elh[j]], s2[j:end])
    end
  end
  s2 = _next_homog_no_lbs(ubs, adj)
  s = sort(append!(s, s2))
  return s, false
end

# same as before, but we do not have cycles here (since we cover them
# earlier), and we have taken away the lower bounds conditions.
function _next_homog_no_lbs(ubs::Vector{Int}, elhn::Vector{Int})
  if length(elhn) == 1
    j = findfirst(j -> j > elhn[1] && ubs[j] != 0, 1:length(ubs))
    if j === nothing
      return findfirst(k -> ubs[k] > 0, 1:length(ubs))
    else
      return Int[j]
    end
  end

  j = findfirst(j -> j > elhn[end] && ubs[j] != 0, 1:length(ubs))
  if j !== nothing
    elhn[end] = j
    return elhn
  end
  _ubs = deepcopy(ubs)
  _ubs[elhn[end]] -= 1
  s = _next_homog_no_lbs(_ubs, elhn[1:end-1])
  nb = count(j -> j == s[end], s)
  j = findfirst(j -> (j == s[end] && ubs[j] > nb) || (j > s[end] && ubs[j] != 0), 1:length(ubs))
  push!(s, j)
  return s
end
  
Base.lastindex(EC::ElevCtx) = number_of_elevations(EC)

function Base.iterate(EC::ElevCtx)
  return _first(EC), _first(EC)
end

function Base.iterate(EC::ElevCtx, st::Vector{Int})
  st == _last(EC) && return nothing
  st2 = _next(EC, st)
  return st2, st2
end

Base.length(EC::ElevCtx) = number_of_elevations(EC)

Base.IteratorSize(::Type{T}) where T <: ElevCtx = Base.HasLength()

Base.eltype(::Type{T}) where T <: ElevCtx= Vector{Int}


#############################################################################
#
#  I/O printing
#
#############################################################################

function Base.show(io::IO, ::MIME"text/plain", EC::ElevCtx{T, U}) where {T, U}
  d = degree_of_elevations(EC)
  println(io, "$d-elevator of a list with objects of type")
  print(io, T)
end

