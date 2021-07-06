export saturation, saturation_with_index, quotient, eliminate
export radical, primary_decomposition, minimal_primes, equidimensional_decomposition_weak,
          equidimensional_decomposition_radical, equidimensional_hull,
          equidimensional_hull_radical
export absolute_primary_decomposition
export iszero, isone, issubset, ideal_membership, radical_membership, isprime, isprimary
export ngens, gens

# constructors #######################################################

@doc Markdown.doc"""
    ideal(g::Vector{T}) where {T <: MPolyElem}
    
    ideal(g::Vector{T}) where {T <: MPolyElem_dec}

Create the ideal generated by the polynomials in `g`, assuring, in the decorated case, that the entries of `g` are homogeneous if the base ring is graded.

    ideal(R::MPolyRing, g::Vector)

Create the ideal generated by the polynomials in `g` as above, specifying `R` as the ambient ring of the ideal. 

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal([x*y-3*x,y^3-2*x^2*y])
ideal generated by: x*y - 3*x, -2*x^2*y + y^3

julia> S, (x, y) = GradedPolynomialRing(QQ, ["x", "y"],  [1, 2])
(Multivariate Polynomial Ring in x, y over Rational Field graded by 
  x -> [1]
  y -> [2], MPolyElem_dec{fmpq,fmpq_mpoly}[x, y])

julia> J = ideal(S, [(x^2+y)^2])
ideal generated by: x^4 + 2*x^2*y + y^2
```
"""
function ideal(g::Vector{T}) where {T <: MPolyElem}
  @assert length(g) > 0
  @assert all(x->parent(x) == parent(g[1]), g)
  return MPolyIdeal(g)
end
function ideal(R::MPolyRing, g::Vector)
  f = elem_type(R)[R(f) for f = g]
  return ideal(f)
end

function ideal(Qxy::MPolyRing{T}, x::MPolyElem{T}) where T <: RingElem 
  return ideal(Qxy, [x])
end

# elementary operations #######################################################
@doc Markdown.doc"""
    :^(I::MPolyIdeal, m::Int)

Return the m-th power of `I`. 

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [x, y])
ideal generated by: x, y

julia> I^3
ideal generated by: x^3, x^2*y, x*y^2, y^3
```
"""
function Base.:^(I::MPolyIdeal, m::Int)
  singular_assure(I)
  return MPolyIdeal(base_ring(I), I.gens.S^m)
end

@doc Markdown.doc"""
    :+(I::MPolyIdeal, J::MPolyIdeal)

Return the sum of `I` and `J`. 

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [x, y])
ideal generated by: x, y

julia> J = ideal(R, [z^2])
ideal generated by: z^2

julia> I+J
ideal generated by: x, y, z^2
```
"""
function Base.:+(I::MPolyIdeal, J::MPolyIdeal)
  singular_assure(I)
  singular_assure(J)
  return MPolyIdeal(base_ring(I), I.gens.S + J.gens.S)
end
Base.:-(I::MPolyIdeal, J::MPolyIdeal) = I+J

@doc Markdown.doc"""
    :*(I::MPolyIdeal, J::MPolyIdeal)

Return the product of `I` and `J`. 

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [x, y])
ideal generated by: x, y

julia> J = ideal(R, [z^2])
ideal generated by: z^2

julia> I*J
ideal generated by: x*z^2, y*z^2
```
"""
function Base.:*(I::MPolyIdeal, J::MPolyIdeal)
  singular_assure(I)
  singular_assure(J)
  return MPolyIdeal(base_ring(I), I.gens.S * J.gens.S)
end

#######################################################

# ideal intersection #######################################################
@doc Markdown.doc"""
    intersect(I::MPolyIdeal, Js::MPolyIdeal...)

Return the intersection of two or more ideals.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2
```
"""
function Base.intersect(I::MPolyIdeal, Js::MPolyIdeal...)
  singular_assure(I)
  si = I.gens.S
  for J in Js
    singular_assure(J)
    si = Singular.intersection(si, J.gens.S)
  end
  return MPolyIdeal(base_ring(I), si)
end

#######################################################

@doc Markdown.doc"""
    quotient(I::MPolyIdeal, J::MPolyIdeal)
    
Return the ideal quotient of `I` by `J`. Alternatively, use `I:J`. 

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [x^4+x^2*y*z+y^3*z, y^4+x^3*z+x*y^2*z, x^3*y+x*y^3])
ideal generated by: x^4 + x^2*y*z + y^3*z, x^3*z + x*y^2*z + y^4, x^3*y + x*y^3

julia> J = ideal(R,[x,y,z])^2
ideal generated by: x^2, x*y, x*z, y^2, y*z, z^2

julia> L = quotient(I,J)
ideal generated by: x^3*z + x*y^2*z + y^4, x^3*y + x*y^3, x^4 + x^2*y*z + y^3*z, x^3*z^2 - x^2*y*z^2 + x*y^2*z^2 - y^3*z^2, x^2*y^2*z - x^2*y*z^2 - y^3*z^2, x^3*z^2 + x^2*y^3 - x^2*y^2*z + x*y^2*z^2

julia> I:J
ideal generated by: x^3*z + x*y^2*z + y^4, x^3*y + x*y^3, x^4 + x^2*y*z + y^3*z, x^3*z^2 - x^2*y*z^2 + x*y^2*z^2 - y^3*z^2, x^2*y^2*z - x^2*y*z^2 - y^3*z^2, x^3*z^2 + x^2*y^3 - x^2*y^2*z + x*y^2*z^2
```
"""
function quotient(I::MPolyIdeal, J::MPolyIdeal)
  singular_assure(I)
  singular_assure(J)
  return MPolyIdeal(base_ring(I), Singular.quotient(I.gens.S, J.gens.S))
end

(::Colon)(I::MPolyIdeal, J::MPolyIdeal) = quotient(I, J)

#######################################################

# saturation #######################################################
@doc Markdown.doc"""
    saturation(I::MPolyIdeal, J::MPolyIdeal)
    
Return the saturation of `I` with respect to `J`.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [z^3, y*z^2, x*z^2, y^2*z, x*y*z, x^2*z, x*y^2, x^2*y])
ideal generated by: z^3, y*z^2, x*z^2, y^2*z, x*y*z, x^2*z, x*y^2, x^2*y

julia> J = ideal(R, [x,y,z])
ideal generated by: x, y, z

julia> K = saturation(I,J)
ideal generated by: z, x*y
```
"""
function saturation(I::MPolyIdeal, J::MPolyIdeal)
  singular_assure(I)
  singular_assure(J)
  K, _ = Singular.saturation(I.gens.S, J.gens.S)
  return MPolyIdeal(base_ring(I), K)
end
#######################################################
@doc Markdown.doc"""
    saturation_with_index(I::MPolyIdeal, J::MPolyIdeal)

Return the saturation of `I` with respect to `J` together with the smallest integer $m$ such that $I:J^m = I:J^{\infty}$.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [z^3, y*z^2, x*z^2, y^2*z, x*y*z, x^2*z, x*y^2, x^2*y])
ideal generated by: z^3, y*z^2, x*z^2, y^2*z, x*y*z, x^2*z, x*y^2, x^2*y

julia> J = ideal(R, [x,y,z])
ideal generated by: x, y, z

julia> K, k = saturation_with_index(I, J)
(ideal generated by: z, x*y, 2)
```
"""
function saturation_with_index(I::MPolyIdeal, J::MPolyIdeal)
  singular_assure(I)
  singular_assure(J)
  K, k = Singular.saturation(I.gens.S, J.gens.S)
  return (MPolyIdeal(base_ring(I), K), k)
 end

# elimination #######################################################
@doc Markdown.doc"""
    eliminate(I::MPolyIdeal, l::Array{T, 1}) where T <: MPolyElem

Given a list of polynomials which are variables, these variables are eliminated from `I`. 

That is, return the ideal of all polynomials in `I` which only depend on the remaining variables.

    eliminate(I::MPolyIdeal, l::AbstractArray{Int, 1})

Given a list of indices which specify variables, these variables are eliminated from `I`. 

That is, return the ideal of all polynomials in `I` which only depend on the remaining variables.


# Examples
```jldoctest
julia> R, (t, x, y, z) = PolynomialRing(QQ, ["t", "x", "y", "z"])
(Multivariate Polynomial Ring in t, x, y, z over Rational Field, fmpq_mpoly[t, x, y, z])

julia> I = ideal(R, [t-x, t^2-y, t^3-z])
ideal generated by: t - x, t^2 - y, t^3 - z

julia> A = [t]
1-element Array{fmpq_mpoly,1}:
 t

julia> TC = eliminate(I,A)
ideal generated by: -x*z + y^2, x*y - z, x^2 - y

julia> A = [1]
1-element Array{Int64,1}:
 1

julia> TC = eliminate(I,A)
ideal generated by: -x*z + y^2, x*y - z, x^2 - y
```
"""
function eliminate(I::MPolyIdeal, l::Array{T, 1}) where T <: MPolyElem
  singular_assure(I)
  B = BiPolyArray(l)
  S = base_ring(I.gens.S)
  s = Singular.eliminate(I.gens.S, [S(x) for x = l]...)
  return MPolyIdeal(base_ring(I), s)
end
function eliminate(I::MPolyIdeal, l::AbstractArray{Int, 1})
  R = base_ring(I)
  return eliminate(I, [gen(R, i) for i=l])
end

### todo: wenn schon GB bzgl. richtiger eliminationsordnung bekannt ...
### Frage: return MPolyIdeal(base_ring(I), s) ???

###################################################

# primary decomposition #######################################################

#######################################################
@doc Markdown.doc"""
    radical(I::MPolyIdeal)
    
Return the radical of `I`. 

# Implemented Algorithms

If the base ring of `I` is a polynomial
ring over a field, a combination of the algorithms of Krick and Logar 
(with modifications by Laplagne) and Kemper is used. For polynomial
rings over the integers, the algorithm proceeds as suggested by 
Pfister, Sadiq, and Steidel. See [KL91](@cite),
[Kem02](@cite), and [PSS11](@cite).

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> RI = radical(I)
ideal generated by: x^4 - x^3*y - x^3 - x^2 - x*y^2 + x*y + x + y^3 + y^2
```
```jldoctest
julia> R, (a, b, c, d) = PolynomialRing(ZZ, ["a", "b", "c", "d"])
(Multivariate Polynomial Ring in a, b, c, d over Integer Ring, fmpz_mpoly[a, b, c, d])

julia> I = intersect(ideal(R, [9,a,b]), ideal(R, [3,c]))
ideal generated by: 9, 3*b, 3*a, b*c, a*c

julia> I = intersect(I, ideal(R, [11,2a,7b]))
ideal generated by: 99, 3*b, 3*a, b*c, a*c

julia> I = intersect(I, ideal(R, [13a^2,17b^4]))
ideal generated by: 39*a^2, 13*a^2*c, 51*b^4, 17*b^4*c, 3*a^2*b^4, a^2*b^4*c

julia> I = intersect(I, ideal(R, [9c^5,6d^5]))
ideal generated by: 78*a^2*d^5, 117*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5, 6*a^2*b^4*d^5, 9*a^2*b^4*c^5, 39*a^2*c^5*d^5, 51*b^4*c^5*d^5, 3*a^2*b^4*c^5*d^5

julia> I = intersect(I, ideal(R, [17,a^15,b^15,c^15,d^15]))
ideal generated by: 1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5, 663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15, 78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15, 39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5, 6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15, 3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5

julia> RI = radical(I)
ideal generated by: 102*b*d, 78*a*d, 51*b*c, 39*a*c, 6*a*b*d, 3*a*b*c
```
"""
function radical(I::MPolyIdeal)
  singular_assure(I)
  R = base_ring(I)
  if elem_type(base_ring(R)) <: FieldElement
  J = Singular.LibPrimdec.radical(I.gens.Sx, I.gens.S)
  elseif base_ring(I.gens.Sx) isa Singular.Integers
  J = Singular.LibPrimdecint.radicalZ(I.gens.Sx, I.gens.S)
  else
   error("not implemented for base ring")
  end
  return ideal(R, J)
end
#######################################################
@doc Markdown.doc"""
    primary_decomposition(I::MPolyIdeal)

Return a primary decomposition of `I`. If `I` is the unit ideal, return `[ideal(1)]`.

# Implemented Algorithms

If the base ring of `I` is a polynomial ring over a field, the algorithm of Gianni, Trager and Zacharias 
is used by default. Alternatively, the algorithm by Shimoyama and Yokoyama can be used by specifying 
`alg=:SY`.  For polynomial rings over the integers, the algorithm proceeds as suggested by 
Pfister, Sadiq, and Steidel. See [GTZ88](@cite), [SY96](@cite), and [PSS11](@cite).

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> L = primary_decomposition(I)
3-element Array{Tuple{MPolyIdeal{fmpq_mpoly},MPolyIdeal{fmpq_mpoly}},1}:
 (ideal generated by: x^3 - x - y^2, ideal generated by: x^3 - x - y^2)
 (ideal generated by: x^2 - 2*x*y - 2*x + y^2 + 2*y + 1, ideal generated by: x - y - 1)
 (ideal generated by: y, x^2, ideal generated by: x, y)

julia> L = primary_decomposition(I, alg=:SY)
3-element Array{Tuple{MPolyIdeal{fmpq_mpoly},MPolyIdeal{fmpq_mpoly}},1}:
 (ideal generated by: x^3 - x - y^2, ideal generated by: x^3 - x - y^2)
 (ideal generated by: x^2 - 2*x*y - 2*x + y^2 + 2*y + 1, ideal generated by: x - y - 1)
 (ideal generated by: y, x^2, ideal generated by: y, x)
```
```jldoctest
julia> R, (a, b, c, d) = PolynomialRing(ZZ, ["a", "b", "c", "d"])
(Multivariate Polynomial Ring in a, b, c, d over Integer Ring, fmpz_mpoly[a, b, c, d])

julia> I = ideal(R, [1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5,
       663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15,
       78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15,
       39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5,
       6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15,
       3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5])
ideal generated by: 1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5, 663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15, 78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15, 39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5, 6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15, 3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5

julia> L = primary_decomposition(I)
8-element Array{Tuple{MPolyIdeal{fmpz_mpoly},MPolyIdeal{fmpz_mpoly}},1}:
 (ideal generated by: d^5, c^5, ideal generated by: d, c)
 (ideal generated by: a^2, b^4, ideal generated by: b, a)
 (ideal generated by: 2, c^5, ideal generated by: 2, c)
 (ideal generated by: 3, ideal generated by: 3)
 (ideal generated by: 13, b^4, ideal generated by: 13, b)
 (ideal generated by: 17, a^2, ideal generated by: 17, a)
 (ideal generated by: 17, d^15, c^15, b^15, a^15, ideal generated by: 17, d, c, b, a)
 (ideal generated by: 9, 3*d^5, d^10, ideal generated by: 3, d)
```
"""
function primary_decomposition(I::MPolyIdeal; alg=:GTZ)
  R = base_ring(I)
  singular_assure(I)
  if elem_type(base_ring(R)) <: FieldElement
    if alg == :GTZ
      L = Singular.LibPrimdec.primdecGTZ(I.gens.Sx, I.gens.S)
    elseif alg == :SY
      L = Singular.LibPrimdec.primdecSY(I.gens.Sx, I.gens.S)
    else
      error("algorithm invalid")
    end
  elseif base_ring(I.gens.Sx) isa Singular.Integers
    L = Singular.LibPrimdecint.primdecZ(I.gens.Sx, I.gens.S)
  else
    error("base ring not implemented")
  end
  return [(ideal(R, q[1]), ideal(R, q[2])) for q in L]
end
########################################################
@doc Markdown.doc"""
    absolute_primary_decomposition(I::MPolyIdeal{fmpq_mpoly})

Return an absolute primary decomposition of `I`. The decomposition is returned
as an array of tuples `(a,b,c,d)`, where `(a,b)` is the (primary, prime) tuple
from `primary_decomposition`, `c` represents a class of conjugated absolute
primes defined over a degree `d` extension of `QQ`.
"""
function absolute_primary_decomposition(I::MPolyIdeal{fmpq_mpoly})
  R = base_ring(I)
  singular_assure(I)
  (S, d) = Singular.LibPrimdec.absPrimdecGTZ(I.gens.Sx, I.gens.S)
  decomp = d[:primary_decomp]
  absprimes = d[:absolute_primes]
  @assert length(decomp) == length(absprimes)
  return [(_map_last_var(R, decomp[i][1], 1, one(QQ)),
           _map_last_var(R, decomp[i][2], 1, one(QQ)),
           _map_to_ext(R, absprimes[i][1]),
           absprimes[i][2]::Int)
          for i in 1:length(decomp)]
end

# the ideals in QQbar[x] come back in QQ[x,a] with an extra variable a added
# and the minpoly of a prepended to the ideal generator list
function _map_to_ext(Qx::MPolyRing, I::Oscar.Singular.sideal)
  Qxa = base_ring(I)
  @assert nvars(Qxa) == nvars(Qx) + 1
  # TODO AbstractAlgebra's coefficients_of_univariate is still broken
  p = I[1]
  minpoly = zero(Hecke.Globals.Qx)
  for (c, e) in zip(coefficients(p), exponent_vectors(p))
    setcoeff!(minpoly, e[nvars(Qxa)], QQ(c))
  end
  R, a = number_field(minpoly)
  Rx, _ = PolynomialRing(R, String.(symbols(Qx)))
  return _map_last_var(Rx, I, 2, a)
end

# the ideals in QQ[x] also come back in QQ[x,a]
function _map_last_var(Qx::MPolyRing, I::Singular.sideal, start, a)
  newgens = elem_type(Qx)[]
  for i in start:ngens(I)
    p = I[i]
    g = MPolyBuildCtx(Qx)
    for (c, e) in zip(coefficients(p), exponent_vectors(p))
      ca = QQ(c)*a^pop!(e)
      push_term!(g, ca, e)
    end
    push!(newgens, finish(g))
  end
  return ideal(Qx, newgens)
end

#######################################################y
@doc Markdown.doc"""
    minimal_primes(I::MPolyIdeal; alg=:GTZ)

Return an array containing the minimal associated prime ideals of `I`.
If `I` is the unit ideal, return `[ideal(1)]`.

# Implemented Algorithms

If the base ring of `I` is a polynomial ring over a field, the algorithm of
Gianni-Trager-Zacharias is used by default and characteristic sets may be
used by specifying `alg=:charSets`. For polynomial rings over the integers, 
the algorithm proceeds as suggested by Pfister, Sadiq, and Steidel.
See [GTZ88](@cite) and [PSS11](@cite).

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> L = minimal_primes(I)
2-element Array{MPolyIdeal{fmpq_mpoly},1}:
 ideal generated by: x - y - 1
 ideal generated by: x^3 - x - y^2

julia> L = minimal_primes(I, alg=:charSets)
2-element Array{MPolyIdeal{fmpq_mpoly},1}:
 ideal generated by: x - y - 1
 ideal generated by: x^3 - x - y^2
```
```jldoctest
julia> R, (a, b, c, d) = PolynomialRing(ZZ, ["a", "b", "c", "d"])
(Multivariate Polynomial Ring in a, b, c, d over Integer Ring, fmpz_mpoly[a, b, c, d])

julia> I = ideal(R, [1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5,
       663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15,
       78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15,
       39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5,
       6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15,
       3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5])
ideal generated by: 1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5, 663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15, 78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15, 39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5, 6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15, 3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5

julia> L = minimal_primes(I)
6-element Array{MPolyIdeal{fmpz_mpoly},1}:
 ideal generated by: d, c
 ideal generated by: b, a
 ideal generated by: 2, c
 ideal generated by: 3
 ideal generated by: 13, b
 ideal generated by: 17, a
```
"""
function minimal_primes(I::MPolyIdeal; alg = :GTZ)
  R = base_ring(I)
  singular_assure(I)
  if elem_type(base_ring(R)) <: FieldElement
    if alg == :GTZ
      l = Singular.LibPrimdec.minAssGTZ(I.gens.Sx, I.gens.S)
    elseif alg == :charSets
      l = Singular.LibPrimdec.minAssChar(I.gens.Sx, I.gens.S)
    else
      error("algorithm invalid")
    end
  elseif base_ring(I.gens.Sx) isa Singular.Integers
    l = Singular.LibPrimdecint.minAssZ(I.gens.Sx, I.gens.S)
  else
    error("base ring not implemented")
  end
  return [ideal(R, i) for i in l]
end
#######################################################
@doc Markdown.doc"""
    equidimensional_decomposition_weak(I::MPolyIdeal)

Return an array of equidimensional ideals where the last element is the
equidimensional hull of `I`, that is, the intersection of the primary
components of `I` of maximal dimension. Each of the previous elements
is an ideal of lower dimension whose associated primes are exactly the associated
primes of `I` of that dimension. If `I` is the unit ideal, return `[ideal(1)]`.

# Implemented Algorithms

The implementation relies on ideas of Eisenbud, Huneke, and Vasconcelos. See [EHV92](@cite). 

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> L = equidimensional_decomposition_weak(I)
2-element Array{MPolyIdeal{fmpq_mpoly},1}:
 ideal generated by: y, x
 ideal generated by: x^5 - 2*x^4*y - 2*x^4 + x^3*y^2 + 2*x^3*y - x^2*y^2 + 2*x^2*y + 2*x^2 + 2*x*y^3 + x*y^2 - 2*x*y - x - y^4 - 2*y^3 - y^2
```
"""
function equidimensional_decomposition_weak(I::MPolyIdeal)
  R = base_ring(I)
  singular_assure(I)
  l = Singular.LibPrimdec.equidim(I.gens.Sx, I.gens.S)
  return [ideal(R, i) for i in l]
end

@doc Markdown.doc"""
    equidimensional_decomposition_radical(I::MPolyIdeal)

Return an array of equidimensional radical ideals increasingly ordered by dimension.
For each dimension, the returned radical ideal is the intersection of the associated primes 
of `I` of that dimension. If `I` is the unit ideal, return `[ideal(1)]`.

# Implemented Algorithms

The implementation combines the algorithms of Krick and Logar (with modifications by Laplagne) and Kemper. See [KL91](@cite) and [Kem02](@cite).

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> L = equidimensional_decomposition_radical(I)
2-element Array{MPolyIdeal{fmpq_mpoly},1}:
 ideal generated by: y, x
 ideal generated by: x^4 - x^3*y - x^3 - x^2 - x*y^2 + x*y + x + y^3 + y^2
```
"""
function equidimensional_decomposition_radical(I::MPolyIdeal)
  R = base_ring(I)
  singular_assure(I)
  l = Singular.LibPrimdec.prepareAss(I.gens.Sx, I.gens.S)
  return [ideal(R, i) for i in l]
end
#######################################################
@doc Markdown.doc"""
    equidimensional_hull(I::MPolyIdeal)

If the base ring of `I` is a polynomial ring over a field, return the intersection
of the primary components of `I` of maximal dimension. In the case of polynomials
over the integers, return the intersection of the primary components of I of
minimal height.  If `I` is the unit ideal, return `[ideal(1)]`. 

# Implemented Algorithms

For polynomial rings over a field, the implementation relies on ideas as used by
Gianni, Trager, and Zacharias or Krick and Logar. For polynomial rings over the integers, 
the algorithm proceeds as suggested by Pfister, Sadiq, and Steidel. See [GTZ88](@cite),
[KL91](@cite),  and [PSS11](@cite).

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> L = equidimensional_hull(I)
ideal generated by: x^5 - 2*x^4*y - 2*x^4 + x^3*y^2 + 2*x^3*y - x^2*y^2 + 2*x^2*y + 2*x^2 + 2*x*y^3 + x*y^2 - 2*x*y - x - y^4 - 2*y^3 - y^2
```
```jldoctest
julia> R, (a, b, c, d) = PolynomialRing(ZZ, ["a", "b", "c", "d"])
(Multivariate Polynomial Ring in a, b, c, d over Integer Ring, fmpz_mpoly[a, b, c, d])

julia> I = ideal(R, [1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5,
       663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15,
       78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15,
       39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5,
       6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15,
       3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5])
ideal generated by: 1326*a^2*d^5, 1989*a^2*c^5, 102*b^4*d^5, 153*b^4*c^5, 663*a^2*c^5*d^5, 51*b^4*c^5*d^5, 78*a^2*d^15, 117*a^2*c^15, 78*a^15*d^5, 117*a^15*c^5, 6*a^2*b^4*d^15, 9*a^2*b^4*c^15, 39*a^2*c^5*d^15, 39*a^2*c^15*d^5, 6*a^2*b^15*d^5, 9*a^2*b^15*c^5, 6*a^15*b^4*d^5, 9*a^15*b^4*c^5, 39*a^15*c^5*d^5, 3*a^2*b^4*c^5*d^15, 3*a^2*b^4*c^15*d^5, 3*a^2*b^15*c^5*d^5, 3*a^15*b^4*c^5*d^5

julia> L = equidimensional_hull(I)
ideal generated by: 3
```
"""
function equidimensional_hull(I::MPolyIdeal)
  R = base_ring(I)
  singular_assure(I)
  if elem_type(base_ring(R)) <: FieldElement
    i = Singular.LibPrimdec.equidimMax(I.gens.Sx, I.gens.S)
  elseif base_ring(I.gens.Sx) isa Singular.Integers
    i = Singular.LibPrimdecint.equidimZ(I.gens.Sx, I.gens.S)
  else
    error("base ring not implemented")
  end
  return ideal(R, i)
end
#######################################################
@doc Markdown.doc"""
    equidimensional_hull_radical(I::MPolyIdeal)

Return the intersection of the associated primes of `I` of maximal dimension.
If `I` is the unit ideal, return `[ideal(1)]`. 

# Implemented Algorithms

The implementation relies on a combination of the algorithms of Krick and Logar 
(with modifications by Laplagne) and Kemper. See [KL91](@cite) and [Kem02](@cite).

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = intersect(ideal(R, [x, y])^2, ideal(R, [y^2-x^3+x]))
ideal generated by: x^3*y - x*y - y^3, x^4 - x^2 - x*y^2

julia> I = intersect(I, ideal(R, [x-y-1])^2)
ideal generated by: x^5*y - 2*x^4*y^2 - 2*x^4*y + x^3*y^3 + 2*x^3*y^2 - x^2*y^3 + 2*x^2*y^2 + 2*x^2*y + 2*x*y^4 + x*y^3 - 2*x*y^2 - x*y - y^5 - 2*y^4 - y^3, x^6 - 2*x^5 - 3*x^4*y^2 - 2*x^4*y + 2*x^3*y^3 + 3*x^3*y^2 + 2*x^3*y + 2*x^3 + 5*x^2*y^2 + 2*x^2*y - x^2 + 3*x*y^4 - 5*x*y^2 - 2*x*y - 2*y^5 - 4*y^4 - 2*y^3

julia> L = equidimensional_hull_radical(I)
ideal generated by: x^4 - x^3*y - x^3 - x^2 - x*y^2 + x*y + x + y^3 + y^2
```
"""
function equidimensional_hull_radical(I::MPolyIdeal)
  R = base_ring(I)
  singular_assure(I)
  i = Singular.LibPrimdec.equiRadical(I.gens.Sx, I.gens.S)
  return ideal(R, i)
end

#######################################################
@doc Markdown.doc"""
    :(==)(I::MPolyIdeal, J::MPolyIdeal)

Return `true` if `I` is equal to `J`, `false` otherwise.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x^2])
ideal generated by: x^2

julia> J = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> I == J
false
```
"""
function Base.:(==)(I::MPolyIdeal, J::MPolyIdeal)
  return issubset(I, J) && issubset(J, I)
end

### todo: wenn schon GB's  bekannt ...

#######################################################
@doc Markdown.doc"""
    issubset(I::MPolyIdeal, J::MPolyIdeal)

Return `true` if `I` is contained in `J`, `false` otherwise.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x^2])
ideal generated by: x^2

julia> J = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> issubset(I, J)
true
```
"""
function Base.issubset(I::MPolyIdeal, J::MPolyIdeal)
  # avoid Singular.contains as it does not save the gb it might compute
  singular_assure(I)
  groebner_assure(J)
  singular_assure(J.gb)
  return Singular.iszero(Singular.reduce(I.gens.S, J.gb.S))
end

### todo: wenn schon GB's  bekannt ...

#######################################################

@doc Markdown.doc"""
    ideal_membership(f::T, I::MPolyIdeal) where T <: MPolyElem

Return `true` if `f` is contained in `I`, `false` otherwise. Alternatively, use `f in I`. 

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> f = x^2
x^2

julia> I = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> ideal_membership(f, I)
true

julia> g = x
x

julia> g in I
false
```
"""
function ideal_membership(f::T, I::MPolyIdeal) where T <: MPolyElem
  groebner_assure(I)
  singular_assure(I.gb)
  Sx = base_ring(I.gb.S)
  return Singular.iszero(reduce(Sx(f), I.gb.S))
end
Base.:in(f::MPolyElem, I::MPolyIdeal) = ideal_membership(f,I)
#######################################################
@doc Markdown.doc"""
    radical_membership(f::T, I::MPolyIdeal) where T <: MPolyElem
   
Return `true` if `f` is contained in the radical of `I`, `false` otherwise.

# Examples
```jldoctest
julia> R, (x,) = PolynomialRing(QQ, ["x"])
(Multivariate Polynomial Ring in x over Rational Field, fmpq_mpoly[x])

julia> f = x
x

julia> I = ideal(R,  [x^2])
ideal generated by: x^2

julia> radical_membership(f, I)
true
```
"""
function radical_membership(f::T, I::MPolyIdeal) where T <: MPolyElem
  singular_assure(I)                                                                                    
  Sx = base_ring(I.gens.S)                                                                                    
  return Singular.LibPolylib.rad_con(Sx(f), I.gens.S) == 1                                                    
end

################################################################################
@doc Markdown.doc"""
    isprime(I::MPolyIdeal)

Return `true` if the ideal `I` is prime, `false` otherwise. 

CAVEAT: The implementation proceeds by computing the minimal associated primes of `I` first. This may take some time.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> isprime(I)
false
```
"""
function isprime(I::MPolyIdeal)
  D = primary_decomposition(I)
  return length(D) == 1 && issubset(D[1][2], D[1][1])
end

################################################################################
@doc Markdown.doc"""
    isprimary(I::MPolyIdeal)

Return `true` if the ideal `I` is primary, `false` otherwise. 

CAVEAT: The implementation proceeds by computing a primary decomposition first. This may take some time.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> isprimary(I)
true
```
"""
function isprimary(I::MPolyIdeal)
  D = primary_decomposition(I)
  return length(D) == 1
end

#######################################################
@doc Markdown.doc"""
    base_ring(I::MPolyIdeal{S}) where {S}

Return the ambient ring of `I`.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> base_ring(I)
Multivariate Polynomial Ring in x, y over Rational Field
```
"""
function base_ring(I::MPolyIdeal{S}) where {S}
  return I.gens.Ox::parent_type(S)
end

#######################################################
@doc Markdown.doc"""
    ngens(I::MPolyIdeal)

Return the number of generators of `I`.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> ngens(I)
3
```
"""
function ngens(I::MPolyIdeal)
  return length(I.gens)
end

#######################################################
@doc Markdown.doc"""
    gens(I::MPolyIdeal)

Return the generators of `I` as an array of multivariate polynomials.

# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x, y])^2
ideal generated by: x^2, x*y, y^2

julia> gens(I)
3-element Array{fmpq_mpoly,1}:
 x^2
 x*y
 y^2
```
"""
function gens(I::MPolyIdeal)
  return [I.gens[Val(:O), i] for i=1:ngens(I)]
end

gen(I::MPolyIdeal, i::Int) = I.gens[Val(:O), i]
getindex(I::MPolyIdeal, i::Int) = gen(I, i)

#######################################################
@doc Markdown.doc"""
    dim(I::MPolyIdeal)

Return the Krull dimension of `I`.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [y-x^2, x-z^3])
ideal generated by: -x^2 + y, x - z^3

julia> dim(I)
1
```
"""
function dim(I::MPolyIdeal)
  if I.dim > -1
    return I.dim
  end
  groebner_assure(I)
  singular_assure(I.gb)
  I.dim = Singular.dimension(I.gb.S)
  return I.dim
end

#######################################################
#######################################################
@doc Markdown.doc"""
    codim(I::MPolyIdeal)

Return the codimension of `I`.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> I = ideal(R, [y-x^2, x-z^3])
ideal generated by: -x^2 + y, x - z^3

julia> codim(I)
2
```
"""
codim(I::MPolyIdeal) = nvars(base_ring(I)) - dim(I)

################################################################################
#
#  iszero and isone functions
#
################################################################################

@doc Markdown.doc"""
    iszero(I::MPolyIdeal)

Return true if `I` is the zero ideal, false otherwise.
# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, y-x^2)
ideal generated by: -x^2 + y

julia> iszero(I)
false
```
"""
function iszero(I::MPolyIdeal)
  lg = gens(I)
  return isempty(lg) || all(iszero, lg)
end

@doc Markdown.doc"""
    isone(I::MPolyIdeal)

Return true if `I` is generated by `1`, false otherwise.
# Examples
```jldoctest
julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> I = ideal(R, [x, x + y, y - 1])
ideal generated by: x, x + y, y - 1

julia> isone(I)
true
```
"""
function isone(I::MPolyIdeal)
  R = base_ring(I)
  if any(x -> (isconstant(x) && isunit(first(coefficients(x)))), gens(I))
    return true
  end
  gb = groebner_basis(I, complete_reduction = true)
  return isconstant(gb[1]) && isunit(first(coefficients(gb[1])))
end
