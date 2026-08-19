```@meta
CurrentModule = Oscar
CollapsedDocStrings = true
DocTestSetup = Oscar.doctestsetup()
```

# Sheaves on Projective Space

We present two algorithms for computing sheaf cohomology over projective $n$-space.
The algorithms are based on Tate resolutions via the **B**ernstein-**G**elfand-**G**elfand-correspondence
as introduced in [EFS03](@cite) and on local cohomology (see [Eis98](@cite)), respectively. While the first
algorithm makes use of syzygy computations over the exterior algebra, the second algorithm is based on
syzygy computations over the symmetric algebra (see [DE02](@cite) for a tutorial). Thus, in most examples,
the first algorithm is much faster.

```@docs
sheaf_cohomology(M::OFPModule{T}, l::Int, h::Int; algorithm::Symbol = :bgg) where {T <: MPolyDecRingElem}
```

## Global sections from the regular multiplication tail

Put ``\mathfrak m=(x_0,\ldots,x_n)`` and choose a tail degree ``s``.  The
finite kernel used here is

```math
\operatorname{Hom}_S(\mathfrak m^{s-d},M)_d.
```

It is represented using only ``M_s``, ``M_{s+1}``, and multiplication by the
variables.  In the stable range it is the degree-``d`` part of the ideal
transform and hence recovers explicit representatives of
``H^0(\mathbb P^n,\widetilde M(d))``.  These are the same multiplication data
that form the ``H^0``-strand of the BGG/Tate tail, but this construction does
not build the full Tate resolution.

A result `B` stores vector-valued numerators ``v_i`` in the zeroth free module
of a presentation of `M`, together with one homogeneous evaluation element
``g``.  After applying the presentation augmentation and sheafifying, its
sections are ``v_i/g``.  The automatic tail detects irrelevant torsion at the
regularity boundary.  The denominator is chosen so that evaluation preserves
the basis and multiplication by ``g`` is injective on ``\widetilde M``.  The
automatic search tries sparse and generic deterministic candidates and checks
each one exactly; an explicit denominator can be supplied if none of these
candidates works.

```@docs
SheafSectionBasis
sheaf_section_basis
```

For a general line bundle, the presentation free module need not have rank
one.  Choose a rational rank-one trivialization which maps the generators of
`M` to ``h_j/f``.  The presentation augmentation sends a tail lift `v_i` to an
element ``m_i`` of `M`; writing ``m_i=\sum_j c_{ij}m_j`` gives the scalar
numerator

```math
H_i=\sum_j c_{ij}h_j.
```

Thus the rational sections are ``H_i/(fg)``, and the common-denominator-free
polynomials ``H_i`` are homogeneous coordinates for the associated rational
map.  They are not normalized and may retain a common fixed factor.

```@docs
TrivializedSheafSectionBasis
rank_one_module_trivialization
trivialization_numerator
trivialized_section_basis
```

For example, the relation ``e_2=Xe_1`` gives a redundant two-generator
presentation of ``\mathcal O_{\mathbb P^2}(1)``:

```julia
P = projective_space(QQ, [:X, :Y, :Z])
S = homogeneous_coordinate_ring(P)
X, Y, Z = gens(S)
G = grading_group(S)
A = embedded_divisor_ambient(S; projective=true)

F = graded_free_module(S, [-G[1], zero(G)])
M, _ = quo(F, [F[2] - X*F[1]])
C = trivialized_section_basis(A, M)

projective_coordinates(C) # [Z, Y, X], up to ordering
rational_map(P, P, projective_coordinates(C))
```

An `EmbeddedDivisor` can be used directly.  If `global_sections_ideal(D)`
represents ``\mathcal O_X(D)`` by the fractional ideal ``N/f``, the divisor
overload constructs the correctly shifted graded module
``((N+I_X)/I_X)e`` with ``\deg(e)=-\deg(f)`` and applies the finite-tail
construction to it.  This is important when both the positive and negative
divisor parts are present.

```julia
D = embedded_divisor(A, ideal(S, [X^2]), ideal(S, [Y]); cleanup=:none)
C = trivialized_section_basis(D; cleanup=:none)

projective_coordinates(C) # [Y*Z, Y^2, X*Y], up to ordering
section_denominator(C)     # X^2
```

The finite-tail constructor itself applies to any finitely generated graded
module over a standard ``\mathbb Z``-graded polynomial ring over a field.  To
turn its vector-valued sections into scalar rational functions and hence a
rational map, the embedded coordinate ideal must annihilate the module and its
associated sheaf must be torsion-free and generically rank one.  Local freeness
is not inferred: for a Cartier divisor the result is a line-bundle linear
system, while for a non-Cartier divisor it is the corresponding torsion-free
rank-one sheaf linear system.
