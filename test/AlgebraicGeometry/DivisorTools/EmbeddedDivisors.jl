@testset "embedded divisor arithmetic" begin
  R, (x, y, z) = polynomial_ring(QQ, [:x, :y, :z])
  A = embedded_divisor_ambient(R)

  # (x*y, y*z) has divisorial component (y) and embedded/high-codimension
  # component (x,z).  The constructor should keep only the divisor component.
  D = effective_embedded_divisor(A, ideal(R, [x*y, y*z]))
  Y = effective_embedded_divisor(A, ideal(R, [y]))
  @test is_equal_divisor(D, Y)

  X = effective_embedded_divisor(A, ideal(R, [x]))
  Z = effective_embedded_divisor(A, ideal(R, [z]))
  @test is_equal_divisor(X + Y - Y, X)
  @test is_equal_divisor(2*X - X, X)
  @test is_equal_divisor(principal_embedded_divisor(A, x, y), X - Y)
  @test linearly_equivalent(X, Y, x, y)
  @test is_effective_divisor(X)
  @test !is_effective_divisor(-X)

  S = global_sections_ideal(X - Y)
  @test is_subset(ideal(R, [y]), section_numerator_ideal(S))
  @test section_denominator(S) == x
  @test is_effective_divisor(effective_representative(S, y))

  Q, q = quo(R, ideal(R, [zero(R)]))
  AQ = embedded_divisor_ambient(Q)
  xq, yq, zq = gens(Q)
  Dq = effective_embedded_divisor(AQ, ideal(Q, [xq*yq, yq*zq]))
  Yq = effective_embedded_divisor(AQ, ideal(Q, [yq]))
  @test is_equal_divisor(Dq, Yq)

  F = decompose_divisor(X - Z)
  @test is_equal_divisor(evaluate_formal_divisor(F), X - Z)
  @test degree_formal_divisor(F) == degree_divisor(X - Z)
end

@testset "projective embedded divisor cleanup" begin
  S, (X, Y, Z) = graded_polynomial_ring(QQ, [:X, :Y, :Z])
  P2 = embedded_divisor_ambient(S; projective=true)

  # In the homogeneous coordinate ring of P^2, (X*Y, X*Z) has the line X = 0
  # plus a codimension-two point.  Only the codimension-one component remains.
  D = effective_embedded_divisor(P2, ideal(S, [X*Y, X*Z]))
  L = effective_embedded_divisor(P2, ideal(S, [X]))
  @test is_equal_divisor(D, L)

  # The irrelevant ideal is removed by saturation/Proj cleanup.
  B = ideal(S, [X, Y, Z])
  E = effective_embedded_divisor(P2, B)
  @test is_one(positive_ideal(E))
end

@testset "unsaturated projective coordinate ideals" begin
  S, (X, Y, Z) = graded_polynomial_ring(QQ, [:X, :Y, :Z])
  e = grading_group(S)[1]
  IX = ideal(S, [X^2, X*Y, X*Z])
  Araw = embedded_divisor_ambient(IX; projective=true, saturate=false)
  Asat = embedded_divisor_ambient(IX; projective=true)

  # Keep the requested raw presentation, but use its saturation for operations
  # on Proj.  Here Proj(S/IX) is the line X = 0.
  @test Oscar._ideal_equal(coordinate_ideal(Araw), IX)
  @test !Oscar._ideal_equal(coordinate_ideal(Araw), coordinate_ideal(Asat))

  Draw = effective_embedded_divisor(Araw, ideal(S, [Y]))
  Dsat = effective_embedded_divisor(Asat, ideal(S, [Y]))
  @test is_equal_divisor(Draw, Dsat)
  @test_throws ErrorException effective_embedded_divisor(Araw, ideal(S, [X]))

  O1 = graded_module_global_sections(Araw, ideal(S, [one(S)]); degree=e)
  @test length(section_basis_numerators(O1)) == 2
  @test Oscar._ideal_equal(ideal(S, section_basis_numerators(O1)), ideal(S, [Y, Z]))

  Ozero = graded_module_global_sections(Araw, IX; degree=e)
  @test isempty(section_basis_numerators(Ozero))

  Craw = trivialized_section_basis(Draw; cleanup=:none, verify=true)
  Csat = trivialized_section_basis(Dsat; cleanup=:none, verify=true)
  @test Set(projective_coordinates(Craw)) == Set([Y, Z])
  @test Set(projective_coordinates(Craw)) == Set(projective_coordinates(Csat))
  @test section_denominator(Craw) == section_denominator(Csat) == Y

  Qsat, _ = quo(S, coordinate_ideal(Asat))
  Dq = effective_embedded_divisor(Araw, ideal(Qsat, [Qsat(Y)]))
  @test is_equal_divisor(Dq, Draw)

  Qraw, _ = quo(S, IX)
  Fraw = graded_free_module(Qraw, 1)
  @test is_one(rank_one_module_ideal(Asat, Fraw))
end

@testset "graded rank-one module bridge" begin
  S, (X, Y, Z) = graded_polynomial_ring(QQ, [:X, :Y, :Z])
  G = grading_group(S)
  e = G[1]
  z = zero(G)
  P2 = embedded_divisor_ambient(S; projective=true)

  L = effective_embedded_divisor(P2, ideal(S, [X]))

  F = graded_free_module(S, 1)
  M, _ = sub(F, [X*F[1]])

  N = rank_one_module_ideal(P2, M)
  @test is_equal_divisor(divisor_from_graded_module(P2, M; convention=:ideal), L)
  @test is_equal_divisor(divisor_from_graded_module(P2, M; convention=:sections), -L)

  SX = graded_module_global_sections(P2, M; degree=e)
  @test length(section_basis_numerators(SX)) == 1
  @test all(h -> h in ideal(S, [X]), section_basis_numerators(SX))

  OP1 = graded_module_global_sections(P2, ideal(S, [one(S)]); denominator=X, degree=z)
  @test length(section_basis_numerators(OP1)) == 3
  @test is_equal_divisor(divisor_from_fractional_ideal(P2, ideal(S, [one(S)]), X), L)

  F2 = graded_free_module(S, 2)
  M2, _ = sub(F2, [F2[1], F2[2]])
  SXexplicit = graded_module_global_sections(P2, M2, [X, X]; degree=e, shift=z)
  @test length(section_basis_numerators(SXexplicit)) == 1
  @test is_equal_divisor(divisor_from_graded_module(P2, M2, [X, X]; convention=:ideal, shift=z), L)
end

@testset "presented rank-one graded modules" begin
  S, (X, Y, Z) = graded_polynomial_ring(QQ, [:X, :Y, :Z])
  G = grading_group(S)
  e = G[1]
  z = zero(G)
  P2 = embedded_divisor_ambient(S; projective=true)
  H = effective_embedded_divisor(P2, ideal(S, [X]))

  O1 = graded_free_module(S, [-e])
  @test is_equal_divisor(divisor_from_graded_module(P2, O1; hyperplane=X), H)
  SO1 = graded_module_global_sections(P2, O1)
  @test section_degree(SO1) == z
  @test section_trivialization_shift(SO1) == degrees_of_generators(O1)[1]
  @test length(section_basis_numerators(SO1)) == 3
  @test_throws ErrorException graded_module_global_sections(P2, O1; degree=0)
  @test_throws ErrorException divisor_from_graded_module(P2, O1; shift=0, hyperplane=X)

  F = graded_free_module(S, [z, z])
  M, _ = quo(F, [Y*F[1] - X*F[2]])
  T = rank_one_module_trivialization(P2, M)
  @test trivialization_denominator(T) == one(S)
  @test section_denominator(graded_module_global_sections(P2, M; degree=z)) == one(S)
  @test is_equal_divisor(divisor_from_graded_module(P2, M; hyperplane=X), H)
  @test length(section_basis_numerators(graded_module_global_sections(P2, M; degree=z))) == 3

  F2 = graded_free_module(S, 2)
  M2, _ = sub(F2, [F2[1], F2[2]])
  @test_throws ErrorException rank_one_module_trivialization(P2, M2)
end

@testset "canonical divisor sections of a projective surface" begin
  k = GF(31991)
  S, (x0, x1, x2, x3) = graded_polynomial_ring(k, [:x0, :x1, :x2, :x3])
  G = grading_group(S)
  e = G[1]
  z = zero(G)
  f = x0^5 + x1^5 + x2^5 + x3^5

  X = variety(f; check=false)
  A = embedded_divisor_ambient(ideal(S, [f]); projective=true)

  Kmod = canonical_bundle(X)
  Kdiv = divisor_from_graded_module(A, Kmod; hyperplane=x0)
  H = effective_embedded_divisor(A, ideal(S, [x0]))

  @test is_equal_divisor(Kdiv, H)

  GK = graded_module_global_sections(A, Kmod; degree=z)
  nums = section_basis_numerators(GK)

  @test length(nums) == 4
  @test all(h -> degree(h) == e, nums)
  @test all(h -> !is_zero(h), nums)
end

@testset "BGG sections from positive and negative divisor parts" begin
  # Preserve the fractional denominator while turning a divisor into map coordinates.
  P = projective_space(QQ, [:X, :Y, :Z])
  S = homogeneous_coordinate_ring(P)
  X, Y, Z = gens(S)
  A = embedded_divisor_ambient(S; projective=true)
  D = embedded_divisor(A, ideal(S, [X^2]), ideal(S, [Y]); cleanup=:none)

  C = trivialized_section_basis(D; cleanup=:none, verify=true)
  @test length(C) == 3
  @test Set(projective_coordinates(C)) == Set([X*Y, Y^2, Y*Z])
  @test section_denominator(C) == X^2
  @test twist(C) == 0
  @test twist(underlying_section_basis(C)) == 0
  @test is_zero(section_trivialization_shift(C))

  phi = rational_map(P, P, projective_coordinates(C))
  @test domain(phi) === P
  @test codomain(phi) === P

  Ctail = trivialized_section_basis(D; tail_degree=1,
                                    bgg_denominator=Z, cleanup=:none)
  @test Set(projective_coordinates(Ctail)) ==
        Set([Z*h for h in projective_coordinates(C)])
  @test section_denominator(Ctail) == X^2*Z

  C1 = trivialized_section_basis(D, 1; cleanup=:none)
  @test length(C1) == 6
  @test Set(projective_coordinates(C1)) ==
        Set([Y*m for m in monomial_basis(S, 2)])
  @test section_denominator(C1) == X^2

  # On a reducible scheme both displayed generators can be zero divisors, even
  # though their sum is a valid element of the positive ideal.  Generator order
  # must not make the fractional-ideal denominator invalid.
  Rred, (u, v, w) = graded_polynomial_ring(QQ, [:u, :v, :w])
  Ared = embedded_divisor_ambient(ideal(Rred, [u*v]); projective=true)
  Dred = embedded_divisor(Ared, ideal(Rred, [u, v]), ideal(Rred, [one(Rred)]);
                          cleanup=:none)
  Sred = global_sections_ideal(Dred; cleanup=:none)
  @test section_denominator(Sred) == u + v
end
