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

@testset "graded rank-one module bridge" begin
  S, (X, Y, Z) = graded_polynomial_ring(QQ, [:X, :Y, :Z])
  P2 = embedded_divisor_ambient(S; projective=true)

  L = effective_embedded_divisor(P2, ideal(S, [X]))

  F = graded_free_module(S, 1)
  M, _ = sub(F, [X*F[1]])

  N = rank_one_module_ideal(P2, M)
  @test is_equal_divisor(divisor_from_graded_module(P2, M; convention=:ideal), L)
  @test is_equal_divisor(divisor_from_graded_module(P2, M; convention=:sections), -L)

  SX = graded_module_global_sections(P2, M; degree=1)
  @test length(section_basis_numerators(SX)) == 1
  @test all(h -> h in ideal(S, [X]), section_basis_numerators(SX))

  OP1 = graded_module_global_sections(P2, ideal(S, [one(S)]); denominator=X, degree=0)
  @test length(section_basis_numerators(OP1)) == 3
  @test is_equal_divisor(divisor_from_fractional_ideal(P2, ideal(S, [one(S)]), X), L)

  F2 = graded_free_module(S, 2)
  M2, _ = sub(F2, [F2[1], F2[2]])
  SXexplicit = graded_module_global_sections(P2, M2, [X, X]; degree=1)
  @test length(section_basis_numerators(SXexplicit)) == 1
  @test is_equal_divisor(divisor_from_graded_module(P2, M2, [X, X]; convention=:ideal), L)
end
