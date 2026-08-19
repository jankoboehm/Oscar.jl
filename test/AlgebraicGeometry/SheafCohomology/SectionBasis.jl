@testset "BGG-tail section basis" begin
  R, (x, y, z) = graded_polynomial_ring(QQ, [:x, :y, :z])
  F = graded_free_module(R, 1)

  B2 = sheaf_section_basis(F, 2; tail_degree = 2, verify = true)
  @test length(B2) == 6
  @test isone(section_denominator(B2))
  @test Set(projective_coordinates(B2)) == Set(monomial_basis(R, 2))

  B0 = sheaf_section_basis(F, 0; tail_degree = 2, denominator = x^2, verify = true)
  @test length(B0) == 1
  @test section_denominator(B0) == x^2
  @test projective_coordinates(B0) == [x^2]

  B1 = sheaf_section_basis(F, 1; tail_degree = 2, denominator = x, verify = true)
  @test length(B1) == 3
  @test section_denominator(B1) == x
  @test Set(projective_coordinates(B1)) == Set([x*m for m in monomial_basis(R, 1)])
end

@testset "safe tail and denominator selection" begin
  R, (x, y, z) = graded_polynomial_ring(QQ, [:x, :y, :z])

  # A saturated module needs no boundary correction: automatic mode should
  # keep the regularity degree and its degree-zero evaluation element.
  O = graded_free_module(R, 1)
  BO = sheaf_section_basis(O, 0)
  @test tail_degree(BO) == 0
  @test isone(section_denominator(BO))

  # The second summand is irrelevant torsion.  At reg(M) = 0 it would give a
  # spurious section, so the automatic tail must advance by one degree.
  F = graded_free_module(R, 2)
  M, _ = quo(F, [x*F[2], y*F[2], z*F[2]])
  @test cm_regularity(M) == 0
  B = sheaf_section_basis(M, 0; verify=true)
  @test tail_degree(B) == 1
  @test length(B) == 1
  @test degree(Int, section_denominator(B)) == 1
  @test_throws ErrorException sheaf_section_basis(M, 0;
                                                   tail_degree=0,
                                                   verify=true)

  # Evaluation at x kills the unique section of the line x=0.  A regular
  # evaluation element keeps the basis nonzero.
  Mline = quotient_ring_as_module(ideal(R, [x]))
  @test_throws ErrorException sheaf_section_basis(Mline, 0;
                                                   tail_degree=1,
                                                   denominator=x,
                                                   verify=true)
  Bline = sheaf_section_basis(Mline, 0;
                              tail_degree=1,
                              denominator=y,
                              verify=true)
  @test length(Bline) == 1
  @test projective_coordinates(Bline) == [y]

  # On two reduced coordinate points, both monomial denominators are zero
  # divisors.  The automatic search must reach the regular sum x+y.
  R2, (u, v) = graded_polynomial_ring(QQ, [:u, :v])
  Mpoints = quotient_ring_as_module(ideal(R2, [u*v]))
  Bpoints = sheaf_section_basis(Mpoints, 0; tail_degree=1, verify=true)
  @test length(Bpoints) == 2
  @test section_denominator(Bpoints) == u + v
  @test Set(projective_coordinates(Bpoints)) == Set([u, v])
  @test_throws ErrorException sheaf_section_basis(Mpoints, 0;
                                                   tail_degree=1,
                                                   denominator=u)

  # The first monomial and the full sum can both be zero divisors.  The
  # deterministic generic pencil must then find, and exactly verify, another
  # linear form.
  Mthree = quotient_ring_as_module(ideal(R2, [u*v*(u + v)]))
  Bthree = sheaf_section_basis(Mthree, 1)
  @test tail_degree(Bthree) == 2
  @test length(Bthree) == 3
  @test !(section_denominator(Bthree) in [u, v, u + v])

  Rother, (xother, _, _) = graded_polynomial_ring(QQ, [:x, :y, :z])
  @test_throws ErrorException sheaf_section_basis(O, 0;
                                                   tail_degree=1,
                                                   denominator=xother)
end

@testset "anticanonical map for rational normal curves" begin
  R2, (x0, x1, x2) = graded_polynomial_ring(QQ, [:x0, :x1, :x2])
  OC = quotient_ring_as_module(ideal(R2, [x0*x2 - x1^2]))
  Bconic = sheaf_section_basis(OC, 1; tail_degree=1, verify=true)
  @test length(Bconic) == 3
  @test isone(section_denominator(Bconic))
  @test Set(projective_coordinates(Bconic)) == Set(gens(R2))

  R3, (X0, X1, X2, X3) = graded_polynomial_ring(QQ, [:x0, :x1, :x2, :x3])
  F = graded_free_module(R3, 3)
  e0, e1, e2 = gens(F)
  rels = [
    X1*e0 - X0*e1,
    X2*e0 - X1*e1,
    X1*e1 - X0*e2,
    X3*e0 - X2*e1,
    X2*e1 - X1*e2,
    X3*e1 - X2*e2,
  ]
  MminusK, _ = quo(F, rels)
  B0 = sheaf_section_basis(MminusK, 0; tail_degree=0, verify=true)
  @test length(B0) == 3
  @test Set(section_numerators(B0)) == Set([e0, e1, e2])
  Btail = sheaf_section_basis(MminusK, 0; tail_degree=1, denominator=X0, verify=true)
  @test length(Btail) == 3
  @test section_denominator(Btail) == X0
  @test Set(section_numerators(Btail)) == Set([X0*e0, X0*e1, X0*e2])
end

@testset "pluricanonical map for complete intersection surface" begin
  R, (x0, x1, x2, x3, x4) = graded_polynomial_ring(QQ, [:x0, :x1, :x2, :x3, :x4])
  Q = x0^2 + x1^2 + x2^2 + x3^2 + x4^2
  F4 = x0^4 + x1^4 + x2^4 + x3^4 + x4^4
  OX = quotient_ring_as_module(ideal(R, [Q, F4]))

  @test length(sheaf_section_basis(OX, 1; tail_degree=1, verify=true)) == 5
  @test length(sheaf_section_basis(OX, 2; tail_degree=2, verify=true)) == 14
  @test length(sheaf_section_basis(OX, 3; tail_degree=3, verify=true)) == 30

  B2 = sheaf_section_basis(OX, 2; tail_degree=2, verify=true)
  @test length(projective_coordinates(B2)) == 14
end

@testset "BGG sections of a presented line bundle" begin
  # Scalarize a redundant two-generator presentation of O(1) into map coordinates.
  P = projective_space(QQ, [:X, :Y, :Z])
  S = homogeneous_coordinate_ring(P)
  X, Y, Z = gens(S)
  G = grading_group(S)
  e = G[1]
  z = zero(G)
  A = embedded_divisor_ambient(S; projective=true)

  F = graded_free_module(S, [-e, z])
  M, _ = quo(F, [F[2] - X*F[1]])
  B = sheaf_section_basis(M, 0; verify=true)
  @test_throws ErrorException projective_coordinates(B)

  T = rank_one_module_trivialization(A, M)
  C = trivialized_section_basis(B, T)
  @test length(C) == 3
  @test Set(section_numerators(C)) == Set([X, Y, Z])
  @test is_one(section_denominator(C))
  @test trivialization_numerator(T, M[2]) == X
  @test underlying_section_basis(C) === B
  @test section_trivialization(C) === T

  phi = rational_map(P, P, projective_coordinates(C))
  @test domain(phi) === P
  @test codomain(phi) === P

  TX = rank_one_module_trivialization(A, M, [one(S), X];
                                      denominator=X, cleanup=:none)
  CX = trivialized_section_basis(B, TX)
  @test projective_coordinates(CX) == projective_coordinates(C)
  @test section_denominator(CX) == X

  Tbad = rank_one_module_trivialization(A, M, [one(S), Y]; cleanup=:none)
  @test_throws ErrorException trivialization_numerator(Tbad, M[1])
  @test_throws ErrorException trivialized_section_basis(B, Tbad)

  Cdirect = trivialized_section_basis(A, M, 0; verify=true)
  @test Set(projective_coordinates(Cdirect)) == Set([X, Y, Z])

  Ared = embedded_divisor_ambient(ideal(S, [X*Y]); projective=true)
  Mred = quotient_ring_as_module(coordinate_ideal(Ared))
  @test_throws ErrorException sheaf_section_basis(Mred, 0;
                                                   tail_degree=1,
                                                   denominator=X)
  Bred = sheaf_section_basis(Mred, 0; tail_degree=1, denominator=Z)
  Tred = rank_one_module_trivialization(Ared, Mred, [one(S)];
                                        denominator=X, cleanup=:none)
  @test_throws ErrorException trivialized_section_basis(Bred, Tred)
end
