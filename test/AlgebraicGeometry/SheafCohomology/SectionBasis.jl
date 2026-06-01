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
