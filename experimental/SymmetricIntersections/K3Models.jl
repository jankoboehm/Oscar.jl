export possible_ideals_for_cubics
export possible_ideals_for_k3

function _subgroup_trivial_action_on_H20(chi1::Oscar.GAPGroupClassFunction, chi2::Oscar.GAPGroupClassFunction)
  @assert chi1.table === chi2.table
  h =  conjugacy_classes(chi1.table)
  dchi1 = det(chi1)
  dchi2 = det(chi2)
  ker = elem_type(chi1.table.GAPGroup)[]
  for i in 1:length(h)
    if dchi1[i] == dchi2[i]
      append!(ker, collect(h[i]))
    end
  end
  ker, _ = sub(chi1.table.GAPGroup, ker)
  return ker
end

function _symplectic_subgroup_k3(chi1::Oscar.GAPGroupClassFunction, chi2::Oscar.GAPGroupClassFunction, p::GAPGroupHomomorphism)
  ker = _subgroup_trivial_action_on_H20(chi1, chi2)
  return p(ker)[1]
end

@doc Markdown.doc"""
    possible_ideals_for_k3(G::Oscar.GAPGroup, Gs::Oscar.GAPGroup, n::Int, d::Int, t::Int)
                                     -> Vector{Tuple{ProjRep, Vector{SymmetricIntersections}}}

Given two small groups $Gs < G$ and three integers `n`, `d` and `t`, return parameter spaces
for ideals generated by `t` homogeneous polynomials of degree `d` in `n` variables defining
K3 surface fixed under an action of $G$ on $\mathbb{P}^{n-1}$ and whose normal subgroup
of symplectic automorphisms is isomorphic to $G_s$.

The output is given in terms a tuple $(prep, symci)$ where `prep` is a faithful projective
representation of $G$ on $\mathbb{C}^n$ and 'symci' is a vector of parameter spaces of ideals
satisfying the previous requirements, one for each possible induced action of $G$ on a set
of generators.

Only the projective representation of `G` fixing a K3 surface with symplectic action given
by $G_s$ are computed (using characters).

Note: for now this is only available for $(n,d,t) = (4,4,1), (6,2,3)$.
"""
function possible_ideals_for_k3(G::Oscar.GAPGroup, Gs::Oscar.GAPGroup, n::Int, d::Int, t::Int)
  bool, RR, sum_index, p = _has_pfr(G, n)
  if bool == false
    return Tuple{ProjRep, Vector{SymmetricIntersections}}[]
  end
  @info "$(length(sum_index)) possible action(s) to consider"
  F = base_field(RR)
  S, _ = grade(polynomial_ring(F, "x" => 0:n-1)[1])
  _, j = homogeneous_component(S, d)
  E = underlying_group(RR)
  Irr = irreducible_characters_underlying_group(RR)
  res = Tuple{ProjRep, Vector{SymmetricIntersections}}[]
  for l in sum_index
    @info "Test a character"
    chi = sum(Irr[l])
    chid = symmetric_power(conj(chi), d)
    ct = constituents(chid, t)
    chis = Oscar.GAPGroupClassFunction[]
    for chi2 in ct
      H = _symplectic_subgroup_k3(chi, chi2)
      if is_isomorphic(H, Gs)
        push!(chis, chi2)
      end
    end
    length(chis) == 0 ? continue : nothing
    @info "$(length(chis)) possibility.ies"
    rep = affording_representation(RR, chi)
    poss = CharGrass[character_grassmannian(homogeneous_polynomial_representation(rep, d), nu) for nu in chis]
    prep = projective_representation(rep, p, check=false)
    poss = SymInter[symmetric_intersections(prep, M, j) for M in poss]
    push!(res, (prep, poss))
  end
  return res
end

@doc Markdown.doc"""
    possible_ideals_for_k3(G::Oscar.GAPGroup n::Int, d::Int, t::Int)
                                     -> Vector{Tuple{ProjRep, Vector{SymmetricIntersections}}}

Given a small group `G` and three integers `n`, `d` and `t`, return parameter spaces
for ideals generated by `t` homogeneous polynomials of degree `d` in `n` variables defining
K3 surface fixed under an action of $G$ on $\mathbb{P}^{n-1}$ which acts symplectically.

The output is given in terms a tuple $(prep, symci)$ where `prep` is a faithful projective
representation of $G$ on $\mathbb{C}^n$ and 'symci' is a vector of parameter spaces of ideals
satisfying the previous requirements, one for each possible induced action of $G$ on a set
of generators.

Only the projective representation of `G` fixing a K3 surface with a symplectic action
are computed (using characters).

Note: for now this is only available for $(n,d,t) = (4,4,1), (6,2,3)$.
"""
function possible_ideals_for_k3(G::Oscar.GAPGroup, n::Int, d::Int, t::Int)
  bool, RR, sum_index, p = _has_pfr(G, n)
  !bool && (return Tuple{ProjRep, Vector{SymmetricIntersections}}[])
  @info "$(length(sum_index)) possible actions to consider"
  F = base_field(RR)
  S, _ = grade(polynomial_ring(F, "x" => 0:n-1)[1])
  _, j = homogeneous_component(S, d)
  E = underlying_group(RR)
  Irr = irreducible_characters_underlying_group(RR)
  res = Tuple{ProjRep, Vector{SymmetricIntersections}}[]
  for l in sum_index
    @info "Test a character"
    chi = sum(Irr[l])
    detchi = det(chi)
    chid = symmetric_power(conj(chi), d)
    ct = constituents(chid, t)
    chis = Oscar.GAPGroupClassFunction[]
    for chi2 in ct
      detchi2 = det(chi2)
      if detchi == detchi2
        push!(chis, chi2)
      end
    end
    length(chis) == 0 && continue
    @info "$(length(chis)) possibility.ies"
    rep = affording_representation(RR, chi)
    poss = CharGrass[character_grassmannian(homogeneous_polynomial_representation(rep, d), nu) for nu in chis]
    prep = projective_representation(rep, p, check=false)
    poss = SymInter[symmetric_intersections(prep, M, j) for M in poss]
    push!(res, (prep, poss))
  end
  return res
end

@doc Markdown.doc"""
    possible_ideals_for_cubics(G::Oscar.GAPGroup)
                                     -> Vector{Tuple{ProjRep, Vector{SymmetricIntersections}}}

Given a small group `G`, return parameter spaces for ideals generating cubic fourfolds fixed under
an action of $G$ on $\mathbb{P}^{5}$ which acts symplectically.

The output is given in terms a tuple $(prep, symci)$ where `prep` is a faithful projective
representation of $G$ on $\mathbb{C}^6$ and 'symci' is a vector of parameter spaces of ideals
satisfying the previous requirements, one for each possible induced action of $G$ on a generator.

Only the projective representation of `G` fixing a cubic fourfold with a symplectic action
are computed (using characters).
"""
function possible_ideals_for_cubics(G::Oscar.GAPGroup)
  bool, RR, sum_index, p = _has_pfr(G, 6)
  !bool && return Tuple{ProjRep, Vector{SymmetricIntersections}}[]
  @info "$(length(sum_index)) possible actions to consider"
  F = base_field(RR)
  S, _ = grade(polynomial_ring(F, "x" => 0:5)[1])
  _, j = homogeneous_component(S, 3)
  E = underlying_group(RR)
  Irr = irreducible_characters_underlying_group(RR)
  res = Tuple{ProjRep, Vector{SymmetricIntersections}}[]
  for l in sum_index
    @info "Test a character"
    chi = sum(Irr[l])
    detchi = det(chi)
    chid = symmetric_power(conj(chi), 3)
    ct = constituents(chid, 1)
    chis = Oscar.GAPGroupClassFunction[]
    for chi2 in ct
      detchi2 = det(chi2)
      if detchi == detchi2*detchi2
        push!(chis, chi2)
      end
    end
    length(chis) == 0 && continue
    @info "$(length(chis)) possibility.ies"
    rep = affording_representation(RR, chi)
    poss = CharGrass[character_grassmannian(homogeneous_polynomial_representation(rep, 3), nu) for nu in chis]
    prep = projective_representation(rep, p, check=false)
    poss = SymInter[symmetric_intersections(prep, M, j) for M in poss]
    push!(res, (prep, poss))
  end
  return res
end

