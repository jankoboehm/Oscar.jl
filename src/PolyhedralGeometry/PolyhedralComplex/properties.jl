@doc Markdown.doc"""
    ambient_dim(PC::PolyhedralComplex)

Return the ambient dimension of `PC`.

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]])
2×4 IncidenceMatrix
[1, 2, 3]
[1, 3, 4]


julia> V = [0 0; 1 0; 1 1; 0 1]
4×2 Matrix{Int64}:
 0  0
 1  0
 1  1
 0  1

julia> PC = PolyhedralComplex(IM, V)
Polyhedral complex in ambient dimension 2

julia> ambient_dim(PC)
2
```
"""
ambient_dim(PC::PolyhedralComplex) = Polymake.fan.ambient_dim(pm_object(PC))::Int

# Alexej: The access functions for vertices/rays of polyhedra are used here.
# As long as everything (e.g. implementation of access, meaningful definition of matrix methods)
# is exactly the same, this can work, otherwise I suggest new access functions
# like `_vertex_complex`.

@doc Markdown.doc"""
    vertices([as::Type,] PC::PolyhedralComplex)

Return an iterator over the vertices of `PC` in the format defined by `as`.

Optional arguments for `as` include
* `PointVector`.

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> V = [0 0; 1 0; 1 1; 0 1];

julia> PC = PolyhedralComplex(IM, V)
Polyhedral complex in ambient dimension 2

julia> vertices(PC)
4-element SubObjectIterator{PointVector{QQFieldElem}}:
 [0, 0]
 [1, 0]
 [1, 1]
 [0, 1]

julia> matrix(QQ, vertices(PC))
[0   0]
[1   0]
[1   1]
[0   1]
```
"""
vertices(as::Type{PointVector{T}}, PC::PolyhedralComplex{T}) where T<:scalar_types = lineality_dim(PC) == 0 ? _vertices(as, PC) : _empty_subobjectiterator(as, pm_object(PC))
_vertices(as::Type{PointVector{T}}, PC::PolyhedralComplex) where T<:scalar_types = SubObjectIterator{as}(pm_object(PC), _vertex_polyhedron, length(_vertex_indices(pm_object(PC))))


function _all_vertex_indices(P::Polymake.BigObject)
    vi = Polymake.get_attachment(P, "_all_vertex_indices")
    if isnothing(vi)
        A = P.VERTICES
        vi = Polymake.Vector{Polymake.to_cxx_type(Int64)}(Vector(1:Polymake.nrows(A)))
        Polymake.attach(P, "_all_vertex_indices", vi)
    end
    return vi
end

function _vertex_or_ray_polyhedron(::Type{Union{PointVector{T}, RayVector{T}}}, P::Polymake.BigObject, i::Base.Integer) where T<:scalar_types
    A = P.VERTICES
    if iszero(A[_all_vertex_indices(P)[i],1])
        return RayVector{T}(@view P.VERTICES[_all_vertex_indices(P)[i], 2:end])
    else
        return PointVector{T}(@view P.VERTICES[_all_vertex_indices(P)[i], 2:end])
    end
end

_vertices(as::Type{Union{RayVector{T}, PointVector{T}}}, PC::PolyhedralComplex) where T<:scalar_types = SubObjectIterator{as}(pm_object(PC), _vertex_or_ray_polyhedron, length(_all_vertex_indices(pm_object(PC))))

vertices_and_rays(PC::PolyhedralComplex{T}) where T<:scalar_types = _vertices(Union{PointVector{T}, RayVector{T}}, PC)

_vector_matrix(::Val{_vertex_or_ray_polyhedron}, PC::Polymake.BigObject; homogenized = false) = homogenized ? PC.VERTICES : @view PC.VERTICES[:, 2:end]

_vertices(::Type{PointVector}, PC::PolyhedralComplex{T}) where T<:scalar_types = _vertices(PointVector{T}, PC)

vertices(PC::PolyhedralComplex{T}) where T<:scalar_types = vertices(PointVector{T}, PC)
_vertices(PC::PolyhedralComplex{T}) where T<:scalar_types = _vertices(PointVector{T}, PC)

_rays(as::Type{RayVector{T}}, PC::PolyhedralComplex) where T<:scalar_types = SubObjectIterator{as}(pm_object(PC), _ray_polyhedral_complex, length(_ray_indices_polyhedral_complex(pm_object(PC))))


rays(as::Type{RayVector{T}}, PC::PolyhedralComplex{T}) where T<:scalar_types = lineality_dim(PC) == 0 ? _rays(RayVector{T}, PC) : _empty_subobjectiterator(as, pm_object(PC))


@doc Markdown.doc"""
    rays_modulo_lineality(as, PC::PolyhedralComplex)

Return the rays of the recession cone of `PC` up to lineality as a `NamedTuple`
with two iterators. If `PC` has lineality `L`, then the iterator
`rays_modulo_lineality` iterates over representatives of the rays of `PC/L`.
The iterator `lineality_basis` gives a basis of the lineality space `L`.

# Examples
```jldoctest
julia> VR = [0 0 0; 1 0 0; 0 1 0; -1 0 0];

julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> far_vertices = [2,3,4];

julia> L = [0 0 1];

julia> PC = PolyhedralComplex(IM, VR, far_vertices, L)
Polyhedral complex in ambient dimension 3

julia> RML = rays_modulo_lineality(PC)
(rays_modulo_lineality = RayVector{QQFieldElem}[[1, 0, 0], [0, 1, 0], [-1, 0, 0]], lineality_basis = RayVector{QQFieldElem}[[0, 0, 1]])

julia> RML.rays_modulo_lineality
3-element SubObjectIterator{RayVector{QQFieldElem}}:
 [1, 0, 0]
 [0, 1, 0]
 [-1, 0, 0]

julia> RML.lineality_basis
1-element SubObjectIterator{RayVector{QQFieldElem}}:
 [0, 0, 1]
```
"""
rays_modulo_lineality(PC::PolyhedralComplex{T}) where T<:scalar_types = rays_modulo_lineality(NamedTuple{(:rays_modulo_lineality, :lineality_basis), Tuple{SubObjectIterator{RayVector{T}}, SubObjectIterator{RayVector{T}}}}, PC)
function rays_modulo_lineality(as::Type{NamedTuple{(:rays_modulo_lineality, :lineality_basis), Tuple{SubObjectIterator{RayVector{T}}, SubObjectIterator{RayVector{T}}}}}, PC::PolyhedralComplex) where T<:scalar_types
    return (
        rays_modulo_lineality = _rays(RayVector{T}, PC),
        lineality_basis = lineality_space(PC)
    )
end
rays_modulo_lineality(as::Type{RayVector{T}}, PC::PolyhedralComplex{T}) where T<:scalar_types = _rays(RayVector{T}, PC)


@doc Markdown.doc"""
    minimal_faces(as, PC::PolyhedralComplex)

Return the minimal faces of a polyhedral complex as a `NamedTuple` with two
iterators. For a polyhedral complex without lineality, the `base_points` are
the vertices. If `PC` has lineality `L`, then every minimal face is an affine
translation `p+L`, where `p` is only unique modulo `L`. The return type is a
dict, the key `:base_points` gives an iterator over such `p`, and the key
`:lineality_basis` lets one access a basis for the lineality space `L` of `PC`.

# Examples
```jldoctest
julia> VR = [0 0 0; 1 0 0; 0 1 0; -1 0 0];

julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> far_vertices = [2,3,4];

julia> L = [0 0 1];

julia> PC = PolyhedralComplex(IM, VR, far_vertices, L)
Polyhedral complex in ambient dimension 3

julia> MFPC = minimal_faces(PC)
(base_points = PointVector{QQFieldElem}[[0, 0, 0]], lineality_basis = RayVector{QQFieldElem}[[0, 0, 1]])

julia> MFPC.base_points
1-element SubObjectIterator{PointVector{QQFieldElem}}:
 [0, 0, 0]

julia> MFPC.lineality_basis
1-element SubObjectIterator{RayVector{QQFieldElem}}:
 [0, 0, 1]
```
"""
minimal_faces(PC::PolyhedralComplex{T}) where T<:scalar_types = minimal_faces(NamedTuple{(:base_points, :lineality_basis), Tuple{SubObjectIterator{PointVector{T}}, SubObjectIterator{RayVector{T}}}}, PC)
function minimal_faces(as::Type{NamedTuple{(:base_points, :lineality_basis), Tuple{SubObjectIterator{PointVector{T}}, SubObjectIterator{RayVector{T}}}}}, PC::PolyhedralComplex{T}) where T<:scalar_types
    return (
        base_points = _vertices(PointVector{T}, PC),
        lineality_basis = lineality_space(PC)
    )
end
minimal_faces(as::Type{PointVector{T}}, PC::PolyhedralComplex{T}) where T<:scalar_types = _vertices(PointVector{T}, PC)


@doc Markdown.doc"""
    rays(PC::PolyhedralComplex)

Return the rays of `PC`

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> VR = [0 0; 1 0; 1 1; 0 1];

julia> PC = PolyhedralComplex(IM, VR, [2])
Polyhedral complex in ambient dimension 2

julia> rays(PC)
1-element SubObjectIterator{RayVector{QQFieldElem}}:
 [1, 0]

julia> matrix(QQ, rays(PC))
[1   0]
```
"""
rays(PC::PolyhedralComplex{T}) where T<:scalar_types = rays(RayVector{T},PC)
_rays(PC::PolyhedralComplex{T}) where T<:scalar_types = _rays(RayVector{T},PC)

_ray_indices_polyhedral_complex(PC::Polymake.BigObject) = collect(Polymake.to_one_based_indexing(PC.FAR_VERTICES))

_ray_polyhedral_complex(::Type{RayVector{T}}, PC::Polymake.BigObject, i::Base.Integer) where T<:scalar_types = RayVector{T}(@view PC.VERTICES[_ray_indices_polyhedral_complex(PC)[i], 2:end])

_matrix_for_polymake(::Val{_ray_polyhedral_complex}) = _vector_matrix

_vector_matrix(::Val{_ray_polyhedral_complex}, PC::Polymake.BigObject; homogenized = false) = @view PC.VERTICES[_ray_indices_polyhedral_complex(PC), (homogenized ? 1 : 2):end]

_maximal_polyhedron(::Type{Polyhedron{T}}, PC::Polymake.BigObject, i::Base.Integer) where T<:scalar_types = Polyhedron{T}(Polymake.fan.polytope(PC, i-1))

_vertex_indices(::Val{_maximal_polyhedron}, PC::Polymake.BigObject) = PC.MAXIMAL_POLYTOPES[:, _vertex_indices(PC)]

_ray_indices(::Val{_maximal_polyhedron}, PC::Polymake.BigObject) = PC.MAXIMAL_POLYTOPES[:, _ray_indices_polyhedral_complex(PC)]

_vertex_and_ray_indices(::Val{_maximal_polyhedron}, PC::Polymake.BigObject) = PC.MAXIMAL_POLYTOPES


@doc Markdown.doc"""
    maximal_polyhedra(PC::PolyhedralComplex)

Return the maximal polyhedra of `PC`

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]])
2×4 IncidenceMatrix
[1, 2, 3]
[1, 3, 4]


julia> VR = [0 0; 1 0; 1 1; 0 1]
4×2 Matrix{Int64}:
 0  0
 1  0
 1  1
 0  1

julia> PC = PolyhedralComplex(IM, VR, [2])
Polyhedral complex in ambient dimension 2

julia> maximal_polyhedra(PC)
2-element SubObjectIterator{Polyhedron{QQFieldElem}}:
 Polyhedron in ambient dimension 2
 Polyhedron in ambient dimension 2
```
"""
maximal_polyhedra(PC::PolyhedralComplex{T}) where T<:scalar_types = SubObjectIterator{Polyhedron{T}}(pm_object(PC), _maximal_polyhedron, n_maximal_polyhedra(PC))


@doc Markdown.doc"""
    n_maximal_polyhedra(PC::PolyhedralComplex)

Return the number of maximal polyhedra of `PC`

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]])
2×4 IncidenceMatrix
[1, 2, 3]
[1, 3, 4]


julia> VR = [0 0; 1 0; 1 1; 0 1]
4×2 Matrix{Int64}:
 0  0
 1  0
 1  1
 0  1

julia> PC = PolyhedralComplex(IM, VR, [2])
Polyhedral complex in ambient dimension 2

julia> n_maximal_polyhedra(PC)
2
```
"""
n_maximal_polyhedra(PC::PolyhedralComplex) = pm_object(PC).N_MAXIMAL_POLYTOPES


@doc Markdown.doc"""
    is_simplicial(PC::PolyhedralComplex)

Determine whether the polyhedral complex is simplicial.

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> VR = [0 0; 1 0; 1 1; 0 1];

julia> PC = PolyhedralComplex(IM, VR)
Polyhedral complex in ambient dimension 2

julia> is_simplicial(PC)
true
```
"""
is_simplicial(PC::PolyhedralComplex) = pm_object(PC).SIMPLICIAL::Bool


@doc Markdown.doc"""
    is_pure(PC::PolyhedralComplex)

Determine whether the polyhedral complex is pure.

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> VR = [0 0; 1 0; 1 1; 0 1];

julia> PC = PolyhedralComplex(IM, VR)
Polyhedral complex in ambient dimension 2

julia> is_pure(PC)
true
```
"""
is_pure(PC::PolyhedralComplex) = pm_object(PC).PURE::Bool


@doc Markdown.doc"""
    dim(PC::PolyhedralComplex)

Compute the dimension of the polyhedral complex.

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> VR = [0 0; 1 0; 1 1; 0 1];

julia> PC = PolyhedralComplex(IM, VR)
Polyhedral complex in ambient dimension 2

julia> dim(PC)
2
```
"""
dim(PC::PolyhedralComplex) = Polymake.fan.dim(pm_object(PC))::Int

@doc Markdown.doc"""
    polyhedra_of_dim(PC::PolyhedralComplex, polyhedron_dim::Int)

Return the polyhedra of a given dimension in the polyhedral complex `PC`.

# Examples
```jldoctest
julia> IM = IncidenceMatrix([[1,2,3],[1,3,4]]);

julia> VR = [0 0; 1 0; 1 1; 0 1];

julia> PC = PolyhedralComplex(IM, VR);

julia> P1s = polyhedra_of_dim(PC,1)
5-element SubObjectIterator{Polyhedron{QQFieldElem}}:
 Polyhedron in ambient dimension 2
 Polyhedron in ambient dimension 2
 Polyhedron in ambient dimension 2
 Polyhedron in ambient dimension 2
 Polyhedron in ambient dimension 2

julia> for p in P1s
       println(dim(p))
       end
1
1
1
1
1
```
"""
function polyhedra_of_dim(PC::PolyhedralComplex{T}, polyhedron_dim::Int) where T<:scalar_types
    n = polyhedron_dim - lineality_dim(PC) + 1
    n < 0 && return nothing
    pfaces = Polymake.fan.cones_of_dim(pm_object(PC), n)
    nfaces = Polymake.nrows(pfaces)
    rfaces = Vector{Int64}()
    nfarf = 0
    farf = Polymake.to_one_based_indexing(pm_object(PC).FAR_VERTICES)
    for index in 1:nfaces
        face = Polymake.row(pfaces, index)
        if face <= farf
            nfarf += 1
        else
            append!(rfaces, index)
        end
    end
    return SubObjectIterator{Polyhedron{T}}(pm_object(PC), _ith_polyhedron, length(rfaces), (f_dim = n, f_ind = rfaces))
end

function _ith_polyhedron(::Type{Polyhedron{T}}, PC::Polymake.BigObject, i::Base.Integer; f_dim::Int = -1, f_ind::Vector{Int64} = Vector{Int64}()) where T<:scalar_types
    pface = Polymake.row(Polymake.fan.cones_of_dim(PC, f_dim), f_ind[i])
    return Polyhedron{T}(Polymake.polytope.Polytope{scalar_type_to_polymake[T]}(VERTICES = PC.VERTICES[collect(pface),:], LINEALITY_SPACE = PC.LINEALITY_SPACE))
end

lineality_space(PC::PolyhedralComplex{T}) where T<:scalar_types = SubObjectIterator{RayVector{T}}(pm_object(PC), _lineality_polyhedron, lineality_dim(PC))

lineality_dim(PC::PolyhedralComplex) = pm_object(PC).LINEALITY_DIM::Int


@doc Markdown.doc"""
    f_vector(PC::PolyhedralComplex)

Compute the vector $(f₀,f₁,f₂,...,f_{dim(PC))$` where $f_i$ is the number of
faces of $PC$ of dimension $i$.

# Examples
```jldoctest
julia> VR = [0 0; 1 0; -1 0; 0 1];

julia> IM = IncidenceMatrix([[1,2,4],[1,3,4]]);

julia> far_vertices = [2,3,4];

julia> PC = PolyhedralComplex(IM, VR, far_vertices);

julia> f_vector(PC)
3-element Vector{Int64}:
 1
 3
 2
```
"""
function f_vector(PC::PolyhedralComplex)
    ldim = lineality_dim(PC)
    f_vec=vcat(zeros(Int64, ldim), [length(polyhedra_of_dim(PC,i)) for i in ldim:dim(PC)])
    return f_vec
end


@doc Markdown.doc"""
    nrays(PC::PolyhedralComplex)

Return the number of rays of `PC`.

# Examples
```jldoctest
julia> VR = [0 0; 1 0; -1 0; 0 1];

julia> IM = IncidenceMatrix([[1,2,4],[1,3,4]]);

julia> far_vertices = [2,3,4];

julia> PC = PolyhedralComplex(IM, VR, far_vertices);

julia> nrays(PC)
3
```
"""
nrays(PC::PolyhedralComplex) = lineality_dim(PC) == 0 ? _nrays(PC) : 0
_nrays(PC::PolyhedralComplex) = length(pm_object(PC).FAR_VERTICES)


@doc Markdown.doc"""
    nvertices(PC::PolyhedralComplex)

Return the number of vertices of `PC`.

# Examples
```jldoctest
julia> VR = [0 0; 1 0; -1 0; 0 1];

julia> IM = IncidenceMatrix([[1,2,4],[1,3,4]]);

julia> far_vertices = [2,3,4];

julia> PC = PolyhedralComplex(IM, VR, far_vertices);

julia> nvertices(PC)
1
```
"""
nvertices(PC::PolyhedralComplex) = lineality_dim(PC) == 0 ? _nvertices(PC) : 0
_nvertices(PC::PolyhedralComplex) = pm_object(PC).N_VERTICES - _nrays(PC)


@doc Markdown.doc"""
    npolyhedra(PC::PolyhedralComplex)

Return the total number of polyhedra in the polyhedral complex `PC`.

# Examples
```jldoctest
julia> VR = [0 0; 1 0; -1 0; 0 1];

julia> IM = IncidenceMatrix([[1,2,4],[1,3,4]]);

julia> far_vertices = [2,3,4];

julia> PC = PolyhedralComplex(IM, VR, far_vertices);

julia> npolyhedra(PC)
6
```
"""
npolyhedra(PC::PolyhedralComplex) = sum(f_vector(PC))

@doc Markdown.doc"""
    codim(PC::PolyhedralComplex)

Compute the codimension of a polyhedral complex.

# Examples
```
julia> VR = [0 0; 1 0; -1 0; 0 1];

julia> IM = IncidenceMatrix([[1,2],[1,3],[1,4]]);

julia> far_vertices = [2,3,4];

julia> PC = PolyhedralComplex(IM, VR, far_vertices)
A polyhedral complex in ambient dimension 2

julia> codim(PC)
1
```
"""
codim(PC::PolyhedralComplex) = ambient_dim(PC)-dim(PC)


@doc Markdown.doc"""
    is_embedded(PC::PolyhedralComplex)

Return `true` if `PC` is embedded, i.e. if its vertices can be computed as a
subset of some $\mathbb{R}^n$.

# Examples
```jldoctest
julia> VR = [0 0; 1 0; -1 0; 0 1];

julia> IM = IncidenceMatrix([[1,2],[1,3],[1,4]]);

julia> PC = PolyhedralComplex(IM, VR)
Polyhedral complex in ambient dimension 2

julia> is_embedded(PC)
true
```
"""
function is_embedded(PC::PolyhedralComplex)
    pmo = pm_object(PC)
    schedule = Polymake.call_method(pmo,:get_schedule,"VERTICES")
    return schedule != nothing
end
