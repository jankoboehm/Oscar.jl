###############################################################################
###############################################################################
### Definition and constructors
###############################################################################
###############################################################################

@doc Markdown.doc"""
    PolyhedralFan(Rays::Union{Oscar.MatElem, AbstractMatrix, SubObjectIterator}, [LS::Union{Oscar.MatElem, AbstractMatrix, SubObjectIterator},] Cones::IncidenceMatrix)

A polyhedral fan formed from rays and cones made of these rays.

`Rays` is given row-wise as representative vectors, with lineality generated by
the rows of `LS`. The cones are given as an IncidenceMatrix, where the columns
represent the rays and the rows represent the cones. There is a `1` at position
`(i,j)` if cone `i` has ray `j` as a generator, otherwise there is a `0`.

# Examples
This fan divides the plane into the four quadrants, its maximal cones which are
generated by $\{ \pm e_1, \pm e_2 \}$.
```jldoctest
julia> Rays = [1 0; 0 1; -1 0; 0 -1];

julia> Cones = IncidenceMatrix([[1, 2], [1, 4], [3, 2], [3, 4]])
4×4 Matrix{Bool}:
 1  1  0  0
 1  0  0  1
 0  1  1  0
 0  0  1  1

julia> PF = PolyhedralFan(Rays, Cones)
A polyhedral fan in ambient dimension 2

julia> iscomplete(PF)
true
"""
struct PolyhedralFan
   pm_fan::Polymake.BigObject
   function PolyhedralFan(pm::Polymake.BigObject)
      return new(pm)
   end
end

@doc Markdown.doc"""
    PolyhedralFan(Rays, Cones)

# Arguments
- `R::Matrix`: Rays generating the cones of the fan; encoded row-wise as representative vectors.
- `Cones::IncidenceMatrix`: An incidence matrix; there is a 1 at position (i,j) if cone i has ray j as extremal ray, and 0 otherwise.

A polyhedral fan formed from rays and cones made of these rays. The cones are
given as an IncidenceMatrix, where the columns represent the rays and the rows
represent the cones.

# Examples
To obtain the upper half-space of the plane:
```jldoctest
julia> R = [1 0; 1 1; 0 1; -1 0; 0 -1];

julia> IM=IncidenceMatrix([[1,2],[2,3],[3,4],[4,5],[1,5]]);

julia> PF=PolyhedralFan(R,IM)
A polyhedral fan in ambient dimension 2
```
"""
function PolyhedralFan(Rays::Union{SubObjectIterator{<:RayVector}, Oscar.MatElem,AbstractMatrix}, Incidence::IncidenceMatrix)
   PolyhedralFan(Polymake.fan.PolyhedralFan{Polymake.Rational}(
      INPUT_RAYS = Rays,
      INPUT_CONES = Incidence,
   ))
end
function PolyhedralFan(Rays::Union{SubObjectIterator{<:RayVector}, Oscar.MatElem,AbstractMatrix}, LS::Union{SubObjectIterator{<:RayVector}, Oscar.MatElem,AbstractMatrix}, Incidence::IncidenceMatrix)
   PolyhedralFan(Polymake.fan.PolyhedralFan{Polymake.Rational}(
      INPUT_RAYS = Rays,
      INPUT_LINEALITY = LS,
      INPUT_CONES = Incidence,
   ))
end

"""
    pm_object(PF::PolyhedralFan)

Get the underlying polymake object, which can be used via Polymake.jl.
"""
pm_object(PF::PolyhedralFan) = PF.pm_fan

PolyhedralFan(itr::AbstractVector{Cone}) = PolyhedralFan(Polymake.fan.check_fan_objects(pm_object.(itr)...))

#Same construction for when the user gives Matrix{Bool} as incidence matrix
function PolyhedralFan(Rays::Union{SubObjectIterator{<:RayVector}, Oscar.MatElem, AbstractMatrix}, LS::Union{Oscar.MatElem, AbstractMatrix}, Incidence::Matrix{Bool})
   PolyhedralFan(Rays, LS, IncidenceMatrix(Polymake.IncidenceMatrix(Incidence)))
end
function PolyhedralFan(Rays::Union{SubObjectIterator{<:RayVector}, Oscar.MatElem, AbstractMatrix}, Incidence::Matrix{Bool})
   PolyhedralFan(Rays, IncidenceMatrix(Polymake.IncidenceMatrix(Incidence)))
end


function PolyhedralFan(C::Cone)
    pmfan = Polymake.fan.check_fan_objects(pm_object(C))
    return PolyhedralFan(pmfan)
end

###############################################################################
###############################################################################
### Display
###############################################################################
###############################################################################
function Base.show(io::IO, PF::PolyhedralFan)
    print(io, "A polyhedral fan in ambient dimension $(ambient_dim(PF))")
end
