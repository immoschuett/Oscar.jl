###############################################################################
###############################################################################
### Definition and constructors
###############################################################################
###############################################################################


# We introduce this abstract (hidden) type to allow for other objects to be
# used like polyhedral fans without duplicating too much code, concretely we
# want to be able to directly access rays, maximal_cones, etc for
# NormalToricVariety's.
abstract type _FanLikeType{T} end

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

julia> is_complete(PF)
true
"""
struct PolyhedralFan{T} <:_FanLikeType{T}
   pm_fan::Polymake.BigObject
   
   PolyhedralFan{T}(pm::Polymake.BigObject) where T<:scalar_types = new{T}(pm)
end

# default scalar type: `fmpq`
PolyhedralFan(x...; non_redundant::Bool = false) = PolyhedralFan{fmpq}(x...; non_redundant = non_redundant)

# Automatic detection of corresponding OSCAR scalar type;
# Avoid, if possible, to increase type stability
PolyhedralFan(p::Polymake.BigObject) = PolyhedralFan{detect_scalar_type(PolyhedralFan, p)}(p)

@doc Markdown.doc"""
    PolyhedralFan{T}(Rays, Cones; non_redundant = false) where T<:scalar_types

# Arguments
- `Rays::MatrixUnion`: Rays generating the cones of the fan; encoded row-wise as representative vectors.
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
function PolyhedralFan{T}(Rays::MatrixUnion, Incidence::IncidenceMatrix; non_redundant::Bool = false) where T<:scalar_types
   if non_redundant
      return PolyhedralFan{T}(Polymake.fan.PolyhedralFan{scalar_type_to_polymake[T]}(
         RAYS = Rays,
         MAXIMAL_CONES = Incidence,
      ))
   else
      return PolyhedralFan{T}(Polymake.fan.PolyhedralFan{scalar_type_to_polymake[T]}(
         INPUT_RAYS = Rays,
         INPUT_CONES = Incidence,
      ))
   end
end
function PolyhedralFan{T}(Rays::MatrixUnion, LS::MatrixUnion, Incidence::IncidenceMatrix; non_redundant::Bool = false) where T<:scalar_types
   if non_redundant
      return PolyhedralFan{T}(Polymake.fan.PolyhedralFan{scalar_type_to_polymake[T]}(
         RAYS = Rays,
         LINEALITY_SPACE = LS,
         MAXIMAL_CONES = Incidence,
      ))
   else
      return PolyhedralFan{T}(Polymake.fan.PolyhedralFan{scalar_type_to_polymake[T]}(
         INPUT_RAYS = Rays,
         INPUT_LINEALITY = LS,
         INPUT_CONES = Incidence,
      ))
   end
end

"""
    pm_object(PF::PolyhedralFan)

Get the underlying polymake object, which can be used via Polymake.jl.
"""
pm_object(PF::PolyhedralFan) = PF.pm_fan

PolyhedralFan(itr::AbstractVector{Cone{T}}) where T<:scalar_types = PolyhedralFan{T}(Polymake.fan.check_fan_objects(pm_object.(itr)...))

#Same construction for when the user gives Matrix{Bool} as incidence matrix
function PolyhedralFan{T}(Rays::MatrixUnion, LS::MatrixUnion, Incidence::Matrix{Bool}) where T<:scalar_types
   PolyhedralFan(Rays, LS, IncidenceMatrix(Polymake.IncidenceMatrix(Incidence)))
end
function PolyhedralFan{T}(Rays::MatrixUnion, Incidence::Matrix{Bool}) where T<:scalar_types
   PolyhedralFan(Rays, IncidenceMatrix(Polymake.IncidenceMatrix(Incidence)))
end


function PolyhedralFan(C::Cone{T}) where T<:scalar_types
    pmfan = Polymake.fan.check_fan_objects(pm_object(C))
    return PolyhedralFan{T}(pmfan)
end

###############################################################################
###############################################################################
### Display
###############################################################################
###############################################################################
function Base.show(io::IO, PF::PolyhedralFan{T}) where T<:scalar_types
    print(io, "A polyhedral fan in ambient dimension $(ambient_dim(PF))")
    T != fmpq && print(io, " with $T type coefficients")
end
