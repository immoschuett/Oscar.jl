################################################################################
# fmpz
@registerSerializationType(fmpz)

function save_internal(s::SerializerState, z::fmpz)
    return string(z)
end

function load_internal(s::DeserializerState, ::Type{fmpz}, str::String)
    return fmpz(str)
end


################################################################################
# fmpq
@registerSerializationType(fmpq)

function save_internal(s::SerializerState, q::fmpq)
    return Dict(
        :num => save_type_dispatch(s, numerator(q)),
        :den => save_type_dispatch(s, denominator(q))
    )
end

function load_internal(s::DeserializerState, ::Type{fmpq}, q::Dict)
    return fmpq(load_type_dispatch(s, fmpz, q[:num]),
                load_type_dispatch(s, fmpz, q[:den]))
end

################################################################################
# Number
@registerSerializationType(Int8)
@registerSerializationType(Int16)
@registerSerializationType(Int32)
@registerSerializationType(Int64, "Base.Int")
@registerSerializationType(Int128)

@registerSerializationType(UInt8)
@registerSerializationType(UInt16)
@registerSerializationType(UInt32)
@registerSerializationType(UInt64)
@registerSerializationType(UInt128)

@registerSerializationType(BigInt)

@registerSerializationType(Float16)
@registerSerializationType(Float32)
@registerSerializationType(Float64)

function save_internal(s::SerializerState, z::Number)
    return string(z)
end

function load_internal(s::DeserializerState, ::Type{T}, str::String) where {T<:Number}
    return parse(T, str)
end


################################################################################
# Strings
@registerSerializationType(String)

function save_internal(s::SerializerState, str::String)
    return str
end

function load_internal(s::DeserializerState, ::Type{String}, str::String)
    return str
end


################################################################################
# Symbol
@registerSerializationType(Symbol)

function save_internal(s::SerializerState, sym::Symbol)
   return string(sym)
end

function load_internal(s::DeserializerState, ::Type{Symbol}, str::String)
   return Symbol(str)
end
