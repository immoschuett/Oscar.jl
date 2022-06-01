module BlockSys

using Oscar

struct BlockSystems
  n::Int
  l::Int
  cur::Vector{Vector{Int}}
  function BlockSystems(n::Int, l::Int)
    @assert n % l == 0
    return new(n, l, [collect((i-1)*l+1:i*l) for i=1:divexact(n, l)])
  end
end

function Base.iterate(B::BlockSystems)
  return B.cur, deepcopy(B.cur)
end

function Base.iterate(B::BlockSystems, st::Array{Vector{Int}})
  if B.l==1||B.l==B.n
    return nothing
  end
  i = length(B.cur)-1
  while true
    j = B.l
    while true
      if st[i][j] < B.n - B.l + j
        st[i][j] += 1
        free = Set(1:B.n)
        for l=1:i-1
          setdiff!(free, st[l])
        end
        if !(st[i][j] in free) 
          continue
        end
        if length(intersect(free, Set(st[i][j]+1:B.n)))<B.l-j
          continue
        end
        setdiff!(free, st[i][1:j])
        while j < B.l
          j += 1
          I = intersect(free, Set(st[i][j-1]:B.n))
          if isempty(I)
            break
          end
          st[i][j] = minimum(I)
          pop!(free, st[i][j])
        end
        i += 1
        while i <= length(st)
          for j=1:B.l
            st[i][j] = minimum(free)
            pop!(free, st[i][j])
          end
          i += 1
        end
        return deepcopy(st), st
      end
      j -= 1
      if j == 1
        i -= 1
        i == 0 && return nothing
        break
      end
    end
  end
end
Base.IteratorSize(::BlockSystems) = Base.SizeUnknown()

function collect_subfields(C::Oscar.GaloisGrp.GaloisCtx{Hecke.qAdicRootCtx})
  SFList = []
  K, _ = number_field(C.f)
  S = Oscar.GaloisGrp.SubfieldLattice(K, C)
  n = degree(C.f)
  Rts = roots(C,7)
  cyc = gap_perm([findfirst(y -> y == x, Rts) for x = map(frobenius,Rts)])
  BL = []
  for d in divisors(n)
    for bls in BlockSystems(n,d)
      #!isinvar(bls,cyc) || push!(BL,bls) + Herer seems to be a bug. cons. 
      # A = [[1, 3], [2, 5], [4, 6]], cyc = (1 2)(3 4)(5 6)
      # this is not inv. but gices nontriv. Field with... Oscar.GaloisGrp.subfield(S, A)
      push!(BL,bls) 
    end 
  end
  VBS = [] # valid blocksystems
  TVBS = []# Temp updated VBS
  SF = Nothing()
  for bls in BL 
      !istriv(bls) || continue
      # pseudotest with VBS
      SF = Oscar.GaloisGrp.subfield(S, bls)
      # update SF
      if typeof(SF) == Tuple{AnticNumberField, NfToNfMor} # i.e not equal nothing
        if !isinvar(bls,cyc)
          println(bls)
        end
        push!(SFList,SF)
        push!(TVBS,bls)
      end
      #update info
      # if TVBS != [] end 
  end 
  return SFList
end

function isinvar(bls,cyc)
  #return true if no contradiction with cyc
  for bl in bls
    Set(cyc.(bl)) in Set.(bls) || return false 
  end 
  return true 
end
function istriv(bls)
  length(bls)!=1 || return true
  iszero(length.(bls).-1) ? (return true) : (return false)  
end
end

#TODOSTUFF implement Klüners combinatorical choices to directly include the cyc and reduce many many iterations

function all_subsets(value,k,D)
  # Dictionary with A -> n_a
  #=
   TODO later: combinatorical optimization here.
   this is kind of partition problem 
   finding all cycles that gives a block combined with k
   keyset for 
  =#

  keyset = Set() # keyset ( k | n_a)
  for key in keys(D)
    if D[key]%k == 0
      push!(keyset,key)
    end
  end 
  S = Hecke.subsets(keyset)
  L = Set()
  for set in S 
    if set == Set()
      continue
    end
    if value == sum(D[i] for i in set ) && 
      push!(L,set)
    end 
  end 

  return L 
end 
  
function all_blocksys_naive(C)
  Rts = roots(C,7)
  cyc = gap_perm([findfirst(y -> y == x, Rts) for x = map(frobenius,Rts)])
  l =  sum(cl for (_,cl) in cycle_structure(cyc))
  # .... 
  
end

#Also good idea:
#
# find alll pos blocks:
# bin. Search tree T, 
# update Orbits (of perm.)
# iter through T (avoids doubles orbit calc.)
# 
#
