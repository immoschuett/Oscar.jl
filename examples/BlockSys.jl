module BlockSys
################################################################################################################################
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
################################################################################################################################
# collect_subfields (gives a list and its blocksystems(debbuging) for valid subfield structures)
################################################################################################################################
function collect_subfields(C::Oscar.GaloisGrp.GaloisCtx{Hecke.qAdicRootCtx},filterinvar=false)
  FieldList,BL = [],[]
  K, _ = number_field(C.f)
  S = Oscar.GaloisGrp.SubfieldLattice(K, C)
  n = degree(C.f)
  Rts = roots(C,7)
  cyc = gap_perm([findfirst(y -> y == x, Rts) for x = map(frobenius,Rts)])  # get the cyc from froeb.
  for d in divisors(n) # generate all possible blocksys.
    for bls in BlockSystems(n,d)
      if filterinvar   # Here seems to be a bug
        !isinvar(bls,cyc) || push!(BL,bls)
      else 
        push!(BL,bls) 
      end 
    end 
  end
##################################################################################################
  VB = [] # found valid blocksys
##################################################################################################
  for bls in BL
      SF = Nothing()
      !istriv(bls) || continue
      # pseudotest / other with VB
      #TODO
      SF = Oscar.GaloisGrp.subfield(S, bls)
      if typeof(SF) == Tuple{AnticNumberField, NfToNfMor} # i.e not equal nothing -> update SF
        push!(FieldList,(bls,SF))
        push!(VB,bls)
      end
  end 
  return FieldList
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
################################################################################################################################
# End Module
################################################################################################################################

#TODOSTUFF implement Klüners combinatorical choices to directly include the cyc and reduce many many iterations

# TODO Tree structure
function all_subsets(value,k,D,min,checkset)
  # Dictionary with A -> n_a
  #=
   TODO later: combinatorical optimization here.
   this is kind of partition problem 
   finding all cycles that gives a block combined with k
   keyset for 
  =#
  keyset = Set() # keyset ( k | n_a)
  for key in keys(D)
    if D[key]%k == 0 && key in checkset
      push!(keyset,key)
    end
  end 
  S = Hecke.subsets(keyset)
  L = []
  for set in S 
    if isempty(set)
      continue
    end
    if !(min in set)  # fixed one in rekursion
      continue
    end
    if value == sum(D[i] for i in set )
      push!(L,collect(set))
    end 
  end 
  return L 
end 

function all_blocksys_naive(C)
  Rts = roots(C,7)
  cyc = gap_perm([findfirst(y -> y == x, Rts) for x = map(frobenius,Rts)])
  n = degree(C.f)
  Cyc = map(collect,orbits(gset(sub(symmetric_group(n),[cyc])[1]))) 
  n_1 = length(Cyc[1])
  l = length(Cyc)
  A = Set{Int64}(2:l)
  Cyc_values = Dict(zip([i for i in 2:l],Cyc[2:l]))
  N_i = Dict(zip([i for i in 1:l],length.(Cyc)))
  set = Set([i for i in 1:l])
  compset = Set()
  return recursion(n,N_i,set,compset)
end

function recursion(n,N_i,set,compset)
  L = []
  v = minimum(set) # fix value on recursion start (v = 1) # contained in first block
  for d in divisors(n)
    for k in divisors(d)
      value = d*k
      S_A = all_subsets(value,k,N_i,v,set)#return Cyc
      println("d =  $d und k = $k")# return s.t dk = sum n_i
      println(S_A)
      for generated_set in S_A
        temp = [[d,k],collect(generated_set)]
        compset2 = generated_set
        set2 = setdiff(set,compset2)
        if !isempty(set2)
          S_R = recursion(n,N_i,set2,compset2)
          println("recursion:")
          println(set2)
          temp = push!(temp,collect(S_R))
        end
        L = push!(L,temp)
      end
      if d == n# pick d/k elementes from the cycle and return it
        return L
        # aktuell L ist der Bauplan für die möglichen Blocksysteme, die wir aus Cyc zusammensetzen können.
        # Hier wird dann jede mögliche Wahl der (d,k) Teilmengen von L_i von einem cycel iteriert.
        #return generate_blocksys(L,Cyc) 
        #TODO 
      end
    end
  end
end
function generate_blocksys(L,T) 
  #where A is a List of Subset of Powerset of { 1 .... l } for init-composing blocks with (d,k) entries.
  # T is the cycle decomposition
  B = []
  for array in L 
    B = vcat!(B,push_array(array,T))
  end 
  return B 
end 

#Also good idea:
#
# find all pos. blocks:
# bin. Search tree T, 
# update Orbits (of perm.)
# iter through T (avoids doubles orbit calc.)
# 
#


################################################################################################################################
# basic tree with unlimited children per node, inpush updated paths to all leaves
# ids are updated during puhses, nodes are stored by id in a Dict
# acces via id. 
################################################################################################################################
mutable struct Node
  parent::Union{Int64,Missing}
  childs::Vector{Int64}
  nchilds::Int64
  value::Any   #later d,n and Vector here
  path::Vector{Int64}
end
mutable struct Tree  
  nodes::Dict{Int64, Node}
  nnodes::Int64
end 
## basic stuff 
Tree(value) = Tree(Dict(zip([1],[Node(missing,Vector{Int64}(),0,value,[1])])),1)
root(T::Tree) = T.nodes[1]
function pushchild!(tree::Tree, parentid::Int , value::Any)
  1 <= parentid <= tree.nnodes || throw(BoundsError(tree, parentid))
  tree.nnodes += 1
  push!(tree.nodes[parentid].childs,tree.nnodes) # add child id to parents child array
  tree.nodes[parentid].nchilds+=1     # add child counter
  #push!(tree.nodes,(tree.nnodes => Node( parentid, Vector{Int64}(),0,value))) # push new child to the Dictionary
  push!(tree.nodes,(tree.nnodes => Node( parentid, Vector{Int64}(),0,value,vcat(T.nodes[parentid].path,tree.nnodes)))) # push new child to the Dictionary

end
function isroot(n::Node)
  typeof(n.parent) == Missing || return false 
  return true 
end 
function isleaf(n::Node)
  n.childs == Vector{Int64}() || return false
  return true 
end 
function all_root2leaf_paths(T::Tree)
  P = []
  for n_i in 1:T.nnodes
      !isleaf(T.nodes[n_i]) || push!(P,T.nodes[n_i].path) 
  end 
  return P
end
################################################################################################################################
### we want to give an iterator that iterates all paths from root to any leaf 
# output array with nodeid's for paths
# TODO iterate over leafs in preorder !
#=
all_root2leaf_paths(T)
T = Tree(123)
pushchild!(T,5,1121233123)
T.nodes
firstpath(T)
isleaf(T.nodes[1])
=#
