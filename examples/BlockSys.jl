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


################################################################################################################################
# basic tree with unlimited children per node, inpush updated paths to all leaves
# ids are updated during puhses, nodes are stored by id in a Dict
# acces via node-id. 
################################################################################################################################
mutable struct Node
  parent::Union{Int64,Missing}
  children::Vector{Int64}
  nchildren::Int64
  value::Any   #later d,n and Vector here
  path::Vector{Int64}  #<- TODO new type path with attributes length and nodeids etc...
end
mutable struct Tree  
  nodes::Dict{Int64, Node}
  nnodes::Int64
end 
function Tree(value)
  return Tree(Dict(zip([1],[Node(missing,Vector{Int64}(),0,value,[1])])),1)
end 
function root(T::Tree)
  return T.nodes[1]
end
function pushchild!(tree::Tree, parentid::Int , value::Any)
  1 <= parentid <= tree.nnodes || throw(BoundsError(tree,parentid))
  tree.nnodes += 1
  push!(tree.nodes[parentid].children,tree.nnodes) # add child id to parents child array
  tree.nodes[parentid].nchildren+=1     # add child counter
  push!(tree.nodes,(tree.nnodes => Node(parentid,Vector{Int64}(),0,value,vcat(tree.nodes[parentid].path,tree.nnodes)))) # push new child to the Dictionary & Update path
  return tree
end
function isroot(n::Node)
  typeof(n.parent) == Missing || return false 
  return true 
end 
function isleaf(n::Node)
  n.children == Vector{Int64}() || return false
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
function read_path(T::Tree,p,Cyc::Vector{Vector{Int64}},Info=0) # where p::path is the path along we want to generate blocksys, Cyc is the array of disjoint Cycles, Info is some extra TODO to avoid generating wrong pps.
  # return a List of all possible blocksys corresponding to this path
  #= 
    TODO implement this function as iterator for new type (just go along the tree and "twistcombine" from state to state)
  =#
  L = []
  for node in p 
    node != 1 || continue
    println(node)
    nv = T.nodes[node].value   # (d,k) => List of used cyc
    key = nv[1]
    Used_cyc = nv[2]
    Used_elem = []
    for used_cyc in Used_cyc
      Used_elem = union(Used_elem,Cyc[used_cyc])
    end 
      #= 
        WARNING here is still a bug, (we only merge some bs incorrectly)
        Hier noch Nach cyclen in Cyc trennen und (d,k) explizit verwenden!!
      =#
    # append results to the last of elements in L (if L = [] generate new)
    if L == []
      for bs in Hecke.subsets(Used_elem,divexact(key[1],key[2]))    # pick d / k Elements from used cycleset
        push!(L,bs)
      end
    else 
      # append on each element each new bs (copy and push) 

      D = []   # temporary naive slow solutione here
      for bs in Hecke.subsets(Used_elem,divexact(key[1],key[2]))    # pick d / k Elements from used cycleset
        for bsl in L 
          push!(D,vcat(bsl,bs))
        end 
      end
      L = deepcopy(D)
    end 
  end 
  return L 
end 
function all_subsets(value,k,D,min,checkset)# naive brute force variant. suff. for subsets in Klüners algorithm. where D Dictionary with A -> n_a 
  #=
   TODO later: combinatorical optimization here. This is kind of partition problem finding all cycles that gives a block combined with k of blocksize d
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
    if !(min in set)  # fixed one in recursion
      continue
    end
    if value == sum(D[i] for i in set )
      push!(L,collect(set))
    end 
  end 
  return L 
end 
function recursion!(T,n,N_i,set,compset,deep)
  L = []
  v = minimum(set) # fix value on recursion start (v = 1) # contained in first block
  for d in divisors(n)
    for k in divisors(d)
      value = d*k
      S_A = all_subsets(value,k,N_i,v,set)#return Cyc
      for generated_set in S_A
        temp = [[d,k],collect(generated_set)]
        println("push:")
        T = pushchild!(T,deep,([d,k] => collect(generated_set))) 
        compset2 = generated_set
        set2 = setdiff(set,compset2)
        if !isempty(set2)
          println("recursion:")
          S_R,T = recursion!(T,n,N_i,set2,compset2,deep+1)  # TODO later only T here , we can manage the content of L with parents of nodes of T
          temp = push!(temp,collect(S_R))
        end
        L = push!(L,temp)
      end
      if d == n# pick d/k elementes from the cycle and return it
        return L,T # TODO later only T here
      end
    end
  end
end
function all_blocksys_naive(C::Oscar.GaloisGrp.GaloisCtx{Hecke.qAdicRootCtx}) # change signature and function name (after i fixed my new BS type)
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
  T = Tree(0)
  recursion!(T,n,N_i,set,compset,1)
  return T 
  # returns the blocksys structure Tree 
end

#Also good idea:
#
# find all pos. blocks cont 1: update in a BST (by Orbits of perm.) During iter we can avoid doublecheck and recalc orbits due to the tree struct.
