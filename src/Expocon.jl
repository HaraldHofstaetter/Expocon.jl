__precompile__()
module Expocon 

export MultiFor
export Lyndon, lyndon_words, graded_lyndon_words
export extend_by_rightmost_subwords
export commutator_length
export coeff, coeff_exp, coeffs_prod_exps
export order_conditions_splitting
export order_conditions_exponential
export order_conditions_exponential_legendre


immutable Lyndon
    s::Int
    n::Int
end

Base.start(::Lyndon) = Int[-1]

function Base.next(L::Lyndon, w::Vector{Int})
    if w == [-1]
        w[end] += 1
        return (copy(w), w)
    end
    m = length(w)
    while length(w) < L.n               
        push!(w, w[end-m+1])
    end
    while length(w) > 0 && w[end] == L.s - 1    
        pop!(w)
    end
    w[end] += 1
    (copy(w), w)
end
    
Base.done(L::Lyndon, w::Vector{Int}) = w == [L.s-1]

function lyndon_words(s::Integer, n::Integer)
    r = Array{Int,1}[]
    for l in Lyndon(s,n)
        push!(r, l)
    end
    sort(r, lt=(x,y)->length(x)<length(y))
end

function graded_lyndon_words(n::Integer)
    W = lyndon_words(2, n)
    W1 = Array{Int,1}[]
    for w in W
        if w!=[1]
            w1 = Int[]
            c=0
            for i in reverse(w)
                if i==0
                    push!(w1, c)
                    c = 0
                else
                    c+=1
                end
            end
            w1 = reverse(w1)    
            push!(W1, w1)
        end
    end    
    W1
end

function extend_by_rightmost_subwords(W::Array{Array{Int64,1},1})
    WW=Dict{Array{Int64,1},Int}(Int64[]=>1)
    for w in W 
        for l=1:length(w)
            WW[w[l:end]] = 1
        end
    end
    return sort(collect(keys(WW)), lt=(x,y)->length(x)<length(y))
end


commutator_length(C::Int) = 1

function commutator_length(C::Vector)
    if length(C)!=2
         error("not well-formed commutator")
    end
    commutator_length(C[1])+commutator_length(C[2])
end


function coeff{R}(W::Array{Int,1}, C::Int, g::Array{R,1}=[]) 
    if length(g)==0
        return length(W)==1&&W[1]==C?1:0    
    else
        return length(W)==1?1g[C]^W[1]:0     
    end
end


function coeff{R}(W::Array{Int,1}, C::Vector, g::Array{R,1}=[])
    if length(C)!=2
         error("not well-formed commutator")
    end
    l1 = commutator_length(C[1])
    l2 = commutator_length(C[2])
    if l1+l2 != length(W)
        return 0
    end
    (coeff(W[1:l1], C[1], g)*coeff(W[l1+1:end], C[2], g) -
     coeff(W[1:l2], C[2], g)*coeff(W[l2+1:end], C[1], g) )      
end


immutable MultiFor
    k::Array{Int,1}
end

Base.start(MF::MultiFor) = Int[]

Base.done(MF::MultiFor, k::Array{Int,1}) = MF.k==k

function Base.next(MF::MultiFor, k::Array{Int,1}) 
    if k==Int[]
        k = zeros(Int, length(MF.k))
        return(copy(k), k)
    end
    for i=1:length(k)
        if k[i]<MF.k[i]
            k[i] += 1
            for j = 1:i-1                 
                k[j] = 0       
            end
            return (copy(k), k)
        end
    end            
end


function coeff_exp{T,S,R}(W::Array{Int,1}, G::Array{Tuple{T,S},1}, g::Array{R,1}=[])
    r = length(W)
    if r==0
        return one(T)
    end
    K = length(G)
    C = [g[2] for g in G]
    x = [g[1] for g in G]
    l = commutator_length.(C)
    Q = div(r, minimum(l))
    c = zero(T)
    for q = 1:Q
        #println("q=",q," -----------------")
        for k = MultiFor((K-1)*ones(Int,q))
            cc = zero(T)
            s = sum([l[k1+1] for k1 in k])
            #println(k, " ", s)
            if s==r
                cc = one(T)
                ll=1
                for k1 in k                
                    cc *= x[k1+1]*coeff(W[ll:ll+l[k1+1]-1], C[k1+1], g) 
                    ll += l[k1+1]
                end        
                #println("coeff = ", cc)
            end     
            c += cc/factorial(q)
        end
    end
    c
end


function coeffs_prod_exps{T,S,R}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1}, g::Array{R,1}=[])
    W1 = extend_by_rightmost_subwords(W)
    m = length(W1)
    J = length(G)
    M = zeros(T, m, m)
    c = zeros(T, m)
    c[1] = one(T)
    for j=1:J
        for k=1:m
            for l=1:m
                r = length(W1[k])-length(W1[l])
                if r>=0 && W1[k][r+1:end]==W1[l]
                    w = W1[k][1:r]
                    M[k,l]  = coeff_exp(w, G[j], g)
                end
            end
        end 
        c = M*c
    end   
    c = [c[findfirst(W1, w)] for w in W]
end    


function order_conditions_splitting{T,S}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1})
    c = coeffs_prod_exps(W, G)
    for i=1:length(W)
        c[i] = c[i] - one(T)/factorial(length(W[i]))
    end
    c
end


function order_conditions_splitting{T}(W::Array{Array{Int64,1},1}, a::Array{T, 1}, b::Array{T, 1})
    sa = length(a)
    sb = length(b)
    G = Array{Tuple{T,Int},1}[]
    for j=1:max(sa, sb)
        if j<=sa && a[j]!=0
            push!(G, [(a[j], 0)])
        end
        if j<=sb && b[j]!=0
            push!(G, [(b[j], 1)])
        end
    end
    order_conditions_splitting(W, G)
end


function order_conditions_exponential{T,S,R}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1}, g::Array{R,1}=[])
    c = coeffs_prod_exps(W, G, g)
    for i=1:length(W)
        w = W[i]
        c[i] = c[i] - one(T)/prod([sum(w[j:end]+1) for j=1:length(w)])
    end
    c
end



function order_conditions_exponential_legendre{T,S}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1})
    c = coeffs_prod_exps(W, G)
    p = maximum([sum(w) for w in W])
    Cinv = inv([(2*n+1)*(-1)^n*sum([(-1)^k//(k+m+1)*binomial(n, k)*binomial(n+k, k) for k=0:n]) for n=0:p-1,m=0:p-1])
    for i=1:length(W)
        w = W[i]
        l = length(w)
        s = zero(T)
        for v in MultiFor(fill(p-1,l))
            s += prod([Cinv[v[j]+1,w[j]]/sum([v[i]+1 for i=j:l]) for j=1:l])
        end
        c[i] -= s
    end
    c
end


end #Expocon
