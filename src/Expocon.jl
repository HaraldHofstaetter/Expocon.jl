__precompile__()
module Expocon 

export MultiFor
export Lyndon, lyndon_words, graded_lyndon_words
export bracketing, lyndon_basis, graded_lyndon_basis
export extend_by_rightmost_subwords
export commutator_length
export coeff, coeff_exp, coeffs_prod_exps
export rhs_splitting
export rhs_exponential_taylor
export rhs_exponential_taylor_symmetric
export rhs_exponential_legendre
export order_conditions_splitting
export order_conditions_exponential_taylor
export order_conditions_exponential_taylor_symmetric
export order_conditions_exponential_legendre
export legendre, dlegendre
export gauss_nodes, gauss_nodes_and_weights
export order_conditions_exponential_gauss
export order_conditions_exponential_nodes
export coeff_trans


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
            c=1
            for i in reverse(w)
                if i==0
                    push!(w1, c)
                    c = 1
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


function bracketing(w, W; square_brackets::Bool=false)
    if length(w) == 1
        return w[1]
    end
    k0 = 0
    for k=2:length(w)
        if findfirst(W, w[k:end])>0
            k0 = k
            break
        end
    end    
    if square_brackets
	return Any[bracketing(w[1:k0-1], W, square_brackets=square_brackets), 
	           bracketing(w[k0:end], W, square_brackets=square_brackets)]
    else
        return (bracketing(w[1:k0-1], W, square_brackets=square_brackets), 
	        bracketing(w[k0:end], W, square_brackets=square_brackets))
    end
end

function lyndon_basis(s::Integer, n::Integer; square_brackets::Bool=false) 
    W = lyndon_words(s, n)
    [bracketing(w, W, square_brackets=square_brackets) for w in W]
end

function graded_lyndon_basis(n::Integer; square_brackets::Bool=false) 
    W = graded_lyndon_words(n)
    [bracketing(w, W, square_brackets=square_brackets) for w in W]
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


rhs_exponential_splitting(W::Array{Array{Int64,1},1}) = [1//factorial(length(w)) for w in W]

function order_conditions_splitting{T,S}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1})
    coeffs_prod_exps(W, G) - rhs_exponential_splitting(W)
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

function rhs_exponential_taylor(W::Array{Array{Int64,1},1})
    T = Rational{Int}    
    c = zeros(T, length(W))
    p = maximum([sum(w) for w in W])  
    for i=1:length(W)
        w = W[i]
        c[i] = one(T)/prod([sum(w[j:end]) for j=1:length(w)])
    end
    c
end    

function order_conditions_exponential_taylor{T,S,R}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1}, g::Array{R,1}=[])
    coeffs_prod_exps(W, G, g) - rhs_exponential_taylor(W)
end


function rhs_exponential_taylor_symmetric(W::Array{Array{Int64,1},1})
    T = Rational{Int}    
    c = zeros(T, length(W))
    p = maximum([sum(w) for w in W])
    Cinv = T[(-1)^(m+n)*(n>=m?binomial(n,m)//2^(n-m):0) for m=0:p-1, n=0:p-1]
    for i=1:length(W)
        w = W[i]
        l = length(w)
        s = zero(T)
        for v in MultiFor(w-1)
            s += prod([Cinv[v[j]+1,w[j]]/sum([v[i]+1 for i=j:l]) for j=1:l])
        end
        c[i] = s
    end
    c
end

function order_conditions_exponential_taylor_symmetric{T,S,R}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1}, g::Array{R,1}=[])
    coeffs_prod_exps(W, G, g) - rhs_exponential_taylor_symmetric(W)
end


function rhs_exponential_legendre(W::Array{Array{Int64,1},1})
    T = Rational{Int}    
    c = zeros(T, length(W))
    p = maximum([sum(w) for w in W])
    Cinv = T[(-1)^(m+n)*binomial(n,m)*binomial(n+m,m) for m=0:p-1, n=0:p-1]
    for i=1:length(W)
        w = W[i]
        l = length(w)
        s = zero(T)
        for v in MultiFor(w-1)
            s += prod([Cinv[v[j]+1,w[j]]/sum([v[i]+1 for i=j:l]) for j=1:l])
        end
        c[i] = s
    end
    c
end

function order_conditions_exponential_legendre{T,S}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1})
    coeffs_prod_exps(W, G) - rhs_exponential_legendre(W)
end


using Giac

legendre{T}(n::Integer, x::T) = (-1)^n*sum([binomial(n,k)*binomial(n+k,k)*(-1)^k*x^k for k=0:n])

dlegendre{T}(n::Integer, x::T) = (-1)^n*sum([binomial(n,k)*binomial(n+k,k)*(-1)^k*k*x^(k-1) for k=1:n])

function gauss_nodes(n::Integer) 
    x = giac_identifier("__x__")
    to_julia(solve(equal(legendre(n, x), 0), x))
end

function gauss_nodes_and_weights(n)
    x = gauss_nodes(n)
    w = [simplify(1/(t*(1-t)*dlegendre(n, t)^2)) for t in x]
    x,w
end


function order_conditions_exponential_gauss{T,S}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1}, q::Integer)
    c = coeffs_prod_exps(W, G)
    c1 = zeros(T, length(W))
    p = maximum([length(w) for w in W])
    C = T[(-1)^(m+n)*binomial(n,m)*binomial(n+m,m) for m=0:p-1, n=0:p-1]
    x,g = gauss_nodes_and_weights(q)
    C1 = [one(giac)*(2*n-1)*g[m]*legendre(n-1,x[m]) for m=1:q, n=1:p]
    for i=1:length(W)
        y = W[i]
        l = length(y)
        s = zero(T)
        for w in MultiFor(fill(l-1,l))
            s1 = zero(T)
            for v in MultiFor(fill(l-1,l))
                s1 += prod([C[v[j]+1,w[j]+1]/sum([v[i]+1 for i=j:l]) for j=1:l])
            end
            s += s1*prod([C1[y[j],w[j]+1] for j=1:l])
        end
        c1[i] = c[i] - s
    end
    c1
end                

function order_conditions_exponential_nodes{T,S}(W::Array{Array{Int64,1},1}, G::Array{Array{Tuple{T,S},1},1}, g::Vector)
    c = coeffs_prod_exps(W, G)    
    c1 = zeros(T, length(W))
    p = maximum([length(w) for w in W])
    q = length(g)
    Cinv = to_julia(giac(:inverse, [g[m]^n for m=1:q, n=0:q])) 
    Cinv = [Cinv[i][j] for i=1:q, j=1:q]
    for i=1:length(W)
        w = W[i]
        l = length(w)
        s = zero(giac)
        for v in MultiFor(fill(q-1,l))
            s += prod([Cinv[v[j]+1,w[j]]/sum([v[i]+1 for i=j:l]) for j=1:l])
        end
        c1[i] = c[i]-s
    end
    c1
end        



coeff_trans(W::Array{Int,1}, C::Int, T::Matrix) = length(W)==1?T[W[1], C]:0

function coeff_trans(W::Array{Int,1}, C::Vector, T::Matrix)
    if length(C)!=2
         error("not well-formed commutator")
    end
    l1 = commutator_length(C[1])
    l2 = commutator_length(C[2])
    if l1+l2 != length(W)
        return 0
    end
    (coeff_trans(W[1:l1], C[1], T)*coeff_trans(W[l1+1:end], C[2], T) -
     coeff_trans(W[1:l2], C[2], T)*coeff_trans(W[l2+1:end], C[1], T) )
end

function coeff_trans{T,S}(W::Array{Int,1}, G::Array{Tuple{T,S},1}, TM::Matrix)
    c = zero(T)
    for (c1, C) in G
        c += c1*coeff_trans(W, C, TM)
    end
    c
end


leading_word(C::Int)=[C]
leading_word(C::Vector) = vcat(leading_word(C[1]), leading_word(C[2]))


function transform{T,S}(B::Vector, G::Array{Tuple{T,S},1}, TM::Matrix)
    G1 = Tuple{T,Any}[]
    for b in B
        W = leading_word(b)
        h = coeff_trans(W, G, TM)
        if !iszero(h)
            push!(G1, (simplify(h), b))
        end
    end
    G1
end

function transform{T,S}(B::Vector, G::Array{Array{Tuple{T,S},1}}, TM::Matrix)
    Array{Tuple{T,S},1}[transform(B, g, TM) for g in G]
end


end #Expocon
