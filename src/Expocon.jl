__precompile__()
module Expocon

import 
Base: (*), /, +, -, show, convert, zero, one, expand

export MultiFor
export Element, Generator, SimpleCommutator, Commutator
export Exponential, Product, Id, Term, LinearCombination
export ZeroElement
export terms
export Word
export Lyndon, lyndon_words, lyndon_basis, lyndon_bracketing
export rightnormed_words, rightnormed_basis, rightnormed_bracketing
export extend_by_rightmost_subwords, leading_word
export is_lie_element, is_homogenous_lie_element
export coeff, coeffs, degree
export distribute, expand_commutators, simplify
export generators, max_length, normalize_lie_elements

abstract type Element end

struct Generator <: Element
    name   ::String
    degree ::Int
end

Generator(name::String) = Generator(name, 1)

Base.show(io::IO, g::Generator) = print(io, g.name)

struct SimpleCommutator <: Element 
    x::Element
    y::Element
end

Base.show(io::IO, sc::SimpleCommutator) = print(io, "[", sc.x, ",", sc.y, "]")

Commutator(g::Element) = g
Commutator(x, y) = SimpleCommutator(Commutator(x), Commutator(y))
Commutator(x::Tuple) = SimpleCommutator(Commutator(x[1]),Commutator(x[2]))

function Commutator(x::Vector)
    @assert length(x)==2 "wrong commutator length"
    SimpleCommutator(Commutator(x[1]),Commutator(x[2]))
end


struct Exponential <: Element
    e::Element
end

Base.exp(e::Element) = Exponential(e)
Base.show(io::IO, e::Exponential) = print(io, "exp(", e.e, ")")

struct Product <: Element
    p::Array{Element,1}    
end

const Id = Product([])
one(::Type{T}) where {T<:Element} = Id
one(x::T) where {T<:Element} = one(T)


function Base.show(io::IO, p::Product) 
    if length(p.p)==0
        print(io, "Id")
    else
        i = start(p.p)
        is_done = done(p.p,i)
        while !is_done
            e, i = next(p.p,i)
            is_done = done(p.p,i)
            if isa(e, LinearCombination) && length(p.p)>1
                print(io, "(", e, ")")
            else
                print(io, e)
            end
            if !is_done
                print(io, "*")
            end
        end
    end
end

struct Term <: Element
    c::Any
    e::Element
end

Base.convert(::Type{Term}, t::Term) = t
Base.convert(::Type{Term}, e::Element) = Term(1, e)


function Base.show(io::IO, t::Term)
    if t.c!=1 
        if !(isa(t.c, Real) && t.c>=0)
            print(io, "(")
        end        
        print(io, t.c)
        if !(isa(t.c, Real) && t.c>=0)
            print(io, ")")
        end        
        print(io, "*")
    end
    if isa(t.e, LinearCombination)
        print(io, "(")
    end
    print(io, t.e)
    if isa(t.e, LinearCombination)
        print(io, ")")
    end
end


struct LinearCombination <: Element
    l::Array{Term,1}    
end

const ZeroElement = LinearCombination([])

zero(::Type{T}) where {T<:Element} = ZeroElement 
zero(x::T) where {T<:Element} = zero(T)


*(c, e::Element) = Term(c,e)
*(e::Element, c) = Term(c,e)
*(c, t::Term) = Term(c*t.c,t.e)
*(t::Term, c) = Term(c*t.c,t.e)
*(c, l::LinearCombination) = LinearCombination([c*t for t in terms(l)])
*(l::LinearCombination, c) = LinearCombination([c*t for t in terms(l)])

*(p::Product, x::Element) = Product(vcat(p.p, x))
*(x::Element, p::Product) = Product(vcat(x, p.p))
*(p1::Product, p2::Product) = Product(vcat(p1.p, p2.p))
*(e1::Element, e2::Element) = Product([e1, e2])
*(t1::Term, t2::Term) = Term(t1.c*t2.c, t1.e*t2.e)
*(t::Term, e::Element) = Term(t.c, t.e*e)
*(e::Element, t::Term) = Term(t.c, e*t.e)
*(l::LinearCombination, e::Element) = Product([l, e]) 
*(e::Element, l::LinearCombination) = Product([e, l])
*(l::LinearCombination, p::Product) = Product([l, p]) 
*(p::Product, l::LinearCombination) = Product([p, l])

+(l1::LinearCombination, l2::LinearCombination) = LinearCombination(vcat(l1.l, l2.l))
+(l::LinearCombination, t::Term) = LinearCombination(vcat(l.l, t))
+(t::Term, l::LinearCombination) = LinearCombination(vcat(t, l.l))
+(t1::Term, t2::Term) =  LinearCombination(vcat(t1, t2))
+(e1::Element, e2::Element) = LinearCombination(vcat(convert(Term, e1), convert(Term, e2)))
+(e::Element) = e
-(t::Term) = Term(-t.c, t.e)
-(e::Element) = Term(-1, e)
-(l::LinearCombination) = LinearCombination([-t for t in terms(l)])
-(e1::Element, e2::Element) = e1+(-e2)


terms(e::Element) = [Term(e)]
terms(x::LinearCombination) = x.l

function Base.show(io::IO, l::LinearCombination) 
    tt=terms(l)
    if length(tt)==0
        print(io, "0")
    else
        i = start(tt)
        is_done = done(tt,i)
        while !is_done
            t, i = next(tt,i)
            is_done = done(tt,i)
            print(io, t)
            if !is_done
                print(io, "+")
            end
        end
    end
end


expand_commutators(e::Element) = e

function expand_commutators(c::SimpleCommutator)
    x = expand_commutators(c.x)
    y = expand_commutators(c.y)
    x*y-y*x
end

expand_commutators(t::Term) = t.c*expand_commutators(t.e)

expand_commutators(l::LinearCombination) = sum([expand_commutators(t) for t in terms(l)])

function expand_commutators(p::Product) 
    if length(p.p)==0
        return Id
    elseif length(p.p)==1
        return expand_commutators(p.p[1])
    else
        return expand_commutators(p.p[1])*expand_commutators(Product(p.p[2:end]))
    end
end


distribute(e1::Element, e2::Element) = e1*e2
distribute(t::Term, l::LinearCombination) = sum([t*t1 for t1 in terms(l)])
distribute(l::LinearCombination, t::Term) = sum([t1*t for t1 in terms(l)])
distribute(l1::LinearCombination, l2::LinearCombination) = sum([t1*t2 for t1 in terms(l1) for t2 in terms(l2)]) 
distribute(e::Element, l::LinearCombination) = distribute(Term(e), l)
distribute(l::LinearCombination, e::Element) = distribute(l, Term(e))


Base.expand(e::Element) = e

function Base.expand(t::Term) 
    ee = expand(t.e)
    if isa(ee, LinearCombination)
        return sum((t.c*t1.c)*t1.e for t1 in terms(ee))
    else
        return t.c*expand(ee)
    end
end

Base.expand(l::LinearCombination) = sum([expand(t) for t in terms(l)])

function Base.expand(p::Product)
    if length(p.p)==0
        return Id
    else
        r = expand(p.p[1])
        for j=2:length(p.p)
            r = distribute(r, expand(p.p[j]))
        end
        return r
    end
end


key(g::Generator) = ('G', g.name)
key(e::Exponential) = ('E', key(e.e))
key(t::Term) = ('T', t.c, key(t.e))
key(c::SimpleCommutator) = ('C', key(c.x), key(c.y))
key(p::Product) = (vcat('P', [key(f) for f in p.p])...)
key(l::LinearCombination) = (vcat('L', sort([key(t) for t in terms(l)]))...)

simplify(g::Generator) = g
simplify(e::Exponential) = Exponential(simplify(e.e))
simplify(t::Term) = Term(t.c, simplify(t.e))
simplify(c::SimpleCommutator) = Commutator(simplify(c.x), simplify(c.y))
simplify(p::Product) = Product([simplify(f) for f in p.p])


function simplify(l::LinearCombination)
    tab=Dict{Any, Term}()    
    for t0 in terms(l)
        t = simplify(t0)
        k = key(t.e)
        if haskey(tab, k)
            tab[k] = Term(tab[k].c+t.c, tab[k].e)
        else
            tab[k] = t
        end    
        if tab[k].c==0
            delete!(tab, k) 
        end     
    end
    LinearCombination(collect(values(tab)))
end



struct Word <: AbstractArray{Generator,1}
    w::Array{Generator,1}
end

Word(x::Vararg{Generator}) = Word([x...])

Base.size(w::Word) = size(w.w)
Base.IndexStyle(::Type{<:Word}) = IndexLinear()
Base.getindex(w::Word, i::Int) = w.w[i]
Base.getindex(w::Word, i) = Word(w.w[i])

function Base.show(io::IO, w::Word) 
    if length(w)==0
        print(io, "∅")
    else
        i = start(w)
        is_done = done(w,i)
        while !is_done
            g, i = next(w,i)
            is_done = done(w,i)
            print(io, g)
            if !is_done
                print(io, ".")
            end
        end
    end
end

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

function lyndon_words(s::Integer, n::Integer; odd_terms_only::Bool=false, 
                      all_lower_terms::Bool=true)
    r = Array{Int,1}[]
    for w in Lyndon(s,n)
        if (all_lower_terms || length(w)==n) && (!odd_terms_only || isodd(length(w)))
            push!(r, w)
        end
    end
    sort(r, lt=(x,y)->length(x)<length(y))
end

function lyndon_words(G::Array{Generator,1}, n::Integer; odd_terms_only::Bool=false, 
                      all_lower_terms::Bool=true)
    s = length(G)
    @assert s==length(unique(G)) "Generators must be distinct"
    r = Word[]
    for w0 in Lyndon(s,n)
        w = Word(G[w0+1])
        d = degree(w)
        if  ((all_lower_terms && d<=n) || d==n) && (!odd_terms_only || isodd(d))
            push!(r, w)
        end
    end
    sort(r, lt=(x,y)->degree(x)<degree(y))
end


Base.length(::Generator) = 1
Base.length(C::SimpleCommutator) = 
    (isa(C.x, SimpleCommutator)?length(C.x):1)+(isa(C.y, SimpleCommutator)?length(C.y):1)

degree(g::Generator) = g.degree
degree(C::SimpleCommutator) = degree(C.x)+degree(C.y) 
degree(w::Word) = sum([degree(g) for g in w])

leading_word(C::Generator) = Word([C])
leading_word(C::SimpleCommutator) = Word(vcat(leading_word(C.x), leading_word(C.y)))

function extend_by_rightmost_subwords(W::Array{Word, 1})
    WW=Dict{Word,Int}(Word([])=>1)
    for w in W 
        for l=1:length(w)
            WW[w[l:end]] = 1
        end
    end
    return sort(collect(keys(WW)), lt=(x,y)->length(x)<length(y))
end

function lyndon_bracketing(w::Word, W::Array{Word, 1})
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
    SimpleCommutator(lyndon_bracketing(w[1:k0-1], W), lyndon_bracketing(w[k0:end], W) )
end

function lyndon_basis(G::Array{Generator,1}, n::Integer; 
                      odd_terms_only::Bool=false, all_lower_terms::Bool=true) 
    W = lyndon_words(G, n)
    [lyndon_bracketing(w, W) for w in W if
        (all_lower_terms || length(w)==n) && (!odd_terms_only || isodd(length(w)))]
end

function analyze_lyndon_word(w::Array{Int,1})
    #println(w)
    q = maximum(w)
    A = Dict{Array{Int64,1}, Int}([[x]=>x for x in 1:q])
    w1 = Int[]
    
    lw = length(w)
    s = 1
    m1 = 1
    m2 = 0
    
    # get a
    a = minimum(w) 
    assert(w[s]==a)
    
    #get av
    s += 1
    while s<=lw && w[s]!=a
        s += 1
    end
    v = w[2:s-1]   
    av = vcat(a,v)  
    #println("a=",a)
    #println("v=",v)
    lav = length(av)  
    while s<=lw
        if m2!=0 # do not change m2 in 1st iteration
            m1 = s
        end
        # get n
        n = 0
        while s+lav<=lw && w[s+lav]==a && w[s:s+lav-1]==av     
            s += lav
            n += 1
        end
        #println("s=",s ," n=", n)
        assert(w[s]==a)
        s+=1     
    
        #get uu
        k = findnext(w, a, s)
        if k>0
            uu = w[s:k-1]
            s = k
        else
            uu = w[s:end]
            s = lw+1
        end
        #do something with uu 
        j = 1
        while !(lexless(v,uu[1:j])&&!lexless(v,uu[1:j-1]))
            j += 1
        end
        u = uu[1:j]
        u1 = uu[j+1:end]  
        m2 = s-length(u1)-1
        x = get!(A, w[m1:m2]) do
            q += 1
        end
        w1 = vcat(w1, x, u1)
        #println("n=",n," uu=",uu, " u=",u, " u1=",u1)
        #println("A_=", w[m1:m2])
    end   
    #println("w1=", w1)
    pp = invperm([A[x] for x in sort(collect(keys(A)), lt=lexless)])
    w2 = [pp[x] for x in  w1]
    tt = fill(Int[],q)
    for (x,y) in A
        tt[pp[y]] = x
    end    
    #println("---------------------")
    w2, tt
end


function lyndon2rightnormed(w::Array{Int, 1})
    aa = minimum(w)
    k=0 # number of occurences of a in w
    for x in w
        if x==aa
            k+=1
        end
    end
    if k==1
        return reverse(w)
    end
    w_1, tt = analyze_lyndon_word(w)
    u_1 = lyndon2rightnormed(w_1)
    y = tt[u_1[end]]
    a = y[1] 
    k0 = findnext(y, a, 2)
    k1 = findlast(y, a)
    v = y[2:k0-1]
    avn = y[k0:k1-1]
    u1 = y[k1+1:end]
    u = vcat(tt[u_1[1:end-1]]...,
             avn, a, u1, reverse(v), a)
end


function rightnormed_words(G::Array{Generator,1}, n::Integer; odd_terms_only::Bool=false, all_lower_terms::Bool=true)
    W = lyndon_words(G, n, odd_terms_only=odd_terms_only, all_lower_terms=all_lower_terms)
    [Word([G[g+1] for g in lyndon2rightnormed([findfirst(G,g)-1 for g in w])]) for w in W]
end


function rightnormed_bracketing(w::Word)
    if length(w) == 1
        return w[1]
    end
    SimpleCommutator(w[1], rightnormed_bracketing(w[2:end]))
end


function rightnormed_basis(G::Array{Generator,1}, n::Integer; 
                      odd_terms_only::Bool=false, all_lower_terms::Bool=true) 
    W = rightnormed_words(G, n, odd_terms_only= odd_terms_only, all_lower_terms=all_lower_terms)
    [rightnormed_bracketing(w) for w in W]
end

coeff(w::Word, g::Generator) = length(w)==1&&w[1]==g?1:0

function coeff(w::Word, c::SimpleCommutator)
    lx = length(c.x)
    ly = length(c.y)
    if lx+ly != length(w)
        return 0
    end
    (coeff(w[1:lx], c.x)*coeff(w[lx+1:end], c.y) -
     coeff(w[1:ly], c.y)*coeff(w[ly+1:end], c.x))
end

coeff(w::Word, t::Term) = t.c*coeff(w, t.e)
coeff(w::Word, l::LinearCombination) = sum(coeff(w,t) for t in terms(l))


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


is_lie_element(e::Element)=false
is_lie_element(g::Generator)=true
is_lie_element(t::Term)=is_lie_element(t.e)
is_lie_element(c::SimpleCommutator) = is_lie_element(c.x) && is_lie_element(c.y)
is_lie_element(l::LinearCombination) = all(is_lie_element.(terms(l))) 

degree(t::Term) = degree(t.e)
is_homogenous_lie_element(e::Element) = is_lie_element(e)
is_homogenous_lie_element(l::LinearCombination) = is_lie_element(l) && (length(l.l)<=1 ||all(degree(l.l[1]).==degree.(l.l[2:end]))) 

function degree(l::LinearCombination)
    @assert is_homogenous_lie_element(l) "homogenous lie element expected"
    length(l.l)==0?-1:degree(l.l[1])
end

generators(g::Generator)=Set([g])
generators(c::SimpleCommutator)=union(generators(c.x), generators(c.y))
generators(t::Term)=generators(t.e)
generators(l::LinearCombination) = union([generators(t) for t in terms(l)]...)

max_length(g::Generator)=1
max_length(c::SimpleCommutator) = max_length(c.x)+max_length(c.y)
max_length(t::Term) = max_length(t.e)
max_length(l::LinearCombination) = maximum([max_length(t) for t in terms(l)])

function normalize_lie_elements(e::Element; order::Array{Generator,1}=Generator[])
    if !is_lie_element(e)
        return e
    end
    G = collect(generators(e))
    order = [g for g in order if g in G]
    order = unique(vcat(order,G))
    W = Word[]
    B = SimpleCommutator[]
    c = Any[]
    for w in Lyndon(length(order), max_length(e))
        w1 = Word([order[g+1] for g in w])
        c0 = coeff(w1, e)
        if c0!=0
            push!(c, c0)
            push!(W, w1)
            push!(B, rightnormed_bracketing(Word([order[g+1] for g in Expocon.lyndon2rightnormed(w)])))
        end
    end
    simplify(sum(convert(Array{Int,2}, inv(Rational{Int}[coeff(w, b) for w in W, b in B]))*c.*B))
end

normalize_lie_elements(e::Exponential; order::Array{Generator,1}=Generator[])=
    Exponential(normalize_lie_elements(e.e, order=order))
normalize_lie_elements(p::Product; order::Array{Generator,1}=Generator[]) = 
    Product([normalize_lie_elements(f, order=order) for f in p.p])


function coeff(w::Word, e::Exponential)
    @assert is_lie_element(e.e) "lie element in exponent expected"
    r = length(w)
    if r==0
        return 1
    end
    tt = terms(e.e)
    K = length(tt)
    C = [t.e for t in tt]
    x = [t.c for t in tt]
    l = length.(C)
    Q = div(r, minimum(l))
    c = 0
    for q = 1:Q
        for k = MultiFor((K-1)*ones(Int,q))
            cc = 0
            s = sum([l[k1+1] for k1 in k])
            if s==r
                cc = 1
                ll=1
                for k1 in k                
                    cc *= x[k1+1]*coeff(w[ll:ll+l[k1+1]-1], C[k1+1]) 
                    ll += l[k1+1]
                end        
            end     
            c += cc*(1//factorial(q))
        end
    end
    c
end

function coeffs(W::Array{Word, 1}, p::Product)
    W1 = extend_by_rightmost_subwords(W)
    m = length(W1)
    J = length(p.p)
    M = Any[0 for i=1:m, j=1:m]
    c = Any[0 for i=1:m]
    c[1] = 1
    for j=1:J
        for k=1:m
            for l=1:m
                r = length(W1[k])-length(W1[l])
                if r>=0 && W1[k][r+1:end]==W1[l]
                    w = W1[k][1:r]
                    M[k,l]  = coeff(w, p.p[j])
                end
            end
        end 
        c = M*c
    end   
    c = [c[findfirst(W1, w)] for w in W]
end    

coeff(w::Word, p::Product) = coeffs([w], p)[1]

coeffs(W::Array{Word,1}, e::Element) = [coeff(w, e) for w in W]



end # Expocon
