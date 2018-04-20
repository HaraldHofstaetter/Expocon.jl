module Expocon

import 
Base: (*), /, +, -, show, convert, zero, one

export Element, Generator, SimpleCommutator, Commutator
export Exponential, Product, Id, Term, LinearCombination
export ZeroElement
export terms
export Word
export Lyndon, lyndon_words, lyndon_basis, lyndon_bracketing
export rightnormed_words, rightnormed_basis, rightnormed_bracketing
export extend_by_rightmost_subwords, leading_word
export coeff

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


*(p::Product, x::Element) = Product(vcat(p.p, x))
*(x::Element, p::Product) = Product(vcat(x, p.p))
*(x::Vararg{Element}) = Product([x...])

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

*(c, e::Element) = Term(c,e)
#*(e::Element, c) = Term(c,e)
*(c, t::Term) = Term(c*t.c,t.e)
#*(t::Term, c) = Term(c*t.c,t.e)

-(t::Term) = Term(-t.c, t.e)
-(e::Element) = Term(-1, e)

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
    l::Dict{Element, Any}
end

# to be removed, not the intended action which should be like +...
LinearCombination(ee::Vararg{Element}) = LinearCombination(
     Dict{Element,Any}([isa(e, Term)?e.e=>e.c:e=>1 for e in ee]))


const ZeroElement = LinearCombination(Dict{Element,Any}())
zero(::Type{T}) where {T<:Element} = ZeroElement 
zero(x::T) where {T<:Element} = zero(T)

-(x::LinearCombination)= LinearCombination(Dict{Element,Any}([e=>-c for (e,c) in x.l]))

function *(c, x::LinearCombination)
    if c==0
        return ZeroElement
    else
        return LinearCombination(Dict{Element,Any}([e=>c*f for (e,f) in x.l]))
    end
end

#*(x::LinearCombination, c) = *(c,x)

function +(x::LinearCombination, y::LinearCombination)
    r = copy(x.l)
    for (e, c) in y.l
        if haskey(r, e)
            r[e] += c
        else
            r[e] = c
        end    
        if r[e]==0
            delete!(r, e) 
        end     
    end
    LinearCombination(r) 
end

function -(x::LinearCombination, y::LinearCombination)
    r = copy(x.l)
    for (e, c) in y.l
        if haskey(r, e)
            r[e] -= c
        else
            r[e] = -c
        end    
        if r[e]==0
            delete!(r, e) 
        end     
    end
    LinearCombination(r) 
end

function +(x::LinearCombination, t::Term)
    r = copy(x.l)
    if haskey(r, t.e)
        r[t.e] += t.c
    else
        r[t.e] = t.c
    end    
    if r[t.e]==0
        delete!(r, t.e) 
    end     
    LinearCombination(r) 
end

+(x::LinearCombination, e::Element) = +(x, convert(Term, e))
+(e::Element, x::LinearCombination) = +(e, x)

function +(t1::Term, t2::Term)
    if t1.e == t2.e
        if t1.c==-t2.c
            return ZeroElement
        else
            return LinearCombination(Dict{Element,Any}(t1.e=>t1.c+t2.c))
        end
    else
        return LinearCombination(Dict{Element,Any}([t1.e=>t1.c, t2.e=>t2.c]))
    end
end
+(e1::Element, e2::Element) = +(convert(Term, e1), convert(Term, e2))

function -(t1::Term, t2::Term)
    if t1.e == t2.e
        if t1.c==t2.c
            return ZeroElement
        else
            return LinearCombination(Dict{Element,Any}(t1.e=>t1.c-t2.c))
        end
    else
        return LinearCombination(Dict{Element,Any}([t1.e=>t1.c, t2.e=>-t2.c]))
    end
end
-(e1::Element, e2::Element) = -(convert(Term, e1), convert(Term, e2))


function -(x::LinearCombination, t::Term)
    r = copy(x.l)
    if haskey(r, t.e)
        r[t.e] -= t.c
    else
        r[t.e] = -t.c
    end    

    if r[t.e]==0
        delete!(r, t.e) 
    end     
    LinearCombination(r) 
end

-(x::LinearCombination, e::Element) = -(x, convert(Term, e))

function -(t::Term, x::LinearCombination)
    r = (-x).l
    if haskey(r, t.e)
        r[t.e] += t.c
    else
        r[t.e] = t.c
    end    
    if r[t.e]==0
        delete!(r, t.e) 
    end     
    r
end


-(e::Element, x::LinearCombination) = -(convert(Term, e), x)

terms(x::LinearCombination) = [Term(c, e) for (e,c) in x.l]

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
    @assert length(G)==length(unique(G)) "Generators must be distinct"
    W = lyndon_words(length(G), n, odd_terms_only=odd_terms_only, all_lower_terms=all_lower_terms)
    [Word([G[g+1] for g in w]) for w in W]
end


Base.length(::Generator) = 1
Base.length(C::SimpleCommutator) = 
    (isa(C.x, SimpleCommutator)?length(C.x):1)+(isa(C.y, SimpleCommutator)?length(C.y):1)

leading_word(C::Generator) = Word([C])
leading_word(C::SimpleCommutator) = Word(vcat(leading_word(C.x), leading_word(C.y)))

function extend_by_rightmost_subwords(W::Array{Word})
    WW=Dict{Word,Int}(Word([])=>1)
    for w in W 
        for l=1:length(w)
            WW[w[l:end]] = 1
        end
    end
    return sort(collect(keys(WW)), lt=(x,y)->length(x)<length(y))
end

function lyndon_bracketing(w::Word, W::Array{Word})
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
    @assert length(G)==length(unique(G)) "Generators must be distinct"
    W = lyndon_words(length(G), n, odd_terms_only=odd_terms_only, all_lower_terms=all_lower_terms)
    [Word([G[g+1] for g in lyndon2rightnormed(w)]) for w in W]
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

function coeff(w::Word, l::LinearCombination)
    sum(t.c*coeff(w,t.e) for t in terms(l))
end

end # Expocon
