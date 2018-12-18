__precompile__()
module Expocon

import 
Base: (*), /, +, -, show, convert, zero, one, expand, iszero, inv, diff, contains

export MultiFor
export Element, Generator, SimpleCommutator, Commutator
export Exponential, Product, Id, Term, LinearCombination
export ZeroElement
export terms, factors, exponent
export Word, all_words
export Lyndon, lyndon_words, lyndon_basis, lyndon_bracketing
export lyndon_factorization
export rightnormed_words, rightnormed_basis, rightnormed_bracketing
export extend_by_rightmost_subwords, leading_word
export is_id, is_lie_element, is_homogenous_lie_element
export adjoint
export coeff, coeffs, degree
export distribute, expand_commutators, simplify_sum, simplify
export generators, max_length, normalize_lie_elements
export commute
export rhs_splitting, rhs_taylor, rhs_taylor_symmetric, rhs_legendre
export splitting_method, mult_t, composition
export exp_superdiagm, coeff_BCH, BCH
export hom, logtriu

abstract type Element end

struct Generator <: Element
    name   ::String
    degree ::Int
    function Generator(name, degree)
        @assert degree>=1 "degree has to be >=1"
        new(name, degree)
    end
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

exponent(e::Exponential) = e.e

Base.exp(e::Element) = Exponential(e)
Base.show(io::IO, e::Exponential) = print(io, "exp(", e.e, ")")

struct Product <: Element
    p::Array{Element,1}    
end
#Note factors stored form right to left

factors(p::Product) = p.p



const Id = Product([])
one(::Type{T}) where {T<:Element} = Id
one(x::T) where {T<:Element} = one(T)



function Base.show(io::IO, p::Product) 
    if length(p.p)==0
        print(io, "Id")
    else
        f = factors(p)
        i = start(f)
        is_done = done(f,i)
        while !is_done
            e, i = next(f,i)
            is_done = done(f,i)
            if isa(e, LinearCombination) && length(f)>1
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

iszero(x::Element) = false
iszero(l::LinearCombination) = length(l.l)==0
iszero(t::Term) = t.c==0 || iszero(t.e)

is_id(e::Element) = false
is_id(p::Product) = length(factors(p))==0
is_id(t::Term) = is_id(t.e)&&t.c==1


*(c, e::Element) = c==1 ? e : Term(c,e)
*(e::Element, c) = c==1 ? e : Term(c,e)
*(c, t::Term) = (c*t.c)*t.e
*(t::Term, c) = (c*t.c)*t.e
#*(c, t::Term) = Term(c*t.c,t.e)
#*(t::Term, c) = Term(c*t.c,t.e)

*(p::Product, x::Element) = Product(vcat(p.p, x))
*(x::Element, p::Product) = Product(vcat(x, p.p))
*(p1::Product, p2::Product) = Product(vcat(p1.p, p2.p))
*(e1::Element, e2::Element) = Product([e1, e2])
*(p::Product, t::Term) = t.c*(p*t.e)
*(t::Term, p::Product) = t.c*(t.e*p)
*(t1::Term, t2::Term) = (t1.c*t2.c)*(t1.e*t2.e)
*(t::Term, e::Element) = t.c*(t.e*e)
*(e::Element, t::Term) = t.c*(e*t.e)

+(l1::LinearCombination, l2::LinearCombination) = LinearCombination(vcat(l1.l, l2.l))
+(l::LinearCombination, t::Term) = LinearCombination(vcat(l.l, t))
+(t::Term, l::LinearCombination) = LinearCombination(vcat(t, l.l))
+(l::LinearCombination, e::Element) = LinearCombination(vcat(l.l, vcat(convert(Term, e))))
+(e::Element, l::LinearCombination) = LinearCombination(vcat(vcat(convert(Term, e), l.l)))
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

distribute_commutators(e1::Element, e2::Element) = SimpleCommutator(e1, e2)
distribute_commutators(t::Term, l::LinearCombination) = sum([t.c*t1.c*SimpleCommutator(t.e,t1.e) for t1 in terms(l)])
distribute_commutators(l::LinearCombination, t::Term) = sum([t1.c*t.c*SimpleCommutator(t1.e,t.e) for t1 in terms(l)]) 
distribute_commutators(l1::LinearCombination, l2::LinearCombination) = sum([t1.c*t2.c*SimpleCommutator(t1.e,t2.e) for t1 in terms(l1) for t2 in terms(l2)]) 
distribute_commutators(e::Element, l::LinearCombination) = distribute_commutators(Term(e), l)
distribute_commutators(l::LinearCombination, e::Element) = distribute_commutators(l, Term(e))

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

function Base.expand(c::SimpleCommutator)
    x = expand(c.x)
    y = expand(c.y)
    distribute_commutators(x, y)
end



key(g::Generator) = ('G', g.name)
key(e::Exponential) = ('E', key(e.e))
key(t::Term) = ('T', t.c, key(t.e))
key(c::SimpleCommutator) = ('C', key(c.x), key(c.y))
key(p::Product) = (vcat('P', [key(f) for f in p.p])...,)
key(l::LinearCombination) = (vcat('L', sort([key(t) for t in terms(l)]))...,)

simplify_sum(g::Generator) = g
simplify_sum(e::Exponential) = Exponential(simplify_sum(e.e))
simplify_sum(t::Term) = Term(t.c, simplify_sum(t.e))
simplify_sum(c::SimpleCommutator) = Commutator(simplify_sum(c.x), simplify_sum(c.y))
simplify_sum(p::Product) = Product([simplify_sum(f) for f in p.p])


function simplify_sum(l::LinearCombination)
    tab=Dict{Any, Term}()    
    for t0 in terms(l)
        t = simplify_sum(t0)
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
    r =  collect(values(tab))
    if length(r) == 0
        return ZeroElement
    elseif length(r) == 1
        t = r[1]
        if t.c==1
            return t.e
        else
            return t
        end
    else
        return LinearCombination(r)
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

function Base.contains(y::Array{T,1}, x::Array{T,1}) where T
    lx = length(x)
    ly = length(y)
    for j=1:ly-lx+1
        if x==y[j:j+lx-1]
            return true                    
        end
    end
    return false
end

Base.contains(y::Word, x::Word) = Base.contains(y.w, x.w)


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

generators(w::Word)=Set(w)
generators(W::Array{Word}) = union(generators.(W)...)

struct Lyndon
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

function lyndon_transform(w::Array{Int,1})
    w1 = Int[]
    c = 0
    for x in w[2:end]
        if x==1
            c += 1
        else
            push!(w1,c)
            c = 0
        end
    end
    push!(w1,c)
    w1
end

function lyndon_words(G::Array{Generator,1}, n::Integer; odd_terms_only::Bool=false, 
                      all_lower_terms::Bool=true, max_generator_order::Integer=n)
    s = length(G)
    @assert s==length(unique(G)) "Generators must be distinct"
    r = Word[]
    f = true
    for j=1:s
        if degree(G[j])!=j
            f = false
            break
        end
    end
    if !f 
       for w0 in Lyndon(s,n)
            w = Word(G[w0+1])
            d = degree(w)
            if  ((all_lower_terms && d<=n) || d==n) && (!odd_terms_only || isodd(d)) &&
                (max_generator_order>=n ||maximum([degree(g) for g in w])<=max_generator_order)
                push!(r, w)
            end
        end
    else # if degree(G[j])==j for all j then this algorithm is much faster
        first = true
        for w0 in Lyndon(2,n)
            if !first
                w1 = lyndon_transform(w0)
                if maximum(w1)<s
                    w = Word(G[w1 .+ 1])
                    d = degree(w)
                    if   ((all_lower_terms && d<=n) || d==n) && (!odd_terms_only || isodd(d)) &&
                        (max_generator_order>=n ||maximum([degree(g) for g in w])<=max_generator_order)
                        push!(r, w)
                    end
                end
            end
            first = false
        end
    end
    sort(r, lt=(x,y)->degree(x)<degree(y))
end

function lyndon_factorization(w::Array{Int,1})
    #taken from
    #Sukhpal Singh Ghuman, Emanuele Giaquinta, Jorma Tarhio:
    #Alternative Algorithms for Lyndon Factorization
    #
    f = Array{Int,1}[]
    k = 0
    while k<length(w)
        i = k+1
        j = k+2
        while true
            if j==length(w)+1 || w[j]<w[i]
                while k<i
                    push!(f, w[k+1:k+j-i])
                    k = k+j-i                    
                end
                break
            else
                if w[j]>w[i]
                    i = k+1
                else
                    i = i+1
                end
                j = j+1
            end
        end
    end
    f
end


Base.length(::Generator) = 1
Base.length(t::Term) = length(t.e)
Base.length(C::SimpleCommutator) = 
    (isa(C.x, SimpleCommutator) ? length(C.x) : 1)+(isa(C.y, SimpleCommutator) ? length(C.y) : 1)

degree(g::Generator) = g.degree
degree(t::Term) = degree(t.e)
degree(C::SimpleCommutator) = degree(C.x)+degree(C.y) 
degree(w::Word) = sum([degree(g) for g in w])

leading_word(C::Generator) = Word([C])
leading_word(C::SimpleCommutator) = Word(vcat(leading_word(C.x), leading_word(C.y)))

adjoint(g::Generator) = isodd(degree(g)) ? g : -g
adjoint(p::Product) = Product(adjoint.(reverse(factors(p))))
adjoint(e::Exponential) = Exponential(adjoint(e.e))
adjoint(c::SimpleCommutator) = SimpleCommutator(adjoint(c.y), adjoint(c.x))        
adjoint(t::Term) = t.c*adjoint(t.e)
adjoint(l::LinearCombination) = sum(adjoint.(terms(l)))

inv(e::Element) = error("not inverible")
inv(p::Product) = Product(reverse(inv.(factors(p))))
inv(ex::Exponential) = Exponential(-exponent(ex))
inv(t::Term) = (isa(t.c,Int) ? 1//t.c : 1/t.c)*inv(t.e)

diff(g::Generator) = degree(g)*g
diff(t::Term) = t.c*diff(t.e)
diff(l::LinearCombination) = sum(diff.(terms(l)))
diff(e::Exponential) = diff(exponent(e))*e
diff(c::SimpleCommutator) = SimpleCommutator(diff(c.x), c.y)+SimpleCommutator(c.x, diff(c.y))
function diff(p::Product)
    f = factors(p)
    sum([prod(vcat(f[1:j-1], diff(f[j]), f[j+1:end])) for j=1:length(f)])
end


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
                      odd_terms_only::Bool=false, all_lower_terms::Bool=true, 
                      max_generator_order::Integer=n) 
    W = lyndon_words(G, n)
    m = length(W)
    B = zeros(Element, m)
    for j=1:m
        w = W[j]
        if length(w) == 1
            B[j] = w[1]
        else
            k0 = 0
            j1 = 0
            for k=2:length(w)
                j1 = findfirst(W, w[k:end])
                if j1>0
                    k0 = k
                    break
                end
            end    
            j2 = findfirst(W, w[1:k0-1])
            B[j] = SimpleCommutator(B[j2], B[j1])
        end
    end
    [B[j] for j=1:m if
        ((all_lower_terms && degree(W[j])<=n) || degree(W[j])==n) && (!odd_terms_only || isodd(degree(W[j]))) &&
        (max_generator_order>=n ||maximum([degree(g) for g in W[j]])<=max_generator_order)]
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


function rightnormed_words(G::Array{Generator,1}, n::Integer; odd_terms_only::Bool=false, 
                           all_lower_terms::Bool=true, max_generator_order::Integer=n)
    W = lyndon_words(G, n, odd_terms_only=odd_terms_only, all_lower_terms=all_lower_terms,
                    max_generator_order=max_generator_order)
    [Word([G[g+1] for g in lyndon2rightnormed([findfirst(G,g)-1 for g in w])]) for w in W]
end


function rightnormed_bracketing(w::Word)
    if length(w) == 1
        return w[1]
    end
    SimpleCommutator(w[1], rightnormed_bracketing(w[2:end]))
end

function rightnormed_bracketing(e::Array{Element, 1})
    if length(e) == 1
        return e[1]
    end
    SimpleCommutator(e[1], rightnormed_bracketing(e[2:end]))
end


function rightnormed_basis(G::Array{Generator,1}, n::Integer; 
                      odd_terms_only::Bool=false, all_lower_terms::Bool=true, 
                      max_generator_order::Integer=n) 
    W = rightnormed_words(G, n, odd_terms_only= odd_terms_only, all_lower_terms=all_lower_terms,
                      max_generator_order=max_generator_order)
    [rightnormed_bracketing(w) for w in W]
end


struct MultiFor
    k::Array{Int,1}
end

Base.length(MF::MultiFor) = prod(MF.k+1)

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


function all_words(g::Array{Generator, 1}, n::Integer; odd_terms_only::Bool=false, 
                      all_lower_terms::Bool=true, max_generator_order::Integer=n)
    #TODO: implement max_generator_order
    nn = [k for k in (all_lower_terms ? 1 : n):n if !odd_terms_only || isodd(k)]
    vcat([[Word([g[j+1] for j in jj]) for jj in MultiFor(fill(length(g)-1,n))] for n in nn]...)
end


is_lie_element(e::Element)=false
is_lie_element(g::Generator)=true
is_lie_element(t::Term)=is_lie_element(t.e)
is_lie_element(c::SimpleCommutator) = is_lie_element(c.x) && is_lie_element(c.y)
is_lie_element(l::LinearCombination) = all(is_lie_element.(terms(l))) 

is_homogenous_lie_element(e::Element) = is_lie_element(e)
is_homogenous_lie_element(l::LinearCombination) = is_lie_element(l) && (length(l.l)<=1 ||all(degree(l.l[1]).==degree.(l.l[2:end]))) 

function degree(l::LinearCombination)
    @assert is_homogenous_lie_element(l) "homogenous lie element expected"
    length(l.l)==0 ? -1 : degree(l.l[1])
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
    if iszero(e)
        return ZeroElement
    end
    if !is_lie_element(e)
        return e
    end
    G = sort(collect(generators(e)), lt=(x,y)->x.name<y.name)
    e = expand(e)
    order = [g for g in order if g in G]
    order = unique(vcat(order,G))
    W = Word[]
    B = Element[] # Generator or SimpleCommutator
    c = Any[]
    for w in Lyndon(length(order), max_length(e))
        w1 = Word([order[g+1] for g in w])
        c0 = coeff(w1, e)
        #if c0!=0  #TODO! check efficiency!!!
            push!(c, c0)
            push!(W, w1)
            wb = Word([order[g+1] for g in Expocon.lyndon2rightnormed(w)])
            push!(B, rightnormed_bracketing(wb))
        #end
    end
    r = simplify_sum(LinearCombination(inv(Rational{Int}[coeff(w, b) for w in W, b in B])*c.*B))
    if isa(r, LinearCombination)
        return  LinearCombination(sort(terms(r), lt=(x,y)->(degree(x.e)<degree(y.e))||
            ((degree(x.e)==degree(y.e))&&(findfirst(B, x.e)<findfirst(B, y.e)))))
    elseif isa(r, Term) && r.c==1
        return r.e 
    else
        return r
    end
end

normalize_lie_elements(e::Exponential; order::Array{Generator,1}=Generator[])=
    Exponential(normalize_lie_elements(e.e, order=order))
normalize_lie_elements(p::Product; order::Array{Generator,1}=Generator[]) = 
    Product([normalize_lie_elements(f, order=order) for f in p.p])


#commute(e1::Element, e2::Element) = iszero(normalize_lie_elements(Commutator(e1,e2)))
#commute(e::Element, ex::Exponential) = commute(e, exponent(ex))
#commute(ex::Exponential, e::Element) = commute(exponent(ex), e)
#commute(ex1::Exponential, ex2::Exponential) = commute(exponent(ex1), exponent(ex2))

commute_normalized(e1::Element, e2::Element) =  false
commute_normalized(t::Term, e::Element) =  commute_normalized(t.e, e) 
commute_normalized(e::Element, t::Term) =  commute_normalized(e, t.e) 
commute_normalized(t1::Term, t2::Term) =  commute_normalized(t1.e, t2.e) 
commute_normalized(g1::Generator, g2::Generator) = g1==g2
commute_normalized(c1::SimpleCommutator, c2::SimpleCommutator) = c1==c2

function commute_normalized(l1::LinearCombination, l2::LinearCombination)
    t1 = terms(l1)
    t2 = terms(l2)
    if length(t1)!=length(t2)
        return false
    elseif length(t1)==0
        return true
    end
    f = commute_normalized(t1[1].e, t2[1].e)
    if !f || length(t1)==1
        return f 
    end
    c1 = t1[1].c
    c2 = t2[1].c
    for j=2:length(t1)
        if !commute_normalized(t1[j].e, t2[j].e) || c1*t2[j].c!=c2*t1[j].c
            return false
        end
    end
    return true
end

commute_normalized(e::Element, ex::Exponential) = commute_normalized(e, exponent(ex))
commute_normalized(ex::Exponential, e::Element) = commute_normalized(exponent(ex), e)
commute_normalized(ex1::Exponential, ex2::Exponential) = commute_normalized(exponent(ex1), exponent(ex2))

commute(e1::Element, e2::Element) = commute_normalized(normalize_lie_elements(e1),normalize_lie_elements(e2))


function simplify(p::Product)
    if length(factors(p))==0
        return Id
    end
    f = normalize_lie_elements.(factors(p))
    F = Tuple{Element, Element, Element}[] # (cummulative exponent ex, cummulative factors q, witness)
    ex = ZeroElement
    q = Id
    if isa(f[1], Exponential)
        ex = exponent(f[1])
        wit = ex
    else
        q = f[1]
        wit = q
    end
    for j=2:length(f)
        if !commute_normalized(f[j-1], f[j])
            ex = simplify_sum(ex)
            push!(F, (ex, q, wit))

            if isa(f[j], Exponential)
                ex = exponent(f[j])
                q = Id
                wit = ex
            else
                ex = ZeroElement
                q = f[j]
                wit = q 
            end
        else
            if isa(f[j], Exponential)
                ex = ex + exponent(f[j])
            else
                q = q*f[j]
            end
        end
    end
    ex = simplify_sum(ex)
    push!(F, (ex, q, wit))

    j = 1
    while true
        if j>length(F)
            break
        end
        (ex, q, wit) = F[j]
        if iszero(ex)&&is_id(q)
            F = vcat(F[1:j-1],F[j+1:end]) #remove F[j]
            if j>1&&j<=length(F)
                (ex1, q1, wit1) = F[j-1]
                (ex2, q2, wit2) = F[j]
                if commute_normalized(wit1, wit2)
                    q = q1*q2
                    ex = simplify_sum(ex1+ex2)
                    F[j-1] = (ex, q, wit1)
                    F = vcat(F[1:j-1],F[j+1:end]) #remove F[j]
                end
            end
            j = 1 #max(1, j-1)
        else
            j += 1
        end
    end

    r = Id
    for j=1:length(F)
        (ex, q, wit) = F[j]
        r = r*q
        if !iszero(ex)
            r = r*Exponential(ex)
        end
    end

    if isa(r, Product) && length(r.p)==1
        return r.p[1]
    elseif isa(r, Term) && isa(r.e, Product) && length(r.e.p)==1
        return r.c*(r.e.p[1])
    else
        return r
    end
end


simplify(e::Element) = normalize_lie_elements(e)
simplify(t::Term) = t.c*simplify(t.e)
simplify(l::LinearCombination) = simplify_sum(sum([expand(simplify(t)) for t in terms(l)]))


function rhs_splitting(W::Array{Word}) 
    G = degree.(collect(generators(W)))
    @assert all(G.==1) "Generators must have degree 1"
    [1//factorial(length(w)) for w in W]
end

function rhs_taylor(W::Array{Word})
    G = degree.(collect(generators(W)))
    @assert length(G)==length(unique(G)) "Generators must have distinct degrees"
    n = length(W)
    c = zeros(Rational{Int}, n)
    W1 = [[degree(g) for g in w] for w in W]
    p = maximum([sum(w) for w in W1])
    for i=1:n
        w = W1[i]
        c[i] = 1//prod([sum(w[j:end]) for j=1:length(w)])
    end
    c
end    


function rhs_taylor_symmetric(W::Array{Word})
    G = degree.(collect(generators(W)))
    @assert length(G)==length(unique(G)) "Generators must have distinct degrees"
    T = Rational{Int}    
    n = length(W)
    c = zeros(T, n)
    W1 = [[degree(g) for g in w] for w in W]
    p = maximum([sum(w) for w in W1])
    Cinv = T[(-1)^(m+n)*(n>=m ? binomial(n,m)//2^(n-m) : 0) for m=0:p-1, n=0:p-1]
    for i=1:n
        w = W1[i]
        l = length(w)
        s = zero(T)
        for v in MultiFor(w-1)
            s += prod([Cinv[v[j]+1,w[j]]/sum([v[i]+1 for i=j:l]) for j=1:l])
        end
        c[i] = s
    end
    c
end


function rhs_legendre(W::Array{Word})
    G = degree.(collect(generators(W)))
    @assert length(G)==length(unique(G)) "Generators must have distinct degrees"
    T = Rational{Int}    
    n = length(W)
    c = zeros(T, n)
    W1 = [[degree(g) for g in w] for w in W]
    p = maximum([sum(w) for w in W1])
    Cinv = T[(-1)^(m+n)*binomial(n,m)*binomial(n+m,m) for m=0:p-1, n=0:p-1]
    for i=1:n
        w = W1[i]
        l = length(w)
        s = zero(T)
        for v in MultiFor(w-1)
            s += prod([Cinv[v[j]+1,w[j]]/sum([v[i]+1 for i=j:l]) for j=1:l])
        end
        c[i] = s
    end
    c
end


function splitting_method(A::Generator, a::Vector, B::Generator, b::Vector)   
    sa = length(a)
    sb = length(b)
    ex = Id
    for j=1:max(sa, sb)
        if j<=sa && a[j]!=0
            ex = exp(a[j]*A)*ex
        end
        if j<=sb && b[j]!=0
            ex = exp(b[j]*B)*ex
        end
    end
    ex
end

function splitting_method(A::Generator, a::Vector, B::Generator, b::Vector, C::Generator, c::Vector)   
    sa = length(a)
    sb = length(b)
    sc = length(c)
    ex = Id
    for j=1:max(sa, sb, sc)
        if j<=sa && a[j]!=0
            ex = exp(a[j]*A)*ex
        end
        if j<=sb && b[j]!=0
            ex = exp(b[j]*B)*ex
        end
        if j<=sc && c[j]!=0
            ex = exp(c[j]*C)*ex
        end
    end
    ex
end

mult_t(e::Exponential, c) = mult_t(e.e, c)
mult_t(g::Generator, c) = c^degree(g)*g
mult_t(t::Term, c) = t.c*mult_t(t.e, c)
mult_t(C::SimpleCommutator, c) = SimpleCommutator(mult_t(C.x, c), mult_t(C.y, c))
mult_t(p::Product, c) = Product([mult_t(f, c) for f in factors(p)])
mult_t(l::LinearCombination, c) = LinearCombination([mult_t(t, c) for t in terms(l)])

function composition(Phi::Product, g::Vector)
    @assert all([isa(f, Exponential) for f in factors(Phi)]) 
    prod([prod([Exponential(mult_t(f.e, c)) for f in factors(Phi)]) for c in g])
end

composition(Phi::Exponential, g::Vector) = composition(Product([Phi]), g)


function exp_superdiagm(x::Array{T,1}) where T
    n = length(x)
    f = 1
    xx = x[:]
    eX = eye(T <: Integer ? Rational{T} : T,n+1)
    for k=1:n
        f *= k
        if T<:Integer
            for j=1:n-k+1
                eX[j,j+k] = xx[j]//f
            end
        else
            for j=1:n-k+1
                eX[j,j+k] = xx[j]/f
            end
        end
        if k<n
            bf = true
            for j=1:n-k
                xx[j] *= x[k+j]
                bf = bf && xx[j]==0
            end
            if bf
                break
            end
        end
    end
    eX
end

function coeff_BCH(G::Array{Generator,1},w::Word; apply_log::Bool=true)
    @assert length(G)==2 && G[1]!=G[2]
    n = length(w)
    x = [c==G[1] ? 1 : 0 for c in w]
    y = 1-x
    eX = exp_superdiagm(x)
    eY = exp_superdiagm(y)
    Q = eX*eY
    if !apply_log
        return Q[1,end]
    end
    for j=1:n+1
        Q[j,j] -= 1
    end
    q = Q[:,end]
    z = q[:]
    for k=2:n
        q = Q*q
        z += ((-1)^(k+1)//k)*q
    end
    z[1]
end

function coeff_BCH(G::Array{Generator,1},w::Word, a::Array{T,1}, b::Array{T,1}; apply_log::Bool=true) where T
    @assert length(G)==2 && G[1]!=G[2]
    @assert length(a)==length(b)
    n = length(w)
    Q = eye(T, n+1)
    for j=1:length(a)
        x = T[c==G[1] ? a[j] : zero(T) for c in w]
        y = T[c==G[2] ? b[j] : zero(T) for c in w]
        eX = exp_superdiagm(x)
        eY = exp_superdiagm(y)
        Q = j==1 ? eX*eY : Q*eX*eY
    end
    if !apply_log
        return Q[1,end]
    end
    for j=1:n+1
        Q[j,j] -= 1
    end
    q = Q[:,end]
    z = q[:]
    for k=2:n
        q = Q*q
        z += ((-1)^(k+1)//k)*q
    end
    z[1]
end

function coeff_BCH(G::Array{Generator,1},w::Word, F::Array{T,2}; apply_log::Bool=true) where T
    n = length(w)
    Q = eye(T, n+1)
    kk = [findfirst(G, c) for c in w]
    for j=1:size(F, 1)
        x = T[k!=0 ? F[j,k] : zero(T) for k in kk]
        eX = exp_superdiagm(x)
        Q = j==1 ? eX : Q*eX
    end
    if !apply_log
        return Q[1,end]
    end
    for j=1:n+1
        Q[j,j] -= 1
    end
    q = Q[:,end]
    z = q[:]
    for k=2:n
        q = Q*q
        z += ((-1)^(k+1)//k)*q
    end
    z[1]
end


function BCH(G::Array{Generator,1}, p::Int; use_rightnormed_basis::Bool=false)    
    @assert length(G)==2 && G[1]!=G[2]
    W = lyndon_words(G, p)
    L = use_rightnormed_basis ? rightnormed_basis(G, p) : lyndon_basis(G, p)
    Phi = inv([coeff(w,b)//1 for w in W, b in L])
    c = Phi*[coeff_BCH(G,w) for w in W]
    [c[j].*L[j] for j=1:length(c) if c[j]!=0]
end

hom(w::Word, g::Generator) = diagm([a==g ? 1 : 0 for a in w], 1)
hom(w::Word, t::Term) = t.c*hom(w, t.e)
hom(w::Word, l::LinearCombination) = sum([hom(w, t) for t in terms(l)])
hom(w::Word, p::Product) = length(factors(p))==0 ? eye(Int,length(w)+1) : prod([hom(w, f) for f in factors(p)])
hom(w::Word, c::SimpleCommutator) = hom(w, c.x)*hom(w, c.y)-hom(w, c.y)*hom(w, c.x)

function hom(w::Word, e::Exponential)
    x = hom(w, e.e)
    @assert iszero(diag(x)) "exponent with constant term"
    y = copy(x)
    r = copy(x)
    for k=2:length(w)
        y = x*y
        if iszero(y)
            break
        end
        r += y*1//factorial(k)
    end
    r += eye(Int, length(w)+1)
    r
end

hom(w::Word, g::Generator, v::Vector) = vcat([w[j]==g ? v[j+1] : 0 for j=1:length(w)],0)
hom(w::Word, t::Term, v::Vector) = t.c .* hom(w, t.e, v)
hom(w::Word, l::LinearCombination, v::Vector) = sum([hom(w, t, v) for t in terms(l)])

function hom(w::Word, p::Product, v::Vector) 
    v1 = copy(v)
    for f in reverse(factors(p))
        if iszero(v1)
            return v1
        end
        v1 = hom(w, f, v1)
    end
    v1
end

hom(w::Word, c::SimpleCommutator, v::Vector) = hom(w, c.x, hom(w, c.y, v))-hom(w, c.y, hom(w, c.x, v))

function hom(w::Word, e::Exponential, v::Vector)
    y = copy(v)
    r = copy(v)
    for k=1:length(w)
        y = hom(w, e.e, y)
        if iszero(y)
            return r
        end
        r += y*1//factorial(k)
    end
    r
end

coeff(w::Word, S::Element) = hom(w, S, vcat(zeros(Int,length(w)), 1))[1] 
coeffs(W::Array{Word,1}, S::Element) = [coeff(w, S) for w in W]


function logtriu(Q::Matrix; last_column_only::Bool=false)
    n,m = size(Q)
    @assert n==m "matrix must be square"    
    @assert istriu(Q) && iszero(diag(Q)-1) "matrix must be upper triangular with unit diagonal"
    Q = copy(Q)
    for j=1:n
        Q[j,j] = 0
    end
    if last_column_only
        q = Q[:,end]
        z = q[:]
    else
        q = copy(Q)
        z = copy(Q)
    end
    for k=2:n
        q = Q*q
        if iszero(q)
            break
        end
        z += ((-1)^(k+1)//k)*q
    end
    z
end

end # Expocon
