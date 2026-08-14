function residue(omega::FunFldDiff, p::Hecke.GenOrdIdl, check_prime::Bool = true)
  if check_prime && !is_prime(p)
    error("not a prime ideal")
  end 

  O = order(p)
  kC = function_field(O)
  k,ev = residue_field(O, p)
  
  if constant_field(kC) != rational_field()
    error("Currently broken for constant fields which are not QQ")
  end
  if p isa Hecke.GenOrdIdl{<:Any, <:KInftyRing}
    error("Infinite places are not implemented")
  end

  B = basis(p)
  i = findfirst(b -> valuation(ideal(O,b), p) == 1, B)
  i = nothing && error("No uniformizer found; this should not happen and is probably a bug")
  t = kC(B[i])

  dt = differential(t)
  f = omega // dt

  vf = valuation(f * O, p)

  #very crude way to compute residue
  if vf > -1
    return zero(k)
  end
  vf = - vf
  g = t^(vf) * f
  for _ in (1:vf-1)
    g = differential(g) // dt
  end

  #denominator is quite expensive for big examples
  den = denominator(O * g)
  num = O(den * g)

  return inv(k(factorial(vf - 1))) * ev(O(num)) * inv(ev(O(den)))

end


function _check_dim(
  forms::Vector{<:FunFldDiff},
  functions::Vector{<:AbstractAlgebra.Generic.FunctionFieldElem}
  )
  #input: a set of rational 1-forms and a finite subset of kC
  #output: the dimension of <forms> modulo <dfunctions>

  if length(forms) == 0
    return 0
  end

  big_space = [[differential(f).f for f in functions]; [omega.f for omega in forms]]
  Dx = lcm([lcm([denominator(a) for a in coordinates(f)]) for f in big_space])
  big_space_cleared = [Dx * f for f in big_space]
  N = maximum(maximum(degree(numerator(a)) for a in coordinates(f)) for f in big_space_cleared) + 1

  k = constant_field(parent(functions[1]))
  to_be_matrix = Vector{Vector{elem_type(k)}}()

  for f in big_space_cleared
    row = Vector{elem_type(k)}()
    for a in coordinates(f)
      coeff = [k(c) for c in Tuple(Hecke.coefficients(numerator(a)))]
      append!(row, [coeff; fill(zero(k), N - length(coeff))])
    end
    push!(to_be_matrix, row)
  end

  A = matrix(to_be_matrix)

  #apply dim(V cap W) = dim(V) + dim(W) - dim(V + W)
  #and   dim(V/S) = dim(V) - dim(S)
  dim_of_sum = rank(A)
  dim_of_dLR = rank(A[1:length(functions), :])
  return dim_of_sum - dim_of_dLR
end

function _change_ring(f::Union{MPolyRingElem, PolyRingElem}, i::NumFieldHom)
  @req domain(i) == base_ring(f) "embedding and base ring of f do not have same domain"
  @req codomain(i) == QQBar "embedding should be into QQBar"
  if typeof(f) <: PolyRingElem
    R,var = polynomial_ring(QQBar, symbols(parent(f))[1])
    return sum([i(c) * var^(n-1) for (n,c) in enumerate(Hecke.coefficients(f))], init = zero(R))
  end
  Rm,gen = polynomial_ring(QQBar, symbols(parent(f)))
  return sum(
    [i(c) * prod(s^i for (i,s) in zip(v,gen)) for (c,v) in zip(Hecke.coefficients(f), exponent_vectors(f))],
    init = zero(Rm)
  )
end

function adjoin(K::AbsSimpleNumField, iota::NumFieldHom, els::Vector{QQBarFieldElem})
  #iota is an embedding of K into QQBar 
  @assert domain(iota) == K && codomain(iota) == QQBar "domain and codomain of morph don't check out"
  #requires K to be simple 
  b = gen(K)
  j = hom(K,K,b)
  L = K
  i = iota
  preimages = Vector{NumFieldElem}()
  for alpha in els
    g = minpoly(alpha)

    for c in 1:30

      theta = i(b) + c * alpha
      h = minpoly(theta)
      Lext,t = number_field(h, :a)
      LextY,Y = polynomial_ring(Lext)

      f = change_base_ring(Lext,minpoly(gen(L)))
      fac = gcd(f(t - c*Y), change_base_ring(Lext,g))

      if isone(degree(fac))
        preim = -coeff(fac,0)//coeff(fac,1)
        Lgen = t - c * preim #Lgen is the generator of L in Lext

        #construct embedding of K into Lext
        j = j * hom(L,Lext,Lgen)

        preimages = [sum(coeff(x,k) * Lgen^k for k in (0:degree(L)-1))  for x in preimages]
        push!(preimages, preim)
        L = Lext
        b = gen(Lext)
        i = hom(Lext,QQBar,theta)
        break
      end

      c == 30 && error("stupid error, enlarge c")
    end
  end
  #L is the field K(els)
  #i is embedding of L into QQBar
  #j is the embedding from K to L 
  #preimages are the elements in els but as elements in K. 
  return L, i, j, preimages

end

function find_preim(K::NumField, iota::NumFieldHom, theta::QQBarFieldElem; prec::Int=256)
  #takes number field K with embedding K -> QQBar and 
  #element of QQBar which has a preimage under this embedding 
  #and returns this element as an element of K.
  if is_rational(theta)
    g = minpoly(theta)
    return -coeff(g,0) // coeff(g,1)
  end
  CC = AcbField(prec)
  alpha = gen(K)
  alpha_hat = CC(iota(alpha))

  n = degree(K)
  M = zero_matrix(integer_ring(), n + 1, n + 3)
  
  C = BigFloat(2)^(prec - 10)

  for i in (1:n)
    M[i,i] = 1
    M[i, n + 2] = round(ZZRingElem, C * BigFloat(real(alpha_hat^(i - 1))))
    M[i, n + 3] = round(ZZRingElem, C * BigFloat(imag(alpha_hat^(i - 1))))
  end
  M[n + 1, n + 1] = 1
  M[n + 1, n + 2] = round(ZZRingElem, C * BigFloat(real(-CC(theta))))
  M[n + 1, n + 3] = round(ZZRingElem, C * BigFloat(imag(-CC(theta))))

  redM = lll(M)

  for c in eachrow(redM)
    c[n + 1] == 0 && continue
    candidate = sum(c[k] * alpha^(k-1) for k in 1:n) // c[n + 1]
    iota(candidate) == theta && return candidate
  end

  return nothing

end

function embed_number_field(K::Union{NumField,QQField}, v::InfPlc)
    @req base_field(K) == rational_field() "base field should be QQ"
    println(v)
    println(embeddings(v))
    iota = embeddings(v)[1]
    _,t = polynomial_ring(rational_field())
    F,gen = embedded_number_field([minpoly(s) for s in Hecke.gens(K)],[ComplexF64(iota(s)) for s in Hecke.gens(K)])
    if length(gen) == 1
        f = hom(K,F,gen[1])
    else 
      f = hom(K,F,gen)
    end
    return F,f
end

function map_function_field_coeffs(f::AbstractAlgebra.Generic.FunctionFieldElem, emb::S, F::AbstractAlgebra.Generic.AbsSimpleFunctionField) where S 
    #F is the same function field as parent(f) except its constant field is an 
    #extension of the constant field of parent(f)
    #i is some map between the constant fields (so this could also be a retraction 
    #of an embedding into QBar) 
    #returns f as an element of F
    x,y = F(gen(base_ring(F))), gen(F)
    num = numerator(f)
    denom = denominator(f)

    return sum([
    sum([emb(a) * x^(j-1) for (j,a) in enumerate(coefficients(b))], init=zero(x)) * y^(i-1)
    for (i,b) in enumerate(coefficients(num))], init=zero(y)
    ) // sum([emb(a) * x^(j-1) for (j,a) in enumerate(coefficients(denom))], init=zero(x))

end

function homogenize(g::AbstractAlgebra.Generic.FunctionFieldElem)
  #input: element from a function field
  #output: (num, denom) with num and denom being homogeneous of the same degree
  #the element num/denom is a function in projective coordinates 
  R,(X,Y,Z) = polynomial_ring(constant_field(parent(g)), [:X,:Y,:Z])

  g_XY = sum([coef(X) * Y^(i-1) for (i,coef) in enumerate(coefficients(numerator(g)))], init=zero(R))
  g_H = sum([Z^(total_degree(g_XY) - total_degree(f)) * f for f in terms(g_XY)], init = zero(R))
  d_H = sum([Z^(degree(denominator(g)) - j) * X^j * coeff(denominator(g),j) for j in (0:degree(denominator(g)))], init = zero(R))
  n = max(total_degree(d_H), total_degree(g_H))
  
  g_H *= Z^(n - total_degree(g_H))
  d_H *= Z^(n - total_degree(d_H))

  return (R(g_H),R(d_H))

end

function _evaluate(p::Hecke.GenOrdIdl)
  M = basis_matrix(p)
  O = order(p)
  a = -M[1,1](0)
  M[1,1] = zero(QQBar)
  v = kernel(transpose(M))
  ev_vec = inv(v[1]) * v
    
    function ev_p(f::AbstractAlgebra.Generic.FunctionFieldElem)
      num = nothing
      denom = one(base_ring(O))
      try 
        num = O(f)
      catch 
        denom = denominator(f * O)
        num = O(denom * f)
      end
      return inv(denom(a)) * sum(alpha(a) * ev for (alpha,ev) in zip(coordinates(num),ev_vec))
    end
    return ev_p
end



"""
    voronoi_cells(points; box_radius = nothing)

Compute the Voronoi diagram of a finite set of points in the complex plane.

`points` can be any vector of numbers convertible to `ComplexF64` (e.g. a
`Vector{ComplexF64}`, or a vector of Hecke/Nemo `acb`/`ComplexFieldElem`
values — these get converted to floating point for the geometric
computation).

Returns `O::Vector{Vector{ComplexF64}}` with `length(O) == length(points)`,
where `O[i]` is the list of vertices, in cyclic (counterclockwise) order,
of the Voronoi cell belonging to `points[i]`.

# Algorithm

Since Hecke/Nemo have no `Polyhedron` type (unlike Sage's
`sage.geometry.polyhedron`), this does NOT use the
lift-to-a-paraboloid-and-take-a-convex-hull trick from
`sage.geometry.voronoi_diagram`. Instead it builds each cell directly as an
intersection of half-planes, which is elementary in 2D:

    C_i = ⋂_{j ≠ i} { z ∈ ℂ : |z - p_i| ≤ |z - p_j| }

Expanding the distance inequality gives a linear condition in z:

    |z-p_i|^2 ≤ |z-p_j|^2
      ⟺ Re( conj(p_j - p_i) * z ) ≤ ( |p_j|^2 - |p_i|^2 ) / 2

Each cell is obtained by starting from a large bounding box (so unbounded
cells still come back as a finite polygon) and clipping it against each of
these half-planes in turn using the Sutherland–Hodgman polygon-clipping
algorithm. This is O(n^2 * (average #vertices)) — fine for small/medium
point sets; for large n a proper Fortune's-algorithm implementation would
be preferable, but this needs no external geometry library.

# Caveats

- Comparisons are done in floating point (`ComplexF64`); if you need
  certified / interval results you'd have to redo the clipping using ball
  arithmetic and interval comparisons (`<=` is not well-defined on `acb`
  balls that straddle each other), which is why we convert to floats here.
- Coincident input points, or more than 3 cells meeting at a single vertex
  degeneracies, are not specially handled.
- `box_radius` lets you force the size of the bounding box the unbounded
  cells get clipped to; by default it's chosen automatically from the
  spread of the input points.

# Example

```julia
julia> pts = ComplexF64[0, 1, 1im, 1+1im, 0.5+0.5im]
julia> O = voronoi_cells(pts)
julia> O[5]   # cell of the interior point 0.5+0.5im
```
"""
function voronoi_cells(points::AbstractVector; box_radius::Union{Nothing,Real}=nothing, return_box::Bool=false)
    n = length(points)
    if n == 0
        empty_O = Vector{Vector{ComplexF64}}()
        return return_box ? (empty_O, ComplexF64[]) : empty_O
    end

    pts = ComplexF64[ComplexF64(Float64(real(p)), Float64(imag(p))) for p in points]

    if box_radius === nothing
        maxabs = maximum(abs.(pts))
        spread = n <= 1 ? 1.0 : maximum(abs(pts[i] - pts[j]) for i in 1:n for j in i+1:n)
        R = 1.1*maxabs
    else
        R = Float64(box_radius)
    end

    cx = sum(real.(pts)) / n
    cy = sum(imag.(pts)) / n

    box = ComplexF64[
        (cx - R) + im*(cy - R),
        (cx + R) + im*(cy - R),
        (cx + R) + im*(cy + R),
        (cx - R) + im*(cy + R),
    ]

    # Clip a convex polygon `poly` (vertices in order) against the half-plane
    #   Re(conj(a) * z) <= b
    function clip_halfplane(poly::Vector{ComplexF64}, a::ComplexF64, b::Float64)
        m = length(poly)
        m == 0 && return poly
        tol = 1e-9 * max(1.0, abs(a), abs(b))
        inside(z) = real(conj(a) * z) <= b + tol
        out = ComplexF64[]
        for k in 1:m
            cur = poly[k]
            nxt = poly[mod1(k + 1, m)]
            cur_in = inside(cur)
            nxt_in = inside(nxt)
            if cur_in
                push!(out, cur)
            end
            if cur_in != nxt_in
                d = nxt - cur
                denom = real(conj(a) * d)
                if abs(denom) > 1e-14
                    t = (b - real(conj(a) * cur)) / denom
                    push!(out, cur + t * d)
                end
            end
        end
        return out
    end

    O = Vector{Vector{ComplexF64}}(undef, n)
    for i in 1:n
        poly = copy(box)
        pi_ = pts[i]
        for j in 1:n
            j == i && continue
            isempty(poly) && break
            pj = pts[j]
            a = pj - pi_
            b = (abs2(pj) - abs2(pi_)) / 2
            poly = clip_halfplane(poly, a, b)
        end
        O[i] = unique(poly)
    end

    if return_box
        xmin, xmax = cx - R, cx + R
        ymin, ymax = cy - R, cy + R
        tol = 1e-8 * max(1.0, R)
        on_box(z) = isapprox(real(z), xmin; atol=tol) || isapprox(real(z), xmax; atol=tol) ||
                    isapprox(imag(z), ymin; atol=tol) || isapprox(imag(z), ymax; atol=tol)

        boxpts = ComplexF64[]
        for cell in O, z in cell
            on_box(z) && push!(boxpts, z)
        end
        # also make sure the 4 corners themselves are included even if no
        # cell happens to touch a given corner
        for c in box
            any(isapprox(c, w; atol=tol) for w in boxpts) || push!(boxpts, c)
        end
        # de-duplicate (within tolerance)
        uniq = ComplexF64[]
        for z in boxpts
            any(isapprox(z, w; atol=tol) for w in uniq) || push!(uniq, z)
        end
        # sort by angle around the box center for a sensible cyclic order
        sort!(uniq, by = z -> atan(imag(z) - cy, real(z) - cx))

        return O, uniq
    end

    return O
end

# =============================================================================
# Float64 Delaunay triangulation (Bowyer–Watson).
#
# This part is purely combinatorial: it decides WHICH triples of sites form
# Delaunay triangles, using ordinary double-precision arithmetic. Getting a
# fully certified triangulation (rigorous in-circle tests) is a much bigger
# undertaking and isn't attempted here; in practice degeneracies only bite
# on genuinely cocircular/collinear configurations, which are rare for
# generic input. The *positions* of the resulting Voronoi vertices ARE
# certified (see `_circumcenter` below) — only the combinatorics is
# approximate.
# =============================================================================
 
struct _Pt
    x::Float64
    y::Float64
end
 
_ccw(a::_Pt, b::_Pt, c::_Pt) =
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x) > 0
 
function _in_circumcircle(a::_Pt, b::_Pt, c::_Pt, p::_Pt)
    # assumes a,b,c listed counterclockwise
    ax, ay = a.x - p.x, a.y - p.y
    bx, by = b.x - p.x, b.y - p.y
    cx, cy = c.x - p.x, c.y - p.y
    det = (ax^2 + ay^2) * (bx * cy - cx * by) -
          (bx^2 + by^2) * (ax * cy - cx * ay) +
          (cx^2 + cy^2) * (ax * by - bx * ay)
    return det > 0
end
 
function _delaunay(pts::Vector{_Pt})
    n = length(pts)
    minx = minimum(p.x for p in pts); maxx = maximum(p.x for p in pts)
    miny = minimum(p.y for p in pts); maxy = maximum(p.y for p in pts)
    dmax = max(maxx - minx, maxy - miny, 1.0)
    midx, midy = (minx + maxx) / 2, (miny + maxy) / 2
 
    # super-triangle enclosing everything
    s1 = _Pt(midx - 20dmax, midy - dmax)
    s2 = _Pt(midx,          midy + 20dmax)
    s3 = _Pt(midx + 20dmax, midy - dmax)
    allpts = vcat(pts, [s1, s2, s3])
    i1, i2, i3 = n + 1, n + 2, n + 3
    tri0 = _ccw(allpts[i1], allpts[i2], allpts[i3]) ? (i1, i2, i3) : (i1, i3, i2)
    triangles = Set{NTuple{3,Int}}([tri0])
 
    for pi in 1:n
        p = allpts[pi]
        bad = [t for t in triangles
               if _in_circumcircle(allpts[t[1]], allpts[t[2]], allpts[t[3]], p)]
        isempty(bad) && continue  # p already (numerically) on the hull edge, skip
 
        edges = Set{Tuple{Int,Int}}()
        for t in bad
            for e in ((t[1], t[2]), (t[2], t[3]), (t[3], t[1]))
                push!(edges, e)
            end
        end
        boundary = [e for e in edges if !((e[2], e[1]) in edges)]
 
        for t in bad
            delete!(triangles, t)
        end
        for e in boundary
            newt = (e[1], e[2], pi)
            if !_ccw(allpts[newt[1]], allpts[newt[2]], allpts[newt[3]])
                newt = (e[2], e[1], pi)
            end
            push!(triangles, newt)
        end
    end
 
    return [t for t in triangles if all(v -> v <= n, t)]
end
 
# =============================================================================
# Certified circumcenter of three sites a,b,c ∈ CC (an AcbField), computed by
# solving the real 2x2 linear system for the offset from `a` in Arb ball
# arithmetic. This is rigorous: the returned AcbFieldElem ball is guaranteed to
# contain the true circumcenter, PROVIDED the denominator ball `D` does not
# contain 0 (i.e. the triple is certifiably non-collinear at the given
# precision). If it does contain 0, increase the precision of the input
# points and retry.
# =============================================================================
 
function _circumcenter(a::AcbFieldElem, b::AcbFieldElem, c::AcbFieldElem)
    CC = parent(a)
    u, v = b - a, c - a
    u1, u2 = real(u), imag(u)
    v1, v2 = real(v), imag(v)
    ru = (u1^2 + u2^2) / 2
    rv = (v1^2 + v2^2) / 2
    D = u1 * v2 - u2 * v1
    if contains(D, 0)
        error("VoronoiCC: circumcenter denominator ball contains 0 " *
              "(near-collinear/cocircular triple at current precision); " *
              "increase precision of the input points.")
    end
    x = (ru * v2 - rv * u2) / D
    y = (u1 * rv - v1 * ru) / D
    return a + CC(x, y)
end
 
_to_float(z::AcbFieldElem) = (Float64(real(z)), Float64(imag(z)))
 
# =============================================================================
# Deduplicate circumcenters that represent the same Voronoi vertex.
#
# Multiple Delaunay triangles share a circumcenter exactly whenever more than
# 3 sites are cocircular (a very natural occurrence for symmetric point
# configurations) -- in that case every triangle among those cocircular sites
# yields the SAME vertex, and their certified balls will overlap (typically
# near-identically). We merge such balls via union-find on pairwise overlap.
# =============================================================================
 
function _dedupe_groups(vs::Vector{AcbFieldElem})
    m = length(vs)
    parent = collect(1:m)
    function find(x)
        while parent[x] != x
            parent[x] = parent[parent[x]]
            x = parent[x]
        end
        return x
    end
    for i in 1:m, j in i+1:m
        if overlaps(vs[i], vs[j])
            ri, rj = find(i), find(j)
            ri != rj && (parent[ri] = rj)
        end
    end
    groups = Dict{Int,Vector{Int}}()
    for i in 1:m
        push!(get!(groups, find(i), Int[]), i)
    end
    return collect(values(groups))  # Vector of index-groups, each = one true vertex
end
 
# =============================================================================
# Main entry point
# =============================================================================
 
"""
    voronoi_diagram(points::Vector{AcbFieldElem}; R=nothing, n_boundary::Int=6)
        -> (vertices, vertex_labels, cells, boundary_vertices, boundary_labels)
 
Voronoi diagram of `points` (elements of a common `AcbField`), computed as
the dual of a Delaunay triangulation.
 
- `vertices[k]` is a certified ball containing the k-th Voronoi vertex.
  Circumcenters from distinct Delaunay triangles are merged into one vertex
  whenever their balls overlap, so a vertex incident to 4+ cocircular sites
  (e.g. from a symmetric point configuration) appears exactly once.
- `vertex_labels[k]` is the sorted list of ALL site indices (into `points`)
  equidistant from `vertices[k]` — normally a triple, but longer for
  cocircular degeneracies. This is a structural, non-numeric identifier for
  the vertex.
- `cells[i]` is a list of indices into `vertices`, in cyclic (angular) order
  around `points[i]`, giving the boundary of the Voronoi cell of the i-th
  input point.
- `boundary_vertices` / `boundary_labels`: same format as `vertices` /
  `vertex_labels`, but for the vertices that touch ONLY the auxiliary
  boundary points below (never a real input point). These are exactly the
  vertices that close off the outer, would-otherwise-be-unbounded cells; they
  don't belong to any `cells[i]` since they aren't adjacent to any real site,
  but they ARE the outer boundary of the whole diagram. Their labels use
  indices `n+1, ..., n+n_boundary` for the auxiliary points, where
  `n = length(points)`.
 
Since some cells would otherwise be unbounded, `n_boundary` auxiliary points
`centroid + R * ζ_{n_boundary}^k` are added around the configuration before
triangulating (`ζ_n = exp(2πi/n)`, computed rigorously via `const_pi`/`exp`
in the given precision). `R` defaults to 8x the max distance from the
centroid to any input point.
"""
function voronoi_diagram(points::Vector{AcbFieldElem}; R::Union{Nothing,Real}=nothing,
                          n_boundary::Int=6)
    n = length(points)
    #n >= 3 || error("VoronoiCC: need at least 3 points")
    CC = parent(points[1])
    RR = ArbField(precision(CC))
 
    cent = sum(points) // CC(n)
    if R === nothing
        cx, cy = _to_float(cent)
        Rf = 4 * maximum(begin
            px, py = _to_float(p)
            hypot(px - cx, py - cy)
        end for p in points)
        R = Rf == 0 ? 1.0 : Rf
    end
 
    pival = const_pi(RR)
    boundary_pts = AcbFieldElem[]
    if n_boundary > 0
        for k in 0:n_boundary-1
            theta = pival * (2k) / n_boundary
            unitk = exp(CC(RR(0), theta))
            push!(boundary_pts, cent + CC(R) * unitk)
        end
    end
 
    allsites = vcat(points, boundary_pts)
 
    # For the COMBINATORIAL triangulation only, perturb the float coordinates
    # by a tiny deterministic amount. Exactly-cocircular or exactly-collinear
    # input (e.g. roots of unity, or symmetric configurations generally) puts
    # the float in-circle test in `_delaunay` right on a knife edge, where
    # ordinary floating-point noise can flip it inconsistently and produce a
    # self-intersecting (invalid) triangulation. A deterministic golden-angle
    # perturbation breaks these ties the same way every time, giving a valid
    # planar triangulation. The certified circumcenters below are computed
    # from the ORIGINAL, unperturbed points, so no accuracy is lost -- and
    # the overlap-based dedup step still correctly re-merges vertices that
    # are truly coincident, since the real circumcenters don't move.
    scale = maximum(hypot(_to_float(z)...) for z in allsites)
    scale = scale == 0 ? 1.0 : scale
    eps = 1e-9 * scale
    golden_angle = 2.399963229728653
    fpts = _Pt[]
    for (idx, z) in enumerate(allsites)
        x, y = _to_float(z)
        push!(fpts, _Pt(x + eps * cos(idx * golden_angle),
                        y + eps * sin(idx * golden_angle)))
    end
    tris = _delaunay(fpts)
 
    raw_vertices = [_circumcenter(allsites[t[1]], allsites[t[2]], allsites[t[3]])
                    for t in tris]
 
    # Merge triangles whose circumcenters coincide (cocircular sites) into a
    # single Voronoi vertex; a vertex's label is then the union of all sites
    # equidistant from it, not just one triangle's triple.
    groups = _dedupe_groups(raw_vertices)
    vertices = [raw_vertices[first(g)] for g in groups]
    vertex_labels = [sort!(unique(vcat([collect(tris[idx]) for idx in g]...)))
                      for g in groups]
    tri_group = Vector{Int}(undef, length(tris))
    for (gidx, g) in enumerate(groups), idx in g
        tri_group[idx] = gidx
    end
 
    cells = Vector{Vector{Int}}(undef, n)
    for site in 1:n
        px, py = _to_float(points[site])
        incident = unique(tri_group[idx] for idx in 1:length(tris) if site in tris[idx])
        # order cyclically by angle of vertex (float midpoint) around the site
        sort!(incident, by = vidx -> begin
            vx, vy = _to_float(vertices[vidx])
            atan(vy - py, vx - px)
        end)
        cells[site] = incident
    end
 
    # Vertices that touch at least one auxiliary boundary point (index > n)
    # -- these are the ones lying on/near the outer boundary of the whole
    # diagram. (A vertex can touch both a real site and a boundary point, in
    # which case it shows up in both `vertices` and `boundary_vertices`.)
    touches_boundary = [any(x -> x > n, lbl) for lbl in vertex_labels]
    boundary_vertices = vertices[touches_boundary]
    boundary_labels = vertex_labels[touches_boundary]
 
    used = sort!(unique(vcat(cells...)))
    newidx = Dict(old => new for (new, old) in enumerate(used))
    vertices = vertices[used]
    vertex_labels = vertex_labels[used]
    for site in 1:n
        cells[site] = [newidx[v] for v in cells[site]]
    end
 
    return vertices, vertex_labels, cells, boundary_vertices, boundary_labels
end
 
