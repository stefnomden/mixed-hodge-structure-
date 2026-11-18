#GPT-6 Astra Ultra generated

# Load your lattice and morphism definitions before including this file.
# Tests for the pasted parametric LatticeHom and current divisor lattice API.
# This file tests behavior only; it does not replace any implementation methods.
using Test

@testset "Divisor lattices and lattice morphisms" begin
    # F = Q(t), presented as a quadratic extension of Q(x), with t^2 = x.
    # The finite divisors above x=1, x=2, x=3 have disjoint, nonempty
    # supports, so they are independent. No support factorization is needed.
    kx, x = Hecke.rational_function_field(QQ, :x)
    ky, y = Hecke.polynomial_ring(kx, :y)
    F, t = Hecke.function_field(y^2 - x)
    O = Hecke.finite_maximal_order(F)
    D1, D2, D3 = [Hecke.divisor(Hecke.ideal(O, x - c)) for c in 1:3]

    L = divisor_lattice([D1, D2])
    K = divisor_lattice([D1, D2, D3])
    Lother = divisor_lattice([D1, D2])
    Z = divisor_lattice(F, Divisor[])

    @testset "Constructors, parents and arithmetic" begin
        @test rank(L) == 2
        @test rank(K) == 3
        @test rank(Z) == 0
        @test function_field(L) === F
        @test function_field(Z) === F
        @test basis(L) == [D1, D2]
        @test_throws ErrorException divisor_lattice(Divisor[])
        @test L(2, -1) == L([2, -1]) == L(ZZRingElem[2, -1]) == L(ZZ[2 -1])
        @test parent(L(2, -1)) === L
        @test L(2, -1) != Lother(2, -1)
        @test coordinates(L(2, -1)) == ZZ[2 -1]
        @test L(1, 2) + L(3, -1) == L(4, 1)
        @test L(1, 2) - L(3, -1) == L(-2, 3)
        @test -L(1, 2) == L(-1, -2)
        @test 3 * L(1, 2) == L(1, 2) * 3 == L(3, 6)
        @test zero(L) == L(0, 0)
        @test zero(L(1, 2)) == zero(L)
        @test iszero(L(1, 2) - L(1, 2))
        @test iszero(zero(Z))
        @test size(coordinates(zero(Z))) == (1, 0)
        @test_throws AssertionError L(1, 2, 3)
        @test_throws AssertionError L(matrix(ZZ, 2, 1, [1, 2]))
        @test_throws AssertionError L(1, 2) + Lother(1, 2)
    end

    @testset "Divisors and lazy summands" begin
        v, w = L(1, 2), L(3, -1)
        @test isnothing(v.divisor_realisation)
        @test isnothing(v.divisor_summands)
        @test divisor(v) == D1 + 2 * D2
        cached = divisor(v)
        @test divisor(v) === cached
        @test divisor(w) == 3 * D1 - D2

        pending = v + w
        @test isnothing(pending.divisor_realisation)
        @test !isnothing(pending.divisor_summands)

        # Both operands have pending sums; scalar multiplication and subtraction
        # must preserve their meaning without prematurely computing divisors.
        doubled = pending + pending
        @test isnothing(doubled.divisor_realisation)
        @test length(pending.divisor_summands) == 2
        @test length(doubled.divisor_summands) == 4
        @test divisor(doubled) == 8 * D1 + 2 * D2
        z = 2 * pending - v
        @test z == L(7, 0)
        @test isnothing(z.divisor_realisation)
        @test !isnothing(z.divisor_summands)
        @test divisor(z) == 7 * D1
        @test isnothing(z.divisor_summands)
        @test divisor(z) == divisor(L(7, 0))

        # Only one operand has cached data: fall back to coordinates.
        fallback = v + L(0, 1)
        @test isnothing(fallback.divisor_summands)
        @test divisor(fallback) == D1 + 3 * D2
        @test divisor(zero(Z)) == Hecke.trivial_divisor(F)
    end

    A = ZZ[1 2 0; 0 1 1]
    B = ZZ[1 0; 0 1; 1 1]
    f = hom(L, K, A)
    g = hom(K, L, B)
    v = L(2, -1)

    @testset "Evaluation, composition and map arithmetic" begin
        @test domain(f) === L
        @test codomain(f) === K
        @test f isa LatticeHom{typeof(L), typeof(K)}
        @test f.group_hom isa FinGenAbGroupHom
        @test matrix(f) == A
        @test f(v) == K(2, 3, -1)
        @test divisor(f(v)) == 2 * D1 + 3 * D2 - D3
        @test f(L(1, 2) + L(3, -1)) == f(L(1, 2)) + f(L(3, -1))
        @test f(3 * v) == 3 * f(v)
        @test g(f(v)) == L(1, 2)
        @test (f * g)(v) == g(f(v))  # Your convention: f first, then g.
        @test matrix(f * g) == ZZ[1 2; 1 2]
        @test (2 * f)(v) == K(4, 6, -2)
        @test (f * 2)(v) == K(4, 6, -2)
        @test (-f)(v) == K(-2, -3, 1)
        @test (0 * f)(v) == zero(K)

        same_f = hom(L, K, [[1, 2, 0], [0, 1, 1]])
        @test f == same_f
        @test f != hom(Lother, K, A)
        @test f != 2 * f

        idL = hom(L, L, identity_matrix(ZZ, rank(L)))
        idK = hom(K, K, identity_matrix(ZZ, rank(K)))
        @test identity(L) == idL
        @test identity(K) == idK
        @test identity(L)(v) == v
        @test (idL * f)(v) == f(v)
        @test (f * idK)(v) == f(v)
        @test_throws AssertionError f(Lother(2, -1))
        @test_throws AssertionError hom(L, K, ZZ[1 0; 0 1])
        # Matrix dimensions alone would allow this composition, but parents differ.
        Kother = divisor_lattice([D1, D2, D3])
        @test_throws AssertionError f * hom(Kother, L, B)
        # Also reject matching matrix sizes when the first map is an endomorphism.
        @test_throws AssertionError idL * hom(Lother, K, A)

        supplied = deepcopy(A)
        protected = hom(L, K, supplied)
        supplied[1, 1] = 99
        @test protected(v) == K(2, 3, -1)
    end

    @testset "Injectivity, surjectivity and zero ranks" begin
        @test is_injective(f)
        @test !is_surjective(f)
        @test !is_injective(g)
        @test is_surjective(g)
        @test !is_injective(f * g)
        @test !is_surjective(f * g)
        scaling = hom(L, L, ZZ[2 0; 0 3])
        @test is_injective(scaling)
        @test !is_surjective(scaling)
        @test !is_bijective(scaling)
        @test is_bijective(hom(L, L, ZZ[1 1; 0 1]))
        @test !is_injective(0 * f)
        @test !is_surjective(0 * f)

        from_zero = hom(Z, L, zero_matrix(ZZ, 0, 2))
        to_zero = hom(L, Z, zero_matrix(ZZ, 2, 0))
        zero_to_zero = hom(Z, Z, zero_matrix(ZZ, 0, 0))
        @test is_injective(from_zero)
        @test !is_surjective(from_zero)
        @test !is_injective(to_zero)
        @test is_surjective(to_zero)
        @test is_bijective(zero_to_zero)
        @test identity(Z) == zero_to_zero
        @test from_zero(zero(Z)) == zero(L)
        @test to_zero(v) == zero(Z)
        @test zero_to_zero(zero(Z)) == zero(Z)
        @test hom(Z, L, Vector{Int}[]) == from_zero
    end

    @testset "Sublattices preserve the integer span" begin
        # 2e1 and 3e1 generate e1: retaining only an independent input row is wrong.
        S, inclusion = sublattice(L, [L(2, 0), L(3, 0)])
        @test rank(S) == 1
        @test domain(inclusion) === S
        @test codomain(inclusion) === L
        @test is_injective(inclusion)
        @test inclusion(S(1)) == L(1, 0)
        @test divisor(S(1)) == D1

        # A full-rank sublattice need not be the whole lattice.
        S2, inclusion2 = sublattice(L, [L(2, 0), L(0, 3), L(4, 3)])
        @test rank(S2) == 2
        @test matrix(inclusion2) == ZZ[2 0; 0 3]
        @test is_injective(inclusion2)
        @test !is_surjective(inclusion2)
        @test inclusion2(S2(1, 1)) == L(2, 3)
        @test divisor(S2(1, 1)) == 2 * D1 + 3 * D2
    end

    @testset "Display writes to the supplied IO" begin
        textL = sprint(show, L)
        textZ = sprint(show, Z)
        textv = sprint(show, v)
        textf = sprint(show, f)
        @test occursin("Lattice of rank 2", textL)
        @test occursin("Zero lattice", textZ)
        @test occursin("Row vector representation", textv)
        @test occursin("Morphism of lattices from", textf)
        @test occursin("Lattice of rank 2", textf)
        @test occursin("Lattice of rank 3", textf)
        @test occursin("Represented by matrix", textf)
    end
end
