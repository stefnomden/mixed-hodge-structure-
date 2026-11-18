# Tests for the current Jacobian and JacobianPoint implementation.
#
# Run from /Users/stefnomden/period_relations after saving this file as
# Lattices/tests/jacobian_test.jl:
#   using Hecke
#   import Hecke: AbstractAlgebra
#   include("Lattices/include.jl")
#   include("Lattices/tests/jacobian_test.jl")
# Using Oscar instead of Hecke and the explicit import also works.
# If the definitions are already loaded, include only this test file.
#
# Function-field input retains its coefficient field. Polynomial input is
# embedded into QQBar and its plane equation is reconstructed in a new ring.
# Equation comparisons allow new variable names and a nonzero scalar factor.
# Polynomial inputs must be irreducible over QQBar; checking this is the
# caller's responsibility, so these tests do not require reducible rejection.
#
# Cache assertions precede operations that populate an unknown cache.
# Principal witnesses are compared through their divisors, since witnesses
# are determined only up to nonzero constants.

using Test

@testset "Jacobian and JacobianPoint" begin
  # E: y^2 = x^3 + 1 over QQBar. These small fixtures include nonzero
  # points of exact orders 2 and 3, not just principal divisors.
  kx, x = Hecke.rational_function_field(QQBar, :jac_test_x; cached=false)
  ky, Y = Hecke.polynomial_ring(kx, :jac_test_Y; cached=false)
  F, y = Hecke.function_field(Y^2 - x^3 - 1, :jac_test_y; cached=false)
  J = jacobian(F)

  Ofin = Hecke.finite_maximal_order(F)
  Oinf = Hecke.infinite_maximal_order(F)
  point_divisor(a, b) =
    Hecke.divisor(Hecke.ideal(Ofin, x - a, Ofin(y - b)))
  Dp = point_divisor(0, 1)
  Dm = point_divisor(0, -1)
  Dt = point_divisor(-1, 0)
  pinf, _ = first(Hecke.factor(Hecke.ideal(Oinf, Hecke.base_ring(Oinf)(inv(x)))))
  Dinf = Hecke.divisor(pinf)
  D2, D3 = Dt - Dinf, Dp - Dinf
  Dzero = Hecke.trivial_divisor(F)
  h = F(x)
  Dh = Hecke.divisor(h)

  # Helper assertions deliberately inspect data without using point equality.
  function check_cache(P, expected)
    flag, f = P.is_principal_with_data
    @test flag === expected
    if flag === true
      @test !isnothing(f)
      if !isnothing(f)
        @test Hecke.parent(f) === Hecke.function_field(P)
        @test !iszero(f)
        @test Hecke.divisor(f) == Hecke.divisor(P)
      end
    else
      @test isnothing(f)
    end
  end

  function check_zero_with_witness(P)
    flag, f = iszero_with_data(P)
    @test flag === true
    @test !isnothing(f)
    if flag === true && !isnothing(f)
      @test Hecke.divisor(f) == Hecke.divisor(P)
    end
    return f
  end

  # Unknown and true states use a nontrivial principal divisor; false uses
  # the nonzero point of order 2. Only public iszero populates these caches.
  function point_with_state(state)
    P = J(state === false ? D2 : Dh)
    if state !== nothing
      @test iszero(P) === state
    end
    return P
  end

  @testset "Fixture identities and field construction" begin
    @test J isa Jacobian{typeof(F)}
    @test J isa AbstractAbVar
    @test Hecke.function_field(J) === F
    @test Hecke.dim(J) == 1
    @test all(Hecke.degree(D) == 1 for D in (Dp, Dm, Dt, Dinf))
    @test Hecke.degree(D2) == Hecke.degree(D3) == 0
    @test Hecke.divisor(y - 1) == 3 * D3
    @test Dh == Dp + Dm - 2 * Dinf
    @test Hecke.divisor(F(x + 1)) == 2 * D2
    @test !Hecke.is_principal(D2)
    @test !Hecke.is_principal(D3)
    eq = plane_equation(J)
    @test eq isa MPolyRingElem
    @test Hecke.base_ring(eq) === QQBar
    @test length(Hecke.gens(Hecke.parent(eq))) == 2
    @test iszero(eq(F(x), y))
  end

  @testset "Point constructors and accessors" begin
    P = jacobian_point(J, D2)
    @test P isa JacobianPoint
    @test Hecke.parent(P) === J
    @test Hecke.function_field(P) === F
    @test Hecke.divisor(P) == D2
    check_cache(P, nothing)
    @test Hecke.divisor(J(Dt, Dinf)) == D2
    @test Hecke.divisor(J(Dp, Dm)) == Dp - Dm
    @test_throws AssertionError J(Dp)
    @test_throws AssertionError J(Dp, Dzero)

    # A different function-field parent must be rejected even if its
    # presentation is identical. cached=false guarantees a distinct parent.
    Fother, _ = Hecke.function_field(Y^2 - x^3 - 1, :jac_test_other; cached=false)
    @test Fother !== F
    @test_throws AssertionError J(Hecke.trivial_divisor(Fother))
  end

  @testset "Lattice-element constructor" begin
    L = divisor_lattice([D2, D3])
    v = L(2, -1)
    P = J(v)
    @test Hecke.parent(P) === J
    @test Hecke.divisor(P) == 2 * D2 - D3
    @test Hecke.divisor(P) == Hecke.divisor(v)
    check_cache(P, nothing)
    @test iszero(J(L(2, 0)))
    @test iszero(J(L(0, 3)))
    @test !iszero(J(L(1, 0)))

    Lpositive = divisor_lattice([Dp])
    @test_throws AssertionError J(Lpositive(1))
  end

  @testset "Zero and principality cache" begin
    Z = zero(J)
    @test Hecke.parent(Z) === J
    @test Hecke.divisor(Z) == Dzero
    check_cache(Z, true)
    @test iszero(Z)
    Zp = zero(J(D2))
    @test Hecke.parent(Zp) === J
    check_cache(Zp, true)

    for D in (Dzero, Dh)
      @testset "Principal divisor $(D == Dzero ? "zero" : "nontrivial")" begin
        P = J(D)
        check_cache(P, nothing)
        @test iszero(P)
        check_cache(P, true)
        saved = P.is_principal_with_data[2]
        @test iszero(P)
        @test P.is_principal_with_data[2] === saved
        @test iszero_with_data(P)[2] === saved
      end
    end
    for D in (D2, D3)
      @testset "Nonprincipal divisor" begin
        P = J(D)
        check_cache(P, nothing)
        @test !iszero(P)
        check_cache(P, false)
        @test iszero_with_data(P) === (false, nothing)
      end
    end
  end

  # Exercise every ordered pair: unknown/true/false. In particular, neither
  # `nothing && flag` nor `xor(nothing, flag)` is valid Julia Boolean logic.
  for a in (nothing, true, false), b in (nothing, true, false)
    @testset "Addition cache ($a, $b)" begin
      P, Q = point_with_state(a), point_with_state(b)
      saved_P, saved_Q = P.is_principal_with_data, Q.is_principal_with_data
      R = P + Q
      @test Hecke.parent(R) === J
      @test Hecke.divisor(R) == Hecke.divisor(P) + Hecke.divisor(Q)
      expected_cache = if a === true && b === true
        true
      elseif (a === true && b === false) || (a === false && b === true)
        false
      else
        nothing
      end
      check_cache(R, expected_cache)
      # A sum is nonzero exactly when just one representative uses D2.
      @test iszero(R) == ((a === false) == (b === false))
      @test P.is_principal_with_data === saved_P
      @test Q.is_principal_with_data === saved_Q
    end
  end

  @testset "Unknown caches on nonprincipal operands" begin
    P, Q = J(D2), J(D3)
    R = P + Q
    check_cache(R, nothing)
    @test !iszero(R)
    check_cache(P, nothing)
    check_cache(Q, nothing)
    for left_zero in (false, true)
      P, Z = J(D2), zero(J)
      R = left_zero ? Z + P : P + Z
      check_cache(R, nothing)
      @test !iszero(R)
      check_cache(P, nothing)
    end
  end

  for state in (nothing, true, false)
    @testset "Negation cache ($state)" begin
      P = point_with_state(state)
      R = -P
      @test Hecke.parent(R) === J
      @test Hecke.divisor(R) == -Hecke.divisor(P)
      check_cache(R, state)
      @test iszero(R) == (state !== false)
      @test Hecke.divisor(-R) == Hecke.divisor(P)
    end
  end

  for state in (nothing, true, false), n in (-3, -2, -1, 0, 1, 2, 3)
    @testset "Scalar cache ($state), n=$n" begin
      P = point_with_state(state)
      saved = P.is_principal_with_data
      R = n * P
      @test Hecke.parent(R) === J
      @test Hecke.divisor(R) == n * Hecke.divisor(P)
      @test Hecke.divisor(P * n) == Hecke.divisor(R)
      expected_cache = if n == 0 || state === true
        true
      elseif state === false && (n == 1 || n == -1)
        false
      else
        nothing
      end
      check_cache(R, expected_cache)
      @test iszero(R) == (state !== false || iseven(n))
      @test P.is_principal_with_data === saved
    end
  end

  @testset "Cancellation and genuine torsion" begin
    # Both classes are nonzero, but their representative sum is principal.
    P, Q = J(Dp - Dinf), J(Dm - Dinf)
    @test !iszero(P)
    @test !iszero(Q)
    R = P + Q
    @test Hecke.divisor(R) != Dzero
    check_cache(R, nothing)
    check_zero_with_witness(R)
    @test iszero(P + (-P))
    @test iszero(P - P)

    for (D, order) in ((D2, 2), (D3, 3))
      @testset "Point of exact order $order" begin
        P = J(D)
        @test !iszero(P)
        for n in (-6, -3, -2, -1, 0, 1, 2, 3, 6)
          @test iszero(n * P) == iszero(mod(n, order))
        end
      end
    end
    # Unknown cache does not mean principal: exercise this separately.
    @test !iszero(2 * J(D3))
    check_zero_with_witness(3 * J(D3))
  end

  @testset "Group laws" begin
    P, Q, R = J(D2), J(D3), J(Dh)
    @test P + Q == Q + P
    @test (P + Q) + R == P + (Q + R)
    @test P + zero(J) == P
    @test zero(J) + P == P
    @test P - zero(J) == P
    @test zero(J) - P == -P
    @test P - Q == P + (-Q)
    @test -(-P) == P
    @test 3 * (P + Q) == 3 * P + 3 * Q
    @test (2 + 3) * P == 2 * P + 3 * P
    @test (-2) * (3 * P) == (-6) * P
  end

  @testset "Equality of classes and witnessing functions" begin
    P, Q = J(D2), J(D2 + Dh)
    @test Hecke.divisor(P) != Hecke.divisor(Q)
    @test P == Q
    @test Q == P
    @test P == P
    @test J(D2) != J(D3)
    @test J(Dh) == zero(J)
    @test J(D2) != zero(J)

    for (left, right, expected) in ((P, Q, inv(h)), (Q, P, h))
      flag, f = is_equal_with_data(left, right)
      @test flag === true
      @test !isnothing(f)
      if flag === true && !isnothing(f)
        @test Hecke.divisor(f) == Hecke.divisor(left) - Hecke.divisor(right)
        @test Hecke.divisor(f / expected) == Dzero
      end
    end
    @test is_equal_with_data(J(D2), J(D3)) === (false, nothing)
    flag, f = is_equal_with_data(P, P)
    @test flag === true
    if flag === true && !isnothing(f)
      @test Hecke.divisor(f) == Dzero
    end
  end

  @testset "Distinct Jacobian parents" begin
    # The constructor creates a fresh Jacobian, even for the same field.
    Jother = jacobian(F)
    @test Jother !== J
    P, Q = J(D2), Jother(D2)
    @test !(P == Q)
    @test !(Q == P)
    @test_throws AssertionError P + Q
    @test_throws AssertionError P - Q
    @test_throws AssertionError is_equal_with_data(P, Q)
  end

  @testset "Display" begin
    # Fresh points keep display's principality computation separate from
    # the cache-policy tests above. Exact display wording is not fixed.
    @test !isempty(sprint(show, J))
    @test !isempty(sprint(show, zero(J)))
    @test !isempty(sprint(show, J(D2)))
  end

  @testset "Jacobian constructors" begin
    # The reconstructed plane equation must hold for the actual field
    # generators. This checks the conversion independently of its algorithm.
    function check_plane_relation(J)
      F = function_field(J)
      P = plane_equation(J)
      @test P isa MPolyRingElem
      @test length(gens(parent(P))) == 2
      @test !iszero(P)
      @test iszero(P(F(gen(base_ring(F))), gen(F)))
    end

    @testset "From an existing function field" begin
      K, x = rational_function_field(QQ, :constructor_x)
      KY, Y = polynomial_ring(K, :constructor_Y)

      F, y = function_field(Y^2 - x^3 + x, :constructor_y)
      J = jacobian(F)
      @test J isa Jacobian{typeof(F)}
      @test function_field(J) === F
      @test base_ring(plane_equation(J)) === QQ
      check_plane_relation(J)

      R = parent(plane_equation(J))
      u, v = gens(R)
      expected = v^2 - u^3 + u
      # A defining equation is only determined up to a nonzero constant.
      @test plane_equation(J) * Hecke.leading_coefficient(expected) ==
        expected * Hecke.leading_coefficient(plane_equation(J))
    end

    @testset "Genus of the normalization of a singular plane model" begin
      K, x = rational_function_field(QQ, :cusp_x; cached=false)
      KY, Y = polynomial_ring(K, :cusp_Y; cached=false)
      F0, y = function_field(Y^2 - x^3, :cusp_y; cached=false)
      J0 = jacobian(F0)
      # The cuspidal plane cubic has arithmetic genus 1, but its
      # smooth projective normalization is rational and has genus 0.
      @test Hecke.dim(J0) == 0
      check_plane_relation(J0)
      @test iszero(J0(Hecke.divisor(F0(x))))
    end

    @testset "Clearing denominators and removing polynomial content" begin
      K, x = rational_function_field(QQ, :denominator_x)
      KY, Y = polynomial_ring(K, :denominator_Y)

      # The factor x+2 is a unit in QQ(x), so it must not remain as an
      # additional vertical component of the reconstructed plane curve.
      defining = 2 * (x + 2) / (x + 3) * (Y^2 - x / (x + 1))
      F, y = function_field(defining, :denominator_y)

      J = jacobian(F)
      @test function_field(J) === F
      check_plane_relation(J)

      P = plane_equation(J)
      u, v = gens(parent(P))
      expected = (u + 1) * v^2 - u
      @test P * Hecke.leading_coefficient(expected) ==
        expected * Hecke.leading_coefficient(P)
    end

    @testset "Polynomial over QQ, scale $scale" for scale in (1, -3)
      R, (x, y) = polynomial_ring(QQ, [:constructor_x, :constructor_y])
      # Linear fixtures are known to be absolutely irreducible.
      # Nonlinear genus-one function fields are tested above.
      P = scale * (y - 2*x - 1)
      J = jacobian(P)

      @test J isa Jacobian
      Q = plane_equation(J)
      @test base_ring(Q) === QQBar
      @test base_ring(base_ring(function_field(J))) === QQBar
      u, v = gens(parent(Q))
      expected = v - 2*u - 1
      @test Q * Hecke.leading_coefficient(expected) ==
        expected * Hecke.leading_coefficient(Q)
      check_plane_relation(J)
    end

    @testset "Polynomial over QQBar, scale $scale" for scale in (1, -3)
      R, (x, y) = polynomial_ring(QQBar, [:constructor_x, :constructor_y])
      a = sqrt(QQBar(2))
      P = scale * (y + a*x + 1)
      J = jacobian(P)

      @test J isa Jacobian
      Q = plane_equation(J)
      @test base_ring(Q) === QQBar
      @test base_ring(base_ring(function_field(J))) === QQBar
      u, v = gens(parent(Q))
      expected = v + a*u + 1
      @test Q * Hecke.leading_coefficient(expected) ==
        expected * Hecke.leading_coefficient(Q)
      check_plane_relation(J)
    end

    @testset "Polynomial over a simple number field, scale $scale" for scale in (1, -3)
      Qz, z = polynomial_ring(QQ, :constructor_z)
      k, a = number_field(z^2 - 2, :constructor_a)
      R, (x, y) = polynomial_ring(k, [:constructor_x, :constructor_y])
      P = scale * (y + a*x + 1)
      J = jacobian(P)

      @test J isa Jacobian
      Pbar = plane_equation(J)
      @test base_ring(Pbar) === QQBar
      @test base_ring(base_ring(function_field(J))) === QQBar
      u, v = gens(parent(Pbar))
      cx = coeff(Pbar, [1, 0])
      cy = coeff(Pbar, [0, 1])
      # Allow either embedding of sqrt(2) and any nonzero scalar
      # normalization. These checks also exclude additional terms.
      @test !iszero(cy)
      @test cx^2 == 2 * cy^2
      @test Pbar == cy*v + cx*u + cy
      check_plane_relation(J)
    end

    @testset "Input shape and coefficient-field restrictions" begin
      R1, (x1,) = polynomial_ring(QQ, [:constructor_x])
      R3, (x3, y3, z3) = polynomial_ring(QQ, [:constructor_x, :constructor_y, :constructor_z])
      @test_throws AssertionError jacobian(x1)
      @test_throws AssertionError jacobian(y3^2 - x3)

      # The first variable is transcendental and the second algebraic,
      # so the polynomial must have positive degree in the second.
      R, (x, y) = polynomial_ring(QQ, [:constructor_x, :constructor_y])
      @test_throws Union{AssertionError, ArgumentError, ErrorException} jacobian(x + 1)

      # Finite coefficient fields are outside the polynomial-input API.
      Rfinite, (xf, yf) = polynomial_ring(GF(5), [:constructor_x, :constructor_y])
      @test_throws ErrorException jacobian(yf^2 - xf)

      # Irreducibility after extending coefficients to QQBar is the
      # caller's responsibility. Reducible input is not tested here.
    end
  end
end
