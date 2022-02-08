@testset begin "MPolyAnyMap/MPolyRing"
  # Construction 
  Qsqrt2, = quadratic_field(-1)
  
  for K in [GF(2), GF(fmpz(2)), GF(2, 2), GF(fmpz(2), 2), ZZ, QQ, Qsqrt2]
    Kx, (x, y) = K["x", "y"]
    h = @inferred hom(Kx, Kx, [y, x])
    @test h(x) == y
    @test h(y) == x
    @test_throws ArgumentError hom(Kx, Kx, [x])
    @test_throws ArgumentError hom(Kx, Kx, [y, y, x])

    if K === QQ
      @test_throws MethodError hom(Kx, Kx, [GF(2)(1), GF(2)(1)])
    end

    h = @inferred hom(Kx, Kx, fmpz[1, 1])
    @test h(x + y) == Kx(2)

    Kh, (z1, z2) = K["z1", "z2"]
    Kh, (zz1, zz2) = grade(Kh)
    h = @inferred hom(Kx, Kh, [z1 + z2, z2])
    @test h(x) == zz1 + zz2
    @test h(y) == zz2
    @test_throws ArgumentError hom(Kx, Kh, [zz1 + zz1^2, zz2])
    h = @inferred hom(Kx, Kh, [zz1 + zz1^2, zz2], check = false)
  
    # julia-function  
    R, (x, y) = K["x", "y"]
    S, (u, v) = R["u", "v"]
    h = hom(S, S, a -> S(a^2), gens(S))
    @test h(u) == u
    @test h(x*u) == x^2 * u
    h = hom(S, S, a -> a^2, gens(S))
    @test h(u) == u
    @test h(x*u) == x^2 * u
  
    A, (x,y) = K["x", "y"]
    f = hom(A, A, [2*x, 5*y])
    R, (u, v) = A["u", "v"]
    h = hom(R, R, f, [u+v, u*v])
    @test (@inferred h(x*u)) == 2*x*u + 2*x*v

    # another issue
    R, (x, y) = K["x", "y"]
    S, (u, v) = R["u", "v"]
    h = hom(S, S, a -> a^2, gens(S))
    @test (@inferred h(x)) == x^2
  end
end