r = pgcd(10, 6)
    #@ requires a >= 0
    #@ requires b > 0
    #@ ensures forall q,r.result == (q,r) ->  b>= r
    #@ ensures forall q,r.result == (q,r) -> r+b*q == a
    

    q = 0
    r = a

    while r >= b:
        #@ invariant 0 <= r
        #@ invariant r + b * q == a
        #@ variant r
        r -= b
        q += 1

    return (q, r)
    

# Exemples et contre-exemples
r = div_mod(5, 3)
#@assert r == (1, 2)

r = div_mod(2, 2)
#@assert r == (1, 0)

r = div_mod(17, 5)
#@assert r == (3, 2)

r = div_mod(24, 5)
#@assert r == (4, 4)

r = div_mod(1, 4)
#@assert r == (0, 1)

r = div_mod(7, 5)
#@assert r != (2, -2)

r = div_mod(14, 4)
#@assert r != (3, 2)
