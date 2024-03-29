#@ function abs(n:int) -> int =if n >= 0 then n else -n

def max_abs(a:int,b:int,c:int)->int:
  #@ ensures (result == abs(a) or result == abs(b) or result == abs(c)) and result >= abs(a) and result >= abs(b) and result >= abs(c) 
  pass

r = max_abs(5,8,2)
#@ assert r == 8

r = max_abs(-2,4,-6)
#@ assert r == 6
r = max_abs(17,-2,4)
#@ assert r == 17
r = max_abs(-2,-4,-10)
#@ assert r == 10
r = max_abs(4,-10,8)
#@ assert r != 8
r = max_abs(4,-10,8)
#@ assert r != 8
r = max_abs(7,-1,-9)
#@ assert r != 7
