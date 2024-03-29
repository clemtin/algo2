#@ predicate oneOf(x:int ,a:int,b:int,c:int) = x==a or x==b or x==c
#@ predicate exch(x:int,y:int,z:int,a:int,b:int,c:int) = oneOf(x,a,b,c) and oneOf(y,a,b,c) and oneOf(z,a,b,c)


#@ function gt(x:int, y:int) -> int = if x>y then 1 else 0

def tri3V2(a:int,b:int,c:int) ->Tuple[int,int,int]:
  #@ requires a!=b and b!=c and a!=c and a>0 and b>0 and c>0
  #@ ensures forall x,y,z. result == (x,y,z)-> x<y<z
  #@ ensures forall x,y,z. result == (x,y,z)-> exch(x,y,z,a,b,c)
  x,y,z = a,b,c
  while (x >= y or y >= z):
    #@ variant gt(x,y)+gt(y,z)+gt(x,z)
    #@ invariant x!=y and y!=z and x!=z
    #@ invariant exch(x,y,z,a,b,c)
    
    if (x>=y):
      x,y = y,x
    else:
      y,z = z,y
  return (x,y,z)
