def expR(A:int, B:int)->int:
  #@ requires
  #@ ensures 
  x,y=A,B
  z=1
  while (y>0):
    #@ variant y
    #@ invariant z*power(x,y)==power(A,B)
    #@ invariant B >=y
    if (y%2==0):
      x,y = .... y//2
    else:
    z,y= ...., y-1
    
  return z