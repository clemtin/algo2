def div_mod(a:int,b:int)->Tuple[int,int]:
  #@ requires a>=0
  #@ requires b>0
  #@ ensures forall q,r.result== (q,r)-> 0 <=r<b
  #@ ensures forall q,r.result== (q,r)-> r+b*q == a
  
  q=0
  r=a
  
  while r>=b:
    #@ invariant 0<= r
    #@ invariant r+b*q ==a
    #@ variant r
    
    #@ assert 0<= r-b and (r-b)+b*(q+1) ==a 
    r-=b
    #@ assert 0<= r and r+b*(q+1) ==a 
    q+=1
    #@ assert 0<= r and r+b*q ==a 
  return (q,r) 
 

r= div_mod(5,3)
#@ assert r ==(1,2)
r= div_mod(2,2)
#@ assert r ==(1,0)
r= div_mod(17,5)
#@ assert r ==(3,2)
r= div_mod(24,5)
#@ assert r ==(4,4)
r= div_mod(1,4)
#@ assert r ==(0,1)

# contre exemples

r= div_mod(7,5)
#@ assert r !=(2,-2)
