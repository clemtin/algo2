def sum(n:int)-> int:
  #@ requires (n>=0)
  #@ ensures result==((n*(n+1)//2))
  pass

r = sum(0)
#@ assert r==0
r = sum(1)
#@ assert r==1
r = sum(2)
#@ assert r==3
r = sum(3)
#@ assert r==6
r = sum(4)
#@ assert r==10
r = sum(5)
#@ assert r==15
# contres exemples 
r = sum(7)
#@ assert r!=26
r = sum(8)
#@ assert r!=21
r = sum(9)
#@ assert r!=13