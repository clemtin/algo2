#@ function fib(n:int)->int
def fib(n:int)->int:
  #@ variant n
  return n if n <=1 else (fib(n-1)+fib(n-2))




def fib_pos(n:int):
  #@ requires n>0
  #@ ensures fib(n)>0
  #@ variant n
  if n>2:
    fib_pos(n-1)
    fib_pos(n-2)


def m_fib(n:int)->int:
  #@ requires n>0
  #@ ensures  result==fib(n)
  fp,fn,i,t=0,1,1,0
  while (i<n):
    #@ variant n-i
    #@ invariant fn==fib(i)
    #@ invariant fp==fib(i-1)
    t=fn
    fn=fn+fp
    fp=t
    i+=1
  return fn
 
r = m_fib(0)
#@ assert r==0
r = m_fib(1)
#@ assert r ==1
r = m_fib(3)
#@ assert r ==2
r = m_fib(4)
#@ assert r ==3
  
# contre exemples
r = m_fib(3)
#@ assert r != 5
