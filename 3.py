def Cube(n):
  #@ requires n>=0
  #@ ensures result ==n*n*n
  i,c,k,m = 0,0,1,6
  while (i<n):
    #@variant n-i
    #@invariant c==i*i*i
    #@invariant 0<=i<=n
    #@invariant k==3*i*i+3*i+1
    #@invariant m== 6*i+6
    c=c+k
    k=k+m
    m=m+6
    i=i+1
  return c    