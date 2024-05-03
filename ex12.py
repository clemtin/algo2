#@predicate sorted(A:list[int]) = forall I,J. 0<=I<=J<len(A) -> A[I] <= A[J]
#@predicate isIn(X:int, A:list[int]) = exists I. 0 <= I < len(A) and X == A[I]
#@predicate isInSub(X:int, A:list[int], D:int, F:int) = 0 <= D <= F <= len(A) -> exists I. D <= I < F and X == A[I]

def recherche_dicho(N, A, X):
  #@requires len(A) == N
  #@requires N > 0
  #@requires sorted(A)
  #@ensures 0 <= result <= N
  #@ensures result < N -> isIn(X, A)
  i = 0
  j = N - 1
  while (i < j-1):
    #@variant j-i
    #@invariant 0 <= i <= j <= N
    m = (i+j) // 2
    if (X < A[m]):
      j = m
    else:
      i = m
  if (i < N and X == A[i]):
    return i
  else:
    return N
