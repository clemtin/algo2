#@function
def recherche_lin(A : list[int], X: int) -> int:
    #@ requires len(A) >= 0
    #@ ensures 0 <= result < len(A) -> X == A[result] 
    #@ ensures result == len(A) -> forall I. 0 <= I < len(A) -> A[I] != X
    pos = 0
    while (pos < len(A) and A[pos] != X):
        #@variant len(A) - pos
        #@invariant 0 <= pos <= len(A)
        #@invariant forall I. 0 <= I < pos -> A[I] != X
        pos = pos + 1
    return pos
    
l2 = [7, 14, 21, 28, 35]
r = recherche_lin(l2, 7)
#@assert r == 0

l3 = [1, 3, 5, 7, 9]
r = recherche_lin(l3, 2)
#@assert r == 5

l1 = [10, 20, 30, 40, 50]
r = recherche_lin(l1, 30)
#@assert r == 2


