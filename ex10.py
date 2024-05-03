def recherche_lin_present(A : list[int], X: int) -> int:
    #@requires exists I. 0 <= I < len(A) and X == A[I]
    #@ensures 0 <= result < len(A)
    #@ensures  X == A[result]
    pos = 0
    while (X != A[pos]):
        #@variant len(A) - pos
        #@invariant 0 <= pos < len(A)
        #@invariant forall I. 0 <= I < pos -> X != A[I]
        #@invariant exists I. pos <= I < len(A) and X == A[I]
        pos = pos + 1
    return pos
    
l1 = [5, 4, 3, 2, 1]
r = recherche_lin_present(l1, 3) 
#@ assert r == 2

l2 = [-1, 0, 6, 4, 2]

r = recherche_lin_present(l2, 4) 
#@ assert r == 3

