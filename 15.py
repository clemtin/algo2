def plateau(T):
    #@requires len(T) > 0
    #@requires forall I, J. 0<=I<J<=len(T)-1 -> T[I] <= T[J]
    #@ensures 1<=result<=len(T)
    #@ensures exists I. 0<=I<=len(T)-result and T[I] == T[I+result-1]
    #@ensures forall I. 0<=I<=len(T)-result-1 -> T[I] != T[I+result]

    i = 1
    p = 1
    while i < len(T):
        #@variant len(T)-i
        #@invariant 1<=p<=i<=len(T)
        #@invariant exists I. 0<=I<=i-p and T[I] == T[I+p-1]
        #@invariant forall I. 0<=I<=i-p-1 -> T[I] < T[I+p]
        if T[i] == T[i-p]:
            p = p+1
        i = i + 1
    return p
