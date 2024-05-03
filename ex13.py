#@predicate subT(l1: list[int], l2:list[int], p:int) = 0 <= p <= len(l2)-len(l1) and forall I. 0<=I<len(l1) -> l1[I] == l2[I+p]

def sous_tableau(s,t,p):
    #@requires 0 <= p <= len(t)-len(s)
    #@ensures result == subT(s,t,p)
    i = 0
    while (i < len(s) and s[i] == t[p+i]):
        #@invariant 0 <= i <= len(s)
        #@invariant subT(s[:i], t, p)
        #@variant len(s)-i
        i = i + 1
    return i == len(s)