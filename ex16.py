#@constant
BLEU = 1

#@constant
BLANC = 2

#@constant
ROUGE = 3

#@lemma L2: forall i1, i2, a, v:int. 0 <= i1 < len(a) and 0 <= i2 < len(a) -> occurrence(v, a[i1<-a[i2]][i2<-a[i1]],0,len(a)) == occurrence(v,a,0,len(a)) 

def drapeau(a):
    #@requires forall i. 0<=i<len(a) -> BLEU <= a[i] <= ROUGE
    #@ensures forall i,j. 0 <= i < j < len(a) -> a[i] <= a[j]
    #@ensures forall v. occurrence(v, a, 0, len(a)) == old(occurrence(v, a, 0, len(a)))
    #@label start
    r = 0
    w = 0
    b = len(a)
    while w < b:
        #@variant b-w
        #@invariant 0 <= r <= w <= b <= len(a)
        #@invariant forall i. 0<=i < r -> a[i] == BLEU
        #@invariant forall i. r<=i < w -> a[i] == BLANC
        #@invariant forall i. w<=i < b -> BLEU <= a[i] <= ROUGE
        #@invariant forall i. b<=i < len(a) -> a[i] == ROUGE
        #@invariant forall v. occurrence(v, a, 0, len(a)) == at(occurrence(v, a, 0, len(a)),start)
        if (a[w] == BLEU):
            a[w],a[r] = a[r],a[w]
            r = r+1
            w = w+1
        elif (a[w] == BLANC):
            w = w+1
        else:
            b = b - 1
            a[w],a[b] = a[b],a[w]
