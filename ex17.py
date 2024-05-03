#@ predicate trie1(a:list[int], d:int, f:int) = d >= 0 and f <= len(a) and forall I. d <= I < f - 1 -> a[I] <= a[I + 1]
#@ predicate trie2(a:list[int], d:int, f:int) = d >= 0 and f <= len(a) and forall I, J. d <= I < J < f -> a[I] <= a[J]

def L1(A:list[int], D:int, F:int):
  #@ requires trie1(A,D,F)
  #@ ensures trie2(A,D,F)

  #@ variant F - D

  if F > D:
    L1(A,D,F-1)

#@ lemma L3: forall A:list[int], D:int, F:int. trie2(A,D,F) -> trie1(A,D,F)

def triBulle(a:list[int]):
  #@ requires len(a) > 0
  #@ ensures trie2(a, 0, len(a))
  #@ ensures forall v. occurrence(v,a,0,len(a)) == old(occurrence(v,a,0,len(a)))

  n = len(a)
  i = n

  #@ label start1
  while i > 0:
    #@ invariant 0 <= i <= n
    #@ invariant trie1(a, i, n)
    #@ invariant trie2(a, i, n)

    #@ invariant forall I. i < I < n -> a[i] <= a[I]
    #@ invariant i < n -> forall I. (0 <= I < i) -> (a[i] >= a[I])

    #@ invariant forall v. occurrence(v,a,0,len(a)) == at(occurrence(v,a,0,len(a)), start1)
    #@ variant i

    #@ call L1(a, i, n)
    j = 0
    #@ label start2
    while j < i - 1:
      #@ invariant 0 <= j < i and j <= n
      #@ invariant forall J. 0 <= J < j -> a[J] <= a[j]
      #@ invariant trie1(a, i, n)
      #@ invariant trie2(a, i, n)

      #@ invariant forall I. i < I < n -> a[i] <= a[I]
      #@ invariant i < n -> forall I. (0 <= I < i) -> (a[i] >= a[I])

      #@ invariant forall v. occurrence(v,a,0,len(a)) == at(occurrence(v,a,0,len(a)), start2)
      #@ variant i - j

      if a[j] > a[j + 1]:
        #@ assert forall v. occurrence(v,a[j<-a[j+1]][j+1<-a[j]],0,len(a)) == at(occurrence(v,a,0,len(a)), start2)
        a[j], a[j + 1] = a[j + 1], a[j]

      j = j + 1
    i = i - 1
