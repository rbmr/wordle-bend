import random, ref, sys
c=ref.load('/home/robert/projects/wordle-bend-wt/proto/words/candidates.txt')[:300]
g=ref.load('/home/robert/projects/wordle-bend-wt/proto/words/guesses.txt')
m=ref.Model(c,g)
memo={}
def brute(st):
    st=tuple(st)
    if st in memo: return memo[st]
    n=len(st)
    if n<=2: r=(0,1,3)[n]
    else:
        best=10**9
        for gg in range(m.G):
            row=m.fb[gg]
            b={}
            for x in st: b.setdefault(row[x],[]).append(x)
            if len(b)<=1: continue
            cost=n
            for r,bb in b.items():
                if r==ref.WIN: continue
                cost+=brute(bb)
            if cost<best: best=cost
        r=best
    memo[st]=r
    return r
random.seed(7)
bad=0
for trial in range(40):
    n=random.randint(3,6)
    idx=sorted(random.sample(range(60),n))
    st=idx
    q,ex=m.quick(st)
    b=brute(st)
    if ex and q!=b: print('EXACT WRONG',idx,q,b); bad+=1
    if q>b: print('TOO HIGH',idx,q,b); bad+=1
    if not ex and q!=2*n: print('bound wrong',idx,q); bad+=1
print('bad',bad)
