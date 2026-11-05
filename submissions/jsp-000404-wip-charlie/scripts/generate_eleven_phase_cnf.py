"""Reproduce the checked eleven-phase residual-cover CNF without a SAT solver."""
import argparse
from itertools import combinations
from pathlib import Path
from generate_eleven_phase_data import catalog, orbit
from generate_eleven_phase_cores import images


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    rows=catalog()
    cores=sorted(images((11,29,176))|images((6,128,184))|images((24,32,48,62,74)))
    assert len(cores)==88
    clauses=[]
    for i,j in combinations(range(len(rows)),2):
        if not (rows[i][0]&rows[j][1] or rows[i][1]&rows[j][0]):
            clauses.append([-(i+1),-(j+1)])
    clauses.extend([-(i+1) for i in core] for core in cores)
    high341=sorted(orbit(341,11))
    for word in high341:
        touching=[i+1 for i,(p,n) in enumerate(rows) if word&p==p and word&n==0]
        assert len(touching)==2
        clauses.append(touching)
    long=[i+1 for i,(p,n) in enumerate(rows) if (p|n).bit_count()==6]
    assert len(long)==22
    # At least three long rows.
    clauses.extend([i for i in long if i not in excluded] for excluded in combinations(long,2))
    nextvar=len(rows)+1
    def at_most(inputs,limit):
        nonlocal nextvar
        previous=None
        counters=[]
        for literal in inputs:
            current=list(range(nextvar,nextvar+limit+1))
            nextvar+=limit+1
            counters.append(current)
            for threshold in range(1,limit+2):
                if previous is not None:
                    clauses.append([-previous[threshold-1],current[threshold-1]])
                if threshold==1:
                    clauses.append([-literal,current[0]])
                elif previous is not None:
                    clauses.append([-literal,-previous[threshold-2],current[threshold-1]])
            previous=current
        clauses.append([-previous[-1]])
        return counters
    long_counter=at_most(long,3)
    medium=sorted(set().union(*(orbit(p,11) for p in (293,331,333))))
    high=sorted(orbit(339,11))
    assert len(medium)==66 and len(high)==22
    missing={}
    for word in medium+high:
        missing[word]=nextvar
        nextvar+=1
        touching=[i+1 for i,(p,n) in enumerate(rows) if word&p==p and word&n==0]
        clauses.append([missing[word],*touching])
    medium_counter=at_most([missing[w] for w in medium],2)
    high_counter=at_most([missing[w] for w in high],1)
    clauses.extend([-missing[h],-missing[m]] for h in high for m in medium)
    args.output.write_text(
        f'p cnf {nextvar-1} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses),
        encoding='ascii',newline='\n')
    print('Wrote',len(clauses),'clauses in',nextvar-1,'variables to',args.output)

if __name__=='__main__':
    main()
