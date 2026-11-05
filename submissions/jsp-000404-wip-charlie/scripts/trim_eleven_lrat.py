"""Trim a RUP-only textual LRAT proof to its backward dependency cone.

Omitting deletion steps is sound for RUP; reject RAT steps, where retaining
deleted clauses can invalidate a proof. Lean still checks the resulting proof.
"""
import sys
from pathlib import Path


def main():
    path=Path(sys.argv[1])
    result=Path(sys.argv[2])
    steps={}
    empty=None
    for line in path.read_text(encoding='ascii').splitlines():
        fields=line.split()
        if len(fields)>1 and fields[1]=='d':
            continue
        numbers=list(map(int,fields))
        first=numbers.index(0,1)
        second=numbers.index(0,first+1)
        identifier=numbers[0]
        clause=numbers[1:first]
        hints=numbers[first+1:second]
        if any(x<0 for x in hints):
            raise ValueError('RAT hints require deletion-aware trimming')
        assert identifier not in steps
        steps[identifier]=(line,[abs(x) for x in hints])
        if not clause:
            empty=identifier
    assert empty is not None
    used=set()
    stack=[empty]
    while stack:
        identifier=stack.pop()
        if identifier in used or identifier not in steps:
            continue
        used.add(identifier)
        stack.extend(steps[identifier][1])
    assert empty in used
    result.write_text(''.join(steps[i][0]+'\n' for i in sorted(used)),encoding='ascii',newline='\n')
    print('Trimmed additions',len(steps),'to',len(used),'bytes',result.stat().st_size)

if __name__=='__main__':
    main()
