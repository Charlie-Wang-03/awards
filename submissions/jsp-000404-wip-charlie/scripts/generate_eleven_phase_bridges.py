"""Instantiate the verified nine-phase geometric bridge at eleven phases."""
import re
from pathlib import Path


def instantiate(source,destination,extra):
    text=Path(f'JSP000404Research/{source}.lean').read_text(encoding='utf-8')
    for old,new in [('NinePhase','ElevenPhase'),('nine-phase','eleven-phase'),
                    ('nine phases','eleven phases'),('twenty','forty'),('Twenty','Forty')]:
        text=text.replace(old,new)
    numbers={9:11,7:9,20:40}
    numbers.update(extra)
    text=re.sub(r'\b(?:'+'|'.join(map(str,numbers))+r')\b',
                lambda match:str(numbers[int(match.group())]),text)
    for old,new in [('four_fifths','five_sixths'),('four-fifths','five-sixths'),
                    ('FourFifths','FiveSixths')]:
        text=text.replace(old,new)
    path=Path(f'JSP000404Research/{destination}.lean')
    path.write_text(text,encoding='utf-8',newline='\n')
    assert all(len(line)<=100 for line in text.splitlines()),path
    print('Wrote',path)


if __name__=='__main__':
    instantiate('NinePhaseOrder','ElevenPhaseOrder',{})
    instantiate('NinePhaseRows','ElevenPhaseRows',{})
    instantiate('NinePhaseSchedule','ElevenPhaseSchedule',{})
    instantiate('OrderedNinePhase','OrderedElevenPhase',{5:6})
    instantiate('PlanarNinePhaseThreshold','PlanarElevenPhaseThreshold',{4:5,5:6})
