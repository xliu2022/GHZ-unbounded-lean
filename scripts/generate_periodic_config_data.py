#!/usr/bin/env python3
"""Reproduce supplemental S2 local configurations; Lean checks certificates separately."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def mask(xs):
    return sum(1 << x for x in xs)

def configurations(n, rows):
    universe = (1 << n) - 1
    outall = 0
    for e, o in rows:
        outall |= o
    result = []
    visits = 0
    def dfs(start, chosen, loc, out):
        nonlocal visits
        visits += 1
        missing = universe ^ loc
        if missing & ~outall == 0:
            result.append((tuple(chosen), missing, out))
        for i in range(start, len(rows)):
            edge, outgoing = rows[i]
            local = edge ^ outgoing
            if loc & local == 0 and out & outgoing == 0:
                dfs(i + 1, chosen + [i], loc | local, out | outgoing)
    dfs(0, [], 0, 0)
    return result, visits

def parse_edge(s):
    return mask(int(a) - 1 for a in s)

eleven = [
    ('123','3'),('456',''),('789',''),
    ('128','8'),('369',''),('457','4'),
    ('129',''),('356',''),('478',''),
    ('134','34'),('279',''),('568',''),
    ('137','3'),('246','6'),('589',''),
    ('145','4'),('238',''),('679','67'),
    ('147','4'),('269','26'),('358','3'),
    ('149','4'),('268','6'),('357','3'),
    ('159','9'),('248',''),('367',''),
    ('167','6'),('235','3'),('489','8'),
    ('178','8'),('259',''),('346','46')]
ten = [('123','13'),('124','14'),('125','5'),('126',''),('134','34'),
       ('135','5'),('136','13'),('145',''),('146','46'),('156','5'),
       ('234','24'),('235',''),('236','36'),('245',''),('246','46'),
       ('256','5'),('345','3'),('346',''),('356','56'),('456','6')]
latin = ['hacebdfg','ahdceb gf'.replace(' ',''),'gfebdach','fgbdaehc',
         'dbfghcae','begfchda','echafgbd','cdahgfeb']
latin = [[ord(c)-ord('a') for c in row] for row in latin]
beta = {(0,0),(0,3),(1,0),(1,2),(2,0),(2,3),(3,0),(3,2),(3,3),
        (4,2),(4,3),(5,0),(5,2),(5,3),(7,0)}
gamma = {(1,4),(2,2),(5,1),(7,6)}
latin_rows = []
for a in range(8):
    for b in range(8):
        c = latin[a][b]
        edge = mask((a,8+b,16+c))
        outgoing = mask(([8+b] if (a,b) in beta else []) + ([16+c] if (a,b) in gamma else []))
        latin_rows.append((edge,outgoing))

def latin_configurations():
    result = []
    visits = 0
    U = 0
    for e,o in latin_rows: U |= o
    def dfs(a, chosen, loc, out):
        nonlocal visits
        visits += 1
        if a == 8:
            missing = ((1<<24)-1)^loc
            if missing & ~U == 0: result.append((tuple(chosen),missing,out))
            return
        for b in range(8):
            e,o = latin_rows[8*a+b]
            l=e^o
            if not (l&loc or o&out): dfs(a+1,chosen+[8*a+b],l|loc,o|out)
    dfs(0,[],0,0)
    return result,visits

all_data={}
for name,n,rows in [('eleven',9,[(parse_edge(e),parse_edge(o)) for e,o in eleven]),
                    ('ten',6,[(parse_edge(e),parse_edge(o)) for e,o in ten])]:
    cfg,visits=configurations(n,rows)
    arcs={}
    for a,s,t in cfg: arcs[s,t]=arcs.get((s,t),0)+1
    all_data[name]={'vertices':n,'edges':rows,'configurations':cfg,
                    'arcs':[[s,t,w] for (s,t),w in sorted(arcs.items())],'visits':visits}
    print(name,'configs',len(cfg),'arcs',len(arcs),'partial states',visits)
cfg,visits=latin_configurations()
arcs={}
for a,s,t in cfg: arcs[s,t]=arcs.get((s,t),0)+1
all_data['latin']={'vertices':24,'edges':latin_rows,'configurations':cfg,
                    'arcs':[[s,t,w] for (s,t),w in sorted(arcs.items())],'visits':visits}
print('latin','configs',len(cfg),'arcs',len(arcs),'partial row states',visits)
output=ROOT/'scripts'/'periodic_config_data.json'
output.write_text(json.dumps(all_data,indent=2)+'\n')
print(output)
