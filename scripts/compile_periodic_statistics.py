#!/usr/bin/env python3
"""Serial kernel-checking of the small, complete Supplement S2 statistics chunks."""
from pathlib import Path
import argparse
import subprocess
import sys
p=argparse.ArgumentParser()
p.add_argument('--from-module')
p.add_argument('--until-module')
p.add_argument('--memory-mb',type=int,default=4000)
a=p.parse_args()
root=Path(__file__).resolve().parents[1]
mods=['Construction/SupportFits','Supplement/Periodic/EnumerationNodup',
      'Supplement/Periodic/SmallCodes','Supplement/Periodic/Cardinality',
      'Supplement/Periodic/BitOutput']
for name,num in [('Eleven',9),('Ten',3),('Latin',13)]:
 mods+=['Supplement/Periodic/'+name+'CatalogueData']
 mods+=['Supplement/Periodic/'+name+f'Output{i:02d}' for i in range(num)]
 mods+=['Supplement/Periodic/'+name+x for x in ['EnumerationOutput','Catalogue']]
 if name=='Eleven':
  mods+=['Supplement/Periodic/ElevenCodeData']
  mods+=['Supplement/Periodic/'+f'ElevenCodeCheck{i:02d}' for i in range(6)]
  mods+=['Supplement/Periodic/ElevenPairCodes']
 mods+=['Supplement/Periodic/'+name+'Statistics']
mods+=['Supplement/Periodic']
if a.from_module:mods=mods[mods.index(a.from_module):]
if a.until_module:mods=mods[:mods.index(a.until_module)+1]
log=root/'verification/foundation-periodic-statistics.log'
log.parent.mkdir(exist_ok=True)
for module in mods:
 if (root/'periodic_compile_pause.flag').exists():
  print('Paused before '+module,flush=True)
  sys.exit(0)
 print('Checking '+module,flush=True)
 cmd=['python3','/workspace/scratch/f48f4c8e3717/run_lean.py','-j1','-M'+str(a.memory_mb),
      'RigidGHZ/'+module+'.lean','-o','.lake/build/lib/lean/RigidGHZ/'+module+'.olean']
 r=subprocess.run(cmd,cwd=root,capture_output=True,text=True)
 with log.open('a') as f:f.write('\n'+module+'\n'+r.stdout+r.stderr+'\nExit '+str(r.returncode)+'\n')
 if r.stdout:print(r.stdout,flush=True)
 if r.stderr:print(r.stderr,flush=True)
 if r.returncode:
  print('FAILED '+module+' '+str(r.returncode),flush=True)
  sys.exit(r.returncode)
 print('DONE '+module,flush=True)
