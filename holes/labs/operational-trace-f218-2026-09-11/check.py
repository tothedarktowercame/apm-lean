"""Offline retained-trace and boundary controls; never changes the real trace."""
import copy, hashlib, json, pathlib, subprocess
root=pathlib.Path(__file__).resolve().parents[3]
out=pathlib.Path(__file__).resolve().parent
source=pathlib.Path('/home/joe/code/futon3c/data/apm-campaigns/jit-all-open-v3/jit-all-open-v3-f218/terminal/combined-operational-trace.json')
raw=source.read_bytes(); trace=json.loads(raw)
cases=[('observed',trace,1,'failed predicate: progressTraceValid')]
for elapsed,expected in [(300000,0),(300001,1)]:
 t=copy.deepcopy(trace);t['progressObservations'][0]['elapsedMs']=elapsed
 cases.append(('synthetic-boundary-'+str(elapsed),t,expected,'ACCEPTED' if expected==0 else 'failed predicate: progressTraceValid'))
results=[]
for name,t,expected,marker in cases:
 p=out/(name+'.json');p.write_text(json.dumps(t,sort_keys=True)+'\n')
 cmd=['lake','env','lean','--run','DarkTower/APMCampaignTraceChecker.lean','--operational',str(p)]
 r=subprocess.run(cmd,cwd=root,text=True,capture_output=True,timeout=90)
 assert r.returncode==expected and marker in r.stdout+r.stderr,(name,r)
 results.append(dict(case=name,command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
(out/'results.json').write_text(json.dumps({'source':str(source),'source_sha256':hashlib.sha256(raw).hexdigest(),'cases':results,'scope':'Observed replay plus explicitly synthetic controls; no recovery or acceptance change.'},indent=2)+'\n')
print('PASS: retained F218 rejected; synthetic 300000ms accepted; 300001ms rejected')
