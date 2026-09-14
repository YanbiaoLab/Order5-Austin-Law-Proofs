"""Serial, memory-monitored Lean kernel checking of the E12857 construction."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT/'proofs/Equation12857/Lean'
BUILD = ROOT/'.build/eq12857'
LOGS = ROOT/'proofs/validation/eq12857-formal'
VERSION = 'leanprover/lean4:v4.33.1'

def check(name, memory, rss_limit, source=None, output=None, search=None, expected_axioms=None):
    source=source or SRC/(name+'.lean')
    output=output or BUILD/(name+'.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.unlink(missing_ok=True)
    log=LOGS/(name+'.log')
    args=['lean','+'+VERSION,'-j1',f'-M{memory}',
          '-DwarningAsError=true','-Dlinter.unusedVariables=false',
          '-Dlinter.unusedSimpArgs=false','-Dlinter.defProp=false',
          '-o',str(output),str(source)]
    search=search or [BUILD]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,search)))
    peak=0;reason=None;start=time.monotonic()
    with log.open('w') as f:
        proc=subprocess.Popen(args,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,
                              start_new_session=True)
        try:
            while proc.poll() is None:
                p=subprocess.run(['ps','-o','rss=','-p',str(proc.pid)],
                                 capture_output=True,text=True)
                rss=int(p.stdout.strip() or 0)/1024
                peak=max(peak,rss)
                if rss>rss_limit: reason='rss_limit'
                if time.monotonic()-start>120: reason='time_limit'
                if reason:
                    os.killpg(proc.pid,signal.SIGKILL)
                    break
                time.sleep(0.2)
            proc.wait()
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid,signal.SIGKILL)
                proc.wait()
    result={'module':name,'status':reason or ('passed' if proc.returncode==0 else 'failed'),
            'exit_code':proc.returncode,'elapsed_seconds':round(time.monotonic()-start,3),
            'peak_rss_mib':round(peak,2),'source':str(source.relative_to(ROOT)),
            'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'lean_version':VERSION,'memory_limit_mib':memory,'rss_limit_mib':rss_limit,
            'command':args,'lean_path':list(map(str,search)),'log':str(log.relative_to(ROOT))}
    if result['status']=='passed' and (name=='Audit' or name.endswith('-Submission')):
        reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text())
        axioms={n:[a.strip() for a in raw.split(',') if a.strip()] for n,raw in reports}
        expected=expected_axioms or ({'Austin12857.infinite_model','Austin12857.equation12857',
                   'Austin12857.equation33436','Austin12857.embed_injective',
                   'Austin12857.confluent','Austin12857.step_decreases'} if name=='Audit'
                  else {'submission','submission.CM.tower_injective'})
        if set(axioms)!=expected or any(set(v)-{'propext','Classical.choice','Quot.sound'}
                                       for v in axioms.values()):
            result['status']='axiom_audit_failed'
        result['axioms']=axioms
    (LOGS/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('module','status','elapsed_seconds','peak_rss_mib')}),flush=True)
    if result['status']!='passed':
        print(log.read_text()[:10000],flush=True)
        raise SystemExit(1)
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only',nargs='+')
    parser.add_argument('--wrappers-only',action='store_true')
    parser.add_argument('--memory-mib',type=int,default=768)
    parser.add_argument('--rss-mib',type=int,default=1024)
    args=parser.parse_args()
    BUILD.mkdir(parents=True,exist_ok=True)
    LOGS.mkdir(parents=True,exist_ok=True)
    names=[] if args.wrappers_only else args.only or ['Basic',*[f'Peak{i}' for i in range(1,11)],'Confluence','Model','Audit']
    results=[]
    for name in names:
        results.append(check(name,args.memory_mib,args.rss_mib))
    if not args.only:
        results.append(check('JudgeMagma',args.memory_mib,args.rss_mib,
                             ROOT/'proofs/support/JudgeMagma/Magma.lean',
                             BUILD/'JudgeMagma/Magma.olean'))
        for eq in ['Equation12857','Equation33436']:
            output=BUILD/eq
            for stem,label in [('JudgeProblem','Goal'),('InfiniteModel','Submission')]:
                results.append(check(eq+'-'+label,args.memory_mib,args.rss_mib,
                                     ROOT/'proofs'/eq/(stem+'.lean'),output/(stem+'.olean'),
                                     [output,BUILD]))
    if not args.only and not args.wrappers_only:
        manifest={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in sorted(SRC.glob('*.lean'))}
        support=ROOT/'proofs/support/JudgeMagma/Magma.lean'
        manifest[str(support.relative_to(ROOT))]=hashlib.sha256(support.read_bytes()).hexdigest()
        for eq in ['Equation12857','Equation33436']:
            for stem in ['JudgeProblem','InfiniteModel']:
                p=ROOT/'proofs'/eq/(stem+'.lean')
                manifest[str(p.relative_to(ROOT))]=hashlib.sha256(p.read_bytes()).hexdigest()
        summary={'status':'passed','lean_version':VERSION,'modules_checked':len(results),
                 'peak_rss_mib':max(r['peak_rss_mib'] for r in results),
                 'total_seconds':round(sum(r['elapsed_seconds'] for r in results),3),
                 'source_hashes':manifest,'results':results}
        (LOGS/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__': main()
