"""Fresh modular and independent certificate builds, with exact axiom audits."""
import hashlib,json,os,re,signal,subprocess,tempfile,time
from pathlib import Path
from export_certificate import ROOT,HERE,MODULES,FORMULAS,certificate_text,problem_text

ALLOWED={'propext','Classical.choice','Quot.sound'}
EXPECTED={
 'TreeSchema':{'column_of_step','target_of_step','conditional_source',
               'inherited_target_is_right_child','explicit_right_child_target','right_child_exclusion_false'},
 'TreeBounds':{'column_rank','target_rank','column_ne_self','target_point_unique','target_inherit_cases'},
 'TreeGeometry':{'column_geometry','column_fork_unique','column_triangle_free',
                 'target_right_empty','code_output_unique'},
 'TreeModel':{'column_no_three_cycle','column_prefix_no_target','step_middle_no_code',
              'step_outer_no_code','source_law_explicit','nontrivial','infinite_model',
              'dual_source_law_explicit','dual_infinite_model'},
}

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(65536),b''):h.update(chunk)
    return h.hexdigest()

def process_tree_rss(pid):
    parents={};rss={}
    with subprocess.Popen(['ps','-axo','pid=,ppid=,rss='],stdout=subprocess.PIPE,text=True) as p:
        for line in p.stdout:
            a,b,c=map(int,line.split());parents[a]=b;rss[a]=c
    children={pid}
    while True:
        more=children|{a for a,b in parents.items() if b in children}
        if more==children:return sum(rss.get(a,0) for a in children)
        children=more

def compile_one(label,src,build,module,expected):
    cmd=['lean','+leanprover/lean4:v4.33.1','-j1','-M128','-DwarningAsError=true',
         '-Dlinter.unusedVariables=false','-o',str(build/f'{module}.olean'),str(src)]
    log=HERE/'logs'/f'{label}.log';log.parent.mkdir(exist_ok=True)
    begin=time.monotonic();peak=0;stop=None
    with log.open('w') as out:
        p=subprocess.Popen(cmd,cwd=ROOT,env=dict(os.environ,LEAN_PATH=str(build)),
                           stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while p.poll() is None:
                peak=max(peak,process_tree_rss(p.pid))
                if peak>192*1024 or time.monotonic()-begin>30:
                    stop='rss_or_time_limit';os.killpg(p.pid,signal.SIGKILL);break
                time.sleep(.05)
            code=p.wait()
        finally:
            if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait()
    text=log.read_text()
    if code!=0 or stop:raise RuntimeError((label,stop,text[:3000]))
    axioms={name:[] for name in re.findall(r"'([^']+)' does not depend on any axioms",text)}
    for name,used in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        axioms[name]=[a.strip() for a in used.split(',')]
    assert set(axioms)==expected,(label,axioms,expected)
    assert all(set(a)<=ALLOWED for a in axioms.values())
    assert 'sorryAx' not in text
    return {'module':label,'status':'passed','exit_code':code,'source':str(src.relative_to(ROOT)),
            'sha256':sha(src),'log':str(log.relative_to(ROOT)),'log_sha256':sha(log),
            'axioms':axioms,'command':cmd,'elapsed_seconds':round(time.monotonic()-begin,3),
            'sampled_peak_rss_mib':round(peak/1024,2)}

def main():
    sources=[];reports=[]
    for name in MODULES:sources.append(ROOT/'proofs/Equation17286'/f'{name}.lean')
    for n in FORMULAS:
        folder=ROOT/f'proofs/Equation{n}'
        assert (folder/'JudgeProblem.lean').read_text()==problem_text(n)
        assert (folder/'InfiniteModel.lean').read_text()==certificate_text(n)
        sources.extend([folder/'JudgeProblem.lean',folder/'InfiniteModel.lean'])
    for src in sources:
        assert not re.search(r'\b(sorry|admit|sorryAx|unsafe|native_decide|axiom)\b',src.read_text()),src
    with tempfile.TemporaryDirectory(prefix='eq17286-modules-') as d:
        for name in MODULES:
            reports.append(compile_one(name,ROOT/'proofs/Equation17286'/f'{name}.lean',Path(d),name,
                                       {'Equation17286Tree.'+t for t in EXPECTED[name]}))
    for n in FORMULAS:
        with tempfile.TemporaryDirectory(prefix=f'eq{n}-independent-') as d:
            folder=ROOT/f'proofs/Equation{n}'
            reports.append(compile_one(f'{n}-JudgeProblem',folder/'JudgeProblem.lean',Path(d),'JudgeProblem',set()))
            inf='infinite_model' if n==17286 else 'dual_infinite_model'
            reports.append(compile_one(f'{n}-InfiniteModel',folder/'InfiniteModel.lean',Path(d),'InfiniteModel',
                {'submission','submission.CM.tower_injective','submission.Equation17286Tree.'+inf}))
    result={'status':'passed','classification':'nontrivial_infinite_model','version':'4.33.1',
            'equations':[f'Equation{n}' for n in FORMULAS],'source_laws':FORMULAS,
            'fresh_directories':3,'reused_olean_files':False,'modules_checked':len(reports),
            'source_hashes':{str(s.relative_to(ROOT)):sha(s) for s in sources},'reports':reports,
            'remote_judge_called':False,'limits':{'lean_memory_mib':128,'rss_stop_mib':192,'seconds':30},
            'sampled_peak_rss_mib':max(r['sampled_peak_rss_mib'] for r in reports),
            'seconds':round(sum(r['elapsed_seconds'] for r in reports),3)}
    (HERE/'summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('reports','source_hashes')},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
