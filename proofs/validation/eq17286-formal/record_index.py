"""Register only this pair and refresh current bilingual inventory summaries."""
import json,re
from audit import audit
from verify import ROOT,HERE,sha

def refresh_readmes(index):
    rows=index['equations']
    targets=[e for e in rows if e['equation'] in ('Equation17286','Equation28626')]
    accepted=len(targets)==2 and all(e.get('aurora_validation',{}).get('status')=='accepted'
        and e['aurora_validation']['certificate_sha256']==sha(ROOT/f'proofs/{e["equation"]}/InfiniteModel.lean')
        for e in targets)
    zh_remote=('两份独立证书随后均经远端 Judge 首次提交返回 **ACCEPTED**（关闭缓存），见[远端验收记录](proofs/validation/eq17286-formal/JUDGE.md)。'
               if accepted else '本批仅本地验证。')
    en_remote=('Both standalone certificates subsequently received **ACCEPTED** on their first remote Judge submission with caching disabled; see the [remote acceptance record](proofs/validation/eq17286-formal/JUDGE.md).'
               if accepted else 'This batch has local verification only.')
    finite=sum(bool(e.get('finite_proof')) for e in rows)
    models=sum(bool(e.get('infinite_model_proof')) for e in rows)
    infinity=sum(bool(e.get('explicit_infinity')) for e in rows)
    impossible=sum(bool(e.get('unrestricted_triviality_proof')) for e in rows)
    both=sum(bool(e.get('finite_proof') and e.get('infinite_model_proof')) for e in rows)
    fopen=[e for e in rows if not e.get('finite_proof')]
    iopen=[e for e in rows if not e.get('infinite_model_proof') and not e.get('unrestricted_triviality_proof')]
    def pairs(es):
        seen=set();out=[]
        for e in es:
            if e['equation'] in seen:continue
            a,b=e['equation'],e['dual'];seen.update((a,b))
            out.append(f'[{a}](proofs/{a}/README.md) / [{b}](proofs/{b}/README.md)')
        return '; '.join(out)
    for fn,zh in [('README.md',False),('README.zh-CN.md',True)]:
        path=ROOT/fn;text=path.read_text()
        for table in ('20.1','20.2','20.3'):
            es=[e for e in rows if e['table']==table]
            nf=sum(not e.get('finite_proof') for e in es)
            nm=sum(bool(e.get('infinite_model_proof')) for e in es)
            ni=sum(bool(e.get('unrestricted_triviality_proof')) for e in es)
            text=re.sub(r'^\| '+re.escape(table)+r' \|.*$',
                        f'| {table} | {len(es)} | {nf} | {nm} | {ni} | {len(es)-nm-ni} |',text,flags=re.M)
        total='合计' if zh else 'Total'
        text=re.sub(r'^\| \*\*'+total+r'\*\* \|.*$',
             f'| **{total}** | **130** | **{len(fopen)}** | **{models}** | **{impossible}** | **{len(iopen)}** |',text,flags=re.M)
        if zh:
            counts=f'当前已归档 **{finite} 份有限平凡性证书**。无限侧：**已有模型证书 {models} 条、已证不存在 {impossible} 条、待解 {len(iopen)} 条**，合计 130 条。已证不存在的 E5834/E40037 不计入待解。'
            current=f'''**截至 2026-09-14：有限侧剩 {len(fopen)} 条待解，无限侧剩 {len(iopen)} 条待解。** 单元素模型均存在；有限侧的任务仍是证明所有有限模型平凡或找到非平凡有限模型。

本批完成 **Equation17286 / Equation28626 两条 Austin 律**。辅助列关系树模型的完整原式、非平凡性和 Nat 单射通过八个空目录 Lean 4.33.1 编译单元。{zh_remote}累计 **{models} 份模型证书、{infinity} 份显式无限性证明、{both} 条两侧证书齐全的方程**。见[模型与成功复盘](proofs/Equation17286/MODEL.zh-CN.md)和[核验报告](proofs/validation/eq17286-formal/README.md)。

此前完成的 E12087/E33884 见[验收记录](proofs/validation/eq12087-formal/JUDGE.md)，E18137/E27863 见[归档报告](proofs/validation/2026-09-14-tree-dual/README.md)；各批本地与远端验证证据分别保留。

- **有限侧待解（{len(fopen)//2} 对、{len(fopen)} 条）**：{pairs(fopen)}。
- **无限侧待解（{len(iopen)//2} 对、{len(iopen)} 条）**：{pairs(iopen)}。'''
        else:
            counts=f'The archive contains **{finite} finite-triviality certificates**. The infinite case has **{models} model certificates, {impossible} proved impossible, and {len(iopen)} open**, totaling 130 equations. E5834/E40037 are proved impossible and excluded from the open count.'
            current=f'''**As of 2026-09-14: {len(fopen)} equations remain open in the finite case and {len(iopen)} in the infinite case.** One-element models always exist; the finite task is to prove all finite models trivial or construct a nontrivial finite model.

This update completes **Equation17286 / Equation28626 as two Austin laws**. The relational tree model proves each exact identity, nontriviality, and a Nat injection in eight fresh Lean 4.33.1 compilation units. {en_remote} Current totals are **{models} model certificates, {infinity} explicit infinitude proofs, and {both} equations with both certificates**. See the [model and retrospective](proofs/Equation17286/MODEL.zh-CN.md) and [verification report](proofs/validation/eq17286-formal/README.md).

Previous completions: [E12087/E33884 acceptance](proofs/validation/eq12087-formal/JUDGE.md) and [E18137/E27863 archive](proofs/validation/2026-09-14-tree-dual/README.md). Their local and remote evidence remains recorded separately.

- **Finite case open ({len(fopen)//2} dual pairs, {len(fopen)} equations)**: {pairs(fopen)}.
- **Infinite case open ({len(iopen)//2} dual pairs, {len(iopen)} equations)**: {pairs(iopen)}.'''
        for name,value in [('certificate-counts',counts),('current-proof-status',current)]:
            text,n=re.subn(f'<!-- {name}:start -->.*?<!-- {name}:end -->',
                           f'<!-- {name}:start -->\n{value}\n<!-- {name}:end -->',text,flags=re.S)
            assert n==1
        lines=[]
        for line in text.splitlines():
            for number in (17286,28626):
                if line.startswith(f'| [Equation{number}]'):
                    cells=line.split('|')
                    cells[-3]=(' 已校验（Lean + Judge） ' if zh else ' Verified (Lean + Judge) ') if accepted else (' 已校验（Lean） ' if zh else ' Verified (Lean) ')
                    cells[-2]=f' [InfiniteModel.lean](proofs/Equation{number}/InfiniteModel.lean) '
                    line='|'.join(cells)
            lines.append(line)
        path.write_text('\n'.join(lines)+'\n')

def main():
    s=audit(check_index=False);indexpath=ROOT/'proofs/index.json';before=sha(indexpath)
    index=json.loads(indexpath.read_text());targets=set(s['equations'])
    others=json.dumps([e for e in index['equations'] if e['equation'] not in targets],ensure_ascii=False)
    manifest=str((HERE/'summary.json').relative_to(ROOT));report=str((HERE/'README.md').relative_to(ROOT))
    for e in index['equations']:
        if e['equation'] not in targets:continue
        n=e['equation'].removeprefix('Equation')
        r=next(r for r in s['reports'] if r['module']==n+'-InfiniteModel')
        goal=f'proofs/{e["equation"]}/JudgeProblem.lean'
        e['infinite_model_proof']=dict(path=r['source'],sha256=r['sha256'],origin='local_formalization',
            validation='local_lean_recompiled_axioms_checked',source='All finite Nat-labelled binary trees; unique relational decoding and joint column-geometry induction',
            goal=f'Exact {e["equation"]}, nontriviality and an explicit Nat injection',dependencies={goal:sha(ROOT/goal)},report=report)
        e['explicit_infinity']=True;e['local_lean_validation']='passed_for_local_formalization'
        e['explicit_infinity_proof']=dict(path=r['source'],sha256=r['sha256'],theorem='submission.CM.tower_injective',validation='local_lean_recompiled_axioms_checked')
        e['model_compilation']=dict(status='passed',checked_sha256=r['sha256'],version=s['version'],log=r['log'],log_sha256=r['log_sha256'],axioms=r['axioms'],elapsed_seconds=r['elapsed_seconds'],sampled_peak_rss_mib=r['sampled_peak_rss_mib'],dependency_manifest=manifest)
        note='2026-09-14: 完整关系树模型与精确对偶完成；八个空目录编译单元核验原式、非平凡性和 Nat 单射。本批仅本地 Lean 验证，未调用远端 Judge。'
        if note not in e.setdefault('notes',[]):e['notes'].append(note)
    index.setdefault('local_formalizations',{}).setdefault('eq17286',{}).update(status='passed',equations=s['equations'],version=s['version'],report=report,manifest=manifest,manifest_sha256=sha(HERE/'summary.json'))
    assert others==json.dumps([e for e in index['equations'] if e['equation'] not in targets],ensure_ascii=False)
    assert sha(indexpath)==before,'Inventory changed during preparation; rerun.'
    refresh_readmes(index)
    files=set(s['source_hashes'])|{r['log'] for r in s['reports']}
    files.update(str(p.relative_to(ROOT)) for p in HERE.iterdir() if p.is_file())
    files.update({'proofs/Equation17286/README.md','proofs/Equation28626/README.md',
                  'proofs/Equation17286/MODEL.zh-CN.md','proofs/Equation17286/ResearchRetrospective-2026-09-14.md',
                  'proofs/README.md','README.md','README.zh-CN.md'})
    for p in files:index.setdefault('archived_files',{})[p]=sha(ROOT/p)
    index['updated_on']='2026-09-14'
    assert sha(indexpath)==before,'Inventory changed during README refresh; rerun.'
    indexpath.write_text(json.dumps(index,ensure_ascii=False,indent=2)+'\n')
    audit()
    print('Registered only Equation17286/Equation28626; refreshed current bilingual counts; preserved other equation entries.')

if __name__=='__main__':main()
