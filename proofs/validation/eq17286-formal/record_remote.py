"""Register audited remote acceptance for this pair, preserving other equations."""
import json
from audit_remote import audit, NUMBERS
from record_index import refresh_readmes
from verify import ROOT, HERE, sha


def main():
    report = audit(check_index=False)
    targets = {f'Equation{n}' for n in NUMBERS}
    audits = {r['equation']: r for r in report['equations']}
    path = ROOT / 'proofs/index.json'
    before = sha(path)
    index = json.loads(path.read_text())
    others = [e for e in index['equations'] if e['equation'] not in targets]
    files = set()
    for entry in index['equations']:
        equation = entry['equation']
        if equation not in targets:
            continue
        out = ROOT / 'proofs/validation/aurora' / equation
        receipt = json.loads((out / 'latest.json').read_text())
        state = json.loads((out / 'submission-state.json').read_text())
        result = receipt['result']
        entry['aurora_validation'] = dict(status='accepted', job_id=receipt['job_id'],
            base_url=state['base_url'], certificate=str((out / 'certificate.lean').relative_to(ROOT)),
            certificate_sha256=audits[equation]['certificate_sha256'],
            result=audits[equation]['receipt'], result_sha256=audits[equation]['receipt_sha256'],
            request_sha256=audits[equation]['request_sha256'],
            execution_fingerprint=result['execution_fingerprint'],
            proof_policy_rev=result['proof_policy_rev'], finished_at=receipt['finished_at'])
        note = ('2026-09-14: 精确独立无限模型证书经远端 Judge 首次提交返回 ACCEPTED，关闭缓存；任务 '
                + receipt['job_id'] + '。远端验收原式与非平凡性；同一证书中的 Nat 单射亦已通过本地 Lean 检查。')
        if note not in entry.setdefault('notes', []):
            entry['notes'].append(note)
        files.update(str(p.relative_to(ROOT)) for p in out.iterdir() if p.is_file())
    index['local_formalizations']['eq17286'].update(remote_judge_status='accepted',
        remote_job_ids={e: audits[e]['remote_job_id'] for e in sorted(targets)},
        remote_report=str((HERE / 'JUDGE.md').relative_to(ROOT)))
    (HERE / 'remote-audit.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    assert sha(path) == before, 'Index changed during preparation; rerun.'
    refresh_readmes(index)
    files.update(str(p.relative_to(ROOT)) for p in HERE.iterdir() if p.is_file())
    files.update({'README.md', 'README.zh-CN.md', 'proofs/README.md',
        'proofs/validation/aurora/README.md', 'proofs/Equation17286/README.md',
        'proofs/Equation28626/README.md', 'proofs/Equation17286/MODEL.zh-CN.md',
        'proofs/Equation17286/ResearchRetrospective-2026-09-14.md'})
    for name in files:
        index['archived_files'][name] = sha(ROOT / name)
    index['updated_on'] = '2026-09-14'
    assert others == [e for e in index['equations'] if e['equation'] not in targets]
    assert sha(path) == before, 'Index changed during README refresh; rerun.'
    temporary = path.with_suffix('.json.eq17286.tmp')
    temporary.write_text(json.dumps(index, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)
    audit()
    print('REGISTERED ACCEPTED: Equation17286 and Equation28626; other equation entries preserved.')


if __name__ == '__main__':
    main()
