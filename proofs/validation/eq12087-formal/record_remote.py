"""Register only verified remote acceptances for E12087 and its dual."""
import json
from audit_judge import remote_audit
from verify import ROOT, HERE, sha


def main():
    targets = ('Equation12087', 'Equation33884')
    audits = {eq: remote_audit(eq, check_index=False) for eq in targets}
    path = ROOT / 'proofs/index.json'
    before = sha(path)
    index = json.loads(path.read_text())
    others = [e for e in index['equations'] if e['equation'] not in targets]
    files = set()
    for entry in index['equations']:
        eq = entry['equation']
        if eq not in targets:
            continue
        out = ROOT / 'proofs/validation/aurora' / eq
        receipt = json.loads((out / 'latest.json').read_text())
        result = receipt['result']
        state = json.loads((out / 'submission-state.json').read_text())
        entry['aurora_validation'] = dict(status='accepted', job_id=receipt['job_id'],
            base_url=state['base_url'], certificate=str((out / 'certificate.lean').relative_to(ROOT)),
            certificate_sha256=audits[eq]['certificate_sha256'],
            result=audits[eq]['receipt'], result_sha256=audits[eq]['receipt_sha256'],
            request_sha256=audits[eq]['request_sha256'],
            execution_fingerprint=result.get('execution_fingerprint'),
            proof_policy_rev=result.get('proof_policy_rev'), finished_at=receipt.get('finished_at'))
        note = ('2026-09-14: 导出证书逐段本地编译及公理检查通过，完整单文件经远端 Judge 返回 ACCEPTED；'
                '任务 ' + receipt['job_id'] + '。远端验证精确原式与非平凡性，显式无限性同时由本地 Nat 单射证明。')
        if note not in entry.setdefault('notes', []):
            entry['notes'].append(note)
        files.update(str(p.relative_to(ROOT)) for p in out.rglob('*') if p.is_file())
        files.update({f'proofs/{eq}/README.md', f'proofs/{eq}/JudgeSubmission.lean'})
    index['local_formalizations']['eq12087'].update(remote_judge_status='accepted',
        remote_job_ids={eq: audits[eq]['remote_job_id'] for eq in targets},
        standalone_manifest=str((HERE / 'judge-local/summary.json').relative_to(ROOT)),
        standalone_manifest_sha256=sha(HERE / 'judge-local/summary.json'))
    for eq in targets:
        result = remote_audit(eq, check_index=False)
        (HERE / (eq + '-remote-audit.json')).write_text(json.dumps(result, indent=2) + '\n')
    files.update(str(p.relative_to(ROOT)) for p in HERE.rglob('*')
                 if p.is_file() and '__pycache__' not in p.parts)
    files.update({'proofs/validation/aurora/README.md', 'proofs/README.md',
        'proofs/Equation12087/MODEL.zh-CN.md', 'README.md', 'README.zh-CN.md'})
    for name in files:
        index.setdefault('archived_files', {})[name] = sha(ROOT / name)
    index['updated_on'] = '2026-09-14'
    assert others == [e for e in index['equations'] if e['equation'] not in targets]
    assert sha(path) == before, 'Index changed; rerun on current state'
    path.write_text(json.dumps(index, ensure_ascii=False, indent=2) + '\n')
    for eq in targets:
        remote_audit(eq)
    print('REGISTERED ACCEPTED: Equation12087 and Equation33884; other entries preserved')


if __name__ == '__main__':
    main()
