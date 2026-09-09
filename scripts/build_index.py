"""Update README tables from the archived inventory; --check is read-only.

Uses only the standard library and hashes files in bounded chunks. This checks
saved evidence and links; it does not run Lean or submit certificates to Judge.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def digest(relative):
    h = hashlib.sha256()
    with (ROOT / relative).open('rb') as stream:
        for chunk in iter(lambda: stream.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def validate_record(value):
    if isinstance(value, list):
        for item in value:
            validate_record(item)
    elif isinstance(value, dict):
        if value.get('path') and value.get('sha256'):
            assert digest(value['path']) == value['sha256'], value['path']
        for key, item in value.items():
            if isinstance(item, str) and item.startswith('proofs/'):
                assert (ROOT / item).exists(), item
                expected = value.get(key + '_sha256')
                if expected:
                    assert digest(item) == expected, item
            elif key == 'dependencies' and isinstance(item, dict):
                for path, expected in item.items():
                    assert digest(path) == expected, path
            else:
                validate_record(item)


def validate(data):
    rows = data['equations']
    by_name = {row['equation']: row for row in rows}
    assert len(rows) == len(by_name) == 130
    assert Counter(row['table'] for row in rows) == {'20.1': 10, '20.2': 96, '20.3': 24}
    for row in rows:
        assert by_name[row['dual']]['dual'] == row['equation']
        validate_record(row)
        for proof_key, compilation_key in [('finite_proof', 'finite_compilation'),
                                           ('infinite_model_proof', 'model_compilation')]:
            compilation = row.get(compilation_key)
            if compilation and compilation.get('status') == 'passed':
                assert digest(row[proof_key]['path']) == compilation['checked_sha256'], row['equation']
        remote = row.get('aurora_validation')
        if remote:
            receipt = json.loads((ROOT / remote['result']).read_text())
            assert receipt['job_id'] == remote['job_id']
            assert receipt['result']['status'] == 'accepted'
            assert receipt['result']['error_code'] == 'ACCEPTED'
        if row.get('unrestricted_triviality_proof'):
            assert not row.get('infinite_model_proof')
    for path, expected in data['archived_files'].items():
        assert digest(path) == expected, path


def render(data, original):
    rows = data['equations']
    missing_finite = Counter(row['table'] for row in rows if not row.get('finite_proof'))
    missing_model = Counter(row['table'] for row in rows if not row.get('infinite_model_proof'))
    meanings = {'20.1': '已知 Austin 律：只有平凡有限模型，存在非平凡无限模型',
                '20.2': '已知只有平凡有限模型；原表中无限侧未知',
                '20.3': '原表中是否存在非平凡有限模型未知'}
    totals = Counter(row['table'] for row in rows)
    summary = ['| 原表 | 方程数 | 原表含义 | 尚无平凡有限 Lean 证书的方程数 | 尚无非平凡无限 Lean 证书的方程数 |',
               '|---|---:|---|---:|---:|']
    for table, meaning in meanings.items():
        summary.append(f'| {table} | {totals[table]} | {meaning} | {missing_finite[table]} | {missing_model[table]} |')
    excluded = sum(bool(row.get('unrestricted_triviality_proof')) for row in rows)
    count_note = ('<!-- certificate-counts:start -->\n'
                  f'当前已提交库存：平凡有限 Lean 证书 {sum(bool(r.get("finite_proof")) for r in rows)} 份，'
                  f'非平凡模型 Lean 证书 {sum(bool(r.get("infinite_model_proof")) for r in rows)} 份。'
                  '“尚无证书”按下方证书列统计，不包含尚未提交的本地文件。'
                  f'无限侧缺口中有 {excluded} 条已证明非平凡模型不可能存在，不属于待补证明。\n'
                  '<!-- certificate-counts:end -->')
    text, count = re.subn(r'^\| 原表 \|[^\n]*\n(?:\|[^\n]*\n)+', '\n'.join(summary) + '\n',
                          original, count=1, flags=re.M)
    assert count == 1
    if '<!-- certificate-counts:start -->' in text:
        text = re.sub(r'<!-- certificate-counts:start -->.*?<!-- certificate-counts:end -->',
                      count_note, text, flags=re.S)
    else:
        end = text.index(summary[-1]) + len(summary[-1])
        text = text[:end] + '\n\n' + count_note + text[end:]
    details = []
    for row in rows:
        name = row['equation']
        finite = row.get('finite_proof')
        model = row.get('infinite_model_proof')
        finite_link = f'[{Path(finite["path"]).name}]({finite["path"]})' if finite else '未收录'
        model_link = f'[{Path(model["path"]).name}]({model["path"]})' if model else '未收录'
        model_status = '未收录'
        if model:
            checked = (row.get('model_compilation', {}).get('status') == 'passed'
                       or row.get('aurora_validation', {}).get('status') == 'accepted')
            model_status = '已校验' if checked else '历史 accepted'
        unrestricted = row.get('unrestricted_triviality_proof')
        if unrestricted:
            model_status = f'[已证不存在]({unrestricted["path"]})'
            model_link = '不可能存在'
        details.append(f'| [{name}](proofs/{name}/README.md) | {row["dual"]} | {row["table"]} | '
                       f'{row["finite_math"]} | {finite_link} | {model_status} | {model_link} |')
    text, count = re.subn(r'^\| \[Equation[^\n]*(?:\n\| \[Equation[^\n]*)*',
                          '\n'.join(details), text, count=1, flags=re.M)
    assert count == 1
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT / 'proofs/index.json').read_text())
    validate(data)
    path = ROOT / 'README.md'
    original = path.read_text()
    rendered = render(data, original)
    for link in re.findall(r'\]\(([^)]+)\)', rendered):
        if '://' not in link and not link.startswith('#'):
            assert (ROOT / link.split('#')[0]).exists(), link
    if args.check:
        assert original == rendered, 'README tables differ from inventory'
    else:
        path.write_text(rendered)
        if 'README.md' in data['archived_files']:
            data['archived_files']['README.md'] = digest('README.md')
            (ROOT / 'proofs/index.json').write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    print('PASS: 130 equations, evidence hashes, accepted receipts, README links and inventory tables')


if __name__ == '__main__':
    main()
