"""Reuse the accepted E22446 proof prefix and export the E22591 opposite operation."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CERTIFICATE = ROOT/'proofs/Equation22591/JudgeSubmission.lean'
MARKER = '\nnamespace submission\nabbrev CM :='


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            digest.update(block)
    return digest.hexdigest()


def export_parts():
    original = ROOT/'proofs/Equation22446/JudgeSubmission.lean'
    receipt = json.loads((ROOT/'proofs/validation/aurora/Equation22446/latest.json').read_text())
    request = json.loads((ROOT/'proofs/validation/aurora/Equation22446/request.json').read_text())
    assert receipt['result']['status'] == 'accepted'
    assert request['code'].encode() == original.read_bytes()
    source = original.read_text()
    assert source.count(MARKER) == 1
    prefix = source[:source.index(MARKER)]
    wrapper = (ROOT/'proofs/Equation22591/InfiniteModel.lean').read_text()
    wrapper = '\n'.join(line for line in wrapper.splitlines()
        if line != 'prelude' and not line.startswith('import '))
    wrapper = wrapper.replace('Equation22446Lineage', 'submission.Equation22446Lineage')
    assert not re.search(r'\b(?:syntax|sorry|admit|sorryAx|axiom)\b', prefix+wrapper)
    return prefix, wrapper


def export():
    prefix, wrapper = export_parts()
    text = prefix+'\n'+wrapper+'\n'
    if CERTIFICATE.exists():
        assert CERTIFICATE.read_text() == text, 'Refuse to overwrite a different certificate'
    else:
        CERTIFICATE.write_text(text)
    (HERE/'ExportWrapper.lean').write_text(
        'prelude\nimport JudgeProblem\nimport ExportLineageSyntaxModel\n'+wrapper+'\n')
    return CERTIFICATE


if __name__ == '__main__':
    path = export()
    print(json.dumps(dict(certificate=str(path.relative_to(ROOT)), bytes=path.stat().st_size,
                          sha256=sha(path))))
