"""Export the verified E22446 import closure into the Judge participant namespace."""
import json

from check_22446_infinite_model import c, import_order, sha

ROOT = c.ROOT
DEST = ROOT/'proofs/Equation22446/JudgeSubmission.lean'


def certificate_parts():
    audit = json.loads((ROOT/'proofs/validation/eq22446-infinite-model/summary.json').read_text())
    assert audit['status'] == 'passed' and audit['model_proved']
    order, core = import_order()
    assert len(order) == 58
    for _, p in order:
        assert sha(p) == audit['source_hashes'][str(p.relative_to(ROOT))], p

    def rename(body):
        for namespace in ['Equation22446Guarded', 'Equation22446Lineage']:
            body = body.replace(namespace, 'submission.'+namespace)
        return body

    sections = []
    for name, source in order:
        if name in {'JudgeMagma.Magma', 'JudgeProblem', 'InfiniteModel'}:
            continue
        body = '\n'.join(line for line in source.read_text().splitlines()
            if line != 'prelude' and not line.startswith(('import ', '#print axioms ')))
        sections.append((name, '/- Checked source module: '+name+' -/\n'+rename(body)))
    wrapper = (ROOT/'proofs/Equation22446/InfiniteModel.lean').read_text()
    wrapper = '\n'.join(line for line in wrapper.splitlines()
                       if line != 'prelude' and not line.startswith('import '))
    wrapper = wrapper.replace('noncomputable instance : Magma CM :=',
                              'noncomputable instance modelMagma : Magma CM :=')
    wrapper = wrapper.replace('inferInstance', 'submission.modelMagma')
    return ['import '+name for name in core], sections, rename(wrapper)


def certificate_text():
    common, sections, wrapper = certificate_parts()
    return ('prelude\nimport JudgeProblem\n'+'\n'.join(common)
            +'\nset_option Elab.async false\n\n'
            +'\n\n'.join(body for _, body in sections)+'\n\n'+wrapper+'\n')


def main():
    body = certificate_text()
    if DEST.exists():
        assert DEST.read_text() == body, 'Preserve a differing export before changing it'
    else:
        DEST.write_text(body)
    print(json.dumps(dict(path=str(DEST.relative_to(ROOT)), bytes=DEST.stat().st_size,
                          sha256=sha(DEST))))


if __name__ == '__main__':
    main()
