"""Export checked modular proofs as standalone Judge certificates."""
from verify import ROOT, module_order


def certificate_parts(eq):
    source_dir, order = module_order()
    imports = {'import JudgeProblem'}
    sections = []
    for name in order:
        lines = (source_dir / (name + '.lean')).read_text().splitlines()
        imports.update(line for line in lines if line.startswith('import Init.'))
        body = '\n'.join(line for line in lines
                         if line != 'prelude' and not line.startswith(('import ', '#print axioms ')))
        sections.append('/- Checked module: ' + name + ' -/\n' + body)
    wrapper = (ROOT / 'proofs' / eq / 'InfiniteModel.lean').read_text()
    wrapper = '\n'.join(line for line in wrapper.splitlines()
                        if line != 'prelude' and not line.startswith('import '))
    rename = lambda text: text.replace('Austin12087Trace', 'submission.Austin12087Trace')
    return sorted(imports), list(zip(order, map(rename, sections))), rename(wrapper)


def certificate_text(eq):
    imports, sections, wrapper = certificate_parts(eq)
    return ('prelude\n' + '\n'.join(imports) + '\nset_option Elab.async false\n\n'
            + '\n\n'.join(body for _, body in sections) + '\n\n' + wrapper + '\n')


if __name__ == '__main__':
    for eq in ('Equation12087', 'Equation33884'):
        path = ROOT / 'proofs' / eq / 'JudgeSubmission.lean'
        text = certificate_text(eq)
        if path.exists():
            assert path.read_text() == text, 'Refuse to overwrite a different export'
        else:
            path.write_text(text)
        print(eq, len(text.encode()), 'bytes')
