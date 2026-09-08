"""Build pinned REPL modules serially for a local interpreted protocol test."""

from pathlib import Path
import hashlib
import json
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import recompile_lean as compiler


def main():
    checkout = ROOT / '.build/judge-finite-extension/lean-repl'
    pinned = 'bbeedf38e0898869fc3b7c009e1ea877b46204e4'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip() == pinned
    custom = ROOT.parent / 'math-distill-equational-stage2/src/judge_v3/lean/REPL/Main.lean'
    (checkout / 'REPL/Main.lean').write_bytes(custom.read_bytes())
    (checkout / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    lib = checkout / '.lake/build/lib/lean'
    lib.mkdir(parents=True, exist_ok=True)
    compiler.RUN = OUT / 'repl-build'
    compiler.MEMORY_MIB = 2048
    compiler.RSS_MIB = 3072
    results = []
    visited = set()

    def build(module):
        if module in visited:
            return
        source = checkout / (module.replace('.', '/') + '.lean')
        for dep in re.findall(r'^import (REPL(?:\.[A-Za-z0-9_]+)*)', source.read_text(), re.M):
            build(dep)
        target = lib / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        record = compiler.compile_file(source, checkout, [lib], module, target)
        assert record['status'] == 'passed', record
        results.append(record)
        visited.add(module)

    build('REPL.Main')
    (checkout / 'Runner.lean').write_text('import REPL.Main\n')
    wrapper = checkout / 'repl-local'
    # This process is in the REPL pool's process group. The pool's existing
    # timeout/shutdown mechanism therefore also terminates the Lean child.
    wrapper.write_text('''#!/usr/bin/env python3
import os, signal, subprocess, sys, time
command = ['lean', '+leanprover/lean4:v4.33.1', '-j1', '-M2048',
           '-Dlinter.defProp=false', '--run', ''' + repr(str(checkout / 'Runner.lean')) + ''']
child = subprocess.Popen(command)
def stopped(sig, frame):
    raise SystemExit(128 + sig)
signal.signal(signal.SIGTERM, stopped)
signal.signal(signal.SIGINT, stopped)
peak = 0
try:
    while child.poll() is None:
        sample = subprocess.run(['ps', '-o', 'rss=', '-p', str(child.pid)], capture_output=True, text=True)
        rss = int(sample.stdout.strip() or 0) / 1024
        peak = max(peak, rss)
        if rss > 3072:
            child.kill()
            child.wait()
            print('RSS limit exceeded', file=sys.stderr)
            break
        time.sleep(.2)
finally:
    if child.poll() is None:
        child.kill()
    code = child.wait()
    with open(''' + repr(str(OUT / 'repl-build/runtime-memory.jsonl')) + ''', 'a') as f:
        import json
        f.write(json.dumps(dict(lean_pid=child.pid, peak_rss_mib=peak, exit_code=code))+'\\n')
sys.exit(code if code >= 0 else 128-code)
''')
    wrapper.chmod(0o755)
    stage2 = ROOT.parent / 'math-distill-equational-stage2/third_party/equational-theories-lean-stage2'
    paths = [lib, ROOT / '.build/recompile/support', stage2 / '.lake/build/lib/lean',
             *sorted(stage2.glob('.lake/packages/*/.lake/build/lib/lean'))]
    env_file = checkout / 'repl.env'
    env_file.write_text('LEAN_PATH=' + ':'.join(map(str, paths)) + '\n')
    manifest = dict(upstream_commit=pinned, lean_version='4.33.1',
                    custom_main=str(custom), custom_main_sha256=hashlib.sha256(custom.read_bytes()).hexdigest(),
                    mode='lean_interpreter_custom_staged_v2', wrapper=str(wrapper), env_file=str(env_file),
                    lean_modules=len(results), build_peak_rss_mib=max(r['peak_rss_mib'] for r in results))
    (compiler.RUN / 'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps(manifest, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
