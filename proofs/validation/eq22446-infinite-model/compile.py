"""Rebuild the archived E22446 model serially with bounded memory; no Mathlib build."""
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time

from verify import HERE, ROOT, verify


def main():
    verify()
    summary = json.loads((HERE/'summary.json').read_text())
    with tempfile.TemporaryDirectory(prefix='eq22446-lean-') as directory:
        build = Path(directory)
        env = dict(os.environ, LEAN_PATH=str(build))
        for record in summary['results']:
            source = ROOT/record['source']
            relative = source.relative_to(ROOT/'proofs/Equation22446')
            if relative.parts[0] == 'Lean':
                relative = Path(*relative.parts[1:])
            output = (build/relative).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            log = build/'compiler.log'
            args = ['lean', '+leanprover/lean4:v4.33.1', '-j1', '-M192',
                '-DwarningAsError=true', '-Dlinter.unusedVariables=false',
                '-Dlinter.unusedSimpArgs=false', '-Dlinter.defProp=false',
                '-o', str(output), str(source)]
            start = time.monotonic()
            peak = 0.0
            stopped = None
            with log.open('w') as stream:
                process = subprocess.Popen(args, cwd=ROOT, env=env, stdout=stream,
                    stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    while process.poll() is None:
                        sample = subprocess.run(['ps', '-o', 'rss=', '-p', str(process.pid)],
                                                capture_output=True, text=True)
                        peak = max(peak, int(sample.stdout.strip() or 0)/1024)
                        if peak > 256:
                            stopped = 'RSS limit'
                        if time.monotonic()-start > 120:
                            stopped = 'time limit'
                        if stopped:
                            os.killpg(process.pid, signal.SIGKILL)
                            break
                        time.sleep(0.1)
                    process.wait()
                finally:
                    if process.poll() is None:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
            if process.returncode or stopped:
                print(log.read_text()[-8000:])
                raise SystemExit(f'{record["module"]}: {stopped or "Lean failure"}')
            print(f'{record["module"]}: passed (sampled RSS {peak:.2f} MiB)', flush=True)
    print('PASS: 58 modules rebuilt; temporary compiler output removed.')


if __name__ == '__main__':
    main()
