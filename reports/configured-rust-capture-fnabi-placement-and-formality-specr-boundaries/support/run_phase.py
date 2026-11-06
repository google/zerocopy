"""Capture an exact pinned Cargo phase, enforcing the parent's1GiB target budget."""
import argparse, hashlib, json, os, pathlib, signal, subprocess, time

def size_bytes(root):
    total = 0
    if root.exists():
        for parent, dirs, files in os.walk(root, followlinks=False):
            for name in files:
                path = pathlib.Path(parent)/name
                try:
                    if not path.is_symlink(): total += path.stat().st_size
                except FileNotFoundError: pass
    return total

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--toolchain', type=pathlib.Path, required=True)
    ap.add_argument('--phase', required=True)
    ap.add_argument('cargo_args', nargs=argparse.REMAINDER)
    a = ap.parse_args()
    root = pathlib.Path(__file__).resolve().parent
    tool = a.toolchain.resolve(strict=True)
    logs = root/'phase-logs'; logs.mkdir(exist_ok=True)
    stem = logs/a.phase
    if stem.with_suffix('.json').exists() or stem.with_suffix('.stdout').exists():
        raise ValueError('new phase name required; never overwrite old outcome')
    args = a.cargo_args
    if args and args[0]=='--': args=args[1:]
    env = os.environ.copy()
    (root/'tmp').mkdir(exist_ok=True)
    env.update(CARGO_HOME=str(root/'cargo-home'), CARGO_TARGET_DIR=str(root/'target'),
               TMPDIR=str(root/'tmp'), CLANG_MODULE_CACHE_PATH=str(root/'clang-cache'),
               RUSTUP_HOME=str(tool.parent.parent),
               RUSTUP_TOOLCHAIN='nightly-2026-04-01',
               RUSTC=str(tool/'bin/rustc'), RUSTDOC=str(tool/'bin/rustdoc'),
               CARGO_BUILD_JOBS='1', CARGO_INCREMENTAL='0',
               FORMALITY_RUN_RUSTC='0',
               CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0')
    env['PATH']=str(tool/'bin')+os.pathsep+env.get('PATH','')
    # Explicit executable paths avoid triggering rustup installation from source rust-toolchain.toml.
    command=[str(tool/'bin/cargo')]+args
    before=time.monotonic_ns(); peak=0; stop=None
    with stem.with_suffix('.stdout').open('xb') as stdout, stem.with_suffix('.stderr').open('xb') as stderr:
        proc=subprocess.Popen(command,cwd=root/'source',env=env,stdout=stdout,stderr=stderr,
                              start_new_session=True)
        while proc.poll() is None:
            peak=max(peak,size_bytes(root/'target'))
            if peak>1024**3: stop='target exceeds parent1GiB bound'
            if time.monotonic_ns()-before>600*10**9: stop='phase exceeds600second owned bound'
            if stop:
                os.killpg(proc.pid,signal.SIGTERM)
                try: proc.wait(timeout=10)
                except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                break
            time.sleep(1)
    peak=max(peak,size_bytes(root/'target'))
    raw=stem.with_suffix('.stdout').read_bytes()+stem.with_suffix('.stderr').read_bytes()
    if any(x in raw for x in [b'panicked at',b'assertion failed',b'Assertion failed']):
        stop='unexpected panic/assertion; stop affected path for diagnosis'
    record=dict(command=command,environment_overrides={k:env[k] for k in
                ['CARGO_HOME','CARGO_TARGET_DIR','TMPDIR','CLANG_MODULE_CACHE_PATH','RUSTUP_HOME','RUSTUP_TOOLCHAIN','RUSTC','RUSTDOC','CARGO_BUILD_JOBS','FORMALITY_RUN_RUSTC',
                 'CARGO_INCREMENTAL','CARGO_PROFILE_DEV_DEBUG','CARGO_PROFILE_TEST_DEBUG']},
                exit=proc.returncode,elapsed_ns=time.monotonic_ns()-before,
                peak_target_bytes=peak,operational_stop=stop,
                source_lock_sha256=hashlib.sha256((root/'source/Cargo.lock').read_bytes()).hexdigest())
    stem.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
    if stop or proc.returncode: raise SystemExit(1)

if __name__=='__main__':main()
