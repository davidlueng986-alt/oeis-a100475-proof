"""Rebuild and verify in a fresh directory; compare deterministic bytes."""
import hashlib, json, pathlib, platform, shutil, subprocess, sys, tempfile
root = pathlib.Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='a100475-replay-') as tmp:
    dest = pathlib.Path(tmp)
    for name in ['build_certificate.cpp', 'verify_certificate.py']:
        shutil.copyfile(root/name, dest/name)
    commands = [
        ['g++', '-O2', '-std=c++17', '-Wall', '-Wextra', '-pedantic', 'build_certificate.cpp', '-o', 'build_certificate'],
        ['./build_certificate'],
        [sys.executable, 'verify_certificate.py']]
    outputs = []
    for cmd in commands:
        r = subprocess.run(cmd, cwd=dest, text=True, capture_output=True, check=True)
        outputs.append({'command': cmd, 'stdout': r.stdout, 'stderr': r.stderr, 'returncode': r.returncode})
    assert (dest/'certificate.tsv').read_bytes() == (root/'certificate.tsv').read_bytes()
    assert json.loads((dest/'verification.json').read_text()) == json.loads((root/'verification.json').read_text())
    result = {'passed': True, 'fresh_directory': True, 'certificate_bytes_match': True,
        'python': sys.version, 'platform': platform.platform(),
        'compiler': subprocess.check_output(['g++', '--version'], text=True).splitlines()[0],
        'certificate_sha256': hashlib.sha256((dest/'certificate.tsv').read_bytes()).hexdigest(),
        'commands': outputs}
(root/'clean_replay.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result))
