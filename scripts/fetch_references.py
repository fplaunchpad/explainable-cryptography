"""Restore the exact local source papers used in the Helios research notes."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Validate local files without downloading')
    parser.add_argument('--directory', type=Path, default=root / '_references')
    args = parser.parse_args()
    manifest = json.loads((root / 'docs/research/reference-papers.json').read_text())
    for entry in manifest:
        target = args.directory / entry['file']
        if target.exists():
            data = target.read_bytes()
        elif args.check:
            raise SystemExit(f'Missing reference: {target}')
        else:
            data = subprocess.run(
                ['curl', '--fail', '--location', '--silent', '--show-error',
                 '--max-time', '60', entry['url']],
                check=True, stdout=subprocess.PIPE,
            ).stdout
        digest = hashlib.sha256(data).hexdigest()
        if digest != entry['sha256']:
            raise SystemExit(f'Checksum mismatch for {target.name}; existing files were not replaced')
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        print(f'Checked {target.name}')


if __name__ == '__main__':
    main()
